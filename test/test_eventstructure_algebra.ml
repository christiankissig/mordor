open Eventstructures
open Types
open Uset

(** The laws of the {!EventStructure} algebra (R7), checked on random
    structures.

    A structure is generated as a random term over {!EventStructure}'s five
    operations, every event with a label of its own, and the laws are checked up
    to {!EventStructure.equal}. The generator is seeded, so a failure names the
    case that failed and that case can be run again. *)

module E = EventStructure
module S = SymbolicEventStructure

let cases = 60

(** {1 Random structures} *)

(* Where a structure is built: its labels shifted by [off] and its symbols
   carrying [suffix]. [home] is where the generator builds by default, and
   [away] is where {!placed} relabels to. *)
type place = { off : int; suffix : string }

let home = { off = 0; suffix = "" }
let away = { off = 1000; suffix = "7" }
let symbol_at place label = "α" ^ string_of_int label ^ place.suffix

(* An event of a random kind, carrying whatever a relabelling has to reach: a
   read or an allocation originates a symbol, a branch holds one in its guard,
   a write in its value. *)
let event ?(place = home) rng label : event =
  let symbol = symbol_at place in
  let sym = ESymbol (symbol label) in
  let base typ =
    { (Events.Event.create typ 0 ()) with label = label + place.off }
  in
    match Random.State.int rng 4 with
    | 0 -> { (base Read) with rval = Some (VSymbol (symbol label)) }
    | 1 -> { (base Write) with wval = Some sym; loc = Some (EVar "x") }
    | 2 -> { (base Branch) with cond = Some (EBinOp (sym, "=", ENum Z.zero)) }
    | _ ->
        {
          (base Malloc) with
          rval = Some (VSymbol (symbol label));
          loc = Some sym;
        }

let singleton ?(place = home) rng label =
  let symbol = symbol_at place in
  let env = Hashtbl.create 2 in
    Hashtbl.replace env ("r" ^ string_of_int label) (ESymbol (symbol label));
    (* A key that spells out a symbol, as a UB assumption's does. *)
    Hashtbl.replace env ("%ub:" ^ symbol label) (ESymbol (symbol label));
    E.singleton ~env
      ~loops:[ label mod 2 ]
      ~thread:(label mod 3) (event ~place rng label)
      [ EBinOp (ESymbol (symbol label), "!=", ENum Z.one) ]
      [ EBinOp (ESymbol (symbol label), ">", ENum Z.zero) ]

(* A random structure over labels of its own, taken from [next]. *)
let rec structure ?(place = home) rng next depth : E.t =
  let leaf () =
    let label = !next in
      incr next;
      singleton ~place rng label
  in
    if depth = 0 then leaf ()
    else
      let sub () = structure ~place rng next (depth - 1) in
        match Random.State.int rng 5 with
        | 0 -> leaf ()
        | 1 -> E.seq (sub ()) (sub ())
        | 2 -> E.seq ~join:true (sub ()) (sub ())
        | 3 -> E.choice (sub ()) (sub ())
        | _ -> E.par (sub ()) (sub ())

(* [check name law] runs [law] on [cases] triples of random structures with
   disjoint labels. *)
let check name (law : E.t -> E.t -> E.t -> bool) () =
  for seed = 1 to cases do
    let rng = Random.State.make [| seed |] in
    let next = ref 0 in
    let a = structure rng next 2 in
    let b = structure rng next 2 in
    let c = structure rng next 2 in
      if not (law a b c) then
        Alcotest.failf "%s fails for seed %d (%d, %d and %d events)" name seed
          (USet.size a.e) (USet.size b.e) (USet.size c.e)
  done

(** {1 The laws} *)

let operations =
  [
    ("seq", fun a b -> E.seq a b);
    ("join", fun a b -> E.seq ~join:true a b);
    ("choice", E.choice);
    ("par", E.par);
  ]

let associative op a b c = E.equal (op (op a b) c) (op a (op b c))
let commutative op a b _ = E.equal (op a b) (op b a)

let unit op a _ _ =
  E.equal (op (E.empty ()) a) a && E.equal (op a (E.empty ())) a

(* Sequencing is the one operation that is not commutative, and the generator
   would be a poor one if it could not tell. *)
let seq_is_ordered a b _ = not (E.equal (E.seq a b) (E.seq b a))

(* The relabelling a fragment undergoes when it is placed: labels shifted,
   symbols renamed, the symbol inside a key renamed with them. *)
let placed s =
  let rename name = name ^ away.suffix in
  let relab name = Some (rename name) in
  let env_key k =
    if String.length k > 4 && String.sub k 0 4 = "%ub:" then
      "%ub:" ^ rename (String.sub k 4 (String.length k - 4))
    else k
  in
    E.relabel ~off:away.off ~relab ~env_key s

(* What relabelling is for: a structure relabelled is the structure that would
   have been built there in the first place. The other laws cannot see an
   omission in [relabel] -- both sides of them go through it -- and this one
   can: a guard, a key or a table it did not reach still says [home]. *)
let relabel_is_building_elsewhere () =
  for seed = 1 to cases do
    let build place =
      structure ~place (Random.State.make [| seed |]) (ref 0) 3
    in
      if not (E.equal (placed (build home)) (build away)) then
        Alcotest.failf "relabel differs from building elsewhere for seed %d"
          seed
  done

let relabel_distributes op a b _ =
  E.equal (placed (op a b)) (op (placed a) (placed b))

let relabel_is_undone (a : E.t) _ _ =
  E.equal a (E.relabel ~off:(-5) (E.relabel ~off:5 a)) && E.equal a (E.relabel a)

let relabel_moves_everything (a : E.t) _ _ =
  let a' = placed a in
    USet.for_all (fun l -> l >= 1000) a'.e
    && Hashtbl.fold (fun _ l ok -> ok && l >= 1000) a'.origin true
    && Hashtbl.fold
         (fun name _ ok -> ok && String.ends_with ~suffix:"7" name)
         a'.origin true
    && (not (E.equal a a'))
    && USet.size a.e = USet.size a'.e

(* The facade says nothing the combinators did not: [dot] is [seq] after a
   singleton, and the combinators' [seq] is the join. *)
let dot_is_seq_of_singleton _ (b : E.t) _ =
  let rng = Random.State.make [| USet.size b.e |] in
  let label = 5000 in
  let ev = event rng label in
  let phi = [ EBoolean true ] in
    E.equal
      (S.dot ~thread:1 ev b phi [])
      (E.seq (E.singleton ~thread:1 ev phi []) b)

let join_is_combinators_seq a b _ = E.equal (S.seq a b) (E.seq ~join:true a b)

(* Operands are left as they were found. *)
let operands_untouched a b _ =
  let a0 = E.relabel a and b0 = E.relabel b in
    List.iter (fun (_, op) -> ignore (op a b)) operations;
    ignore (placed a);
    E.equal a a0 && E.equal b b0

let suite =
  let case name law = Alcotest.test_case name `Quick (check name law) in
    ( "EventStructure algebra",
      List.concat_map
        (fun (name, op) ->
          [
            case (name ^ " is associative") (associative op);
            case (name ^ " has empty as its unit") (unit op);
            case ("relabel distributes over " ^ name) (relabel_distributes op);
          ]
        )
        operations
      @ [
          case "choice is commutative" (commutative E.choice);
          case "par is commutative" (commutative E.par);
          case "seq is not commutative" seq_is_ordered;
          Alcotest.test_case "relabel is building elsewhere" `Quick
            relabel_is_building_elsewhere;
          case "relabel is undone by its inverse" relabel_is_undone;
          case "relabel moves every label and symbol" relabel_moves_everything;
          case "dot is seq after a singleton" dot_is_seq_of_singleton;
          case "the combinators' seq is the join" join_is_combinators_seq;
          case "operands are left untouched" operands_untouched;
        ]
    )
