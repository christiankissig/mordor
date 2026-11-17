(** {1 Büchi arithmetic}

    The questions MoRDor puts to the solver -- whether two locations may alias,
    whether a branch condition can hold, whether a justification's predicate is
    satisfiable -- are over the expressions of the program's events. With
    multiplication of two unknown values, these questions can encode polynomial
    equations over the naturals, and are undecidable in general.

    Büchi arithmetic, the first-order theory of the naturals with addition and
    the function V₂ (the largest power of 2 dividing a number), is decidable:
    its relations are those recognised by finite automata reading numbers in
    binary. It defines

    - addition, subtraction and comparisons;
    - multiplication by a constant, and division and remainder by a constant;
    - the bitwise operations [&], [|], [^] and [~], which programs use for flag
      words and tagged pointers.

    It does not define multiplication of two unknowns, nor division or remainder
    by an unknown.

    This module checks that every arithmetic expression in an event structure
    stays inside that fragment. A factor or divisor is allowed when it is a
    constant (it mentions no symbol and no register) or a truth value, which
    takes finitely many values ({!finite_range}). The check runs on the
    expressions as the interpreter built them, after registers have been
    replaced by their values, so [r1 * r2] with both registers holding numerals
    is a constant product and passes. *)

open Types

(** An expression outside the fragment, and why. *)
type violation = {
  event : int;  (** The event whose expression it is. *)
  field : string;  (** Which expression of the event: location, value, ... *)
  term : expr;  (** The offending subterm. *)
  reason : string;
}

(** Whether [e] mentions no symbol and no register. *)
let rec is_closed = function
  | ENum _ | EBoolean _ -> true
  | ESymbol _ | EVar _ -> false
  | EBinOp (a, _, b) -> is_closed a && is_closed b
  | EUnOp (_, a) -> is_closed a
  | EOr es -> List.for_all is_closed es

(** Whether [e] takes finitely many values whatever its symbols are: a constant,
    or a truth value. A product with such a term, or a division by it, is a
    finite case split over its values, each case multiplying or dividing by a
    constant, so it stays in the fragment. [1 / !b], the idiom for undefined
    behaviour when [b] holds, is one. *)
let rec finite_range e =
  is_closed e
  ||
  match e with
  | EBoolean _ -> true
  | EUnOp ("!", _) -> true
  | EBinOp (_, ("=" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||"), _) -> true
  | EOr _ -> true
  | EUnOp ("-", a) -> finite_range a
  | _ -> false

(** The subterms of [e] outside the fragment, with the reason for each. *)
let rec offending (e : expr) : (expr * string) list =
  match e with
  | ENum _ | EBoolean _ | ESymbol _ | EVar _ -> []
  | EUnOp (_, a) -> offending a
  | EOr es -> List.concat_map offending es
  | EBinOp (a, op, b) ->
      let here =
        match op with
        | "*" when not (finite_range a || finite_range b) ->
            [ (e, "product of two non-constant terms") ]
        | ("/" | "%") when not (finite_range b) ->
            [
              ( e,
                Printf.sprintf "%s by a non-constant term"
                  (if op = "/" then "division" else "remainder")
              );
            ]
        | _ -> []
      in
        here @ offending a @ offending b

(** Every expression of the structure outside the fragment: the locations,
    written values and branch conditions of the events, and the value
    restrictions recorded for them. *)
let check (structure : symbolic_event_structure) : violation list =
  let of_expr event field e =
    List.map (fun (term, reason) -> { event; field; term; reason }) (offending e)
  in
  let of_opt event field = function
    | Some e -> of_expr event field e
    | None -> []
  in
  let from_events =
    Hashtbl.fold
      (fun label (ev : event) acc ->
        of_opt label "location" ev.loc
        @ of_opt label "value" ev.wval
        @ of_opt label "condition" ev.cond
        @ acc
      )
      structure.events []
  in
  let from_restrictions =
    Hashtbl.fold
      (fun label guards acc ->
        List.concat_map (of_expr label "value restriction") guards @ acc
      )
      structure.restrict []
  in
  (* A guard is recorded on every event after its branch, so the same term
     turns up once per event. Report it once, at the first event. *)
  let seen = Hashtbl.create 16 in
    from_events @ from_restrictions
    |> List.sort (fun a b -> compare a.event b.event)
    |> List.filter (fun v ->
        let key = show_expr v.term in
          if Hashtbl.mem seen key then false
          else (
            Hashtbl.replace seen key ();
            true
          )
    )

let describe ?source_spans v =
  let where =
    match Option.bind source_spans (fun t -> Hashtbl.find_opt t v.event) with
    | Some span ->
        Printf.sprintf " (line %d, column %d)" span.start_line span.start_col
    | None -> ""
  in
    Printf.sprintf "event %d%s, %s: %s in %s" v.event where v.field v.reason
      (show_expr v.term)
