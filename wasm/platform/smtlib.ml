(** MoRDor's expressions as SMT-LIB assertions, for the browser's
    {!Smt_backend}, which hands Z3 text instead of building terms through its
    API (W4, #180).

    The translation follows [src/native/z3_translate.ml] term for term. Every
    term there is an integer or a boolean, except inside [&], [|] and [^], which
    go through 64-bit bitvectors and come back with [bv2int], so a term's sort
    here is one of the two. Symbols are declared as integer constants, as
    [Z3_translate.get_var] makes them. *)

open Types

type sort = Int | Bool

let symbol name =
  if String.contains name '|' || String.contains name '\\' then
    failwith ("Smtlib: symbol cannot be quoted in SMT-LIB: " ^ name);
  "|" ^ name ^ "|"

let numeral n =
  if Z.sign n < 0 then "(- " ^ Z.to_string (Z.neg n) ^ ")" else Z.to_string n

let app op args = "(" ^ op ^ " " ^ String.concat " " args ^ ")"

(* to_bitvec of z3_translate.ml: true -> 1, false -> 0; an integer -> int2bv *)
let to_bv64 (t, sort) =
  match sort with
  | Bool -> app "ite" [ t; "#x0000000000000001"; "#x0000000000000000" ]
  | Int -> app "(_ int2bv 64)" [ t ]

(* [var name] is called for every symbol, in the order z3_translate.ml's
   expr_to_z3 would first meet it. *)
let rec term var expr =
  match expr with
  | ENum n -> (numeral n, Int)
  | EVar v | ESymbol v ->
      var v;
      (symbol v, Int)
  | EBoolean b -> ((if b then "true" else "false"), Bool)
  | EBinOp (lhs, op, rhs) -> (
      let ((l, _) as lt) = term var lhs in
      let ((r, _) as rt) = term var rhs in
      let bool x = (x, Bool) and int x = (x, Int) in
        match op with
        | "=" -> bool (app "=" [ l; r ])
        | "!=" -> bool (app "not" [ app "=" [ l; r ] ])
        | ("<" | ">" | "<=" | ">=") as o -> bool (app o [ l; r ])
        | ("+" | "-" | "*") as o -> int (app o [ l; r ])
        | "/" -> int (app "div" [ l; r ])
        | ("&" | "|" | "^") as o ->
            let bvop =
              match o with
              | "&" -> "bvand"
              | "|" -> "bvor"
              | _ -> "bvxor"
            in
              int (app "bv2int" [ app bvop [ to_bv64 lt; to_bv64 rt ] ])
        | "&&" -> bool (app "and" [ l; r ])
        | "||" -> bool (app "or" [ l; r ])
        | "=>" -> bool (app "=>" [ l; r ])
        | _ -> failwith ("Unsupported operator: " ^ op)
    )
  | EUnOp ("!", rhs) -> (
      match term var rhs with
      | r, Bool -> (app "not" [ r ], Bool)
      | r, Int -> (app "=" [ r; "0" ], Bool)
    )
  | EUnOp ("~", rhs) -> (app "-" [ fst (term var rhs) ], Int)
  | EUnOp (op, _) -> failwith (Printf.sprintf "Unsupported unary operator %s" op)
  | EOr [] -> ("false", Bool)
  | EOr [ c ] -> term var c
  | EOr clauses ->
      (app "or" (List.map (fun c -> fst (term var c)) clauses), Bool)

(** [assertions var exprs] is an SMT-LIB script that declares the symbols
    [exprs] name and asserts each of [exprs]; [var] is told each symbol, in
    order. *)
let assertions var exprs =
  let named = ref [] in
  let var v =
    var v;
    named := v :: !named
  in
  let asserted = List.map (fun e -> app "assert" [ fst (term var e) ]) exprs in
  let decls =
    List.sort_uniq compare !named
    |> List.map (fun v -> Printf.sprintf "(declare-fun %s () Int)" (symbol v))
  in
    String.concat "\n" (decls @ asserted)
