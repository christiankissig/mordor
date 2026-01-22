(** Expression and Value module *)

open Types
open Uset

(** Check if string is a symbol *)
let is_symbol s =
  String.length s > 0
  && (String.contains greek_alpha s.[0] || String.contains zh_alpha s.[0])

let is_register_name s = String.length s > 0 && String.starts_with ~prefix:"r" s
let is_global_name s = (not (is_symbol s)) && not (is_register_name s)

(** Mutual recursion for Value and Expr *)
module rec Value : sig
  type t = value_type

  val number : Z.t -> value_type
  val symbol : string -> value_type
  val var : string -> value_type
  val boolean : bool -> value_type
  val equal : value_type -> value_type -> bool
  val get_symbols : value_type -> string list
  val subst : value_type -> value_type -> value_type -> value_type
  val is_number : value_type -> bool
  val is_not_var : value_type -> bool
  val to_string : value_type -> string
  val relabel : relab:(string -> string option) -> value_type -> value_type
end = struct
  type t = value_type

  let number n = VNumber n
  let symbol s = VSymbol s
  let var s = VVar s
  let boolean b = VBoolean b

  let equal (v1 : value_type) (v2 : value_type) =
    match (v1, v2) with
    | VNumber n1, VNumber n2 -> Z.equal n1 n2
    | VSymbol s1, VSymbol s2 -> String.equal s1 s2
    | VVar s1, VVar s2 -> String.equal s1 s2
    | VBoolean b1, VBoolean b2 -> b1 = b2
    | _ -> false

  let get_symbols = function
    | VSymbol s when is_symbol s -> [ s ]
    | _ -> []

  let to_string = function
    | VNumber n -> Z.to_string n
    | VSymbol s -> s
    | VVar v -> v
    | VBoolean b -> string_of_bool b

  let subst v a b =
    match v with
    | VSymbol _ when equal v a -> b
    | _ -> v

  let is_number = function
    | VNumber _ -> true
    | _ -> false

  let is_not_var = function
    | VVar _ -> false
    | _ -> true

  let relabel ~relab v =
    match v with
    | VSymbol s -> (
        match relab s with
        | Some s' -> VSymbol s'
        | None -> v
      )
    | _ -> v
end

and Expr : sig
  type t = expr

  val binop : t -> string -> t -> t
  val unop : string -> t -> t
  val var : string -> t
  val num : Z.t -> t
  val equal : t -> t -> bool
  val get_symbols : t -> string list
  val extract_registers : t -> string list
  val is_flat : t -> bool
  val inverse : t -> t
  val flipped : t -> t
  val subst : t -> string -> t -> t
  val to_string : t -> string
  val flatten : t -> t list
  val is_tautology : t -> bool
  val is_contradiction : t -> bool
  val is_value : t -> bool
  val is_var : t -> bool
  val is_register : t -> bool
  val is_expression : t -> bool
  val is_number : t -> bool
  val compare : t -> t -> int
  val sort_expr : t -> t
  val evaluate : ?env:(string -> t option) -> t -> t
  val evaluate_conjunction : ?env:(string -> t option) -> t list -> t list
  val to_value : t -> value_type option
  val of_value : value_type -> t
  val simplify_dnf : expr list list -> expr list list
  val relabel : ?relab:(string -> string option) -> expr -> expr
  val simplify_disjunction : expr list -> expr list -> expr list
end = struct
  type t = expr

  let binop lhs op rhs = EBinOp (lhs, op, rhs)
  let unop op rhs = EUnOp (op, rhs)
  let var v = EVar v
  let num n = ENum n

  let of_value = function
    | VNumber n -> ENum n
    | VSymbol s -> ESymbol s
    | VVar v -> EVar v
    | VBoolean b -> EBoolean b

  let is_value = function
    | ENum _ -> true
    | EVar _ -> true
    | ESymbol _ -> true
    | EBoolean _ -> true
    | _ -> false

  let to_value = function
    | ENum n -> Some (VNumber n)
    | EVar v -> Some (VVar v)
    | ESymbol s -> Some (VSymbol s)
    | EBoolean b -> Some (VBoolean b)
    | _ -> None

  let is_var = function
    | EVar _ -> true
    | _ -> false

  let is_register = function
    | EVar v -> is_symbol v
    | _ -> false

  let is_expression e = not (is_value e)

  let rec compare expr1 expr2 =
    match (expr1, expr2) with
    | ENum n1, ENum n2 -> Z.compare n1 n2
    | EBoolean b1, EBoolean b2 -> Bool.compare b1 b2
    | ESymbol s1, ESymbol s2 -> String.compare s1 s2
    | EVar v1, EVar v2 -> String.compare v1 v2
    | EBinOp (l1, op1, r1), EBinOp (l2, op2, r2) ->
        let c = String.compare op1 op2 in
          if c <> 0 then c
          else
            let c_l = compare l1 l2 in
              if c_l <> 0 then c_l else compare r1 r2
    | EUnOp (op1, r1), EUnOp (op2, r2) ->
        let c = String.compare op1 op2 in
          if c <> 0 then c else compare r1 r2
    | EOr clauses_1, EOr clauses_2 -> List.compare compare clauses_1 clauses_2
    | ESymbol _, _ -> -1
    | _, ESymbol _ -> 1
    | EVar _, _ -> -1
    | _, EVar _ -> 1
    | ENum _, _ -> -1
    | _, ENum _ -> 1
    | EBoolean _, _ -> -1
    | _, EBoolean _ -> 1
    | EBinOp _, _ -> -1
    | _, EBinOp _ -> 1
    | EUnOp _, _ -> -1
    | _, EUnOp _ -> 1

  (** Sort expressions for canonical form *)
  let rec sort_expr expr =
    match expr with
    | EUnOp (op, e) ->
        let e_sorted = sort_expr e in
          EUnOp (op, e_sorted)
    | EBinOp (lhs, op, rhs) when List.mem op [ "="; "!="; "+"; "*"; "&&"; "||" ]
      ->
        let lhs_sorted = sort_expr lhs in
        let rhs_sorted = sort_expr rhs in
          (* Commutative operations - sort operands by swapping if needed *)
          if compare lhs_sorted rhs_sorted > 0 then EBinOp (rhs, op, lhs)
            (* Swap operands *)
          else expr
    | EBinOp (lhs, op, rhs) ->
        let lhs_sorted = sort_expr lhs in
        let rhs_sorted = sort_expr rhs in
          EBinOp (lhs_sorted, op, rhs_sorted)
    | _ -> expr

  let equal e1 e2 = compare e1 e2 = 0

  let rec get_symbols = function
    | EVar v when is_symbol v -> [ v ]
    | ESymbol s when is_symbol s -> [ s ]
    | EBinOp (lhs, _, rhs) -> get_symbols lhs @ get_symbols rhs
    | EUnOp (_, rhs) -> get_symbols rhs
    | EOr clauses ->
        List.map get_symbols clauses
        |> List.flatten
        |> List.sort_uniq String.compare
    | _ -> []

  let rec extract_registers = function
    | EVar v when is_register_name v -> [ v ]
    | EBinOp (lhs, _, rhs) -> extract_registers lhs @ extract_registers rhs
    | EUnOp (_, rhs) -> extract_registers rhs
    | EOr clauses ->
        List.map extract_registers clauses
        |> List.flatten
        |> List.sort_uniq String.compare
    | _ -> []

  let is_flat = function
    | EBinOp (lhs, op, rhs) ->
        let comp_ops = [ "="; "!="; "<"; ">"; "<="; ">=" ] in
          List.mem op comp_ops && is_value lhs && is_value rhs
    | _ -> false

  let inverse = function
    | EBinOp (lhs, op, rhs) ->
        let inv_op =
          match op with
          | "=" -> "!="
          | "!=" -> "="
          | "<" -> ">="
          | ">=" -> "<"
          | ">" -> "<="
          | "<=" -> ">"
          | _ -> op
        in
          EBinOp (lhs, inv_op, rhs)
    | e -> e

  let flipped = function
    | EBinOp (lhs, op, rhs) ->
        let flip_op =
          match op with
          | "=" -> "="
          | "!=" -> "!="
          | "<" -> ">"
          | ">" -> "<"
          | ">=" -> "<="
          | "<=" -> ">="
          | "+" -> "+"
          | "*" -> "*"
          | _ -> op
        in
          if List.mem op [ "-"; "/"; "!"; "=>" ] then EBinOp (lhs, op, rhs)
          else EBinOp (rhs, flip_op, lhs)
    | e -> e

  let rec subst (e : expr) (a : string) (b : expr) =
    let eq x y = Value.equal x y in
      match e with
      | EBinOp (lhs, op, rhs) ->
          let new_lhs =
            match lhs with
            | EVar v -> if v = a then b else lhs
            | _ -> subst lhs a b
          in
          let new_rhs =
            match rhs with
            | EVar v -> if v = a then b else rhs
            | _ -> subst rhs a b
          in
            EBinOp (new_lhs, op, new_rhs)
      | EUnOp (op, rhs) ->
          let new_rhs =
            match rhs with
            | EVar v -> if v = a then b else rhs
            | _ -> subst rhs a b
          in
            EUnOp (op, new_rhs)
      | e -> e

  let rec to_string = function
    | ENum n -> Z.to_string n
    | EBoolean b -> string_of_bool b
    | ESymbol s -> s
    | EVar v -> v
    | EBinOp (lhs, op, rhs) ->
        Printf.sprintf "(%s %s %s)" (to_string lhs) op (to_string rhs)
    | EUnOp (op, rhs) -> Printf.sprintf "%s(%s)" op (to_string rhs)
    | EOr clauses -> List.map to_string clauses |> String.concat " ∨ "

  let rec flatten = function
    | EBinOp (lhs, "&&", rhs) ->
        let l_flat = flatten lhs in
        let r_flat = flatten rhs in
          l_flat @ r_flat
    | e -> [ e ]

  let rec is_tautology = function
    | EBoolean b -> b
    | EBinOp (lhs, op, rhs) when op = "&&" ->
        is_tautology lhs && is_tautology rhs
    | EBinOp (lhs, op, rhs) when op = "||" ->
        is_tautology lhs || is_tautology rhs
    | EBinOp (lhs, op, rhs) when op = "!=" -> (
        match (to_value lhs, to_value rhs) with
        | Some lv, Some rv -> not (Value.equal lv rv)
        | _ -> false
      )
    | EBinOp (lhs, op, rhs) when List.mem op [ "="; "<="; ">=" ] -> (
        match (to_value lhs, to_value rhs) with
        | Some lv, Some rv -> Value.equal lv rv
        | _ -> false
      )
    (* TODO more cases *)
    | _ -> false

  let is_contradiction = function
    | EBoolean b -> not b
    | EBinOp (lhs, op, rhs) -> (
        match (to_value lhs, to_value rhs) with
        | Some (VNumber lv), Some (VNumber rv) -> (
            match op with
            | "=" -> not (Z.equal lv rv)
            | "!=" -> Z.equal lv rv
            | "<" -> Z.geq lv rv
            | ">" -> Z.leq lv rv
            | "<=" -> Z.gt lv rv
            | ">=" -> Z.lt lv rv
            | _ -> false
          )
        | Some (VVar ln), Some (VVar rn) when ln = rn ->
            List.mem op [ "<"; ">"; "!=" ]
        | Some (VSymbol ln), Some (VSymbol rn) when ln = rn ->
            List.mem op [ "<"; ">"; "!=" ]
        | Some lv, Some rv -> (
            match op with
            | "!=" -> Value.equal lv rv
            | _ -> false
          )
        | _ -> false
      )
    (* TODO more cases *)
    | _ -> false

  let is_number = function
    | ENum _ -> true
    | _ -> false

  (** Evaluate expression with environment for variables *)
  let rec evaluate ?(env = fun _ -> None) expr =
    match expr with
    | ENum _ -> expr
    | EBoolean _ -> expr
    | ESymbol _ -> expr
    | EVar v -> (
        match env v with
        | Some v_expr -> v_expr
        | None -> expr
      )
    | EUnOp (op, rhs) when op = "!" -> (
        let r_val = evaluate ~env rhs in
          match r_val with
          | EBoolean b -> EBoolean (not b)
          | EUnOp ("!", r_val) -> r_val
          | EBinOp (l, op, r) -> (
              match op with
              | "=" -> EBinOp (l, "!=", r)
              | "!=" -> EBinOp (l, "=", r)
              | "<" -> EBinOp (l, ">=", r)
              | ">" -> EBinOp (l, "<=", r)
              | "<=" -> EBinOp (l, ">", r)
              | ">=" -> EBinOp (l, "<", r)
              | _ -> EUnOp (op, r_val)
            )
          | _ -> EUnOp (op, r_val)
      )
    | EUnOp (op, rhs) ->
        let r_val = evaluate ~env rhs in
          EUnOp (op, r_val)
    | EBinOp (lhs, "+", rhs) -> (
        let l_val = evaluate ~env lhs in
        let r_val = evaluate ~env rhs in
          match (l_val, r_val) with
          | EBinOp (l1, "-", r1), r2 when Expr.equal r1 r2 -> l1
          | ENum n1, _ when Z.equal n1 Z.zero -> r_val
          | _, ENum n2 when Z.equal n2 Z.zero -> l_val
          | ENum n1, ENum n2 -> ENum (Z.add n1 n2)
          | _ -> EBinOp (l_val, "+", r_val)
      )
    | EBinOp (lhs, "-", rhs) -> (
        let l_val = evaluate ~env lhs in
        let r_val = evaluate ~env rhs in
          match (l_val, r_val) with
          | EBinOp (l1, "+", r1), r2 when Expr.equal r1 r2 -> l1
          | EBinOp (l1, "+", r1), r2 when Expr.equal l1 r2 -> r1
          | _, ENum n2 when Z.equal n2 Z.zero -> l_val
          | ENum n1, ENum n2 -> ENum (Z.sub n1 n2)
          | _ -> EBinOp (l_val, "-", r_val)
      )
    | EBinOp (lhs, "*", rhs) -> (
        let l_val = evaluate ~env lhs in
        let r_val = evaluate ~env rhs in
          match (l_val, r_val) with
          | _, ENum n when n = Z.zero -> ENum Z.zero
          | _, ENum n when n = Z.one -> l_val
          | ENum n, _ when n = Z.zero -> ENum Z.zero
          | ENum n, _ when n = Z.one -> r_val
          | ENum n1, ENum n2 -> ENum (Z.mul n1 n2)
          | _ -> EBinOp (l_val, "*", r_val)
      )
    | EBinOp (lhs, "&&", rhs) -> (
        let l_val = evaluate ~env lhs in
        let r_val = evaluate ~env rhs in
          if Expr.equal l_val r_val then l_val
          else
            match (l_val, r_val) with
            | _, EBoolean false -> EBoolean false
            | EBoolean false, _ -> EBoolean false
            | _, EBoolean true -> l_val
            | EBoolean true, _ -> r_val
            | _ -> EBinOp (l_val, "&&", r_val)
      )
    | EBinOp (lhs, "||", rhs) -> (
        let l_val = evaluate ~env lhs in
        let r_val = evaluate ~env rhs in
          if Expr.equal l_val r_val then l_val
          else
            match (l_val, r_val) with
            | l_val, EBinOp (r1, "||", r2) when Expr.equal l_val r1 ->
                EBinOp (l_val, "||", r2) |> Expr.evaluate
            | l_val, EBinOp (r1, "||", r2) when Expr.equal l_val r2 ->
                EBinOp (l_val, "||", r1) |> Expr.evaluate
            | EBinOp (l1, "||", r1), r2 when Expr.equal r2 l1 ->
                EBinOp (r2, "||", r1) |> Expr.evaluate
            | EBinOp (l1, "||", r1), r2 when Expr.equal r2 r1 ->
                EBinOp (r2, "||", l1) |> Expr.evaluate
            | EBinOp (l1, "<", r1), EBinOp (l2, ">=", r2)
              when equal l1 l2 && equal r1 r2 -> EBoolean true
            | EBinOp (l1, ">=", r1), EBinOp (l2, "<", r2)
              when equal l1 l2 && equal r1 r2 -> EBoolean true
            | EBinOp (l1, "<", r1), EBinOp (l2, "=", r2)
              when equal l1 l2 && equal r1 r2 -> EBinOp (l1, "<=", r1)
            | EBinOp (l1, "=", r1), EBinOp (l2, "<", r2)
              when equal l1 l2 && equal r1 r2 -> EBinOp (l1, "<=", r1)
            | EBinOp (l1, ">", r1), EBinOp (l2, "=", r2)
              when equal l1 l2 && equal r1 r2 -> EBinOp (l1, ">=", r1)
            | EBinOp (l1, "=", r1), EBinOp (l2, ">", r2)
              when equal l1 l2 && equal r1 r2 -> EBinOp (l1, ">=", r1)
            | _, EBoolean true -> EBoolean true
            | EBoolean true, _ -> EBoolean true
            | _, EBoolean false -> l_val
            | EBoolean false, _ -> r_val
            | _ -> EBinOp (l_val, "||", r_val)
      )
    | EBinOp (lhs, op, rhs) -> (
        let l_val = evaluate ~env lhs in
        let r_val = evaluate ~env rhs in
          match (l_val, r_val) with
          | ENum n1, ENum n2 -> (
              match op with
              | "/" ->
                  if Z.equal n2 Z.zero then failwith "Division by zero"
                  else ENum (Z.div n1 n2)
              | "=" -> EBoolean (Z.equal n1 n2)
              | "!=" -> EBoolean (not (Z.equal n1 n2))
              | "<" -> EBoolean (Z.lt n1 n2)
              | ">" -> EBoolean (Z.gt n1 n2)
              | "<=" -> EBoolean (Z.leq n1 n2)
              | ">=" -> EBoolean (Z.geq n1 n2)
              | _ -> EBinOp (l_val, op, r_val)
            )
          | EBoolean b1, EBoolean b2 -> (
              match op with
              | "=" -> EBoolean (b1 = b2)
              | "!=" -> EBoolean (b1 <> b2)
              | _ -> EBinOp (l_val, op, r_val)
            )
          | EVar v1, EVar v2
            when List.mem op [ "="; "<="; ">=" ] && String.equal v1 v2 ->
              EBoolean true
          | ESymbol v1, ESymbol v2
            when List.mem op [ "="; "<="; ">=" ] && String.equal v1 v2 ->
              EBoolean true
          | EVar v1, EVar v2
            when List.mem op [ "!="; "<"; ">" ] && String.equal v1 v2 ->
              EBoolean false
          | ESymbol v1, ESymbol v2
            when List.mem op [ "!="; "<"; ">" ] && String.equal v1 v2 ->
              EBoolean false
          | e1, e2 -> (
              let cmp = compare e1 e2 in
                if cmp = 0 then
                  match op with
                  | "=" -> EBoolean true
                  | "!=" -> EBoolean false
                  | "<=" -> EBoolean true
                  | ">=" -> EBoolean true
                  | "&&" -> e1
                  | "||" -> e1
                  | _ -> EBinOp (e1, op, e2)
                else
                  (* order commutative operations *)
                  match op with
                  | "=" | "!=" | "&&" | "+" | "*" ->
                      if cmp < 0 then EBinOp (e1, op, e2)
                      else EBinOp (e2, op, e1)
                  | _ -> EBinOp (e1, op, e2)
            )
      )
    | EOr clauses ->
        (* evaluate each clause in the OR *)
        let normalised_clauses =
          List.map (evaluate ~env) clauses
          (* flatten nested ORs *)
          |> List.map (fun (clause : t) ->
              match clause with
              | EOr clauses -> clauses
              | _ -> [ clause ]
          )
          |> List.flatten
          (* sort and remove duplicates *)
          |> List.sort_uniq compare
        in
          if
            List.exists
              (fun e1 ->
                List.exists
                  (fun e2 -> equal e2 (inverse e1 |> evaluate ~env))
                  normalised_clauses
              )
              normalised_clauses
          then EBoolean true
          else EOr normalised_clauses

  let evaluate_conjunction ?(env = fun _ -> None) exprs =
    List.map (evaluate ~env) exprs
    (* flatten nested conjunctions *)
    |> List.map (fun expr ->
        match expr with
        | EBinOp (lhs, "&&", rhs) -> [ lhs; rhs ]
        | _ -> [ expr ]
    )
    |> List.flatten
    (* sort and remove duplicates *)
    |> List.filter (fun e -> not (equal e (EBoolean true)))
    |> List.sort_uniq compare

  (** Relabel symbols in an expression using a relabelling function *)

  let relabel ?(relab = fun s -> None) expr =
    let rec aux e =
      match e with
      | ESymbol v -> (
          match relab v with
          | Some v' -> ESymbol v'
          | None -> e
        )
      | EBinOp (lhs, op, rhs) -> EBinOp (aux lhs, op, aux rhs)
      | EUnOp (op, rhs) -> EUnOp (op, aux rhs)
      | EOr clauses -> EOr (List.map aux clauses)
      | _ -> e
    in
      aux expr |> evaluate

  (** DNF Simplification *)

  (** Remove double negations from an expression *)
  let rec remove_double_negation expr =
    match expr with
    | EUnOp ("!", EUnOp ("!", e)) -> remove_double_negation e
    | EUnOp ("!", e) -> EUnOp ("!", remove_double_negation e)
    | EBinOp (lhs, op, rhs) ->
        EBinOp (remove_double_negation lhs, op, remove_double_negation rhs)
    | _ -> expr

  (** Check if two expressions are contradictory (one is the negation of the
      other) *)
  let are_contradictory e1 e2 =
    match (e1, e2) with
    | EUnOp ("!", inner1), inner2 when equal inner1 inner2 -> true
    | inner1, EUnOp ("!", inner2) when equal inner1 inner2 -> true
    | EBinOp (l1, op1, r1), EBinOp (l2, op2, r2) ->
        (* Check if they're inverse operations on same operands *)
        if equal l1 l2 && equal r1 r2 then
          match (op1, op2) with
          | "=", "!=" | "!=", "=" -> true
          | "<", ">=" | ">=", "<" -> true
          | ">", "<=" | "<=", ">" -> true
          | _ -> false
        else false
    | _ -> false

  (** Check if a clause is a tautology (contains contradictory literals) *)
  let is_clause_contradiction clause =
    let rec check_pairs = function
      | [] -> false
      | e :: rest -> List.exists (are_contradictory e) rest || check_pairs rest
    in
      check_pairs clause

  (** Remove duplicate expressions from a list *)
  let remove_duplicates exprs =
    let rec aux seen = function
      | [] -> List.rev seen
      | e :: rest ->
          if List.exists (equal e) seen then aux seen rest
          else aux (e :: seen) rest
    in
      aux [] exprs

  (** Check if clause1 subsumes clause2 (clause1 is a subset of clause2) *)
  let clause_subsumes clause1 clause2 =
    List.for_all (fun e1 -> List.exists (equal e1) clause2) clause1

  (** Remove subsumed clauses - if clause A is subset of clause B, remove B *)
  let remove_subsumed_clauses clauses =
    let rec aux acc = function
      | [] -> List.rev acc
      | clause :: rest ->
          (* Check if this clause is subsumed by any existing clause in acc *)
          let is_subsumed =
            List.exists (fun c -> clause_subsumes c clause) acc
          in
            if is_subsumed then aux acc rest
            else
              (* Remove any clauses in acc that are subsumed by this clause *)
              let acc' =
                List.filter (fun c -> not (clause_subsumes clause c)) acc
              in
                aux (clause :: acc') rest
    in
      aux [] clauses

  (** Simplify a single clause (conjunction of expressions) *)
  let simplify_clause clause =
    let clause = List.map remove_double_negation clause in

    (* Check for contradictions *)
    if is_clause_contradiction clause then None
      (* Contradiction - this clause is false *)
    else
      (* Check for tautologies and contradictions within literals *)
      let clause = List.filter (fun e -> not (is_contradiction e)) clause in

      (* If any literal is a tautology in a conjunction, we can't simplify further *)
      (* But if we have true && x, we can simplify to x *)
      let clause =
        if List.exists is_tautology clause then
          List.filter (fun e -> not (is_tautology e)) clause
        else clause
      in

      (* Remove duplicates *)
      let clause = remove_duplicates clause in

      (* Sort for canonical form *)
      let clause = List.sort compare clause in

      if List.length clause = 0 then Some [ EBoolean true ]
        (* Empty conjunction is true *)
      else Some clause

  (** Check if DNF contains complementary single-literal clauses forming a
      tautology *)
  let has_complementary_clauses clauses =
    (* Check all pairs of single-literal clauses *)
    let rec check_pairs = function
      | [] -> false
      | clause :: rest ->
          (* Only check single-literal clauses *)
          if List.length clause = 1 then
            let e = List.hd clause in
            (* Check if any remaining single-literal clause is contradictory *)
            let found =
              List.exists
                (fun other_clause ->
                  if List.length other_clause = 1 then
                    let other_e = List.hd other_clause in
                      are_contradictory e other_e
                  else false
                )
                rest
            in
              if found then true else check_pairs rest
          else check_pairs rest
    in
      check_pairs clauses

  (** Simplify DNF: list of clauses where each clause is a conjunction *)
  let simplify_dnf (dnf : expr list list) : expr list list =
    (* Step 1: Simplify each clause *)
    let simplified_clauses = List.filter_map simplify_clause dnf in

    (* Step 2: Remove duplicate clauses *)
    let unique_clauses =
      let rec remove_dup_clauses seen = function
        | [] -> List.rev seen
        | clause :: rest ->
            if
              List.exists
                (fun c ->
                  List.length c = List.length clause
                  && List.for_all2 equal c clause
                )
                seen
            then remove_dup_clauses seen rest
            else remove_dup_clauses (clause :: seen) rest
      in
        remove_dup_clauses [] simplified_clauses
    in

    (* Step 2.5: Check for complementary clauses (e.g., A ∨ !A = tautology) *)
    if has_complementary_clauses unique_clauses then [ [ EBoolean true ] ]
    else
      (* Step 3: Check if any clause is a tautology (if so, entire DNF is true) *)
      let has_tautology_dnf =
        List.exists
          (fun clause ->
            List.length clause = 1
            &&
            match List.hd clause with
            | EBoolean true -> true
            | _ -> false
          )
          unique_clauses
      in

      if has_tautology_dnf then [ [ EBoolean true ] ]
      else
        (* Step 4: Remove subsumed clauses *)
        let minimal_clauses = remove_subsumed_clauses unique_clauses in

        (* Step 5: Handle empty DNF *)
        if List.length minimal_clauses = 0 then [ [ EBoolean false ] ]
        else minimal_clauses

  (** Simplifies the disjunction of two conjunctions of expressions *)
  let simplify_disjunction exprs1 exprs2 =
    let exprs1 = evaluate_conjunction exprs1 |> USet.of_list in
    let exprs2 = evaluate_conjunction exprs2 |> USet.of_list in
    (* common conjuncts in both disjuncts *)
    let common_exprs =
      USet.filter
        (fun e -> USet.exists (fun e2 -> Expr.equal e e2) exprs2)
        exprs1
    in
    (* conjuncts which are only in one disjunct *)
    let only_exprs1 =
      USet.filter
        (fun e -> not (USet.exists (fun e2 -> Expr.equal e e2) exprs2))
        exprs1
    in
    let only_exprs2 =
      USet.filter
        (fun e -> not (USet.exists (fun e1 -> Expr.equal e e1) exprs1))
        exprs2
    in
    (* conjuncts which have a complementary in the other disjunct *)
    (* TODO check that inverse of disjunction is subset of top-level conjunction
       *)
    let compl_exprs1 =
      USet.filter
        (fun e1 ->
          USet.exists
            (fun e2 -> Expr.equal (Expr.inverse e1 |> Expr.evaluate) e2)
            only_exprs2
        )
        only_exprs1
    in
    let compl_exprs2 =
      USet.filter
        (fun e2 ->
          USet.exists
            (fun e1 -> Expr.equal (Expr.inverse e2 |> Expr.evaluate) e1)
            only_exprs1
        )
        only_exprs2
    in
    (* distribute cross product of remaining conjuncts *)
    let make_cross_conjuction exprs1 exprs2 =
      URelation.cross exprs1 exprs2
      |> USet.map (fun (e1, e2) ->
          if Expr.equal e1 e2 then e1 else Expr.evaluate (EOr [ e1; e2 ])
      )
    in
    let cross_exprs =
      make_cross_conjuction
        (USet.set_minus only_exprs1 compl_exprs1)
        (USet.set_minus only_exprs2 compl_exprs2)
    in
    let compl1_only2 =
      make_cross_conjuction compl_exprs1
        (USet.set_minus only_exprs2 compl_exprs2)
    in
    let only1_compl2 =
      make_cross_conjuction
        (USet.set_minus only_exprs1 compl_exprs1)
        compl_exprs2
    in
      (* final disjunction in conjunctive normal form *)
      USet.inplace_union common_exprs cross_exprs
      |> USet.inplace_union compl1_only2
      |> USet.inplace_union only1_compl2
      |> USet.to_list
      |> List.sort_uniq compare
      |> List.filter (fun e -> not (Expr.equal e (EBoolean true)))
end
