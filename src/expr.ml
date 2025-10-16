(** Expression and Value module *)

open Types

(** Check if string is a symbol *)
let is_symbol s =
  String.length s > 0
  && (String.contains greek_alpha s.[0] || String.contains zh_alpha s.[0])

(** Check if value is a number *)
let is_number = function
  | VNumber _ -> true
  | _ -> false

(** Mutual recursion for Value and Expr *)
module rec Value : sig
  val number : Z.t -> value_type
  val symbol : string -> value_type
  val var : string -> value_type
  val expression : expr -> value_type
  val boolean : bool -> value_type
  val of_value : value_type -> value_type
  val make : value_type -> value_type
  val equal : value_type -> value_type -> bool
  val get_symbols : value_type -> string list
  val to_string : value_type -> string
  val subst : value_type -> value_type -> value_type -> value_type
end = struct
  let number n = VNumber n
  let symbol s = VSymbol s
  let var s = VVar s
  let expression e = VExpression e
  let boolean b = VBoolean b

  let of_value = function
    | VNumber n -> VNumber n
    | VSymbol s -> VSymbol s
    | VVar v -> VVar v
    | VExpression e -> VExpression e
    | VBoolean b -> VBoolean b

  let make = function
    | VNumber _ as n -> n
    | VSymbol _ as s -> s
    | VVar _ as v -> v
    | VExpression _ as e -> e
    | VBoolean _ as b -> b

  let equal v1 v2 =
    match (v1, v2) with
    | VNumber n1, VNumber n2 -> Z.equal n1 n2
    | VSymbol s1, VSymbol s2 -> String.equal s1 s2
    | VVar v1, VVar v2 -> String.equal v1 v2
    | VBoolean b1, VBoolean b2 -> b1 = b2
    | VExpression e1, VExpression e2 -> Expr.equal e1 e2
    | _ -> false

  let get_symbols = function
    | VSymbol s when is_symbol s -> [ s ]
    | VExpression e -> Expr.get_symbols e
    | _ -> []

  let to_string = function
    | VNumber n -> Z.to_string n
    | VSymbol s -> s
    | VVar v -> v
    | VBoolean b -> string_of_bool b
    | VExpression e -> Expr.to_string e

  let subst v a b =
    match v with
    | VSymbol _ when equal v a -> b
    | VExpression e -> VExpression (Expr.subst e a b)
    | _ -> v
end

and Expr : sig
  type t = expr

  val binop : value_type -> string -> value_type -> t
  val unop : string -> value_type -> t
  val or_ : t list list -> t
  val var : string -> t
  val num : Z.t -> t
  val equal : t -> t -> bool
  val get_symbols : t -> string list
  val is_flat : t -> bool
  val inverse : t -> t
  val flipped : t -> t
  val subst : t -> value_type -> value_type -> t
  val to_string : t -> string
  val flatten : t -> t list
  val is_tautology : t -> bool
  val is_contradiction : t -> bool
end = struct
  type t = expr

  let binop lhs op rhs = EBinOp (lhs, op, rhs)
  let unop op rhs = EUnOp (op, rhs)
  let or_ clauses = EOr clauses
  let var v = EVar v
  let num n = ENum n

  let rec equal e1 e2 =
    match (e1, e2) with
    | ENum n1, ENum n2 -> Z.equal n1 n2
    | EVar v1, EVar v2 -> String.equal v1 v2
    | EBinOp (l1, op1, r1), EBinOp (l2, op2, r2) ->
        op1 = op2 && Value.equal l1 l2 && Value.equal r1 r2
    | EUnOp (op1, r1), EUnOp (op2, r2) -> op1 = op2 && Value.equal r1 r2
    | EOr c1, EOr c2 ->
        List.length c1 = List.length c2
        && List.for_all2
             (fun a b ->
               List.length a = List.length b && List.for_all2 equal a b
             )
             c1 c2
    | _ -> false

  let rec get_symbols = function
    | EVar v when is_symbol v -> [ v ]
    | EBinOp (lhs, _, rhs) -> Value.get_symbols lhs @ Value.get_symbols rhs
    | EUnOp (_, rhs) -> Value.get_symbols rhs
    | EOr clauses ->
        List.flatten
          (List.map (fun c -> List.flatten (List.map get_symbols c)) clauses)
    | _ -> []

  let is_flat = function
    | EBinOp (lhs, op, rhs) ->
        let comp_ops = [ "="; "!="; "<"; ">"; "<="; ">=" ] in
          List.mem op comp_ops
          && (not
                ( match lhs with
                | VExpression _ -> true
                | _ -> false
                )
             )
          && not
               ( match rhs with
               | VExpression _ -> true
               | _ -> false
               )
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

  let rec subst e a b =
    let eq x y = Value.equal x y in
      match e with
      | EBinOp (lhs, op, rhs) ->
          let new_lhs =
            if eq lhs a then b
            else
              match lhs with
              | VExpression e -> VExpression (subst e a b)
              | _ -> lhs
          in
          let new_rhs =
            if eq rhs a then b
            else
              match rhs with
              | VExpression e -> VExpression (subst e a b)
              | _ -> rhs
          in
            EBinOp (new_lhs, op, new_rhs)
      | EUnOp (op, rhs) ->
          let new_rhs =
            if eq rhs a then b
            else
              match rhs with
              | VExpression e -> VExpression (subst e a b)
              | _ -> rhs
          in
            EUnOp (op, new_rhs)
      | e -> e

  let rec to_string = function
    | ENum n -> Z.to_string n
    | EVar v -> v
    | EBinOp (lhs, op, rhs) ->
        Printf.sprintf "(%s %s %s)" (Value.to_string lhs) op
          (Value.to_string rhs)
    | EUnOp (op, rhs) -> Printf.sprintf "%s(%s)" op (Value.to_string rhs)
    | EOr clauses ->
        let clause_str =
          List.map (fun c -> String.concat " ∧ " (List.map to_string c)) clauses
        in
          String.concat " ∨ " clause_str

  let rec flatten = function
    | EBinOp (lhs, "&&", rhs) ->
        let l_flat =
          match lhs with
          | VExpression e -> flatten e
          | _ -> [ EVar "?" ]
        in
        let r_flat =
          match rhs with
          | VExpression e -> flatten e
          | _ -> [ EVar "?" ]
        in
          l_flat @ r_flat
    | e -> [ e ]

  let is_tautology = function
    | EBinOp (lhs, op, rhs) when Value.equal lhs rhs ->
        List.mem op [ "="; "<="; ">=" ]
    | _ -> false

  let is_contradiction = function
    | EBinOp (VNumber l, op, VNumber r) ->
        let b =
          match op with
          | "=" -> Z.equal l r
          | "!=" -> not (Z.equal l r)
          | "<" -> Z.lt l r
          | ">" -> Z.gt l r
          | "<=" -> Z.leq l r
          | ">=" -> Z.geq l r
          | _ -> true
        in
          not b
    | EBinOp (lhs, op, rhs) when Value.equal lhs rhs ->
        List.mem op [ "<"; ">"; "!=" ]
    | _ -> false
end
