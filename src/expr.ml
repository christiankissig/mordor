(** Expression and Value module *)

open Types

(** Check if string is a symbol *)
let is_symbol s =
  String.length s > 0
  && (String.contains greek_alpha s.[0] || String.contains zh_alpha s.[0])

(** Mutual recursion for Value and Expr *)
module rec Value : sig
  val number : Z.t -> value_type
  val symbol : string -> value_type
  val var : string -> value_type
  val boolean : bool -> value_type
  val equal : value_type -> value_type -> bool
  val get_symbols : value_type -> string list
  val to_string : value_type -> string
  val subst : value_type -> value_type -> value_type -> value_type
  val is_number : value_type -> bool
end = struct
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
end

and Expr : sig
  type t = expr

  val binop : t -> string -> t -> t
  val unop : string -> t -> t
  val or_ : t list list -> t
  val var : string -> t
  val num : Z.t -> t
  val equal : t -> t -> bool
  val get_symbols : t -> string list
  val is_flat : t -> bool
  val inverse : t -> t
  val flipped : t -> t
  val subst : t -> string -> t -> t
  val to_string : t -> string
  val flatten : t -> t list
  val is_tautology : t -> bool
  val is_contradiction : t -> bool
  val is_value : t -> bool
  val is_expression : t -> bool
  val is_number : t -> bool
  val evaluate : t -> (string -> t option) -> t
  val to_value : t -> value_type option
  val of_value : value_type -> t
end = struct
  type t = expr

  let binop lhs op rhs = EBinOp (lhs, op, rhs)
  let unop op rhs = EUnOp (op, rhs)
  let or_ clauses = EOr clauses
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

  let is_expression e = not (is_value e)

  let rec equal e1 e2 =
    match (e1, e2) with
    | EBoolean b1, EBoolean b2 -> b1 = b2
    | ENum n1, ENum n2 -> Z.equal n1 n2
    | EVar v1, EVar v2 -> String.equal v1 v2
    | ESymbol s1, ESymbol s2 -> String.equal s1 s2
    | EBinOp (l1, op1, r1), EBinOp (l2, op2, r2) ->
        op1 = op2 && equal l1 l2 && equal r1 r2
    | EUnOp (op1, r1), EUnOp (op2, r2) -> op1 = op2 && equal r1 r2
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
    | ESymbol s when is_symbol s -> [ s ]
    | EBinOp (lhs, _, rhs) -> get_symbols lhs @ get_symbols rhs
    | EUnOp (_, rhs) -> get_symbols rhs
    | EOr clauses ->
        List.flatten
          (List.map (fun c -> List.flatten (List.map get_symbols c)) clauses)
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
    | EOr clauses ->
        let clause_str =
          List.map (fun c -> String.concat " ∧ " (List.map to_string c)) clauses
        in
          String.concat " ∨ " clause_str

  let rec flatten = function
    | EBinOp (lhs, "&&", rhs) ->
        let l_flat = flatten lhs in
        let r_flat = flatten rhs in
          l_flat @ r_flat
    | e -> [ e ]

  let rec is_tautology = function
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
  let rec evaluate expr env =
    match expr with
    | ENum _ -> expr
    | EBoolean _ -> expr
    | ESymbol _ -> expr
    | EVar v -> (
        match env v with
        | Some v_expr -> v_expr
        | None -> expr
      )
    | EUnOp (op, rhs) ->
        let r_val = evaluate rhs env in
          EUnOp (op, r_val)
    | EBinOp (lhs, op, rhs) -> (
        let l_val = evaluate lhs env in
        let r_val = evaluate rhs env in
          match (l_val, r_val) with
          | ENum n1, ENum n2 -> (
              match op with
              | "+" -> ENum (Z.add n1 n2)
              | "-" -> ENum (Z.sub n1 n2)
              | "*" -> ENum (Z.mul n1 n2)
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
              | "&&" -> EBoolean (b1 && b2)
              | "||" -> EBoolean (b1 || b2)
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
          | _ -> EBinOp (l_val, op, r_val)
      )
    | EOr clauses ->
        let eval_clause clause = List.map (fun e -> evaluate e env) clause in
          EOr (List.map eval_clause clauses)
end
