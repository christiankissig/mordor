(* Abstract Syntax Tree definitions *)
type expr = 
  | EpsilonA of expr_a
  | EpsilonB of expr_b

and expr_a =
  | Var of string              (* r *)
  | Deref of expr_a           (* *εA *)
  | Alpha of string           (* α *)
  | Natural of int            (* ℕ *)
  | Add of expr_a * expr_a    (* εA + εA *)
  | Sub of expr_a * expr_a    (* εA - εA *)
  | Mul of expr_a * expr_a    (* εA * εA *)
  | Div of expr_a * expr_a    (* εA / εA *)

and expr_b =
  | Eq of expr_a * expr_a     (* εA = εA *)
  | Lt of expr_a * expr_a     (* εA < εA *)
  | Not of expr_b             (* ¬εB *)
  | And of expr_b * expr_b    (* εB ∧ εB *)
  | Or of expr_b * expr_b     (* εB ∨ εB *)

type program = 
  | Skip
  | Seq of program * program
  | Par of program * program
  | If of expr * program * program
  | While of expr * program
  | Assign of string * expr
  | AssignOp of string * string * expr  (* ri :=o x *)
  | VarAssignOp of string * string * expr  (* x :=o ε *)
  | RefAssign of string * string  (* ri := &x *)
  | RefAssignOp of string * string * expr  (* ri :=o *ε *)
  | DerefAssign of string * string * expr  (* *ε1 :=o ε2 *)
  | Fence of string
  | FAA of string * string * string * expr * expr  (* ri := FAAor,ow(x, ε) *)
  | CAS of string * string * string * expr * expr * expr  (* ri := CASor,ow(x, ε1, ε2) *)
  | Malloc of string * expr  (* ri := malloc(ε) *)
  | Free of string  (* free(ri) *)

(* Token definitions *)
type token =
  | SKIP | SEQ | PAR | IF | ELSE | WHILE
  | ASSIGN | ASSIGN_OP of string | REF | DEREF
  | FENCE of string | FAA of string * string | CAS of string * string
  | MALLOC | FREE
  | LPAREN | RPAREN | LBRACE | RBRACE
  | COMMA | SEMICOLON
  | IDENT of string | NUM of int | ALPHA of string
  | PLUS | MINUS | MULT | DIV
  | EQ | LT | NOT | AND | OR
  | EPSILON | EPSILON_A | EPSILON_B
  | EOF

(* Lexer *)
let tokenize input =
  let len = String.length input in
  let rec aux pos acc =
    if pos >= len then List.rev (EOF :: acc)
    else
      match input.[pos] with
      | ' ' | '\t' | '\n' | '\r' -> aux (pos + 1) acc
      | '(' -> aux (pos + 1) (LPAREN :: acc)
      | ')' -> aux (pos + 1) (RPAREN :: acc)
      | '{' -> aux (pos + 1) (LBRACE :: acc)
      | '}' -> aux (pos + 1) (RBRACE :: acc)
      | ',' -> aux (pos + 1) (COMMA :: acc)
      | ';' -> aux (pos + 1) (SEMICOLON :: acc)
      | '&' -> aux (pos + 1) (REF :: acc)
      | '*' -> aux (pos + 1) (MULT :: acc)
      | '+' -> aux (pos + 1) (PLUS :: acc)
      | '-' -> aux (pos + 1) (MINUS :: acc)
      | '/' -> aux (pos + 1) (DIV :: acc)
      | '=' -> aux (pos + 1) (EQ :: acc)
      | '<' -> aux (pos + 1) (LT :: acc)
      | _ when pos + 2 < len && String.sub input pos 3 = "¬" ->
          aux (pos + 3) (NOT :: acc)
      | _ when pos + 2 < len && String.sub input pos 3 = "∧" ->
          aux (pos + 3) (AND :: acc)
      | _ when pos + 2 < len && String.sub input pos 3 = "∨" ->
          aux (pos + 3) (OR :: acc)
      | '|' when pos + 1 < len && input.[pos + 1] = '|' ->
          aux (pos + 2) (PAR :: acc)
      | ':' when pos + 2 < len && input.[pos + 1] = '=' ->
          if pos + 3 < len && input.[pos + 3] = ' ' then
            let op = String.make 1 input.[pos + 2] in
            aux (pos + 4) (ASSIGN_OP op :: acc)
          else
            aux (pos + 2) (ASSIGN :: acc)
      | _ when pos + 1 < len && String.sub input pos 2 = "ε" -> 
          if pos + 2 < len then
            let next_char = String.sub input (pos + 2) 1 in
            match next_char with
            | "A" -> aux (pos + 3) (EPSILON_A :: acc)
            | "B" -> aux (pos + 3) (EPSILON_B :: acc)
            | _ -> aux (pos + 2) (EPSILON :: acc)
          else
            aux (pos + 2) (EPSILON :: acc)
      | _ when pos + 1 < len && String.sub input pos 2 = "α" -> 
          (* Handle Greek letter alpha as identifier *)
          let start_pos = pos in
          let rec read_alpha p =
            if p >= len then p
            else if p + 1 < len && String.sub input p 2 = "α" then read_alpha (p + 2)
            else match input.[p] with
            | c when c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || 
                     c >= '0' && c <= '9' || c = '_' -> read_alpha (p + 1)
            | _ -> p
          in
          let end_pos = read_alpha (pos + 2) in
          let alpha_name = String.sub input start_pos (end_pos - start_pos) in
          aux end_pos (ALPHA alpha_name :: acc)
      | _ when pos + 2 < len && String.sub input pos 3 = "ℕ" -> 
          aux (pos + 3) (NUM 0 :: acc)  (* Natural number placeholder *)
      | c when c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' ->
          let start_pos = pos in
          let rec read_ident p =
            if p >= len then p
            else match input.[p] with
            | c when c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || 
                     c >= '0' && c <= '9' || c = '_' -> read_ident (p + 1)
            | _ -> p
          in
          let end_pos = read_ident pos in
          let ident = String.sub input start_pos (end_pos - start_pos) in
          let token = match ident with
            | "skip" -> SKIP
            | "if" -> IF
            | "else" -> ELSE
            | "while" -> WHILE
            | "malloc" -> MALLOC
            | "free" -> FREE
            | _ when String.length ident > 5 && String.sub ident 0 5 = "fence" ->
                let suffix = String.sub ident 5 (String.length ident - 5) in
                FENCE suffix
            | _ when String.length ident > 3 && String.sub ident 0 3 = "FAA" ->
                (* Parse FAA_or,ow - simplified parsing *)
                let suffix = String.sub ident 3 (String.length ident - 3) in
                if String.length suffix > 0 && suffix.[0] = '_' then
                  let params = String.sub suffix 1 (String.length suffix - 1) in
                  (* Simple parsing of "or,ow" - could be more sophisticated *)
                  (match String.split_on_char ',' params with
                   | [or_val; ow_val] -> FAA (or_val, ow_val)
                   | _ -> FAA ("", ""))
                else
                  FAA ("", "")
            | _ when String.length ident > 3 && String.sub ident 0 3 = "CAS" ->
                (* Parse CAS_or,ow - simplified parsing *)
                let suffix = String.sub ident 3 (String.length ident - 3) in
                if String.length suffix > 0 && suffix.[0] = '_' then
                  let params = String.sub suffix 1 (String.length suffix - 1) in
                  (* Simple parsing of "or,ow" - could be more sophisticated *)
                  (match String.split_on_char ',' params with
                   | [or_val; ow_val] -> CAS (or_val, ow_val)
                   | _ -> CAS ("", ""))
                else
                  CAS ("", "")
            | _ when String.length ident > 5 && String.sub ident 0 5 = "fence" ->
                let suffix = String.sub ident 5 (String.length ident - 5) in
                FENCE suffix
            | _ -> IDENT ident
          in
          aux end_pos (token :: acc)
      | c when c >= '0' && c <= '9' ->
          let rec read_num p acc_num =
            if p >= len then (p, acc_num)
            else match input.[p] with
            | c when c >= '0' && c <= '9' -> 
                read_num (p + 1) (acc_num * 10 + (int_of_char c - int_of_char '0'))
            | _ -> (p, acc_num)
          in
          let (end_pos, num) = read_num pos 0 in
          aux end_pos (NUM num :: acc)
      | _ -> aux (pos + 1) acc
  in
  aux 0 []

(* Parser *)
exception ParseError of string

let parse_error msg = raise (ParseError msg)

let rec parse_program tokens =
  match tokens with
  | [] | [EOF] -> (Skip, [EOF])
  | _ -> parse_program_seq tokens

and parse_program_seq tokens =
  let (prog1, tokens') = parse_program_par tokens in
  match tokens' with
  | SEQ :: tokens'' ->
      let (prog2, tokens''') = parse_program_seq tokens'' in
      (Seq (prog1, prog2), tokens''')
  | _ -> (prog1, tokens')

and parse_program_par tokens =
  let (prog1, tokens') = parse_program_base tokens in
  match tokens' with
  | PAR :: tokens'' ->
      let (prog2, tokens''') = parse_program_par tokens'' in
      (Par (prog1, prog2), tokens''')
  | _ -> (prog1, tokens')

and parse_program_base tokens =
  match tokens with
  | SKIP :: tokens' -> (Skip, tokens')
  | LBRACE :: tokens' ->
      let (prog, tokens'') = parse_program tokens' in
      (match tokens'' with
       | RBRACE :: tokens''' -> (prog, tokens''')
       | _ -> parse_error "Expected '}'")
  | IF :: LPAREN :: tokens' ->
      let (expr, tokens'') = parse_expr tokens' in
      (match tokens'' with
       | RPAREN :: LBRACE :: tokens''' ->
           let (then_prog, tokens'''') = parse_program tokens''' in
           (match tokens'''' with
            | RBRACE :: ELSE :: LBRACE :: tokens''''' ->
                let (else_prog, tokens'''''') = parse_program tokens''''' in
                (match tokens'''''' with
                 | RBRACE :: tokens''''''' -> (If (expr, then_prog, else_prog), tokens''''''')
                 | _ -> parse_error "Expected '}' after else block")
            | RBRACE :: tokens''''' -> (If (expr, then_prog, Skip), tokens''''')
            | _ -> parse_error "Expected '}' after then block")
       | _ -> parse_error "Expected ')' and '{' after if condition")
  | WHILE :: LPAREN :: tokens' ->
      let (expr, tokens'') = parse_expr tokens' in
      (match tokens'' with
       | RPAREN :: LBRACE :: tokens''' ->
           let (body, tokens'''') = parse_program tokens''' in
           (match tokens'''' with
            | RBRACE :: tokens''''' -> (While (expr, body), tokens''''')
            | _ -> parse_error "Expected '}' after while body")
       | _ -> parse_error "Expected ')' and '{' after while condition")
  | IDENT r :: ASSIGN :: tokens' ->
      let (expr, tokens'') = parse_expr tokens' in
      (Assign (r, expr), tokens'')
  | IDENT r :: ASSIGN_OP op :: IDENT x :: tokens' ->
      (AssignOp (r, op, EpsilonA (Var x)), tokens')
  | IDENT x :: ASSIGN_OP op :: EPSILON :: tokens' ->
      (VarAssignOp (x, op, EpsilonA (Natural 0)), tokens')  (* Placeholder for ε *)
  | IDENT r :: ASSIGN_OP op :: MULT :: tokens' ->
      let (expr, tokens'') = parse_expr tokens' in
      (RefAssignOp (r, op, expr), tokens'')
  | MULT :: tokens' ->
      let (_, tokens'') = parse_expr tokens' in
      (match tokens'' with
       | ASSIGN_OP op :: tokens''' ->
           let (expr2, tokens'''') = parse_expr tokens''' in
           (DerefAssign ("*", op, expr2), tokens'''')
       | _ -> parse_error "Expected assignment operator after dereference")
  | FENCE o :: tokens' ->
      (Fence o, tokens')
(*  | IDENT r :: ASSIGN :: FAA (or_val, ow_val) :: tokens' ->
      (* Simplified FAA parsing *)
      let (expr, tokens'') = parse_expr tokens' in
      (FAA (r, or_val, ow_val, expr, EpsilonA (Natural 0)), tokens'')
  | IDENT r :: ASSIGN :: CAS (or_val, ow_val) :: tokens' ->
      (* Simplified CAS parsing *)
      let (expr, tokens'') = parse_expr tokens' in
      (CAS (r, or_val, ow_val, expr, EpsilonA (Natural 0), EpsilonA (Natural 0)), tokens'')
  | IDENT r :: ASSIGN :: MALLOC :: LPAREN :: tokens' ->
      let (expr, tokens'') = parse_expr tokens' in
      (match tokens'' with
       | RPAREN :: tokens''' -> (Malloc (r, expr), tokens''')
       | _ -> parse_error "Expected ')' after malloc argument")*)
  | FREE :: LPAREN :: IDENT r :: RPAREN :: tokens' ->
      (Free r, tokens')
  | _ -> parse_error "Unexpected token in program"

and parse_expr tokens =
  parse_expr_or tokens

and parse_expr_or tokens =
  let (expr1, tokens') = parse_expr_and tokens in
  let rec aux left tokens =
    match tokens with
    | OR :: tokens' ->
        let (right, tokens'') = parse_expr_and tokens' in
        let combined = match (left, right) with
          | (EpsilonB b1, EpsilonB b2) -> EpsilonB (Or (b1, b2))
          | _ -> parse_error "Type error: OR expects boolean expressions"
        in
        aux combined tokens''
    | _ -> (left, tokens)
  in
  aux expr1 tokens'

and parse_expr_and tokens =
  let (expr1, tokens') = parse_expr_not tokens in
  let rec aux left tokens =
    match tokens with
    | AND :: tokens' ->
        let (right, tokens'') = parse_expr_not tokens' in
        let combined = match (left, right) with
          | (EpsilonB b1, EpsilonB b2) -> EpsilonB (And (b1, b2))
          | _ -> parse_error "Type error: AND expects boolean expressions"
        in
        aux combined tokens''
    | _ -> (left, tokens)
  in
  aux expr1 tokens'

and parse_expr_not tokens =
  match tokens with
  | NOT :: tokens' ->
      let (expr, tokens'') = parse_expr_not tokens' in
      (match expr with
       | EpsilonB b -> (EpsilonB (Not b), tokens'')
       | _ -> parse_error "Type error: NOT expects boolean expression")
  | _ -> parse_expr_rel tokens

and parse_expr_rel tokens =
  let (expr1, tokens') = parse_expr_add tokens in
  match tokens' with
  | EQ :: tokens'' ->
      let (expr2, tokens''') = parse_expr_add tokens'' in
      (match (expr1, expr2) with
       | (EpsilonA a1, EpsilonA a2) -> (EpsilonB (Eq (a1, a2)), tokens''')
       | _ -> parse_error "Type error: EQ expects arithmetic expressions")
  | LT :: tokens'' ->
      let (expr2, tokens''') = parse_expr_add tokens'' in
      (match (expr1, expr2) with
       | (EpsilonA a1, EpsilonA a2) -> (EpsilonB (Lt (a1, a2)), tokens''')
       | _ -> parse_error "Type error: LT expects arithmetic expressions")
  | _ -> (expr1, tokens')

and parse_expr_add tokens =
  let (expr1, tokens') = parse_expr_mul tokens in
  let rec aux left tokens =
    match tokens with
    | PLUS :: tokens' ->
        let (right, tokens'') = parse_expr_mul tokens' in
        let combined = match (left, right) with
          | (EpsilonA a1, EpsilonA a2) -> EpsilonA (Add (a1, a2))
          | _ -> parse_error "Type error: ADD expects arithmetic expressions"
        in
        aux combined tokens''
    | MINUS :: tokens' ->
        let (right, tokens'') = parse_expr_mul tokens' in
        let combined = match (left, right) with
          | (EpsilonA a1, EpsilonA a2) -> EpsilonA (Sub (a1, a2))
          | _ -> parse_error "Type error: SUB expects arithmetic expressions"
        in
        aux combined tokens''
    | _ -> (left, tokens)
  in
  aux expr1 tokens'

and parse_expr_mul tokens =
  let (expr1, tokens') = parse_expr_primary tokens in
  let rec aux left tokens =
    match tokens with
    | MULT :: tokens' ->
        let (right, tokens'') = parse_expr_primary tokens' in
        let combined = match (left, right) with
          | (EpsilonA a1, EpsilonA a2) -> EpsilonA (Mul (a1, a2))
          | _ -> parse_error "Type error: MUL expects arithmetic expressions"
        in
        aux combined tokens''
    | DIV :: tokens' ->
        let (right, tokens'') = parse_expr_primary tokens' in
        let combined = match (left, right) with
          | (EpsilonA a1, EpsilonA a2) -> EpsilonA (Div (a1, a2))
          | _ -> parse_error "Type error: DIV expects arithmetic expressions"
        in
        aux combined tokens''
    | _ -> (left, tokens)
  in
  aux expr1 tokens'

and parse_expr_primary tokens =
  match tokens with
  | IDENT x :: tokens' -> (EpsilonA (Var x), tokens')
  | NUM n :: tokens' -> (EpsilonA (Natural n), tokens')
  | ALPHA a :: tokens' -> (EpsilonA (Alpha a), tokens')
  | MULT :: tokens' ->
      let (expr, tokens'') = parse_expr_primary tokens' in
      (match expr with
       | EpsilonA a -> (EpsilonA (Deref a), tokens'')
       | _ -> parse_error "Type error: dereference expects arithmetic expression")
  | LPAREN :: tokens' ->
      let (expr, tokens'') = parse_expr tokens' in
      (match tokens'' with
       | RPAREN :: tokens''' -> (expr, tokens''')
       | _ -> parse_error "Expected ')' after expression")
  | EPSILON :: tokens' -> (EpsilonA (Natural 0), tokens')  (* Placeholder *)
  | EPSILON_A :: tokens' -> (EpsilonA (Natural 0), tokens')  (* Placeholder *)
  | EPSILON_B :: tokens' -> (EpsilonB (Eq (Natural 0, Natural 0)), tokens')  (* Placeholder *)
  | _ -> parse_error "Expected expression"

and string_of_expr = function
  | EpsilonA a -> string_of_expr_a a
  | EpsilonB b -> string_of_expr_b b

and string_of_expr_a = function
  | Var x -> x
  | Deref a -> "*" ^ string_of_expr_a a
  | Alpha a -> a
  | Natural n -> string_of_int n
  | Add (a1, a2) -> "(" ^ string_of_expr_a a1 ^ " + " ^ string_of_expr_a a2 ^ ")"
  | Sub (a1, a2) -> "(" ^ string_of_expr_a a1 ^ " - " ^ string_of_expr_a a2 ^ ")"
  | Mul (a1, a2) -> "(" ^ string_of_expr_a a1 ^ " * " ^ string_of_expr_a a2 ^ ")"
  | Div (a1, a2) -> "(" ^ string_of_expr_a a1 ^ " / " ^ string_of_expr_a a2 ^ ")"

and string_of_expr_b = function
  | Eq (a1, a2) -> "(" ^ string_of_expr_a a1 ^ " = " ^ string_of_expr_a a2 ^ ")"
  | Lt (a1, a2) -> "(" ^ string_of_expr_a a1 ^ " < " ^ string_of_expr_a a2 ^ ")"
  | Not b -> "¬(" ^ string_of_expr_b b ^ ")"
  | And (b1, b2) -> "(" ^ string_of_expr_b b1 ^ " ∧ " ^ string_of_expr_b b2 ^ ")"
  | Or (b1, b2) -> "(" ^ string_of_expr_b b1 ^ " ∨ " ^ string_of_expr_b b2 ^ ")"

(* Main parsing function *)
let parse input =
  let tokens = tokenize input in
  let (prog, remaining) = parse_program tokens in
  match remaining with
  | [EOF] -> prog
  | _ -> parse_error "Unexpected tokens at end of input"

(* Pretty printing *)
let rec string_of_program = function
  | Skip -> "skip"
  | Seq (p1, p2) -> string_of_program p1 ^ "; " ^ string_of_program p2
  | Par (p1, p2) -> string_of_program p1 ^ " || " ^ string_of_program p2
  | If (e, p1, p2) -> "if (" ^ string_of_expr e ^ ") {" ^ string_of_program p1 ^ "} else {" ^ string_of_program p2 ^ "}"
  | While (e, p) -> "while (" ^ string_of_expr e ^ ") {" ^ string_of_program p ^ "}"
  | Assign (r, e) -> r ^ " := " ^ string_of_expr e
  | AssignOp (r, op, e) -> r ^ " :=" ^ op ^ " " ^ string_of_expr e
  | VarAssignOp (x, op, e) -> x ^ " :=" ^ op ^ " " ^ string_of_expr e
  | RefAssign (r, x) -> r ^ " := &" ^ x
  | RefAssignOp (r, op, e) -> r ^ " :=" ^ op ^ " *" ^ string_of_expr e
  | DerefAssign (deref, op, e) -> "*" ^ deref ^ " :=" ^ op ^ " " ^ string_of_expr e
  | Fence o -> "fence_" ^ o
  | FAA (r, or_val, ow_val, x, e) -> r ^ " := FAA_" ^ or_val ^ "," ^ ow_val ^ "(" ^ string_of_expr x ^ ", " ^ string_of_expr e ^ ")"
  | CAS (r, or_val, ow_val, x, e1, e2) -> r ^ " := CAS_" ^ or_val ^ "," ^ ow_val ^ "(" ^ string_of_expr x ^ ", " ^ string_of_expr e1 ^ ", " ^ string_of_expr e2 ^ ")"
  | Malloc (r, e) -> r ^ " := malloc(" ^ string_of_expr e ^ ")"
  | Free r -> "free(" ^ r ^ ")"

(* Example usage *)
let () =
  let test_inputs = [
    "skip";
    "x := 5";
    "x := y + z * 2";
    "if (x = 5) { skip } else { y := 1 }";
    "if (x < y) { x := x + 1 }";
    "while (x < 10) { x := x + 1 }";
    "if (x = y ∧ z < 5) { skip }";
    "x := *y + 3";
    "fence_o";
  ] in
  List.iter (fun input ->
    Printf.printf "\nParsing: %s\n" input;
    try
      let parsed = parse input in
      Printf.printf "Result: %s\n" (string_of_program parsed)
    with
    | ParseError msg -> Printf.printf "Parse error: %s\n" msg
  ) test_inputs
