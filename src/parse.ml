(** Parser for sMRD litmus tests *)
open Types

(** Token types *)
type token_type =
  | NONATOMIC
  | RELAXED
  | RELEASE
  | ACQUIRE
  | STRONG
  | NORMAL
  | SC
  | FADD
  | CAS
  | IF
  | ELSE
  | WHILE
  | DO
  | SKIP
  | QDO
  | QWHILE
  | FENCE
  | MALLOC
  | FREE
  | LOCK
  | UNLOCK
  | LOAD
  | STORE
  | ALLOW
  | FORBID
  | NAME
  | VALUES
  | INT of Z.t
  | REGISTER of string
  | ATLOC of string
  | GLOBAL of string
  | STRING of string
  | BACKTICK of string
  | COMMENT of string
  | QUOTE
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | ARROW
  | RARROW
  | AND
  | OR
  | PERCENT
  | NEQ
  | GEQ
  | GT
  | LEQ
  | LT
  | ASSIGN
  | EQ
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | LDBRACKET
  | COLONRLX
  | COLONREL
  | COLONACQ
  | COLONSC
  | COLONV
  | COLONVRLX
  | COLONVREL
  | COLONVACQ
  | COLONVSC
  | RDBRACKET
  | LBRACKET
  | RBRACKET
  | SEMICOLON
  | COMMA
  | BANG
  | DOT
  | HASH
  | AMPERSAND
  | CARET
  | PIPE
  | TILDE
  | IN
  | NOTIN
  | FORALL
  | PARALLEL
  | EOF

type token = { typ : token_type; line : int; col : int }

(** Tokenizer state *)
type tokenizer = {
  src : string;
  mutable index : int;
  mutable line : int;
  mutable line_start : int;
}

let make_tokenizer src = { src; index = 0; line = 1; line_start = 0 }

let current_char t =
  if t.index < String.length t.src then Some t.src.[t.index] else None

let advance t =
  match current_char t with
  | Some '\n' ->
      t.index <- t.index + 1;
      t.line <- t.line + 1;
      t.line_start <- t.index
  | Some _ -> t.index <- t.index + 1
  | None -> ()

let make_token t typ = { typ; line = t.line; col = t.index - t.line_start + 1 }

let is_whitespace = function
  | ' ' | '\t' | '\n' | '\r' -> true
  | _ -> false

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false

let is_alpha = function
  | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
  | _ -> false

let is_alnum c = is_alpha c || is_digit c

let skip_whitespace t =
  while
    match current_char t with
    | Some c when is_whitespace c ->
        advance t;
        true
    | _ -> false
  do
    ()
  done

let read_while t pred =
  let buf = Buffer.create 16 in
    while
      match current_char t with
      | Some c when pred c ->
          Buffer.add_char buf c;
          advance t;
          true
      | _ -> false
    do
      ()
    done;
    Buffer.contents buf

let starts_with t str =
  let len = String.length str in
    t.index + len <= String.length t.src && String.sub t.src t.index len = str

let try_keyword t =
  let keywords =
    [
      ("nonatomic", NONATOMIC);
      ("na", NONATOMIC);
      ("relaxed", RELAXED);
      ("rlx", RELAXED);
      ("release", RELEASE);
      ("rel", RELEASE);
      ("acquire", ACQUIRE);
      ("acq", ACQUIRE);
      ("strong", STRONG);
      ("normal", NORMAL);
      ("sequentially_consistent", SC);
      ("sc", SC);
      ("FADD", FADD);
      ("fadd", FADD);
      ("CAS", CAS);
      ("cas", CAS);
      ("if", IF);
      ("else", ELSE);
      ("while", WHILE);
      ("do", DO);
      ("skip", SKIP);
      ("qdo", QDO);
      ("qwhile", QWHILE);
      ("fence", FENCE);
      ("malloc", MALLOC);
      ("free", FREE);
      ("lock", LOCK);
      ("unlock", UNLOCK);
      ("load", LOAD);
      ("store", STORE);
      ("allow", ALLOW);
      ("forbid", FORBID);
      ("name", NAME);
      ("values", VALUES);
    ]
  in
    List.find_map
      (fun (word, tok) ->
        if starts_with t word then
          let next_idx = t.index + String.length word in
            if next_idx >= String.length t.src || not (is_alnum t.src.[next_idx])
            then Some (word, tok)
            else None
        else None
      )
      keywords

let next_token t =
  skip_whitespace t;

  if t.index >= String.length t.src then make_token t EOF
  else
    (* Try keyword *)
    match try_keyword t with
    | Some (word, tok) ->
        t.index <- t.index + String.length word;
        make_token t tok
    | None -> (
        match current_char t with
        | None -> make_token t EOF
        (* Numbers *)
        | Some c when is_digit c ->
            let num_str = read_while t (fun c -> is_alnum c || c = 'x') in
            let token = make_token t (INT (Z.of_string num_str)) in
              token
        (* Registers *)
        | Some 'r'
          when let next_idx = t.index + 1 in
                 next_idx < String.length t.src && is_alnum t.src.[next_idx] ->
            advance t;
            let rest = read_while t is_alnum in
              make_token t (REGISTER ("r" ^ rest))
        (* AtLoc *)
        | Some '@' ->
            advance t;
            let loc = read_while t is_alnum in
              make_token t (ATLOC ("@" ^ loc))
        (* Global variables *)
        | Some c when is_alpha c ->
            let name = read_while t is_alnum in
              make_token t (GLOBAL name)
        (* Strings *)
        | Some '"' ->
            advance t;
            let str = read_while t (( <> ) '"') in
              advance t;
              (* consume closing quote *)
              make_token t (STRING str)
        (* Backticks *)
        | Some '`' ->
            advance t;
            let label = read_while t (( <> ) '`') in
              advance t;
              (* consume closing backtick *)
              make_token t (BACKTICK label)
        (* Comments *)
        | Some '/' when starts_with t "//" ->
            let comment = read_while t (( <> ) '\n') in
              make_token t (COMMENT comment)
        (* Multi-character operators *)
        | Some ':' when starts_with t ":rlx=" ->
            t.index <- t.index + 5;
            make_token t COLONRLX
        | Some ':' when starts_with t ":rel=" ->
            t.index <- t.index + 5;
            make_token t COLONREL
        | Some ':' when starts_with t ":acq=" ->
            t.index <- t.index + 5;
            make_token t COLONACQ
        | Some ':' when starts_with t ":sc=" ->
            t.index <- t.index + 4;
            make_token t COLONSC
        | Some ':' when starts_with t ":vrlx=" ->
            t.index <- t.index + 6;
            make_token t COLONVRLX
        | Some ':' when starts_with t ":vrel=" ->
            t.index <- t.index + 6;
            make_token t COLONVREL
        | Some ':' when starts_with t ":vacq=" ->
            t.index <- t.index + 6;
            make_token t COLONVACQ
        | Some ':' when starts_with t ":vsc=" ->
            t.index <- t.index + 5;
            make_token t COLONVSC
        | Some ':' when starts_with t ":v=" ->
            t.index <- t.index + 3;
            make_token t COLONV
        | Some ':' when starts_with t ":=" ->
            t.index <- t.index + 2;
            make_token t ASSIGN
        | Some '=' when starts_with t "=>" ->
            t.index <- t.index + 2;
            make_token t ARROW
        | Some '~' when starts_with t "~~>" ->
            t.index <- t.index + 3;
            make_token t RARROW
        | Some '|' when starts_with t "|||" ->
            t.index <- t.index + 3;
            make_token t PARALLEL
        | Some '&' when starts_with t "&&" ->
            t.index <- t.index + 2;
            make_token t AND
        | Some '|' when starts_with t "||" ->
            t.index <- t.index + 2;
            make_token t OR
        | Some '%' when starts_with t "%%" ->
            t.index <- t.index + 2;
            make_token t PERCENT
        | Some '!' when starts_with t "!=" ->
            t.index <- t.index + 2;
            make_token t NEQ
        | Some '>' when starts_with t ">=" ->
            t.index <- t.index + 2;
            make_token t GEQ
        | Some '<' when starts_with t "<=" ->
            t.index <- t.index + 2;
            make_token t LEQ
        | Some '[' when starts_with t "[[" ->
            t.index <- t.index + 2;
            make_token t LDBRACKET
        | Some ']' when starts_with t "]]" ->
            t.index <- t.index + 2;
            make_token t RDBRACKET
        (* Single character tokens *)
        | Some '\'' ->
            advance t;
            make_token t QUOTE
        | Some '+' ->
            advance t;
            make_token t PLUS
        | Some '-' ->
            advance t;
            make_token t MINUS
        | Some '*' ->
            advance t;
            make_token t STAR
        | Some '/' ->
            advance t;
            make_token t SLASH
        | Some '>' ->
            advance t;
            make_token t GT
        | Some '<' ->
            advance t;
            make_token t LT
        | Some '=' ->
            advance t;
            make_token t EQ
        | Some '(' ->
            advance t;
            make_token t LPAREN
        | Some ')' ->
            advance t;
            make_token t RPAREN
        | Some '{' ->
            advance t;
            make_token t LBRACE
        | Some '}' ->
            advance t;
            make_token t RBRACE
        | Some '[' ->
            advance t;
            make_token t LBRACKET
        | Some ']' ->
            advance t;
            make_token t RBRACKET
        | Some ';' ->
            advance t;
            make_token t SEMICOLON
        | Some ',' ->
            advance t;
            make_token t COMMA
        | Some '!' ->
            advance t;
            make_token t BANG
        | Some '.' ->
            advance t;
            make_token t DOT
        | Some '#' ->
            advance t;
            make_token t HASH
        | Some '&' ->
            advance t;
            make_token t AMPERSAND
        | Some '^' ->
            advance t;
            make_token t CARET
        | Some '|' ->
            advance t;
            make_token t PIPE
        | Some '~' ->
            advance t;
            make_token t TILDE
        (* Unicode operators: ∈ (U+2208) and ∉ (U+2209) *)
        | Some '\xE2' when starts_with t "\xE2\x88\x88" ->
            (* ∈ (element of) - UTF-8: E2 88 88 *)
            t.index <- t.index + 3;
            make_token t IN
        | Some '\xE2' when starts_with t "\xE2\x88\x89" ->
            (* ∉ (not element of) - UTF-8: E2 88 89 *)
            t.index <- t.index + 3;
            make_token t NOTIN
        | Some c ->
            failwith
              (Printf.sprintf
                 "Tokenizer error at line %d, col %d: unexpected character '%c'"
                 t.line
                 (t.index - t.line_start + 1)
                 c
              )
      )

let tokenize src =
  let t = make_tokenizer src in
  let rec collect acc =
    let tok = next_token t in
      match tok.typ with
      | COMMENT _ -> collect acc (* Skip comments *)
      | EOF -> List.rev (tok :: acc)
      | _ -> collect (tok :: acc)
  in
    collect []

(** Parser state *)
type parser = {
  tokens : token list;
  mutable index : int;
  mutable bitwise : bool;
  mutable malloc_index : int;
}

let make_parser src =
  { tokens = tokenize src; index = 0; bitwise = false; malloc_index = 0 }

let current_token p =
  if p.index < List.length p.tokens then List.nth p.tokens p.index
  else { typ = EOF; line = 0; col = 0 }

let peek_token p = current_token p

let advance_parser p =
  if p.index < List.length p.tokens then p.index <- p.index + 1

let expect p expected =
  let tok = current_token p in
    if tok.typ = expected then (
      advance_parser p;
      tok
    )
    else
      failwith
        (Printf.sprintf "Parse error at line %d: expected %s" tok.line
           ( match expected with
           | EOF -> "EOF"
           | _ -> "token"
           )
        )

let expect_opt p expected =
  let tok = current_token p in
    if tok.typ = expected then (
      advance_parser p;
      Some tok
    )
    else None

(** AST types *)
type ast_expr =
  | EInt of Z.t
  | ERegister of string
  | EGlobal of string
  | EAtLoc of string
  | EASet of string
  | EMalloc of ast_expr
  | EBinOp of ast_expr * string * ast_expr
  | EUnOp of string * ast_expr
  | ETuple of ast_expr * ast_expr

type assign_info = { mode : mode; volatile : bool }

type ast_stmt =
  | SThread of { lhs : ast_stmt list; rhs : ast_stmt list }
  | SDerefStore of { pointer : ast_expr; expr : ast_expr; assign : assign_info }
  | SGlobalStore of { global : string; expr : ast_expr; assign : assign_info }
  | SGlobalLoad of { register : string; global : string; assign : assign_info }
  | SDeref of { register : string; pointer : ast_expr; assign : assign_info }
  | SCas of {
      register : string;
      params : ast_expr list;
      modes : mode list;
      assign : assign_info;
    }
  | SFAdd of {
      register : string;
      params : ast_expr list;
      modes : mode list;
      assign : assign_info;
    }
  | SRegisterStore of { register : string; expr : ast_expr }
  | SIf of {
      condition : ast_expr;
      body : ast_stmt list;
      else_body : ast_stmt list option;
    }
  | SWhile of { condition : ast_expr; body : ast_stmt list }
  | SQWhile of { condition : ast_expr; body : ast_stmt list }
  | SDo of { body : ast_stmt list; condition : ast_expr }
  | SQDo of { body : ast_stmt list; condition : ast_expr }
  | SFence of { mode : mode }
  | SLock of { global : string option }
  | SUnlock of { global : string option }
  | SFree of { register : string }
  | SMalloc of {
      register : string;
      size : ast_expr;
      pc : int;
      label : string list;
    }
  | SLabeled of { label : string list; stmt : ast_stmt }

type ast_config = {
  name : string;
  values : Z.t list;
  defacto : ast_expr list;
  constraint_ : ast_expr list;
}

type ast_assertion =
  | AOutcome of {
      outcome : string;
      condition : ast_expr;
      model : string option;
    }
  | AModel of { model : string }
  | AChained of { model : string; outcome : string; rest : ast_litmus }

and ast_litmus = {
  config : ast_config;
  program : ast_stmt list;
  assertion : ast_assertion option;
}

(** Expression parsing with precedence *)
let infix_prec = function
  | "^" | "|" | "&" -> (28, 29)
  | "*" | "/" -> (26, 27)
  | "+" | "-" -> (24, 25)
  | "=" | "!=" | "<" | ">" | "<=" | ">=" | "∈" | "∉" -> (22, 23)
  | "=>" -> (20, 21)
  | "&&" | "||" -> (18, 19)
  | _ -> (-1, -1)

let is_prefix_op = function
  | "!" | "~" | "&" -> true
  | _ -> false

let token_to_binop = function
  | PLUS -> Some "+"
  | MINUS -> Some "-"
  | STAR -> Some "*"
  | SLASH -> Some "/"
  | EQ -> Some "="
  | NEQ -> Some "!="
  | LT -> Some "<"
  | GT -> Some ">"
  | LEQ -> Some "<="
  | GEQ -> Some ">="
  | AND -> Some "&&"
  | OR -> Some "||"
  | AMPERSAND -> Some "&"
  | PIPE -> Some "|"
  | CARET -> Some "^"
  | ARROW -> Some "=>"
  | IN -> Some "∈"
  | NOTIN -> Some "∉"
  | _ -> None

let token_to_unop = function
  | BANG -> Some "!"
  | TILDE -> Some "~"
  | AMPERSAND -> Some "&"
  | _ -> None

let rec parse_expr p ?(min_prec = 0) () =
  let parse_atom () =
    match (current_token p).typ with
    | INT n ->
        advance_parser p;
        EInt n
    | REGISTER r ->
        advance_parser p;
        ERegister r
    | GLOBAL g ->
        advance_parser p;
        EGlobal g
    | ATLOC loc ->
        advance_parser p;
        EAtLoc loc
    | DOT -> (
        advance_parser p;
        match (current_token p).typ with
        | GLOBAL g ->
            advance_parser p;
            EASet g
        | _ -> failwith "Expected global after ."
      )
    | MALLOC ->
        advance_parser p;
        EMalloc (parse_expr p ())
    | _ ->
        failwith
          (Printf.sprintf
             "Parse error: unexpected token in expression at line %d"
             (current_token p).line
          )
  in

  let rec parse_prefix () =
    match (current_token p).typ with
    | LPAREN ->
        advance_parser p;
        let e = parse_expr p () in
        let _ = expect p RPAREN in
          e
    | LBRACKET ->
        advance_parser p;
        let v1 = parse_prefix () in
        let _ = expect p COMMA in
        let v2 = parse_prefix () in
        let _ = expect p RBRACKET in
          ETuple (v1, v2)
    | _ -> (
        match token_to_unop (current_token p).typ with
        | Some op ->
            advance_parser p;
            let rhs = parse_prefix () in
              EUnOp (op, rhs)
        | None -> parse_atom ()
      )
  in

  let rec parse_infix lhs =
    match token_to_binop (current_token p).typ with
    | Some op ->
        let left_prec, right_prec = infix_prec op in
          if left_prec < min_prec then lhs
          else (
            (* Track bitwise operators *)
            if List.mem op [ "~"; "&"; "|"; "^" ] then p.bitwise <- true;
            advance_parser p;
            let rhs = parse_expr p ~min_prec:right_prec () in
              parse_infix (EBinOp (lhs, op, rhs))
          )
    | None -> lhs
  in

  let lhs = parse_prefix () in
    parse_infix lhs

(** Parse memory order *)
let parse_memory_order p =
  match (current_token p).typ with
  | NONATOMIC ->
      advance_parser p;
      Nonatomic
  | RELAXED ->
      advance_parser p;
      Relaxed
  | RELEASE ->
      advance_parser p;
      Release
  | ACQUIRE ->
      advance_parser p;
      Acquire
  | SC ->
      advance_parser p;
      SC
  | NORMAL ->
      advance_parser p;
      Normal
  | STRONG ->
      advance_parser p;
      Strong
  | _ -> Relaxed

let parse_memory_order_opt p =
  match (current_token p).typ with
  | NONATOMIC | RELAXED | RELEASE | ACQUIRE | SC | NORMAL | STRONG ->
      Some (parse_memory_order p)
  | _ -> None

(** Parse assignment operators *)
let parse_assign p =
  match (current_token p).typ with
  | COLONRLX | ASSIGN ->
      advance_parser p;
      { mode = Relaxed; volatile = false }
  | COLONREL ->
      advance_parser p;
      { mode = Release; volatile = false }
  | COLONACQ ->
      advance_parser p;
      { mode = Acquire; volatile = false }
  | COLONSC ->
      advance_parser p;
      { mode = SC; volatile = false }
  | COLONVRLX | COLONV ->
      advance_parser p;
      { mode = Relaxed; volatile = true }
  | COLONVREL ->
      advance_parser p;
      { mode = Release; volatile = true }
  | COLONVACQ ->
      advance_parser p;
      { mode = Acquire; volatile = true }
  | COLONVSC ->
      advance_parser p;
      { mode = SC; volatile = true }
  | _ -> failwith "Expected assignment operator"

(** Parse parameter list *)
let parse_params p parse_elem =
  let _ = expect p LPAREN in
  let rec collect acc =
    if (current_token p).typ = RPAREN then (
      advance_parser p;
      List.rev acc
    )
    else
      let elem = parse_elem () in
      let acc' = elem :: acc in
        if (current_token p).typ = COMMA then (
          advance_parser p;
          collect acc'
        )
        else
          let _ = expect p RPAREN in
            List.rev acc'
  in
    collect []

(** Parse program statements *)
let rec parse_program p =
  let landmark = Landmark.register "parse_program" in
    Landmark.enter landmark;
    let rec parse_stmts acc labels =
      let tok = current_token p in
      let pc = tok.line in

      match tok.typ with
      | BACKTICK label ->
          advance_parser p;
          parse_stmts acc (label :: labels)
      | LBRACE ->
          advance_parser p;
          let lhs = parse_program p in
          let _ = expect p RBRACE in
          let _ = expect p PARALLEL in
          let _ = expect p LBRACE in
          let rhs = parse_program p in
          let _ = expect p RBRACE in
          let stmt = SThread { lhs; rhs } in
            parse_stmts (stmt :: acc) []
      | STAR ->
          advance_parser p;
          let pointer = parse_expr p () in
          let assign = parse_assign p in
          let expr = parse_expr p () in
          let stmt = SDerefStore { pointer; expr; assign } in
          let stmt =
            if labels <> [] then SLabeled { label = List.rev labels; stmt }
            else stmt
          in
            parse_stmts (stmt :: acc) []
      | GLOBAL g -> (
          advance_parser p;
          match (current_token p).typ with
          | COLONRLX
          | COLONREL
          | COLONACQ
          | COLONSC
          | COLONV
          | COLONVRLX
          | COLONVREL
          | COLONVACQ
          | COLONVSC
          | ASSIGN ->
              let assign = parse_assign p in
              let expr = parse_expr p () in
              let stmt = SGlobalStore { global = g; expr; assign } in
              let stmt =
                if labels <> [] then SLabeled { label = List.rev labels; stmt }
                else stmt
              in
                parse_stmts (stmt :: acc) []
          | DOT -> (
              advance_parser p;
              match (current_token p).typ with
              | STORE ->
                  advance_parser p;
                  let params = parse_params p (fun () -> parse_expr p ()) in
                  let expr = List.nth params 0 in
                  let mode =
                    if List.length params > 1 then
                      match List.nth params 1 with
                      | _ -> Relaxed (* Would need to parse mode from expr *)
                    else Relaxed
                  in
                  let assign = { mode; volatile = false } in
                  let stmt = SGlobalStore { global = g; expr; assign } in
                  let stmt =
                    if labels <> [] then
                      SLabeled { label = List.rev labels; stmt }
                    else stmt
                  in
                    parse_stmts (stmt :: acc) []
              | _ -> failwith "Expected store after ."
            )
          | _ -> failwith "Expected assignment after global"
        )
      | REGISTER r -> (
          advance_parser p;
          let assign = parse_assign p in
            match (current_token p).typ with
            | GLOBAL g ->
                advance_parser p;
                let mode =
                  match (current_token p).typ with
                  | DOT ->
                      advance_parser p;
                      let _ = expect p LOAD in
                      let _ = expect p LPAREN in
                      let m = parse_memory_order p in
                      let _ = expect p RPAREN in
                        m
                  | _ -> assign.mode
                in
                let assign = { assign with mode } in
                let stmt = SGlobalLoad { register = r; global = g; assign } in
                let stmt =
                  if labels <> [] then
                    SLabeled { label = List.rev labels; stmt }
                  else stmt
                in
                  parse_stmts (stmt :: acc) []
            | STAR ->
                advance_parser p;
                let pointer = parse_expr p () in
                let stmt = SDeref { register = r; pointer; assign } in
                let stmt =
                  if labels <> [] then
                    SLabeled { label = List.rev labels; stmt }
                  else stmt
                in
                  parse_stmts (stmt :: acc) []
            | CAS ->
                advance_parser p;
                let all_params =
                  parse_params p (fun () ->
                      match parse_memory_order_opt p with
                      | Some m -> `Mode m
                      | None -> `Expr (parse_expr p ())
                  )
                in
                let modes =
                  List.filter_map
                    (function
                      | `Mode m -> Some m
                      | _ -> None
                      )
                    all_params
                in
                let params =
                  List.filter_map
                    (function
                      | `Expr e -> Some e
                      | _ -> None
                      )
                    all_params
                in
                let stmt = SCas { register = r; params; modes; assign } in
                let stmt =
                  if labels <> [] then
                    SLabeled { label = List.rev labels; stmt }
                  else stmt
                in
                  parse_stmts (stmt :: acc) []
            | FADD ->
                advance_parser p;
                let all_params =
                  parse_params p (fun () ->
                      match parse_memory_order_opt p with
                      | Some m -> `Mode m
                      | None -> `Expr (parse_expr p ())
                  )
                in
                let modes =
                  List.filter_map
                    (function
                      | `Mode m -> Some m
                      | _ -> None
                      )
                    all_params
                in
                let params =
                  List.filter_map
                    (function
                      | `Expr e -> Some e
                      | _ -> None
                      )
                    all_params
                in
                let stmt = SFAdd { register = r; params; modes; assign } in
                let stmt =
                  if labels <> [] then
                    SLabeled { label = List.rev labels; stmt }
                  else stmt
                in
                  parse_stmts (stmt :: acc) []
            | _ ->
                let expr = parse_expr p () in
                let stmt = SRegisterStore { register = r; expr } in
                let stmt =
                  if labels <> [] then
                    SLabeled { label = List.rev labels; stmt }
                  else stmt
                in
                  parse_stmts (stmt :: acc) []
        )
      | IF ->
          advance_parser p;
          let _ = expect p LPAREN in
          let condition = parse_expr p () in
          let _ = expect p RPAREN in
          let _ = expect p LBRACE in
          let body = parse_program p in
          let _ = expect p RBRACE in
          let else_body =
            match expect_opt p ELSE with
            | Some _ ->
                let _ = expect p LBRACE in
                let else_stmts = parse_program p in
                let _ = expect p RBRACE in
                  if else_stmts = [] then None else Some else_stmts
            | None -> None
          in
          let stmt = SIf { condition; body; else_body } in
          let stmt =
            if labels <> [] then SLabeled { label = List.rev labels; stmt }
            else stmt
          in
            parse_stmts (stmt :: acc) []
      | WHILE ->
          advance_parser p;
          let _ = expect p LPAREN in
          let condition = parse_expr p () in
          let _ = expect p RPAREN in
          let _ = expect p LBRACE in
          let body = parse_program p in
          let _ = expect p RBRACE in
          let stmt = SWhile { condition; body } in
          let stmt =
            if labels <> [] then SLabeled { label = List.rev labels; stmt }
            else stmt
          in
            parse_stmts (stmt :: acc) []
      | QWHILE ->
          advance_parser p;
          let _ = expect p LPAREN in
          let condition = parse_expr p () in
          let _ = expect p RPAREN in
          let _ = expect p LBRACE in
          let body = parse_program p in
          let _ = expect p RBRACE in
          let stmt = SQWhile { condition; body } in
          let stmt =
            if labels <> [] then SLabeled { label = List.rev labels; stmt }
            else stmt
          in
            parse_stmts (stmt :: acc) []
      | DO ->
          advance_parser p;
          let _ = expect p LBRACE in
          let body = parse_program p in
          let _ = expect p RBRACE in
          let _ = expect p WHILE in
          let _ = expect p LPAREN in
          let condition = parse_expr p () in
          let _ = expect p RPAREN in
          let stmt = SDo { body; condition } in
            parse_stmts (stmt :: acc) []
      | QDO ->
          advance_parser p;
          let _ = expect p LBRACE in
          let body = parse_program p in
          let _ = expect p RBRACE in
          let _ = expect p QWHILE in
          let _ = expect p LPAREN in
          let condition = parse_expr p () in
          let _ = expect p RPAREN in
          let stmt = SQDo { body; condition } in
            parse_stmts (stmt :: acc) []
      | FENCE ->
          advance_parser p;
          let _ = expect p LPAREN in
          let mode = parse_memory_order p in
          let _ = expect p RPAREN in
          let stmt = SFence { mode } in
          let stmt =
            if labels <> [] then SLabeled { label = List.rev labels; stmt }
            else stmt
          in
            parse_stmts (stmt :: acc) []
      | LOCK ->
          advance_parser p;
          let global =
            match (current_token p).typ with
            | GLOBAL g ->
                advance_parser p;
                Some g
            | _ -> None
          in
          let stmt = SLock { global } in
          let stmt =
            if labels <> [] then SLabeled { label = List.rev labels; stmt }
            else stmt
          in
            parse_stmts (stmt :: acc) []
      | UNLOCK ->
          advance_parser p;
          let global =
            match (current_token p).typ with
            | GLOBAL g ->
                advance_parser p;
                Some g
            | _ -> None
          in
          let stmt = SUnlock { global } in
          let stmt =
            if labels <> [] then SLabeled { label = List.rev labels; stmt }
            else stmt
          in
            parse_stmts (stmt :: acc) []
      | FREE -> (
          advance_parser p;
          let _ = expect p LPAREN in
            match (current_token p).typ with
            | GLOBAL g ->
                advance_parser p;
                let _ = expect p RPAREN in
                  (* Generate load from global *)
                  p.malloc_index <- p.malloc_index - 1;
                  let reg = Printf.sprintf "r%d" p.malloc_index in
                  let load_stmt =
                    SGlobalLoad
                      {
                        register = reg;
                        global = g;
                        assign = { mode = Relaxed; volatile = false };
                      }
                  in
                  let free_stmt = SFree { register = reg } in
                    parse_stmts (free_stmt :: load_stmt :: acc) []
            | REGISTER r ->
                advance_parser p;
                let _ = expect p RPAREN in
                let stmt = SFree { register = r } in
                let stmt =
                  if labels <> [] then
                    SLabeled { label = List.rev labels; stmt }
                  else stmt
                in
                  parse_stmts (stmt :: acc) []
            | _ -> failwith "Expected register or global in free"
        )
      | SKIP ->
          advance_parser p;
          parse_stmts acc []
      | SEMICOLON ->
          advance_parser p;
          parse_stmts acc labels
      | RBRACE | PARALLEL | PERCENT | EOF ->
          (* End of block *)
          List.rev acc
      | _ ->
          failwith
            (Printf.sprintf "Unexpected token in program at line %d" tok.line)
    in

    let stmts = parse_stmts [] [] in

    (* Post-process malloc expressions *)
    let process_malloc stmts =
      List.fold_right
        (fun stmt acc ->
          match stmt with
          | SGlobalStore { global; expr = EMalloc size; assign } ->
              p.malloc_index <- p.malloc_index - 1;
              let reg = Printf.sprintf "r%d" p.malloc_index in
              let malloc_stmt =
                SMalloc { register = reg; size; pc = 0; label = [] }
              in
              let store_stmt =
                SGlobalStore { global; expr = ERegister reg; assign }
              in
                malloc_stmt :: store_stmt :: acc
          | SRegisterStore { register; expr = EMalloc size } ->
              let malloc_stmt =
                SMalloc { register; size; pc = 0; label = [] }
              in
                malloc_stmt :: acc
          | _ -> stmt :: acc
        )
        stmts []
    in
      Landmark.exit landmark;
      process_malloc stmts

(** Parse configuration *)
let parse_config p =
  let name = ref "" in
  let values = ref [] in
  let defacto = ref [] in
  let constraint_ = ref [] in

  (* Parse name *)
  ( if expect_opt p NAME <> None then
      let _ = expect p EQ in
        while
          not
            (List.mem (current_token p).typ
               [ VALUES; LBRACKET; PERCENT; LDBRACKET ]
            )
        do
          ( match (current_token p).typ with
          | GLOBAL g | REGISTER g -> name := !name ^ g
          | INT n -> name := !name ^ Z.to_string n
          | _ -> ()
          );
          advance_parser p
        done
  );

  (* Parse values *)
  if expect_opt p VALUES <> None then (
    let _ = expect p EQ in
    let _ = expect p LBRACE in
      while (current_token p).typ <> RBRACE do
        ( match (current_token p).typ with
        | INT n ->
            values := n :: !values;
            advance_parser p
        | _ -> advance_parser p
        );
        let _ = expect_opt p COMMA in
          ()
      done;
      let _ = expect p RBRACE in
        ()
  );

  (* Parse defacto *)
  while expect_opt p LBRACKET <> None do
    let expr = parse_expr p () in
      defacto := expr :: !defacto;
      let _ = expect p RBRACKET in
        ()
  done;

  (* Parse constraints *)
  while expect_opt p LDBRACKET <> None do
    let expr = parse_expr p () in
      constraint_ := expr :: !constraint_;
      let _ = expect p RDBRACKET in
        ()
  done;

  (* Skip to %% if we parsed config *)
  if !name <> "" || !values <> [] || !defacto <> [] || !constraint_ <> [] then
    while (current_token p).typ <> PERCENT do
      advance_parser p
    done;
  (* Always consume %% if present *)
  let _ = expect_opt p PERCENT in
    ();

    {
      name = !name;
      values = List.rev !values;
      defacto = List.rev !defacto;
      constraint_ = List.rev !constraint_;
    }

(** Parse litmus test *)
let rec parse_litmus p =
  let config = parse_config p in
    p.bitwise <- false;
    let program = parse_program p in
    let assertion =
      if expect_opt p PERCENT <> None then Some (parse_assertion p) else None
    in
      { config; program; assertion }

(** Parse assertion *)
and parse_assertion p =
  let parse_outcome () =
    match (current_token p).typ with
    | ALLOW ->
        advance_parser p;
        "allow"
    | FORBID ->
        advance_parser p;
        "forbid"
    | _ -> failwith "Expected allow or forbid"
  in

  let parse_check () =
    let _ = expect p LBRACKET in
      if expect_opt p RBRACKET <> None then (None, None)
      else
        let model =
          match (current_token p).typ with
          | GLOBAL g | REGISTER g -> Some g
          | SC -> Some "sc"
          | RELAXED -> Some "relaxed"
          | RELEASE -> Some "release"
          | ACQUIRE -> Some "acquire"
          | NONATOMIC -> Some "nonatomic"
          | NORMAL -> Some "normal"
          | STRONG -> Some "strong"
          | _ -> None
        in
          if model <> None then advance_parser p;
          let outcome =
            if expect_opt p EQ <> None then Some (parse_outcome ()) else None
          in
          let _ = expect p RBRACKET in
            (model, outcome)
  in

  if (current_token p).typ = LBRACKET then
    let model, _ = parse_check () in
      AModel { model = Option.value model ~default:"" }
  else if expect_opt p RARROW <> None then
    let model, outcome = parse_check () in
    let _ = expect p PERCENT in
    let rest = parse_litmus p in
      AChained
        {
          model = Option.value model ~default:"";
          outcome = Option.value outcome ~default:"allow";
          rest;
        }
  else
    let outcome = parse_outcome () in
    let condition = parse_expr p () in
    let model, _ = parse_check () in
      AOutcome { outcome; condition; model }

(** Main parse function *)
let parse src =
  let p = make_parser src in
    parse_litmus p

(** Convert AST to Types.expr for compatibility *)
let rec ast_expr_to_expr = function
  | EInt n -> ENum n
  | ERegister r -> EVar r
  | EGlobal g -> EVar g
  | EAtLoc l -> EVar l
  | EASet s -> EVar ("." ^ s)
  | EMalloc e -> EUnOp ("malloc", VExpression (ast_expr_to_expr e))
  | EBinOp (l, op, r) ->
      EBinOp
        (VExpression (ast_expr_to_expr l), op, VExpression (ast_expr_to_expr r))
  | EUnOp (op, e) -> EUnOp (op, VExpression (ast_expr_to_expr e))
  | ETuple (e1, e2) ->
      (* Represent tuple as a special binop *)
      EBinOp
        ( VExpression (ast_expr_to_expr e1),
          ",",
          VExpression (ast_expr_to_expr e2)
        )
