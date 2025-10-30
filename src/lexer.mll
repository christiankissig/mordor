{
(** Lexer for sMRD litmus tests *)

exception Lexer_error of string

}

(* Regular expressions *)
let whitespace = [' ' '\t' '\r' '\n']
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z' '_']
let alnum = alpha | digit
let hex_digit = digit | ['a'-'f' 'A'-'F']

(* Main lexer rule *)
rule token = parse
  | [' ' '\t' '\r']+      { token lexbuf }
  | '\n'                  { Lexing.new_line lexbuf; token lexbuf }
  | "//" [^ '\n']* '\n'   { Lexing.new_line lexbuf; token lexbuf }
  | "//" [^ '\n']* eof    { token lexbuf }

  (* Keywords *)
  | "nonatomic"           { Parser.NONATOMIC }
  | "na"                  { Parser.NONATOMIC }
  | "relaxed"             { Parser.RELAXED }
  | "rlx"                 { Parser.RELAXED }
  | "release"             { Parser.RELEASE }
  | "rel"                 { Parser.RELEASE }
  | "acquire"             { Parser.ACQUIRE }
  | "acq"                 { Parser.ACQUIRE }
  | "strong"              { Parser.STRONG }
  | "normal"              { Parser.NORMAL }
  | "sequentially_consistent" { Parser.SC }
  | "sc"                  { Parser.SC }
  | "FADD"                { Parser.FADD }
  | "fadd"                { Parser.FADD }
  | "CAS"                 { Parser.CAS }
  | "cas"                 { Parser.CAS }
  | "if"                  { Parser.IF }
  | "else"                { Parser.ELSE }
  | "while"               { Parser.WHILE }
  | "do"                  { Parser.DO }
  | "skip"                { Parser.SKIP }
  | "qdo"                 { Parser.QDO }
  | "qwhile"              { Parser.QWHILE }
  | "fence"               { Parser.FENCE }
  | "malloc"              { Parser.MALLOC }
  | "free"                { Parser.FREE }
  | "lock"                { Parser.LOCK }
  | "unlock"              { Parser.UNLOCK }
  | "load"                { Parser.LOAD }
  | "store"               { Parser.STORE }
  | "allow"               { Parser.ALLOW }
  | "forbid"              { Parser.FORBID }
  | "name"                { Parser.NAME }
  | "values"              { Parser.VALUES }

  (* Multi-character operators (must come before single-char ones) *)
  | ":rlx="               { Parser.COLONRLX }
  | ":rel="               { Parser.COLONREL }
  | ":acq="               { Parser.COLONACQ }
  | ":sc="                { Parser.COLONSC }
  | ":vrlx="              { Parser.COLONVRLX }
  | ":vrel="              { Parser.COLONVREL }
  | ":vacq="              { Parser.COLONVACQ }
  | ":vsc="               { Parser.COLONVSC }
  | ":v="                 { Parser.COLONV }
  | ":="                  { Parser.ASSIGN }
  | "~~>"                 { Parser.RARROW }
  | "!="                  { Parser.NEQ }
  | ">="                  { Parser.GEQ }
  | "<="                  { Parser.LEQ }
  | "=="                  { Parser.EQ }
  | "[["                  { Parser.LDBRACKET }
  | "]]"                  { Parser.RDBRACKET }
  | "|||"                 { Parser.PARALLEL }
  | "||"                  { Parser.OR }
  | "&&"                  { Parser.AND }
  | "in"                  { Parser.IN }
  | "notin"               { Parser.NOTIN }
  | "forall"              { Parser.FORALL }

  (* Single-character operators and delimiters *)
  | "+"                   { Parser.PLUS }
  | "-"                   { Parser.MINUS }
  | "*"                   { Parser.STAR }
  | "/"                   { Parser.SLASH }
  | "%"                   { Parser.PERCENT }
  | ">"                   { Parser.GT }
  | "<"                   { Parser.LT }
  | "="                   { Parser.EQ }
  | "("                   { Parser.LPAREN }
  | ")"                   { Parser.RPAREN }
  | "{"                   { Parser.LBRACE }
  | "}"                   { Parser.RBRACE }
  | "["                   { Parser.LBRACKET }
  | "]"                   { Parser.RBRACKET }
  | ";"                   { Parser.SEMICOLON }
  | ","                   { Parser.COMMA }
  | "!"                   { Parser.BANG }
  | "."                   { Parser.DOT }
  | "&"                   { Parser.AMPERSAND }
  | "^"                   { Parser.CARET }
  | "|"                   { Parser.PIPE }
  | "~"                   { Parser.TILDE }
  | "'"                   { Parser.QUOTE }

  (* Numbers - handle both decimal and hex *)
  | digit+ as num
  | "0x" hex_digit+ as num { Parser.INT (Z.of_string num) }

  (* Registers *)
  | 'r' alnum+ as reg     { Parser.REGISTER reg }

  (* AtLoc variables *)
  | '@' alnum+ as loc     { Parser.ATLOC loc }

  (* Strings *)
  | '"' ([^ '"']* as str) '"' { Parser.STRING str }

  (* Backticks *)
  | '`' ([^ '`']* as label) '`' { Parser.BACKTICK label }

  (* Global variables (identifiers) *)
  | alpha alnum* as id    { Parser.GLOBAL id }

  | eof                   { Parser.EOF }
  | _ as c                { raise (Lexer_error (Printf.sprintf "Unexpected character: %c" c)) }
