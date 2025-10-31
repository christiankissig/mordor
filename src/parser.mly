%{
(** Parser for sMRD litmus tests *)

[@@@warning "-69"] (* Disable unused field warnings - fields are used externally *)

(* Import AST types from Ast module *)
open Ast

(* Helper to create labeled statements *)
let make_labeled labels stmt =
  if labels = [] then stmt
  else SLabeled { label = List.rev labels; stmt }

%}

(* Token declarations *)
%token NONATOMIC RELAXED RELEASE ACQUIRE STRONG NORMAL SC
%token FADD CAS IF ELSE WHILE DO SKIP QDO QWHILE FENCE
%token MALLOC FREE LOCK UNLOCK LOAD STORE
%token ALLOW FORBID NAME VALUES
%token <Z.t> INT
%token <string> REGISTER ATLOC GLOBAL STRING BACKTICK
%token QUOTE PLUS MINUS STAR SLASH RARROW
%token AND OR PERCENT NEQ GEQ GT LEQ LT ASSIGN EQ
%token LPAREN RPAREN LBRACE RBRACE LDBRACKET RDBRACKET
%token LBRACKET RBRACKET SEMICOLON COMMA BANG DOT
%token AMPERSAND CARET PIPE TILDE IN NOTIN FORALL PARALLEL
%token COLONRLX COLONREL COLONACQ COLONSC
%token COLONV COLONVRLX COLONVREL COLONVACQ COLONVSC
%token EOF

(* Operator precedence and associativity *)
%left OR
%left AND
%left PIPE
%left CARET
%left AMPERSAND
%left EQ NEQ
%left LT GT LEQ GEQ IN NOTIN
%left PLUS MINUS
%left STAR SLASH PERCENT
%right BANG TILDE
%left DOT

(* Start symbols *)
%start <Ast.ast_litmus> litmus
%start <Ast.ast_expr> expr_only

%%

(* Main litmus test *)
litmus:
  | config=config? program=program assertion=assertion? EOF
    { { config; program; assertion } }
  ;

(* Configuration *)
config:
  c=config_body PERCENT PERCENT { c }

config_body:
  | name=name_section? values=values_section? defacto=defacto_list
  constraint_=constraint_list
    { {
        name = (match name with Some n -> n | None -> "");
        values = (match values with Some v -> v | None -> []);
        defacto;
        constraint_;
      } }
  ;

name_section:
  | NAME EQ name_parts=name_part+ { String.concat "" name_parts }
  ;

name_part:
  | GLOBAL { $1 }
  | REGISTER { $1 }
  | INT { Z.to_string $1 }
  ;

int_list:
  | (* empty *) { [] }
  | n=INT { [n] }
  | n=INT COMMA rest=int_list { n :: rest }
  ;

values_section:
  | VALUES EQ LBRACE values=int_list RBRACE { values }
  ;

defacto_list:
  | { [] }
  | defacto=defacto_item rest=defacto_list { defacto :: rest }
  ;

defacto_item:
  | LBRACKET e=expr RBRACKET { e }
  ;

constraint_list:
  | { [] }
  | c=constraint_item rest=constraint_list { c :: rest }
  ;

constraint_item:
  | LDBRACKET e=expr RDBRACKET { e }
  ;

(* Program - list of statements and threads *)
program:
  | stmts=statement_list { stmts }
  ;

threads:
  | t=thread { [t] }
  | t=thread PARALLEL rest=threads { t :: rest }
  ;

(* Thread - statements enclosed in braces *)
thread:
  | LBRACE stmts=statement_list RBRACE { stmts }
  ;

statement_list:
  | s=statement { [s] }
  | s=statement rest=statement_list { s :: rest }
  ;

(* Statement with optional labels *)
statement:
  | labels=label_list s=stmt_base { make_labeled labels s }
  | SEMICOLON { SSkip }
  | threads=threads SEMICOLON? { SThreads { threads } }
  ;

label_list:
  | (* empty *) { [] }
  | l=label rest=label_list { l :: rest }
  ;

label:
  | BACKTICK { $1 }
  ;

stmt_base:

  (* Volatile pointer load pattern: :v= *reg := expr *)
  | mode=volatile_assign_mode STAR reg=REGISTER ASSIGN e=expr
    { let load, assign = mode in
      SRegisterStore {
        register = reg;
        expr = ELoad { address = e; load }
      } }

  (* Regular register store: reg := expr *)
  | reg=REGISTER ASSIGN e=expr
    { SRegisterStore { register = reg; expr = e } }

  (* Global store with memory order: global :mode= expr *)
  | global=GLOBAL mode=assign_mode e=expr
    { SGlobalStore { global; expr = e; assign = mode } }

  (* Pointer store: *expr := expr *)
  | STAR e1=expr ASSIGN e2=expr
    { SStore { address = e1; expr = e2; assign = { mode = Relaxed; volatile = false } } }

  (* Explicit load: reg := load(mode, expr) *)
  | reg=REGISTER ASSIGN LOAD LPAREN mode=memory_order COMMA e=expr RPAREN
    { SRegisterStore {
        register = reg;
        expr = ELoad { address = e; load = { mode; volatile = false } }
      } }

  (* Explicit store: store(mode, addr, val) *)
  | STORE LPAREN mode=memory_order COMMA e1=expr COMMA e2=expr RPAREN
    { SStore {
        address = e1;
        expr = e2;
        assign = { mode; volatile = false }
      } }

  (* CAS: reg := cas(mode, addr, expected, desired) *)
  | reg=REGISTER ASSIGN CAS LPAREN mode=memory_order COMMA e1=expr COMMA e2=expr COMMA e3=expr RPAREN
    { SCAS {
        register = reg;
        address = e1;
        expected = e2;
        desired = e3;
        mode
      } }

  (* FADD: reg := fadd(mode, addr, operand) *)
  | reg=REGISTER ASSIGN FADD LPAREN mode=memory_order COMMA e1=expr COMMA e2=expr RPAREN
    { SFADD {
        register = reg;
        address = e1;
        operand = e2;
        mode
      } }

  (* Control flow *)
  | IF LPAREN cond=expr RPAREN then_body=block_or_stmt else_part=else_clause?
    { SIf { condition = cond; then_body; else_body = else_part } }

  | WHILE LPAREN cond=expr RPAREN body=block_or_stmt
    { SWhile { condition = cond; body } }

  | DO body=block_or_stmt WHILE LPAREN cond=expr RPAREN
    { SDo { body; condition = cond } }

  | QDO body=block_or_stmt QWHILE LPAREN cond=expr RPAREN
    { SQDo { body; condition = cond } }

  (* Fence *)
  | FENCE LPAREN mode=memory_order RPAREN
    { SFence { mode } }

  (* Lock/Unlock *)
  | LOCK global=GLOBAL?
    { SLock { global } }

  | UNLOCK global=GLOBAL?
    { SUnlock { global } }

  (* Malloc *)
  | MALLOC LPAREN reg=REGISTER COMMA size=expr RPAREN
    { SMalloc { register = reg; size; pc = 0; label = [] } }
  | MALLOC reg=REGISTER COMMA size=expr
    { SMalloc { register = reg; size; pc = 0; label = [] } }

  (* Free *)
  | FREE LPAREN reg=REGISTER RPAREN
    { SFree { register = reg } }

  | FREE LPAREN global=GLOBAL RPAREN
    { (* Generate a load from global then free *)
      SFree { register = "tmp_" ^ global } }

  (* Skip *)
  | SKIP
    { SSkip }
  ;

block_or_stmt:
  | LBRACE stmts=statement_list RBRACE { stmts }
  | s=stmt_base { [s] }
  ;

else_clause:
  | ELSE body=block_or_stmt { body }
  ;

(* Assignment modes *)
assign_mode:
  | COLONRLX { { mode = Relaxed; volatile = false } }
  | COLONREL { { mode = Release; volatile = false } }
  | COLONACQ { { mode = Acquire; volatile = false } }
  | COLONSC { { mode = SC; volatile = false } }
  | ASSIGN { { mode = Relaxed; volatile = false } }
  ;

volatile_assign_mode:
  | COLONVRLX { ({ mode = Relaxed; volatile = true }, { mode = Relaxed; volatile = true }) }
  | COLONVREL { ({ mode = Release; volatile = true }, { mode = Release; volatile = true }) }
  | COLONVACQ { ({ mode = Acquire; volatile = true }, { mode = Acquire; volatile = true }) }
  | COLONVSC { ({ mode = SC; volatile = true }, { mode = SC; volatile = true }) }
  | COLONV { ({ mode = Relaxed; volatile = true }, { mode = Relaxed; volatile = true }) }
  ;

memory_order:
  | NONATOMIC { Nonatomic }
  | RELAXED { Relaxed }
  | RELEASE { Release }
  | ACQUIRE { Acquire }
  | SC { SC }
  | NORMAL { Normal }
  | STRONG { Strong }
  ;

(* Expressions *)
expr_only:
  | e=expr EOF { e }
  ;

expr:
  | e1=expr PLUS e2=expr { EBinOp (e1, "+", e2) }
  | e1=expr MINUS e2=expr { EBinOp (e1, "-", e2) }
  | e1=expr STAR e2=expr { EBinOp (e1, "*", e2) }
  | e1=expr SLASH e2=expr { EBinOp (e1, "/", e2) }
  | e1=expr PERCENT e2=expr { EBinOp (e1, "%", e2) }
  | e1=expr AND e2=expr { EBinOp (e1, "&&", e2) }
  | e1=expr OR e2=expr { EBinOp (e1, "||", e2) }
  | e1=expr PIPE e2=expr { EBinOp (e1, "|", e2) }
  | e1=expr AMPERSAND e2=expr { EBinOp (e1, "&", e2) }
  | e1=expr CARET e2=expr { EBinOp (e1, "^", e2) }
  | e1=expr EQ e2=expr { EBinOp (e1, "==", e2) }
  | e1=expr NEQ e2=expr { EBinOp (e1, "!=", e2) }
  | e1=expr LT e2=expr { EBinOp (e1, "<", e2) }
  | e1=expr GT e2=expr { EBinOp (e1, ">", e2) }
  | e1=expr LEQ e2=expr { EBinOp (e1, "<=", e2) }
  | e1=expr GEQ e2=expr { EBinOp (e1, ">=", e2) }
  | e1=expr IN e2=expr { EBinOp (e1, "in", e2) }
  | e1=expr NOTIN e2=expr { EBinOp (e1, "notin", e2) }
  | e1=expr COMMA e2=expr { ETuple (e1, e2) }
  | e1=expr DOT e2=expr { EBinOp (e1, ".", e2) }
  | LPAREN e1=expr COMMA e2=expr RPAREN { ETuple (e1, e2) }

  | BANG e=expr { EUnOp ("!", e) }
  | TILDE e=expr { EUnOp ("~", e) }
  | MINUS e=expr %prec BANG { EUnOp ("-", e) }
  | STAR e=expr %prec BANG { EUnOp ("*", e) }
  | AMPERSAND e=expr %prec BANG { EUnOp ("&", e) }

  | MALLOC LPAREN e=expr RPAREN { EMalloc e }
  | MALLOC e=expr { EMalloc e }
  | LOAD LPAREN mode=memory_order COMMA e=expr RPAREN
    { ELoad { address = e; load = { mode; volatile = false } } }

  | FORALL e=expr { EUnOp ("forall", e) }

  | LPAREN e=expr RPAREN { e }

  | n=INT { EInt n }
  | reg=REGISTER { ERegister reg }
  | global=GLOBAL { EGlobal global }
  | atloc=ATLOC { EAtLoc atloc }
  | DOT s=STRING { EASet s }
  | QUOTE s=STRING { EASet s }
  ;

(* Assertion *)
assertion:
  | PERCENT PERCENT a=assertion_body { a }
  ;

assertion_body:
  | LBRACKET model=model_name? RBRACKET
    { AModel { model = (match model with Some m -> m | None -> "") } }

  | RARROW check=assertion_check PERCENT rest=litmus
    { let model, outcome = check in
      AChained {
        model = (match model with Some m -> m | None -> "");
        outcome = (match outcome with Some o -> o | None -> "allow");
        rest;
      } }

  | outcome=outcome_keyword cond=expr check=assertion_check
    { let model, _ = check in
      AOutcome {
        outcome;
        condition = cond;
        model = model;
      } }
  ;

assertion_check:
  | LBRACKET model=model_name? eq=outcome_eq? RBRACKET
    { (model, eq) }
  | (* empty *) { (None, None) }
  ;

outcome_eq:
  | EQ outcome=outcome_keyword { outcome }
  ;

outcome_keyword:
  | ALLOW { "allow" }
  | FORBID { "forbid" }
  ;

model_name:
  | GLOBAL { $1 }
  | REGISTER { $1 }
  | SC { "sc" }
  | RELAXED { "relaxed" }
  | RELEASE { "release" }
  | ACQUIRE { "acquire" }
  | NONATOMIC { "nonatomic" }
  | NORMAL { "normal" }
  | STRONG { "strong" }
  ;

%%
