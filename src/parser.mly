%{
(** Parser for MoRDor litmus tests *)

open Ast
open Parser_state
open Types

%}

(* Token declarations *)
%token NONATOMIC RELAXED RELEASE ACQUIRE STRONG NORMAL SC RELACQ
%token FADD CAS IF ELSE WHILE DO FENCE
%token MALLOC FREE LOCK UNLOCK
%token ALLOW FORBID NAME MODEL VALUES
%token LOAD STORE SKIP
%token <Z.t> INT
%token <string> REGISTER ATLOC GLOBAL STRING BACKTICK
%token QUOTE PLUS MINUS STAR SLASH RARROW
%token AND OR PERCENT NEQ GEQ GT LEQ LT ASSIGN EQ
%token LPAREN RPAREN LBRACE RBRACE LDBRACKET RDBRACKET
%token LBRACKET RBRACKET SEMICOLON COMMA BANG DOT
%token AMPERSAND CARET PIPE TILDE IN NOTIN FORALL PARALLEL
%token COLONRLX COLONREL COLONACQ COLONSC
%token COLONV COLONVRLX COLONVREL COLONVACQ COLONVSC
%token UNDERSCORE
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
  | name=name_section? model=config_model_section? values=values_section?
  defacto=defacto_list constraints=constraint_list
    { {
        name;
        model;
        values = (match values with Some v -> v | None -> []);
        defacto;
        constraints;
      } }
  ;

name_section:
  | NAME EQ name_parts=name_part+ { String.concat "" name_parts }
  | NAME EQ n=STRING { n }
  ;

name_part:
  | GLOBAL { $1 }
  | REGISTER { $1 }
  | INT { Z.to_string $1 }
  ;

config_model_section:
  | MODEL EQ model_name=model_name { model_name }
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
  | t1=thread PARALLEL t2=thread {
      inc_thread_id();
      let threads = [t1] in
      inc_thread_id();
      threads @ [t2]
    }
  | t=thread PARALLEL rest=threads { inc_thread_id(); t :: rest }
  ;

thread:
  | LBRACE
    stmts=statement_list
    RBRACE
    {
      push_thread();
      let result = stmts in
      pop_thread();
      result
    }
  ;

statement_list:
  | s=statement SEMICOLON rest=statement_list { s :: rest }
  | s=statement SEMICOLON { [s] }
  | s=statement { [s] }
;

statement:
  (* Statement with optional labels *)
| labels=label_list s=stmt_base {
      inc_pc ();
      let span = make_source_span $startpos $endpos in
      make_ast_node
        ~thread_ctx:(Some (current_thread_ctx()))
        ~src_ctx:(Some (current_src_ctx()))
        ~loop_ctx:(Some (current_loop_ctx()))
        ~source_span:(Some span)
        (make_labeled labels s)
    }
  (* Parallel threads *)
  | threads=threads {
      let span = make_source_span $startpos $endpos in
      make_ast_node
        ~thread_ctx:(Some (current_thread_ctx()))
        ~src_ctx:(Some (current_src_ctx()))
        ~loop_ctx:(Some (current_loop_ctx()))
        ~source_span:(Some span)
        (SThreads { threads })
    }
  ;

label_list:
  | (* empty *) { [] }
  | l=label rest=label_list { l :: rest }
  ;

label:
  | BACKTICK { $1 }
  ;

stmt_base:

  (** Register to register move **)

  (* Register assign from register: reg1 := reg2 *)
  (* needed to contrast load from global below *)
  | reg1=REGISTER ASSIGN reg2=REGISTER
    { SRegisterStore { register = reg1; expr = ERegister reg2 } }

  | reg=REGISTER ASSIGN AMPERSAND global=GLOBAL
    { SRegisterRefAssign { register = reg; global } }

  (** Loads from global variables **)

  (** Load from global variables **)

  (* Load from global with default memory order: reg := global *)
  | reg=REGISTER ASSIGN global=GLOBAL
    { SGlobalLoad {
        register = reg;
        global;
        load = { mode = Relaxed; volatile = false }
    } }

  | reg=REGISTER ASSIGN global=GLOBAL DOT LOAD LPAREN RPAREN
    { SGlobalLoad {
        register = reg;
        global;
        load = { mode = Relaxed; volatile = false }
    } }

  (* Volatile load from global pattern 2: reg := :v= global *)
  | reg=REGISTER mode=volatile_assign_mode global=GLOBAL
    { let load, assign = mode in
      SGlobalLoad {
        register = reg;
        global;
        load
      } }

  (* Explicit load from global with memory order: reg :mode= global *)
  | reg=REGISTER mode=assign_mode global=GLOBAL
    { SGlobalLoad {
      register = reg;
        global;
        load = mode
      } }

  | reg=REGISTER ASSIGN global=GLOBAL DOT LOAD LPAREN mode=mode RPAREN
    { SGlobalLoad {
      register = reg;
        global;
        load = mode
      } }

  (** Loads from pointers **)

  (* Pointer load: reg := *expr *)
  | reg=REGISTER ASSIGN STAR e=expr
    { SLoad {
        register = reg;
        address = e;
        load = { mode = Relaxed; volatile = false }
    } }

  (* Volatile pointer load pattern 2: reg :v= *expr *)
  | reg=REGISTER mode=volatile_assign_mode  STAR e=expr
    { let load, assign = mode in
      SLoad {
        register = reg;
        address = e;
        load
      } }

  (* Explicit pointer load: reg :mode= *expr *)
  | reg=REGISTER mode=assign_mode STAR e=expr
    { SLoad {
        register = reg;
        address = e;
        load = mode
      } }

  (** Register store *)

  (* Regular register store: reg := expr *)
  | reg=REGISTER ASSIGN e=expr
    { SRegisterStore { register = reg; expr = e } }

  (** Stores to global variables **)

  (* Global store with default memory order: global := expr *)
  | global=GLOBAL ASSIGN e=expr
    { SGlobalStore { global; expr = e; assign = { mode = Relaxed; volatile =
      false } } }

  | global=GLOBAL DOT STORE LPAREN e=expr RPAREN
    { SGlobalStore { global; expr = e; assign = { mode = Relaxed; volatile =
      false } } }

  (* Global store with memory order: global :mode= expr *)
  | global=GLOBAL mode=assign_mode e=expr
    { SGlobalStore { global; expr = e; assign = mode } }

  | global=GLOBAL DOT STORE LPAREN e=expr COMMA mode=mode RPAREN
    { SGlobalStore { global; expr = e; assign = mode } }

  (* Volatile global store pattern 2: global :v= expr *)
  | global=GLOBAL mode=volatile_assign_mode e=expr
    { let load, assign = mode in
      SGlobalStore { global; expr = e; assign } }

  (** Stores to pointers **)

    (* Pointer store: *expr := expr *)
  | STAR e1=expr ASSIGN e2=expr
    { SStore { address = e1; expr = e2; assign = { mode = Relaxed; volatile = false } } }

  (* Volatile pointer store pattern 2: *expr :v= expr *)
  | STAR e1=expr mode=volatile_assign_mode e2=expr
    { let load, assign = mode in
      SStore { address = e1; expr = e2; assign } }

  (* Explicit pointer store: *expr :mode= expr *)
  | STAR e1=expr mode=assign_mode e2=expr
    { SStore { address = e1; expr = e2; assign = mode } }

  (* CAS: reg := cas(mode, addr, expected, desired) *)
  | reg=REGISTER ASSIGN
        CAS LPAREN
          load_mode=memory_order COMMA
          assign_mode=memory_order COMMA
          e1=expr COMMA
          e2=expr COMMA
          e3=expr
        RPAREN
    { SCAS {
        register = reg;
        address = e1;
        expected = e2;
        desired = e3;
        load_mode;
        assign_mode
      } }

  (* FADD: reg := fadd(rmw_mode, load_mode, assign_mode, addr, operand) *)
  | reg=REGISTER ASSIGN
      FADD LPAREN
        rmw_mode=rmw_mode COMMA
        load_mode=memory_order COMMA
        assign_mode=memory_order COMMA
        e1=expr COMMA
        e2=expr
      RPAREN
    { SFADD {
        register = reg;
        address = e1;
        operand = e2;
        rmw_mode;
        load_mode;
        assign_mode
      } }


  (* FADD: reg := fadd(load_mode, assign_mode, addr, operand) *)
  | reg=REGISTER ASSIGN
      FADD LPAREN
        load_mode=memory_order COMMA
        assign_mode=memory_order COMMA
        e1=expr COMMA
        e2=expr
      RPAREN
    { SFADD {
        register = reg;
        address = e1;
        operand = e2;
        rmw_mode = "strong";
        load_mode;
        assign_mode
      } }

  (* Control flow *)
  | IF LPAREN cond=expr RPAREN then_body=block_or_stmt else_part=else_clause?
    { SIf { condition = cond; then_body; else_body = else_part } }

  | WHILE LPAREN cond=expr RPAREN body=block_or_stmt
    {
      inc_loop_id();
      push_loop();
      let result = SWhile { condition = cond; body } in
      pop_loop();
      result
    }

  | DO body=block_or_stmt WHILE LPAREN cond=expr RPAREN
    {
      inc_loop_id();
      push_loop();
      let result = SDo { body; condition = cond } in
      pop_loop();
      result
    }

  (* Fence *)
  | FENCE LPAREN mode=memory_order RPAREN
    { SFence { mode } }

  (* Lock/Unlock *)
  | LOCK global=GLOBAL?
    { SLock { global } }

  | UNLOCK global=GLOBAL?
    { SUnlock { global } }

  (* Malloc *)
  | reg=REGISTER ASSIGN MALLOC LPAREN size=expr RPAREN
    { SRegMalloc { register = reg; size; } }

  | reg=REGISTER ASSIGN MALLOC size=expr
    { SRegMalloc { register = reg; size; } }

  | global=GLOBAL ASSIGN MALLOC LPAREN size=expr RPAREN
    { SGlobalMalloc { global; size; } }

  | global=GLOBAL ASSIGN MALLOC size=expr
    { SGlobalMalloc { global; size; } }

  (* Free *)
  | FREE LPAREN reg=REGISTER RPAREN
    { SFree { register = reg } }

  | FREE LPAREN global=GLOBAL RPAREN
    { (* Generate a load from global then free *)
      SFree { register = "tmp_" ^ global } }

  | SKIP { SSkip }

  ;

block_or_stmt:
  | LBRACE stmts=statement_list RBRACE { stmts }
  | s=statement { [ s ] }
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
  | RELACQ { ReleaseAcquire }
  ;

mode:
  | RELAXED { { mode = Relaxed; volatile = false } }
  | RELEASE { { mode = Release; volatile = false } }
  | ACQUIRE { { mode = Acquire; volatile = false } }
  | SC { { mode = SC; volatile = false } }
  | NONATOMIC { { mode = Nonatomic; volatile = false } }
  ;

rmw_mode:
  | NORMAL { "normal" }
  | STRONG { "strong" }
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
  | e1=expr EQ e2=expr { EBinOp (e1, "=", e2) }
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
  | AMPERSAND e=expr { EUnOp ("&", e) }

  | FORALL e=expr { EUnOp ("forall", e) }

  | LPAREN e=expr RPAREN { e }

  | n=INT { EInt n }
  | reg=REGISTER { ERegister reg }
  | global=GLOBAL { EGlobal global }
  | atloc=ATLOC { EAtLoc atloc }
  | DOT s=STRING { EASet s }
  | DOT s=GLOBAL { EASet s }
  | QUOTE s=STRING { EASet s }
  ;

(* Assertion *)
assertion:
  | PERCENT PERCENT a=assertion_body { a }
  ;

assertion_body:
  | LBRACKET model=model_name? RBRACKET
    { AModel { model = (match model with Some m -> m | None -> "") } }

  | RARROW check=assertion_check PERCENT PERCENT rest=litmus
    { let model, outcome = check in
      AChained {
        model = (match model with Some m -> m | None -> "");
        outcome = (match outcome with Some o -> o | None -> "allow");
        rest;
      } }

  | outcome=outcome_keyword cond=expr check=assertion_check message=outcome_message?
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

outcome_message:
  | s=STRING { s }
  ;

model_name:
  | UNDERSCORE {"" }
  | name=GLOBAL { String.lowercase_ascii name }
  | REGISTER { $1 } (* for rc11 - tokenization conflict TODO *)
  | SC { "sc" }
  | RELAXED { "relaxed" }
  | RELEASE { "release" }
  | ACQUIRE { "acquire" }
  | NONATOMIC { "nonatomic" }
  | NORMAL { "normal" }
  | STRONG { "strong" }
  ;

%%
