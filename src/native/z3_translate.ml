(** {1 Z3 Translation}

    MoRDor's expressions as Z3 terms, for the native {!Smt_backend}. Moved from
    [solver.ml] by W2 (#178), unchanged. *)

open Printf
open Types

(** Solver context encapsulating Z3 state.

    Contains the Z3 context, solver instance, and variable mappings. *)
type context = {
  ctx : Z3.context;  (** Z3 context for all operations *)
  solver : Z3.Solver.solver;  (** Z3 solver instance *)
  vars : (string, Z3.Expr.expr) Hashtbl.t;
      (** Variable name to Z3 expression mapping *)
}

(** {1 Context Management}

    Functions for creating and managing Z3 solver contexts. *)

(** The Z3 context this domain solves in.

    A [Z3.context] is the whole AST manager, and building one costs both time
    and a few megabytes of memory that OCaml cannot see: the native allocation
    hangs off a small wrapper, so nothing about it pressures the GC into
    finalising it. Creating one per query -- which is what a fresh context in
    {!create_context} amounted to -- left hundreds of them alive at once.
    Analysing seqlock-1 peaked at 334MB RSS against an OCaml heap of 1.6MB, and
    at [--threads 8], with each domain building its own, at 973MB.

    So the context is per domain rather than per query. A Z3 context is not
    thread-safe, and domain-local storage is exactly the scope that gives each
    domain one of its own to itself. Reuse also lets Z3 hash-cons across
    queries: the predicates asked about here repeat heavily, and repeated
    subformulas now share nodes instead of being rebuilt per context.

    What must not be shared is the state a query builds up. The [Z3.Solver]
    instance holds the assertions, and [Solver.solve] reports a binding for
    every variable in [vars], so both stay per query in {!create_context} below
    -- otherwise a later query would inherit an earlier one's constraints, and
    every model would name variables the caller never asked about. *)
let z3_context_key = Domain.DLS.new_key (fun () -> Z3.mk_context [])

(* Built here, on the main domain, so that Z3's one-time global initialisation
   happens before any domain is spawned rather than in whichever workers first
   reach for a solver together. *)
let () = ignore (Domain.DLS.get z3_context_key)

(** Create a new solver context.

    Reuses this domain's Z3 context, and pairs it with a fresh Z3 solver and an
    empty variable table so that no constraint or variable carries over from an
    earlier query.

    @return A new context ready for use *)
let create_context () =
  let ctx = Domain.DLS.get z3_context_key in
  let solver = Z3.Solver.mk_solver ctx None in
  let vars = Hashtbl.create 32 in
    { ctx; solver; vars }

(** Get or create a Z3 variable by name.

    If the variable exists, returns it. Otherwise creates a new integer-typed Z3
    constant and registers it in the context's variable table.

    @param context The solver context
    @param name Variable name
    @return Z3 expression for this variable *)
let get_var context name =
  try Hashtbl.find context.vars name
  with Not_found ->
    let sort = Z3.Arithmetic.Integer.mk_sort context.ctx in
    let var = Z3.Expr.mk_const_s context.ctx name sort in
      Hashtbl.add context.vars name var;
      var

(** {1 Z3 Conversion Functions}

    Functions for converting internal representations to Z3 expressions. *)

(** Convert a bitvector-compatible expression to bitvector type.

    Handles conversion of booleans and integers to bitvectors of specified
    width.

    @param context The solver context
    @param expr Z3 expression to convert
    @param bitwidth Target bitvector width
    @return Z3 bitvector expression *)
and to_bitvec context expr bitwidth =
  if Z3.BitVector.is_bv expr then expr
  else if Z3.Boolean.is_bool expr then
    (* Convert boolean to bitvector: true -> 1, false -> 0 *)
    let zero_bv = Z3.BitVector.mk_numeral context.ctx "0" bitwidth in
    let one_bv = Z3.BitVector.mk_numeral context.ctx "1" bitwidth in
      Z3.Boolean.mk_ite context.ctx expr one_bv zero_bv
  else
    (* Integer to bitvector *)
    Z3.Arithmetic.Integer.mk_int2bv context.ctx bitwidth expr

(** Convert a value to Z3 expression.

    @param context The solver context
    @param value The value to convert
    @return Z3 expression representation *)
let rec value_to_z3 context value =
  match value with
  | VNumber n -> Z3.Arithmetic.Integer.mk_numeral_s context.ctx (Z.to_string n)
  | VSymbol s | VVar s -> get_var context s
  | VBoolean b ->
      if b then Z3.Boolean.mk_true context.ctx
      else Z3.Boolean.mk_false context.ctx

(** Convert an expression to Z3 representation.

    Recursively converts expression trees, handling:
    - Literals (numbers, booleans, variables, symbols)
    - Binary operations (arithmetic, comparison, logical, bitwise)
    - Unary operations (negation, logical not)
    - Disjunctions

    Special handling is provided for mixed integer/bitvector operations.

    @param context The solver context
    @param expr The expression to convert
    @return Z3 expression *)
and expr_to_z3 context expr =
  match expr with
  | ENum n -> Z3.Arithmetic.Integer.mk_numeral_s context.ctx (Z.to_string n)
  | EVar v -> get_var context v
  | EBoolean b ->
      if b then Z3.Boolean.mk_true context.ctx
      else Z3.Boolean.mk_false context.ctx
  | ESymbol s -> get_var context s
  | EBinOp (lhs, op, rhs) -> (
      let l = expr_to_z3 context lhs in
      let r = expr_to_z3 context rhs in
        match op with
        (* Comparison operators *)
        | "=" ->
            (* Handle mixed bitvector/integer comparisons *)
            if Z3.BitVector.is_bv l && not (Z3.BitVector.is_bv r) then
              let bitwidth = Z3.BitVector.get_size (Z3.Expr.get_sort l) in
              let r_bv = to_bitvec context r bitwidth in
                Z3.Boolean.mk_eq context.ctx l r_bv
            else if Z3.BitVector.is_bv r && not (Z3.BitVector.is_bv l) then
              let bitwidth = Z3.BitVector.get_size (Z3.Expr.get_sort r) in
              let l_bv = to_bitvec context l bitwidth in
                Z3.Boolean.mk_eq context.ctx l_bv r
            else Z3.Boolean.mk_eq context.ctx l r
        | "!=" ->
            Z3.Boolean.mk_not context.ctx (Z3.Boolean.mk_eq context.ctx l r)
        | "<" -> Z3.Arithmetic.mk_lt context.ctx l r
        | ">" -> Z3.Arithmetic.mk_gt context.ctx l r
        | "<=" -> Z3.Arithmetic.mk_le context.ctx l r
        | ">=" -> Z3.Arithmetic.mk_ge context.ctx l r
        (* Arithmetic operators *)
        | "+" -> Z3.Arithmetic.mk_add context.ctx [ l; r ]
        | "-" -> Z3.Arithmetic.mk_sub context.ctx [ l; r ]
        | "*" -> Z3.Arithmetic.mk_mul context.ctx [ l; r ]
        | "/" -> Z3.Arithmetic.mk_div context.ctx l r
        (* Bitwise operators (via bitvector conversion) *)
        | "&" ->
            let bitwidth = 64 in
            let l_bv = to_bitvec context l bitwidth in
            let r_bv = to_bitvec context r bitwidth in
            let result_bv = Z3.BitVector.mk_and context.ctx l_bv r_bv in
              (* Convert back to integer *)
              Z3.BitVector.mk_bv2int context.ctx result_bv false
        | "|" ->
            let bitwidth = 64 in
            let l_bv = to_bitvec context l bitwidth in
            let r_bv = to_bitvec context r bitwidth in
            let result_bv = Z3.BitVector.mk_or context.ctx l_bv r_bv in
              (* Convert back to integer *)
              Z3.BitVector.mk_bv2int context.ctx result_bv false
        | "^" ->
            let bitwidth = 64 in
            let l_bv = to_bitvec context l bitwidth in
            let r_bv = to_bitvec context r bitwidth in
            let result_bv = Z3.BitVector.mk_xor context.ctx l_bv r_bv in
              (* Convert back to integer *)
              Z3.BitVector.mk_bv2int context.ctx result_bv false
        (* Logical operators *)
        | "&&" -> Z3.Boolean.mk_and context.ctx [ l; r ]
        | "||" -> Z3.Boolean.mk_or context.ctx [ l; r ]
        | "=>" -> Z3.Boolean.mk_implies context.ctx l r
        | _ -> failwith ("Unsupported operator: " ^ op)
    )
  | EUnOp ("!", rhs) ->
      let r = expr_to_z3 context rhs in
        if Z3.Boolean.is_bool r then Z3.Boolean.mk_not context.ctx r
        else
          (* Integer semantics: !x is true iff x = 0 *)
          let zero = Z3.Arithmetic.Integer.mk_numeral_i context.ctx 0 in
            Z3.Boolean.mk_eq context.ctx r zero
  | EUnOp ("~", rhs) ->
      let r = expr_to_z3 context rhs in
        Z3.Arithmetic.mk_unary_minus context.ctx r
  | EUnOp (op, _) -> failwith (sprintf "Unsupported unary operator %s" op)
  | EOr clauses ->
      List.map (expr_to_z3 context) clauses |> Z3.Boolean.mk_or context.ctx
