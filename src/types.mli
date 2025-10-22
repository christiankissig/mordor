(** Core type definitions for sMRD *)

(** {1 Options} *)

(** Configuration options for sMRD *)
type options = {
  dependencies : bool;
  just_structure : bool;
  exhaustive : bool;
  forcerc11 : bool;
  forceimm : bool;
  forcenocoh : bool;
  coherent : string;
}

(** Default option values *)
val default_options : options

(** {1 Event Types} *)

(** Types of memory and control flow events *)
type event_type =
  | Read
  | Write
  | Lock
  | Unlock
  | Fence
  | Init
  | Branch
  | Loop
  | Malloc
  | Free
  | RMW
  | CRMW

(** Convert event type to string representation *)
val event_type_to_string : event_type -> string

(** {1 Memory Ordering Modes} *)

(** Memory ordering modes for atomic operations *)
type mode = Relaxed | Acquire | Release | SC | Normal | Strong | Nonatomic

(** Convert mode to string representation *)
val mode_to_string : mode -> string

(** Convert mode to string, returning empty string for Relaxed *)
val mode_to_string_or : mode -> string

(** {1 Unicode Symbols} *)

(** Unicode symbols for mathematical notation *)
module Unicode : sig
  val wedge : string
  val vee : string
  val region : string
  val emptyset : string
  val top : string
  val cap : string
  val cup : string
  val dunion : string
  val in_ : string
  val notin : string
  val rhd : string
  val perp : string
  val vdash : string
  val disjoint : string
  val forall : string
  val exists : string
  val langle : string
  val rangle : string
end

(** {1 Symbolic Alphabets} *)

(** Greek alphabet for symbolic values *)
val greek_alpha : string

(** Chinese numerals for allocation symbols *)
val zh_alpha : string

(** {1 Utility Types} *)

(** Unordered set implemented as a hashtable *)
type 'a uset = ('a, 'a) Hashtbl.t

(** {1 Values and Expressions} *)

(** Value representation *)
type value_type =
  | VNumber of Z.t
  | VSymbol of string
  | VVar of string
  | VExpression of expr
  | VBoolean of bool

(** Expression representation *)
and expr =
  | EBinOp of value_type * string * value_type
  | EUnOp of string * value_type
  | EOr of expr list list
  | EVar of string
  | ENum of Z.t

(** {1 Events} *)

(** Event structure representing a memory or control flow event *)
type event = {
  label : int;
  van : int;
  typ : event_type;
  id : value_type option;
  rval : value_type option;
  wval : value_type option;
  rmod : mode;
  wmod : mode;
  fmod : mode;
  cond : value_type option;
  volatile : bool;
  strong : mode option;
  lhs : int option;
  rhs : int option;
  pc : int option;
  hide : bool;
  quot : int option;
}

(** Create a default event with given type and label *)
val make_event : event_type -> int -> event

(** {1 Symbolic Event Structure} *)

(** Symbolic event structure representing program execution *)
type symbolic_event_structure = {
  e : int uset;
  po : (int * int) uset;
  rmw : (int * int) uset;
  lo : (int * int) uset;
  restrict : (int, expr list) Hashtbl.t;
  cas_groups : (int, int list * expr list uset) Hashtbl.t;
  pwg : expr list;
  fj : (int * int) uset;
  p : (string * string) uset;
  constraint_ : expr list;
}

(** {1 Continuation Type} *)

(** Continuation with mutable line buffer and default computation *)
type ('a, 'b) continuation = { lines : 'a list ref; default : unit -> 'b Lwt.t }

(** {1 Function Maps} *)

(** Function map type with default value *)
type ('a, 'b) func = { map : ('a, 'b) Hashtbl.t; default : unit -> 'b }

(** Create a new function map with optional default function *)
val make_func : ?default:(unit -> 'b) -> unit -> ('a, 'b) func

(** Find a value in the function map *)
val func_find : ('a, 'b) func -> 'a -> 'b option

(** Add or update a key-value pair in the function map *)
val func_add : ('a, 'b) func -> 'a -> 'b -> ('a, 'b) func

(** Get a value from the function map, using default if not found *)
val func_get : ('a, 'b) func -> 'a -> 'b

type justification = {
  p : expr list; (* Predicates/conditions *)
  d : string uset; (* Dependency symbols *)
  fwd : (int * int) uset; (* Forwarding edges (event pairs) *)
  we : (int * int) uset; (* Write-elision edges (event pairs) *)
  w : event; (* The write event being justified *)
  op : string * justification option * expr option; (* Operation tag *)
}

(** Symbolic Execution *)
type symbolic_execution = {
  ex_e : int uset; (* Event set *)
  rf : (int * int) uset; (* Reads-from relation *)
  dp : (int * int) uset; (* Dependencies *)
  ppo : (int * int) uset; (* Preserved program order *)
  ex_rmw : (int * int) uset; (* RMW pairs *)
  ex_p : expr list; (* Predicates *)
  conds : expr list; (* Conditions *)
  fix_rf_map : (string, value_type) Hashtbl.t; (* Fixed RF mappings *)
  justs : justification list; (* Justifications *)
  pointer_map : (int, value_type) Hashtbl.t option; (* Pointer mappings *)
}
