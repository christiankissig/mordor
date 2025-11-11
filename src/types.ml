open Uset

(** Basic types *)

type 'a uset = 'a USet.t

(** Memory ordering modes *)

type mode =
  | Relaxed
  | Acquire
  | Release
  | ReleaseAcquire
  | SC
  | Normal
  | Strong
  | Nonatomic

let mode_to_string = function
  | Relaxed -> "rlx"
  | Acquire -> "acq"
  | Release -> "rel"
  | ReleaseAcquire -> "ra"
  | SC -> "sc"
  | Normal -> ""
  | Strong -> "strong"
  | Nonatomic -> "na"

let mode_to_string_or = function
  | Relaxed -> ""
  | m -> mode_to_string m

(** Unicode symbols *)
module Unicode = struct
  let wedge = "\u{2227}"
  let vee = "\u{2228}"
  let region = "\u{1d63}"
  let emptyset = "\u{2205}"
  let top = "\u{22a4}"
  let cap = "\u{2229}"
  let cup = "\u{222a}"
  let dunion = "\u{2294}"
  let in_ = "\u{2208}"
  let notin = "\u{2209}"
  let rhd = "\u{25B7}"
  let perp = "\u{22a5}"
  let vdash = "\u{22a2}"
  let disjoint = "\u{2a02}"
  let forall = "\u{2200}"
  let exists = "\u{2203}"
  let langle = "\u{27e8}"
  let rangle = "\u{27e9}"
end

(** Greek alphabet for symbolic values *)
let greek_alpha = "αβγδεζηθικλμνξοπρστυφχψωΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ"

(** Chinese numerals for allocation symbols *)
let zh_alpha = "一二三四五六七八九十"

(** Value representation *)
type value_type =
  | VNumber of Z.t
  | VSymbol of string
  | VVar of string
  | VBoolean of bool

(** Expression representation *)
and expr =
  | EBinOp of expr * string * expr
  | EUnOp of string * expr
  | EOr of expr list list
  | EVar of string
  | ESymbol of string
  | EBoolean of bool
  | ENum of Z.t

(** Event types *)
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

let event_type_to_string = function
  | Read -> "R"
  | Write -> "W"
  | Lock -> "L"
  | Unlock -> "U"
  | Fence -> "F"
  | Init -> "I"
  | Branch -> "B"
  | Malloc -> "A"
  | Free -> "D"
  | RMW -> "RMW"
  | CRMW -> "CRMW"
  | _ -> "E"

(** Event structure *)
type event = {
  label : int;
  van : int;
  typ : event_type;
  id : value_type option;
  loc : expr option;
  rval : value_type option;
  wval : expr option;
  rmod : mode;
  wmod : mode;
  fmod : mode;
  cond : expr option;
  volatile : bool;
  strong : mode option;
  lhs : int option;
  rhs : int option;
  pc : int option;
  hide : bool;
  quot : int option;
}

(** Symbolic Event Structures *)
type symbolic_event_structure = {
  e : int uset; (* Set of event IDs *)
  po : (int * int) uset; (* Program order relation *)
  po_iter : (int * int) uset; (* Program order across loop iterations *)
  rmw : (int * int) uset; (* Read-modify-write pairs *)
  lo : (int * int) uset; (* Lock order *)
  restrict : (int, expr list) Hashtbl.t; (* Event restrictions *)
  cas_groups : (int, int list * expr list uset) Hashtbl.t; (* CAS groupings *)
  pwg : expr list; (* Per-write guarantees *)
  fj : (int * int) uset; (* Fork-join edges *)
  p : (string * string) uset; (* Register mappings *)
  constraint_ : expr list; (* Constraints *)
}

(** Justifications *)
type justification = {
  p : expr list; (* Predicates/conditions *)
  d : string uset; (* Dependency symbols *)
  fwd : (int * int) uset; (* Forwarding edges (event pairs) *)
  we : (int * int) uset; (* Write-elision edges (event pairs) *)
  w : event; (* The write event being justified *)
  op : string * justification option * expr option; (* Operation tag *)
}

(** Symbolic Executions *)
type symbolic_execution = {
  ex_e : int uset; (* Event set *)
  rf : (int * int) uset; (* Reads-from relation *)
  dp : (int * int) uset; (* Dependencies *)
  ppo : (int * int) uset; (* Preserved program order *)
  ex_rmw : (int * int) uset; (* RMW pairs *)
  ex_p : expr list; (* Predicates *)
  conds : expr list; (* Conditions *)
  fix_rf_map : (string, expr) Hashtbl.t; (* Fixed RF mappings *)
  justs : justification list; (* Justifications *)
  pointer_map : (int, value_type) Hashtbl.t option; (* Pointer mappings *)
}

(** Futures *)
type future = (int * int) uset

type future_set = future uset
type history = int uset

(** Function map type *)
type ('a, 'b) func = { map : ('a, 'b) Hashtbl.t; default : unit -> 'b }

(** Create function map *)
let make_func ?(default = fun () -> failwith "No default") () =
  { map = Hashtbl.create 16; default }

let func_find f key = try Some (Hashtbl.find f.map key) with Not_found -> None

let func_add f key value =
  Hashtbl.replace f.map key value;
  f

let func_get f key =
  match func_find f key with
  | Some v -> v
  | None -> f.default ()
