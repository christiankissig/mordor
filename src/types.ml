open Uset

(** Basic types *)

type 'a uset = 'a USet.t

type mode =
  | Relaxed
  | Acquire
  | Release
  | ReleaseAcquire
  | SC
  | Normal
  | Strong
  | Nonatomic
  | Consume

let pp_mode fmt mode =
  Format.fprintf fmt "%s"
    ( match mode with
    | Relaxed -> "rlx"
    | Acquire -> "acq"
    | Release -> "rel"
    | ReleaseAcquire -> "ra"
    | SC -> "sc"
    | Normal -> ""
    | Strong -> "strong"
    | Nonatomic -> "na"
    | Consume -> "con"
    )

let show_mode mode = Format.asprintf "%a" pp_mode mode

type event_type =
  | Read
  | Write
  | Lock
  | Unlock
  | Fence
  | Init
  | Terminal
    (* Terminal events used to capture the terminal state of the
  program outside of memory-effectful events, e.g. register state *)
  | Branch
  | Loop
  | Malloc
  | Free
  | RMW
  | CRMW
[@@deriving show]

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

(** Pretty-printers *)

let pp_z fmt z = Format.fprintf fmt "%s" (Z.to_string z)

let pp_int_uset fmt uset =
  Format.fprintf fmt "{%s}"
    (String.concat ", " (List.map string_of_int (USet.to_list uset)))

let pp_int_urel fmt uset =
  Format.fprintf fmt "{%s}"
    (String.concat ", "
       (List.map
          (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
          (USet.to_list uset)
       )
    )

let pp_string_uset fmt uset =
  Format.fprintf fmt "{%s}"
    (String.concat ", "
       (List.map (fun a -> Printf.sprintf "%s" a) (USet.to_list uset))
    )

let event_type_to_string typ =
  match typ with
  | Read -> "R"
  | Write -> "W"
  | Lock -> "L"
  | Unlock -> "U"
  | Fence -> "F"
  | Init -> "I"
  | Terminal -> "T"
  | Branch -> "B"
  | Loop -> "Loop"
  | Malloc -> "A"
  | Free -> "D"
  | RMW -> "RMW"
  | CRMW -> "CRMW"

let pp_event_type fmt typ = Format.fprintf fmt "%s" (event_type_to_string typ)
let mode_to_string m = show_mode m

let mode_to_string_or = function
  | Relaxed -> ""
  | m -> show_mode m

(** Value representation *)
type value_type =
  | VNumber of Z.t [@printer pp_z]
  | VSymbol of string
  | VVar of string
  | VBoolean of bool
[@@deriving show]

let pp_esymbol fmt sym = Format.fprintf fmt "%s" sym

(** Expression representation *)
type expr =
  | EBinOp of expr * string * expr
  | EUnOp of string * expr
  | EOr of expr list list
  | EVar of string
  | ESymbol of string [@printer pp_esymbol]
  | EBoolean of bool
  | ENum of Z.t [@printer pp_z]
[@@deriving show]

(** Event types *)

(* let pp_event_type = function *)
(*   | Read -> "R" *)
(*   | Write -> "W" *)
(*   | Lock -> "L" *)
(*   | Unlock -> "U" *)
(*   | Fence -> "F" *)
(*   | Init -> "I" *)
(*   | Branch -> "B" *)
(*   | Malloc -> "A" *)
(*   | Free -> "D" *)
(*   | RMW -> "RMW" *)
(*   | CRMW -> "CRMW" *)
(*   | _ -> "E" *)

(** Event structure *)
type event = {
  label : int;
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
  is_rdmw : bool;
}
[@@deriving show]

let pp_structure_p fmt p =
  Format.fprintf fmt "{%s}"
    (String.concat ",\n\t"
       (List.map
          (fun (lbl, env) ->
            Printf.sprintf "%d: {%s}" lbl
              (String.concat ", "
                 (List.map
                    (fun (k, v) -> Printf.sprintf "%s -> %s" k (show_expr v))
                    (Hashtbl.fold (fun k v acc -> (k, v) :: acc) env [])
                 )
              )
          )
          (Hashtbl.fold (fun k v acc -> (k, v) :: acc) p [])
       )
    )

(** Symbolic Event Structures *)
type symbolic_event_structure = {
  e : int uset; [@printer pp_int_uset] (* Set of event IDs *)
  events : (int, event) Hashtbl.t; [@opaque]
      (* Mapping from event IDs to events *)
  po : (int * int) uset; [@printer pp_int_urel] (* Program order relation *)
  po_iter : (int * int) uset; [@printer pp_int_urel]
      (* Program order across loop iterations *)
  rmw : (int * int) uset; [@printer pp_int_urel] (* Read-modify-write pairs *)
  lo : (int * int) uset; [@printer pp_int_urel] (* Lock order *)
  restrict : (int, expr list) Hashtbl.t; [@opaque] (* Event restrictions *)
  cas_groups : (int, int list * expr list uset) Hashtbl.t; [@opaque]
      (* CAS groupings *)
  pwg : expr list; (* Per-write guarantees *)
  fj : (int * int) uset; [@printer pp_int_urel] (* Fork-join edges *)
  p : (int, (string, expr) Hashtbl.t) Hashtbl.t; [@printer pp_structure_p]
      (* Register state per event
  *)
  constraint_ : expr list; [@opaque] (* Constraints *)
  conflict : (int * int) uset; [@printer pp_int_urel] (* Conflict relation *)
  origin : (string, int) Hashtbl.t; [@opaque] (* Origin mapping for symbols *)
  loop_indices : (int, int list) Hashtbl.t; [@opaque]
      (* Mapping from events to their loop indices *)
  thread_index : (int, int) Hashtbl.t; [@opaque]
  (* Mapping from events to their thread indices *)
  (* cached event filters *)
  write_events : int uset; [@printer pp_int_uset]
  read_events : int uset; [@printer pp_int_uset]
  rlx_write_events : int uset; [@printer pp_int_uset]
  rlx_read_events : int uset; [@printer pp_int_uset]
  fence_events : int uset; [@printer pp_int_uset]
  branch_events : int uset; [@printer pp_int_uset]
  malloc_events : int uset; [@printer pp_int_uset]
  free_events : int uset; [@printer pp_int_uset]
  terminal_events : int uset; [@printer pp_int_uset]
}
[@@deriving show]

(** Justifications *)
type justification = {
  p : expr list; [@opaque] (* Predicates/conditions *)
  d : string uset; [@printer pp_string_uset] (* Dependency symbols *)
  fwd : (int * int) uset; [@printer pp_int_urel]
      (* Forwarding edges (event pairs) *)
  we : (int * int) uset; [@printer pp_int_urel]
      (* Write-elision edges (event pairs) *)
  w : event; (* The write event being justified *)
  op : string * justification option * expr option; [@opaque] (* Operation tag *)
}
[@@deriving show]

let pp_fix_rf_map fmt fix_rf_map =
  Format.fprintf fmt "{%s}"
    (String.concat ", "
       (Hashtbl.fold
          (fun k v acc -> Printf.sprintf "%s -> %s" k (show_expr v) :: acc)
          fix_rf_map []
       )
    )

let pp_expr_list fmt exprs =
  Format.fprintf fmt "[%s]" (String.concat "; " (List.map show_expr exprs))

let pp_env fmt env =
  Format.fprintf fmt "{%s}"
    (String.concat ", "
       (Hashtbl.fold
          (fun k v acc -> Printf.sprintf "%s -> %s" k (show_expr v) :: acc)
          env []
       )
    )

(* The main type with custom printers *)
type symbolic_execution = {
  id : int;
  ex_e : int uset; [@printer pp_int_uset]
  rf : (int * int) uset; [@printer pp_int_urel]
  dp : (int * int) uset; [@printer pp_int_urel]
  ppo : (int * int) uset; [@printer pp_int_urel]
  ex_rmw : (int * int) uset; [@printer pp_int_urel]
  ex_p : expr list; [@printer pp_expr_list]
  fix_rf_map : (string, expr) Hashtbl.t; [@printer pp_fix_rf_map]
  pointer_map : (int, value_type) Hashtbl.t option; [@opaque]
  final_env : (string, expr) Hashtbl.t; [@printer pp_env]
}
[@@deriving show]

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

(** Source code connection *)
type source_span = {
  start_line : int;
  start_col : int;
  end_line : int;
  end_col : int;
}
[@@deriving show, yojson]

type event_source_code_span = (int, source_span) Hashtbl.t
