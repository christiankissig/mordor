(** Event operations and utilities for sMRD *)

open Expr
open Printf
open Types
open Uset

(** Mode utility functions *)
module ModeOps = struct
  let checked_read = function
    | Relaxed -> Relaxed
    | Acquire -> Acquire
    | SC -> Acquire
    | Release -> failwith "Read cannot be release"
    | ReleaseAcquire -> Acquire
    | Normal | Strong -> failwith "Invalid mode for read"
    | Nonatomic -> failwith "Nonatomic unimplemented"
    | Consume -> Consume

  let read m = try checked_read m with _ -> Relaxed

  let checked_write = function
    | Relaxed -> Relaxed
    | Release -> Release
    | ReleaseAcquire -> Release
    | SC -> Release
    | Acquire -> failwith "Write cannot be acquire"
    | Normal | Strong -> failwith "Invalid mode for write"
    | Nonatomic -> failwith "Nonatomic unimplemented"
    | Consume -> failwith "Consume unimplemented"

  let write m = try checked_write m with _ -> Relaxed

  (* Mode ordering: Relaxed < Acquire, Relaxed < Release, Acquire < SC, Release < SC *)
  let mode_order : (mode * mode) USet.t =
    let all_modes =
      USet.of_list [ Relaxed; Acquire; Release; SC; Normal; Strong; Nonatomic ]
    in
    let base_order =
      USet.of_list
        [ (Relaxed, Acquire); (Relaxed, Release); (Acquire, SC); (Release, SC) ]
    in
      base_order
      |> URelation.transitive_closure
      |> URelation.reflexive_closure all_modes

  let mode_le m1 m2 = USet.mem mode_order (m1, m2)
end

module Event : sig
  type t = event

  val create :
    event_type ->
    int ->
    ?id:Value.t ->
    ?loc:Expr.t ->
    ?rval:Value.t ->
    ?wval:Expr.t ->
    ?rmod:mode ->
    ?wmod:mode ->
    ?fmod:mode ->
    ?volatile:bool ->
    ?strong:mode ->
    ?lhs:int ->
    ?rhs:int ->
    ?pc:int ->
    unit ->
    event

  val clone : event -> event
  val to_string : event -> string
  val equal : event -> event -> bool
  val is_read : event -> bool
  val is_write : event -> bool
  val is_fence : event -> bool
  val is_lock : event -> bool
  val is_unlock : event -> bool
  val is_init : event -> bool
  val is_malloc : event -> bool
  val is_free : event -> bool
  val is_read_write : event -> bool
  val is_mem_func : event -> bool
  val is_lock_unlock : event -> bool
  val is_ordering : event -> bool
  val get_symbols : event -> string USet.t
  val relabel : relab:(string -> string option) -> event -> event
end = struct
  type t = event

  (** Event predicates *)
  let is_read e = e.typ = Read

  let is_write e = e.typ = Write
  let is_fence e = e.typ = Fence
  let is_lock e = e.typ = Lock
  let is_unlock e = e.typ = Unlock
  let is_init e = e.typ = Init
  let is_malloc e = e.typ = Malloc
  let is_free e = e.typ = Free
  let is_read_write e = is_read e || is_write e
  let is_mem_func e = is_malloc e || is_free e
  let is_lock_unlock e = is_lock e || is_unlock e
  let is_ordering e = is_lock_unlock e || is_fence e

  (** Create event with specialized initialization *)
  let create typ label ?id ?loc ?rval ?wval ?(rmod = Relaxed) ?(wmod = Relaxed)
      ?(fmod = Relaxed) ?(volatile = false) ?strong ?lhs ?rhs ?pc () =
    let base =
      {
        label;
        typ;
        id = None;
        loc = None;
        rval = None;
        wval = None;
        cond = None;
        rmod = Relaxed;
        wmod = Relaxed;
        fmod = Relaxed;
        volatile = false;
        strong = None;
        is_rdmw = false;
      }
    in
      match typ with
      | Fence -> { base with fmod }
      | Malloc -> { base with id = rval; loc; rval }
      | Lock | Unlock -> { base with id }
      | _ ->
          { base with id; loc; rval; wval; rmod; wmod; fmod; volatile; strong }

  (** Clone an event *)
  let clone e = { e with label = e.label }

  (** Event to string *)
  let to_string e =
    if is_init e then ""
    else
      let volatile_prefix = if e.volatile then "v" else "" in
      let main_str =
        match e.typ with
        | Init -> "Init"
        | Terminal -> "Terminal"
        | Read ->
            sprintf "R%s %s %s" (mode_to_string_or e.rmod)
              (Option.fold ~none:"_" ~some:Expr.to_string e.loc)
              (Option.fold ~none:"_" ~some:Value.to_string e.rval)
        | Write ->
            sprintf "W%s %s %s" (mode_to_string_or e.wmod)
              (Option.fold ~none:"_" ~some:Expr.to_string e.loc)
              (Option.fold ~none:"_" ~some:Expr.to_string e.wval)
        | Lock -> Option.fold ~none:"" ~some:Value.to_string e.id
        | Unlock -> Option.fold ~none:"" ~some:Value.to_string e.id
        | Fence -> sprintf "F%s" (mode_to_string_or e.fmod)
        | Branch ->
            sprintf "B %s" (Option.fold ~none:"_" ~some:Expr.to_string e.cond)
        | Malloc ->
            sprintf "Alloc %s %s"
              (Option.fold ~none:"_" ~some:Value.to_string e.rval)
              (Option.fold ~none:"_" ~some:Expr.to_string e.wval)
        | Free ->
            sprintf "Free %s" (Option.fold ~none:"_" ~some:Value.to_string e.id)
      in
        sprintf "%d: %s%s" e.label volatile_prefix main_str

  (** Event equality *)
  let equal e1 e2 =
    e1.label = e2.label
    && e1.typ = e2.typ
    && ( match (e1.id, e2.id) with
      | None, None -> true
      | Some v1, Some v2 -> Value.equal v1 v2
      | _ -> false
      )
    && ( match (e1.loc, e2.loc) with
      | None, None -> true
      | Some v1, Some v2 -> Expr.equal v1 v2
      | _ -> false
      )
    && ( match (e1.rval, e2.rval) with
      | None, None -> true
      | Some v1, Some v2 -> Value.equal v1 v2
      | _ -> false
      )
    &&
    match (e1.wval, e2.wval) with
    | None, None -> true
    | Some v1, Some v2 -> Expr.equal v1 v2
    | _ -> false

  let get_symbols e =
    let symbols = USet.create () in
      ( match e.loc with
      | Some v ->
          USet.inplace_union symbols (Expr.get_symbols v |> USet.of_list)
          |> ignore
      | None -> ()
      );
      ( match e.rval with
      | Some v ->
          USet.inplace_union symbols (Value.get_symbols v |> USet.of_list)
          |> ignore
      | None -> ()
      );
      ( match e.wval with
      | Some v ->
          USet.inplace_union symbols (Expr.get_symbols v |> USet.of_list)
          |> ignore
      | None -> ()
      );
      symbols

  let relabel ~relab e =
    {
      e with
      loc = Option.map (Expr.relabel ~relab) e.loc;
      rval = Option.map (Value.relabel ~relab) e.rval;
      wval = Option.map (Expr.relabel ~relab) e.wval;
    }
end

let get_loc structure event_id =
  let events = structure.events in
    Hashtbl.find_opt events event_id
    |> Option.map (fun event -> event.loc)
    |> Option.join

let get_val structure e =
  let events = structure.events in
    try
      let event = Hashtbl.find events e in
        match event.wval with
        | Some v -> Some v
        | None -> (
            match event.rval with
            | Some v -> Some (Expr.of_value v)
            | None -> None
          )
    with Not_found -> None

(** Get value from event e, or create symbolic value based on x's location *)
let vale structure e x =
  let events = structure.events in
    match Hashtbl.find_opt events e with
    | Some event when event.label >= 0 -> (
        match get_val structure e with
        | Some v -> v
        | None ->
            let loc_x =
              match get_loc structure x with
              | Some l -> Expr.to_string l
              | None -> string_of_int x
            in
              EVar (sprintf "v(%s)" loc_x)
      )
    | _ ->
        let loc_x =
          match get_loc structure x with
          | Some l -> Expr.to_string l
          | None -> string_of_int x
        in
          EVar (sprintf "v(%s)" loc_x)

(** Get location from event e, or create symbolic location based on x's location
*)
let loce structure e x =
  let events = structure.events in
    match Hashtbl.find_opt events e with
    | Some event when event.label >= 0 -> (
        match get_loc structure e with
        | Some l -> l
        | None ->
            let loc_x =
              match get_loc structure x with
              | Some l -> Expr.to_string l
              | None -> string_of_int x
            in
              EVar (sprintf "l(%s)" loc_x)
      )
    | _ ->
        let loc_x =
          match get_loc structure x with
          | Some l -> Expr.to_string l
          | None -> string_of_int x
        in
          EVar (sprintf "l(%s)" loc_x)

(* Event type filters *)
let filter_events structure e_set typ ?mode () =
  let events = structure.events in
    USet.filter
      (fun e ->
        try
          let event = Hashtbl.find events e in
            event.typ = typ
            &&
            match mode with
            | None -> true
            | Some m -> (
                match event.typ with
                | Read -> event.rmod = m
                | Write -> event.wmod = m
                | Fence -> event.fmod = m
                | _ -> false
              )
        with Not_found -> false
      )
      e_set

let is_rdmw structure e =
  match Hashtbl.find_opt structure.events e with
  | Some event -> event.is_rdmw
  | None -> false
