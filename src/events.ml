(** Event operations and utilities for sMRD *)

open Types
open Expr
open Printf

(** Mode utility functions *)
module ModeOps = struct
  let to_string_or = function
    | Relaxed -> ""
    | m -> mode_to_string m

  let checked_read = function
    | Relaxed -> Relaxed
    | Acquire -> Acquire
    | SC -> Acquire
    | Release -> failwith "Read cannot be release"
    | Normal | Strong -> failwith "Invalid mode for read"
    | Nonatomic -> failwith "Nonatomic unimplemented"

  let read m = try checked_read m with _ -> Relaxed

  let checked_write = function
    | Relaxed -> Relaxed
    | Release -> Release
    | SC -> Release
    | Acquire -> failwith "Write cannot be acquire"
    | Normal | Strong -> failwith "Invalid mode for write"
    | Nonatomic -> failwith "Nonatomic unimplemented"

  let write m = try checked_write m with _ -> Relaxed

  (* Mode ordering: Relaxed < Acquire, Relaxed < Release, Acquire < SC, Release < SC *)
  let mode_order : (mode * mode) Uset.t =
    let all_modes =
      Uset.of_list [ Relaxed; Acquire; Release; SC; Normal; Strong; Nonatomic ]
    in
    let base_order =
      Uset.of_list
        [ (Relaxed, Acquire); (Relaxed, Release); (Acquire, SC); (Release, SC) ]
    in
      base_order |> Uset.transitive_closure |> Uset.reflexive_closure all_modes

  let mode_le m1 m2 = Uset.mem mode_order (m1, m2)
end

(** Value equality from Uset module *)
let value_equality = Uset.value_equality

(** Event predicates *)
let is_read e = e.typ = Read

let is_write e = e.typ = Write
let is_fence e = e.typ = Fence
let is_lock e = e.typ = Lock
let is_unlock e = e.typ = Unlock
let is_init e = e.typ = Init
let is_branch e = e.typ = Branch
let is_loop e = e.typ = Loop
let is_malloc e = e.typ = Malloc
let is_free e = e.typ = Free
let is_rmw e = e.typ = RMW || e.typ = CRMW
let is_crmw e = e.typ = CRMW
let is_read_write e = is_read e || is_write e
let is_mem_func e = is_malloc e || is_free e
let is_lock_unlock e = is_lock e || is_unlock e
let is_ordering e = is_lock_unlock e || is_fence e

(** Event field accessors with validation *)
let has_id e =
  match e.typ with
  | Read | Write | Malloc | Free | RMW | CRMW -> true
  | _ -> false

let has_val e =
  match e.typ with
  | Read | Write | Malloc -> true
  | _ -> false

let has_wval e =
  match e.typ with
  | Write | Malloc | RMW | CRMW -> true
  | _ -> false

let has_rval e =
  match e.typ with
  | Read | Malloc | RMW | CRMW -> true
  | _ -> false

let has_cond e =
  match e.typ with
  | Branch | Loop | RMW | CRMW -> true
  | _ -> false

let get_id e =
  if has_id e then
    match e.id with
    | Some id -> id
    | None -> failwith (sprintf "Event %d does not have an id" e.label)
  else failwith (sprintf "Event %d type does not support id" e.label)

let get_wval e =
  if has_wval e then
    match e.wval with
    | Some v -> v
    | None -> failwith (sprintf "Event %d does not have a wval" e.label)
  else failwith (sprintf "Event %d type does not support wval" e.label)

let get_rval e =
  if has_rval e then
    match e.rval with
    | Some v -> v
    | None -> failwith (sprintf "Event %d does not have an rval" e.label)
  else failwith (sprintf "Event %d type does not support rval" e.label)

let get_cond e =
  if has_cond e then
    match e.cond with
    | Some c -> c
    | None -> failwith (sprintf "Event %d does not have a cond" e.label)
  else failwith (sprintf "Event %d type does not support cond" e.label)

(** Get event ordering mode *)
let event_order e =
  match e.typ with
  | Read -> e.rmod
  | Write -> e.wmod
  | Fence -> e.fmod
  | Init -> e.wmod
  | Lock | Unlock -> Relaxed
  | Malloc | Branch | Loop | Free -> Relaxed
  | RMW | CRMW -> failwith "RMW/CRMW order not directly accessible"

(** Create event with specialized initialization *)
let make_event_with typ label ~id ~rval ~wval ~rmod ~wmod ~fmod ~cond ~volatile
    ~strong ~lhs ~rhs ~pc =
  let base = make_event typ label in
  let rmod =
    match rmod with
    | Some m -> m
    | None -> Relaxed
  in
  let wmod =
    match wmod with
    | Some m -> m
    | None -> Relaxed
  in
  let fmod =
    match fmod with
    | Some m -> m
    | None -> Relaxed
  in
    match typ with
    | Fence ->
        {
          base with
          rmod = ModeOps.read fmod;
          wmod = ModeOps.write fmod;
          fmod;
          id;
          rval;
          wval;
          cond;
          volatile;
          strong;
          lhs;
          rhs;
          pc;
        }
    | Malloc ->
        {
          base with
          id = rval;
          (* For malloc, id is set to rval *)
          rval;
          wval;
          rmod;
          wmod;
          fmod;
          cond;
          volatile;
          strong;
          lhs;
          rhs;
          pc;
        }
    | _ ->
        {
          base with
          id;
          rval;
          wval;
          rmod;
          wmod;
          fmod;
          cond;
          volatile;
          strong;
          lhs;
          rhs;
          pc;
        }

(** Clone an event *)
let clone_event e = { e with label = e.label }

(** Event to string *)
let event_to_string e =
  if is_init e then ""
  else
    let volatile_prefix = if e.volatile then "v" else "" in
    let main_str =
      match e.typ with
      | Init -> ""
      | Read ->
          sprintf "R%s %s %s"
            (ModeOps.to_string_or e.rmod)
            (Option.fold ~none:"_" ~some:Expr.to_string e.loc)
            (Option.fold ~none:"_" ~some:Value.to_string e.rval)
      | Write ->
          sprintf "W%s %s %s"
            (ModeOps.to_string_or e.wmod)
            (Option.fold ~none:"_" ~some:Expr.to_string e.loc)
            (Option.fold ~none:"_" ~some:Expr.to_string e.wval)
      | Lock -> Option.fold ~none:"" ~some:Value.to_string e.id
      | Unlock -> Option.fold ~none:"" ~some:Value.to_string e.id
      | Fence -> sprintf "F%s" (ModeOps.to_string_or e.fmod)
      | Branch ->
          sprintf "[%s]" (Option.fold ~none:"_" ~some:Expr.to_string e.cond)
      | Loop ->
          sprintf "%s%s%s" Unicode.langle
            (Option.fold ~none:"_" ~some:Expr.to_string e.cond)
            Unicode.rangle
      | Malloc ->
          sprintf "Alloc %s %s"
            (Option.fold ~none:"_" ~some:Value.to_string e.rval)
            (Option.fold ~none:"_" ~some:Expr.to_string e.wval)
      | Free ->
          sprintf "Free %s" (Option.fold ~none:"_" ~some:Value.to_string e.id)
      | RMW ->
          sprintf "%s . R%s %s . W%s %s"
            (Option.fold ~none:"_" ~some:Value.to_string e.id)
            (ModeOps.to_string_or e.rmod)
            (Option.fold ~none:"_" ~some:Value.to_string e.rval)
            (ModeOps.to_string_or e.wmod)
            (Option.fold ~none:"_" ~some:Expr.to_string e.wval)
      | CRMW ->
          let rmod_extra =
            if e.rmod <> e.fmod then sprintf "+%s" (ModeOps.to_string_or e.rmod)
            else ""
          in
            sprintf "%s . R%s %s . [%s]%s . %s %s"
              (Option.fold ~none:"_" ~some:Value.to_string e.id)
              (ModeOps.to_string_or e.fmod)
              (Option.fold ~none:"_" ~some:Value.to_string e.rval)
              (Option.fold ~none:"_" ~some:Expr.to_string e.cond)
              rmod_extra
              (ModeOps.to_string_or e.wmod)
              (Option.fold ~none:"_" ~some:Expr.to_string e.wval)
    in
      sprintf "%d: %s%s" e.van volatile_prefix main_str

(** Event equality *)
let event_equal e1 e2 =
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

(** Events container/manager *)
module EventsContainer = struct
  type t = {
    mutable events : (int, event) Hashtbl.t;
    mutable next_label : int;
    mutable next_van : int;
  }

  let create () = { events = Hashtbl.create 16; next_label = 1; next_van = 1 }

  let add t ?van ?label e =
    let van =
      match van with
      | Some v -> v
      | None ->
          let v = t.next_van in
            t.next_van <- v + 1;
            v
    in
    let label =
      match label with
      | Some l -> l
      | None ->
          let l = t.next_label in
            t.next_label <- l + 1;
            l
    in
    let e = { e with van; label } in
      Hashtbl.replace t.events label e;
      (* Update next_label to be at least label + 1 *)
      t.next_label <- max t.next_label (label + 1);
      (* Update next_van to be at least van + 1 *)
      t.next_van <- max t.next_van (van + 1);
      e

  let set_next_van t n = t.next_van <- n
  let get t label = Hashtbl.find_opt t.events label

  let get_exn t label =
    match get t label with
    | Some e -> e
    | None -> failwith (sprintf "Event %d not found" label)

  (** Map events matching criteria to a USet of their labels *)
  let map t event_labels ?typ ?mode ?mode_op ?second_mode () =
    let result = Uset.create () in
      Uset.iter
        (fun label ->
          match get t label with
          | None -> ()
          | Some e ->
              let type_match =
                match typ with
                | None -> true
                | Some t -> e.typ = t
              in
              let mode_match =
                match (mode, mode_op) with
                | None, _ -> true
                | Some m, None -> event_order e = m
                | Some m, Some ">" -> ModeOps.mode_le m (event_order e)
                | Some _, Some op ->
                    failwith (sprintf "ModeOp '%s' not supported" op)
              in
              let second_mode_match =
                match second_mode with
                | None -> true
                | Some sm -> e.strong = Some sm
              in
                if type_match && mode_match && second_mode_match then
                  Uset.add result label |> ignore
        )
        event_labels;
      result

  let all t =
    let result = Uset.create () in
      Hashtbl.iter (fun label _ -> Uset.add result label |> ignore) t.events;
      result

  let clone t =
    let new_t = create () in
      new_t.next_label <- t.next_label;
      new_t.next_van <- t.next_van;
      Hashtbl.iter
        (fun label e -> Hashtbl.replace new_t.events label (clone_event e))
        t.events;
      new_t

  let rewrite t label new_event =
    Hashtbl.replace t.events label new_event;
    t
end

let get_loc events e =
  try
    let event = Hashtbl.find events e in
      event.loc
  with Not_found -> None

let get_val events e =
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
let vale events e x =
  match Hashtbl.find_opt events e with
  | Some event when event.label >= 0 -> (
      match get_val events e with
      | Some v -> v
      | None ->
          let loc_x =
            match get_loc events x with
            | Some l -> Expr.to_string l
            | None -> string_of_int x
          in
            EVar (sprintf "v(%s)" loc_x)
    )
  | _ ->
      let loc_x =
        match get_loc events x with
        | Some l -> Expr.to_string l
        | None -> string_of_int x
      in
        EVar (sprintf "v(%s)" loc_x)

(** Get location from event e, or create symbolic location based on x's location
*)
let loce events e x =
  match Hashtbl.find_opt events e with
  | Some event when event.label >= 0 -> (
      match get_loc events e with
      | Some l -> l
      | None ->
          let loc_x =
            match get_loc events x with
            | Some l -> Expr.to_string l
            | None -> string_of_int x
          in
            EVar (sprintf "l(%s)" loc_x)
    )
  | _ ->
      let loc_x =
        match get_loc events x with
        | Some l -> Expr.to_string l
        | None -> string_of_int x
      in
        EVar (sprintf "l(%s)" loc_x)

(* Event type filters *)
let filter_events events e_set typ =
  Uset.filter
    (fun e ->
      try
        let event = Hashtbl.find events e in
          event.typ = typ
      with Not_found -> false
    )
    e_set
