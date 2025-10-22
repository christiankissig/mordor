(** Event operations and utilities for sMRD *)

open Types
open Expr

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
    | None -> failwith (Printf.sprintf "Event %d does not have an id" e.label)
  else failwith (Printf.sprintf "Event %d type does not support id" e.label)

let get_wval e =
  if has_wval e then
    match e.wval with
    | Some v -> v
    | None -> failwith (Printf.sprintf "Event %d does not have a wval" e.label)
  else failwith (Printf.sprintf "Event %d type does not support wval" e.label)

let get_rval e =
  if has_rval e then
    match e.rval with
    | Some v -> v
    | None -> failwith (Printf.sprintf "Event %d does not have an rval" e.label)
  else failwith (Printf.sprintf "Event %d type does not support rval" e.label)

let get_cond e =
  if has_cond e then
    match e.cond with
    | Some c -> c
    | None -> failwith (Printf.sprintf "Event %d does not have a cond" e.label)
  else failwith (Printf.sprintf "Event %d type does not support cond" e.label)

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

(** Value to string (you may need to implement this based on your value_type) *)
let rec value_to_string = function
  | VNumber z -> Z.to_string z
  | VSymbol s -> s
  | VVar v -> v
  | VExpression expr -> expr_to_string expr
  | VBoolean b -> string_of_bool b

and expr_to_string = function
  | EBinOp (v1, op, v2) ->
      Printf.sprintf "(%s %s %s)" (value_to_string v1) op (value_to_string v2)
  | EUnOp (op, v) -> Printf.sprintf "(%s %s)" op (value_to_string v)
  | EOr exprs ->
      Printf.sprintf "Or(%s)"
        (String.concat " | "
           (List.map
              (fun l -> String.concat " & " (List.map expr_to_string l))
              exprs
           )
        )
  | EVar v -> v
  | ENum z -> Z.to_string z

(** Event to string *)
let event_to_string e =
  if is_init e then ""
  else
    let volatile_prefix = if e.volatile then "v" else "" in
    let main_str =
      match e.typ with
      | Init -> ""
      | Read ->
          Printf.sprintf "R%s %s %s"
            (ModeOps.to_string_or e.rmod)
            (Option.fold ~none:"_" ~some:value_to_string e.id)
            (Option.fold ~none:"_" ~some:value_to_string e.rval)
      | Write ->
          Printf.sprintf "W%s %s %s"
            (ModeOps.to_string_or e.wmod)
            (Option.fold ~none:"_" ~some:value_to_string e.id)
            (Option.fold ~none:"_" ~some:value_to_string e.wval)
      | Lock -> Option.fold ~none:"" ~some:value_to_string e.id
      | Unlock -> Option.fold ~none:"" ~some:value_to_string e.id
      | Fence -> Printf.sprintf "F%s" (ModeOps.to_string_or e.fmod)
      | Branch ->
          Printf.sprintf "[%s]"
            (Option.fold ~none:"_" ~some:value_to_string e.cond)
      | Loop ->
          Printf.sprintf "%s%s%s" Unicode.langle
            (Option.fold ~none:"_" ~some:value_to_string e.cond)
            Unicode.rangle
      | Malloc ->
          Printf.sprintf "Alloc %s %s"
            (Option.fold ~none:"_" ~some:value_to_string e.rval)
            (Option.fold ~none:"_" ~some:value_to_string e.wval)
      | Free ->
          Printf.sprintf "Free %s"
            (Option.fold ~none:"_" ~some:value_to_string e.id)
      | RMW ->
          Printf.sprintf "%s . R%s %s . W%s %s"
            (Option.fold ~none:"_" ~some:value_to_string e.id)
            (ModeOps.to_string_or e.rmod)
            (Option.fold ~none:"_" ~some:value_to_string e.rval)
            (ModeOps.to_string_or e.wmod)
            (Option.fold ~none:"_" ~some:value_to_string e.wval)
      | CRMW ->
          let rmod_extra =
            if e.rmod <> e.fmod then
              Printf.sprintf "+%s" (ModeOps.to_string_or e.rmod)
            else ""
          in
            Printf.sprintf "%s . R%s %s . [%s]%s . %s %s"
              (Option.fold ~none:"_" ~some:value_to_string e.id)
              (ModeOps.to_string_or e.fmod)
              (Option.fold ~none:"_" ~some:value_to_string e.rval)
              (Option.fold ~none:"_" ~some:value_to_string e.cond)
              rmod_extra
              (ModeOps.to_string_or e.wmod)
              (Option.fold ~none:"_" ~some:value_to_string e.wval)
    in
      Printf.sprintf "%d: %s%s" e.van volatile_prefix main_str

(** Value type equality *)
let rec value_type_equal v1 v2 =
  match (v1, v2) with
  | VNumber z1, VNumber z2 -> Z.equal z1 z2
  | VSymbol s1, VSymbol s2 -> s1 = s2
  | VVar v1, VVar v2 -> v1 = v2
  | VExpression e1, VExpression e2 -> expr_equal e1 e2
  | VBoolean b1, VBoolean b2 -> b1 = b2
  | _ -> false

and expr_equal e1 e2 =
  match (e1, e2) with
  | EBinOp (v1, op1, v2), EBinOp (v3, op2, v4) ->
      op1 = op2 && value_type_equal v1 v3 && value_type_equal v2 v4
  | EUnOp (op1, v1), EUnOp (op2, v2) -> op1 = op2 && value_type_equal v1 v2
  | EOr l1, EOr l2 ->
      List.length l1 = List.length l2
      && List.for_all2
           (fun ll1 ll2 ->
             List.length ll1 = List.length ll2
             && List.for_all2 expr_equal ll1 ll2
           )
           l1 l2
  | EVar v1, EVar v2 -> v1 = v2
  | ENum z1, ENum z2 -> Z.equal z1 z2
  | _ -> false

(** Event equality *)
let event_equal e1 e2 =
  e1.label = e2.label
  && e1.typ = e2.typ
  && ( match (e1.id, e2.id) with
     | None, None -> true
     | Some v1, Some v2 -> value_type_equal v1 v2
     | _ -> false
     )
  && ( match (e1.rval, e2.rval) with
     | None, None -> true
     | Some v1, Some v2 -> value_type_equal v1 v2
     | _ -> false
     )
  &&
  match (e1.wval, e2.wval) with
  | None, None -> true
  | Some v1, Some v2 -> value_type_equal v1 v2
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
    | None -> failwith (Printf.sprintf "Event %d not found" label)

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
                    failwith (Printf.sprintf "ModeOp '%s' not supported" op)
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

let loc events e =
  try
    let event = Hashtbl.find events e in
      event.id
  with Not_found -> None

let val_ events e =
  try
    let event = Hashtbl.find events e in
      match event.wval with
      | Some v -> Some v
      | None -> event.rval
  with Not_found -> None

(** Get value from event e, or create symbolic value based on x's location *)
let vale events e x =
  match Hashtbl.find_opt events e with
  | Some event when event.label >= 0 -> (
      match val_ events e with
      | Some v -> v
      | None ->
          let loc_x =
            match loc events x with
            | Some l -> Value.to_string l
            | None -> string_of_int x
          in
            VVar (Printf.sprintf "v(%s)" loc_x)
    )
  | _ ->
      let loc_x =
        match loc events x with
        | Some l -> Value.to_string l
        | None -> string_of_int x
      in
        VVar (Printf.sprintf "v(%s)" loc_x)

(** Get location from event e, or create symbolic location based on x's location
*)
let loce events e x =
  match Hashtbl.find_opt events e with
  | Some event when event.label >= 0 -> (
      match loc events e with
      | Some l -> l
      | None ->
          let loc_x =
            match loc events x with
            | Some l -> Value.to_string l
            | None -> string_of_int x
          in
            VVar (Printf.sprintf "l(%s)" loc_x)
    )
  | _ ->
      let loc_x =
        match loc events x with
        | Some l -> Value.to_string l
        | None -> string_of_int x
      in
        VVar (Printf.sprintf "l(%s)" loc_x)
