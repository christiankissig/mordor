(** A one-line display of the pipeline's progress, on stderr, for the CLI.

    A stage has a name, what it counts, and how many there are when it knows.
    Stages nest: the display shows the innermost, and a stage that took longer
    than a second leaves a line behind when it finishes, indented by how deep it
    was. [tick] counts one of the stage's items done and [found] counts what it
    has found, both from any domain; the line is redrawn at most ten times a
    second, by whichever domain gets there.

    Off unless {!enabled} is set, which the CLI does when stderr is a terminal.
    Logging clears the line before it writes ({!interrupt}), and the next update
    draws it again. *)

let enabled = ref false

type stage = {
  name : string;
  unit : string;
  total : int option;
  done_ : int Atomic.t;
  found : int Atomic.t;
  mutable found_unit : string;
  mutable detail : string;
  started : float;
}

let lock = Mutex.create ()

(* Innermost first. Changed only under [lock]. *)
let stages : stage list ref = ref []
let last_drawn = Atomic.make 0.
let showing = ref false

(* Writers to stderr in progress ({!while_writing}): no redraw meanwhile. *)
let writing = Atomic.make 0

let width () =
  match Option.bind (Sys.getenv_opt "COLUMNS") int_of_string_opt with
  | Some w when w > 20 -> w
  | _ -> 100

let duration seconds =
  if seconds < 60. then Printf.sprintf "%.1fs" seconds
  else if seconds < 3600. then
    Printf.sprintf "%dm%02ds"
      (int_of_float seconds / 60)
      (int_of_float seconds mod 60)
  else
    Printf.sprintf "%dh%02dm"
      (int_of_float seconds / 3600)
      (int_of_float seconds mod 3600 / 60)

(* 12345 as "12,345". *)
let thousands n =
  let s = string_of_int n in
  let len = String.length s in
  let b = Buffer.create (len + (len / 3)) in
    String.iteri
      (fun i c ->
        if i > 0 && (len - i) mod 3 = 0 && c <> '-' then Buffer.add_char b ',';
        Buffer.add_char b c
      )
      s;
    Buffer.contents b

let line stage now =
  let done_ = Atomic.get stage.done_ in
  let found = Atomic.get stage.found in
  let counts =
    match stage.total with
    | Some total when total > 0 ->
        let bar_width = 20 in
        let filled = min bar_width (done_ * bar_width / total) in
          Printf.sprintf "[%s%s] %s/%s %s %3d%%"
            (String.concat "" (List.init filled (fun _ -> "█")))
            (String.make (bar_width - filled) ' ')
            (thousands done_) (thousands total) stage.unit
            (done_ * 100 / total)
    | _ ->
        let spinner = [| "|"; "/"; "-"; "\\" |] in
        let spin =
          spinner.(int_of_float ((now -. stage.started) *. 4.) mod 4)
        in
          if stage.unit = "" then spin
          else Printf.sprintf "%s %s %s" spin (thousands done_) stage.unit
  in
  let found =
    if found > 0 || stage.found_unit <> "" then
      Printf.sprintf " · %s %s" (thousands found) stage.found_unit
    else ""
  in
  let detail = if stage.detail = "" then "" else " · " ^ stage.detail in
    Printf.sprintf "%s %s%s%s · %s" stage.name counts found detail
      (duration (now -. stage.started))

(* Visible width: the bar's blocks are three bytes each. *)
let visible s =
  let n = ref 0 in
    String.iter (fun c -> if Char.code c land 0xC0 <> 0x80 then incr n) s;
    !n

let truncate s w =
  if visible s <= w then s
  else
    (* Cut on a character boundary, counting as [visible] does. *)
    let b = Buffer.create w in
    let n = ref 0 in
      String.iter
        (fun c ->
          let starts = Char.code c land 0xC0 <> 0x80 in
            if starts then incr n;
            if !n <= w then Buffer.add_char b c
        )
        s;
      Buffer.contents b

let draw_locked now =
  match !stages with
  | [] -> ()
  | stage :: _ ->
      prerr_string ("\r" ^ truncate (line stage now) (width () - 1) ^ "\027[K");
      flush stderr;
      showing := true;
      Atomic.set last_drawn now

let clear_locked () =
  if !showing then (
    prerr_string "\r\027[K";
    flush stderr;
    showing := false
  )

(* Redraw if a tenth of a second has passed, unless another domain is. *)
let update () =
  if !enabled then
    let now = Unix.gettimeofday () in
      if
        Atomic.get writing = 0
        && now -. Atomic.get last_drawn >= 0.1
        && Mutex.try_lock lock
      then
        Fun.protect
          ~finally:(fun () -> Mutex.unlock lock)
          (fun () -> draw_locked now)

(** [interrupt ()] clears the line, so that something else can write to the
    terminal. The next update draws it again. *)
let interrupt () =
  if !enabled then Mutex.protect lock (fun () -> clear_locked ())

(** [while_writing f] runs [f], which writes to the terminal, with the line
    cleared and not redrawn until it returns: a domain updating meanwhile would
    otherwise draw it back in the middle of what [f] writes. *)
let while_writing f =
  if not !enabled then f ()
  else (
    Atomic.incr writing;
    Fun.protect
      ~finally:(fun () -> Atomic.decr writing)
      (fun () ->
        interrupt ();
        f ()
      )
  )

(** [start ?total ?found name ~unit] begins a stage of [total] items counted as
    [unit], if it knows how many, and whose finds are counted as [found]. *)
let start ?total ?(found = "") ~unit name =
  if !enabled then
    Mutex.protect lock (fun () ->
        stages :=
          {
            name;
            unit;
            total;
            done_ = Atomic.make 0;
            found = Atomic.make 0;
            found_unit = found;
            detail = "";
            started = Unix.gettimeofday ();
          }
          :: !stages;
        draw_locked (Unix.gettimeofday ())
    )

(** [finish ()] ends the innermost stage, leaving a line behind it if it took
    more than a second. *)
let finish () =
  if !enabled then
    Mutex.protect lock (fun () ->
        match !stages with
        | [] -> ()
        | stage :: outer ->
            let now = Unix.gettimeofday () in
              clear_locked ();
              ( if now -. stage.started >= 1. then
                  let depth = List.length outer in
                  let summary =
                    let done_ = Atomic.get stage.done_ in
                    let found = Atomic.get stage.found in
                      Printf.sprintf "%s%s%s%s%s in %s"
                        (String.make (2 * depth) ' ')
                        stage.name
                        ( if stage.unit = "" then ""
                          else
                            Printf.sprintf ": %s %s" (thousands done_)
                              stage.unit
                        )
                        ( if found > 0 || stage.found_unit <> "" then
                            Printf.sprintf ", %s %s" (thousands found)
                              stage.found_unit
                          else ""
                        )
                        (if stage.detail = "" then "" else ", " ^ stage.detail)
                        (duration (now -. stage.started))
                  in
                    prerr_endline summary
              );
              stages := outer;
              if outer <> [] then draw_locked now
    )

(** [tick ()] counts one item of the innermost stage done. *)
let tick () =
  if !enabled then (
    ( match !stages with
    | stage :: _ -> Atomic.incr stage.done_
    | [] -> ()
    );
    update ()
  )

(** [found ?unit n] counts [n] more finds for the innermost stage, as [unit] if
    the stage does not already name them. *)
let found ?unit n =
  if !enabled then (
    ( match !stages with
    | stage :: _ ->
        ignore (Atomic.fetch_and_add stage.found n);
        Option.iter
          (fun unit -> if stage.found_unit = "" then stage.found_unit <- unit)
          unit
    | [] -> ()
    );
    update ()
  )

(** [set_done n] and [set_detail s] replace the innermost stage's count and its
    note, for a stage that knows them rather than counts them. *)
let set_done n =
  if !enabled then (
    ( match !stages with
    | stage :: _ -> Atomic.set stage.done_ n
    | [] -> ()
    );
    update ()
  )

let set_detail s =
  if !enabled then (
    Mutex.protect lock (fun () ->
        match !stages with
        | stage :: _ -> stage.detail <- s
        | [] -> ()
    );
    update ()
  )

(** [stage ?total ?found name ~unit f] runs the stage [f ()], a promise. *)
let stage ?total ?found ~unit name f =
  if not !enabled then f ()
  else (
    start ?total ?found ~unit name;
    Lwt.finalize f (fun () ->
        finish ();
        Lwt.return_unit
    )
  )
