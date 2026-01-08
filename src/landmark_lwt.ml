(** Helper module for profiling Lwt code with Landmarks *)

(** Wrap an Lwt computation with landmarks tracking. This ensures the landmark
    stays open while the Lwt promise is being resolved.

    Usage: let my_function arg = Landmark_lwt.wrap "my_function" (fun () -> let*
    result = some_lwt_computation arg in Lwt.return result ) *)
let wrap name f =
  let landmark = Landmark.register name in
    Landmark.enter landmark;
    Lwt.finalize
      (fun () -> f ())
      (fun () ->
        Landmark.exit landmark;
        Lwt.return_unit
      )

(** Wrap an Lwt computation with an existing landmark. Useful when you want to
    reuse a landmark across multiple calls.

    Usage: let my_landmark = Landmark.register "my_operation"

    let process item = Landmark_lwt.wrap_with_landmark my_landmark (fun () -> (*
    Lwt code here *) ) *)
let wrap_with_landmark landmark f =
  Landmark.enter landmark;
  Lwt.finalize
    (fun () -> f ())
    (fun () ->
      Landmark.exit landmark;
      Lwt.return_unit
    )

(** Track an Lwt list iteration. Similar to Lwt_list.iter_s but with landmarks
    tracking.

    Usage: Landmark_lwt.iter_s "processing_items" process_item items *)
let iter_s name f list =
  let landmark = Landmark.register name in
    Landmark.enter landmark;
    Lwt.finalize
      (fun () -> Lwt_list.iter_s f list)
      (fun () ->
        Landmark.exit landmark;
        Lwt.return_unit
      )

(** Track an Lwt list map. Similar to Lwt_list.map_s but with landmarks
    tracking.

    Usage: Landmark_lwt.map_s "mapping_items" transform_item items *)
let map_s name f list =
  let landmark = Landmark.register name in
    Landmark.enter landmark;
    Lwt.finalize
      (fun () -> Lwt_list.map_s f list)
      (fun () ->
        Landmark.exit landmark;
        Lwt.return_unit
      )

(** Track an Lwt parallel operation. Similar to Lwt.join but with landmarks
    tracking.

    Usage: Landmark_lwt.join "parallel_operations" [op1; op2; op3] *)
let join name promises =
  let landmark = Landmark.register name in
    Landmark.enter landmark;
    Lwt.finalize
      (fun () -> Lwt.join promises)
      (fun () ->
        Landmark.exit landmark;
        Lwt.return_unit
      )
