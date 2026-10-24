(** [caller ()] is the first caller in MoRDor's own code outside the solver, by
    function name: outside this file, [solver.ml] and the platform
    implementations in [src/native/]. A closure passed to [Hashtbl.filteri] is
    reported as its caller. It is ["?"] where the runtime gives no call stack.
    For diagnostics: S7's trace and W1's query dump. *)
let caller () =
  let slots =
    Printexc.get_callstack 24
    |> Printexc.backtrace_slots
    |> Option.value ~default:[||]
  in
    Array.to_list slots
    |> List.find_map (fun slot ->
        match Printexc.Slot.location slot with
        | Some loc
          when String.starts_with ~prefix:"src/" loc.filename
               && (not (String.starts_with ~prefix:"src/native/" loc.filename))
               && not
                    (List.mem loc.filename
                       [ "src/call_site.ml"; "src/solver.ml" ]
                    ) ->
            Some (Option.value (Printexc.Slot.name slot) ~default:loc.filename)
        | _ -> None
    )
    |> Option.value ~default:"?"
