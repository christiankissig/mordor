(** {1 Semantics Selection}

    The step of the pipeline that turns an interpreted program into executions,
    under the semantics the options select. Either way it follows
    [Interpret.step_interpret] and fills [ctx.executions] for
    [Assertion.step_check_assertions]:

    {[
      Lwt.return ctx
      |> Parse.step_parse_litmus
      |> Interpret.step_interpret
      |> Semantics.step_calculate_executions
      |> Assertion.step_check_assertions
    ]} *)

open Context

(** [step_calculate_executions lwt_ctx] is sMRD's
    [Elaborations.step_generate_justifications] followed by
    [Executions.step_calculate_dependencies], or {!Promising}'s step for PS1.0
    and PS2.0, as [ctx.options.semantics] says. *)
let step_calculate_executions (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let%lwt ctx = lwt_ctx in
    match ctx.options.semantics with
    | Smrd ->
        Lwt.return ctx
        |> Elaborations.step_generate_justifications
        |> Executions.step_calculate_dependencies
    | Promising1 | Promising2 ->
        Promising.step_calculate_executions (Lwt.return ctx)

(** [require_smrd ~command ctx] fails unless [ctx] computes executions under
    sMRD: for the commands that show what only sMRD computes -- justifications,
    dependencies, futures, event-structure relations. *)
let require_smrd ~command (options : options) =
  if options.semantics <> Smrd then
    failwith
      (Printf.sprintf
         "The %s command shows sMRD's justifications and dependencies, which \
          %s does not compute; only run supports --semantics %s."
         command
         (show_semantics options.semantics)
         ( match options.semantics with
         | Promising1 -> "ps1"
         | _ -> "ps2"
         )
      )
