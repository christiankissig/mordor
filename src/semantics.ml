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

(** {1 Comparing Across Semantics}

    A compared coherence model checks the executions sMRD enumerated for the
    primary model, and admits some of them. Promising semantics enumerates
    executions of its own, so it is compared by outcome instead: a model admits
    an execution when it allows that execution's outcome -- sMRD's symbolic
    final values able to equal a promising run's concrete ones, or two
    promising runs ending alike. *)

let is_promising model = semantics_of_model_name model <> None

let outcome_of (execution : Types.symbolic_execution) =
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) execution.final_env []

let executions_of (ctx : mordor_ctx) =
  Option.fold ~none:[] ~some:Uset.USet.values ctx.executions

(** The executions sMRD enumerates and the given coherence models admit, per
    model: enumerated once, the first model primary and the rest checked as
    assertion models are, into [model_executions]. *)
let smrd_admitted (ctx : mordor_ctx) models =
  match models with
  | [] -> Lwt.return []
  | first :: _ ->
      let sub =
        {
          ctx with
          options = { ctx.options with semantics = Smrd; coherent = first };
          compare_models = [];
          assertion_models = models;
          model_admissions = None;
          model_executions = None;
          executions = None;
          justifications = None;
          fwd_es_ctx = None;
        }
      in
      let%lwt sub =
        Lwt.return sub
        |> Elaborations.step_generate_justifications
        |> Executions.step_calculate_dependencies
      in
        Lwt.return
          (List.map
             (fun m ->
               if m = first then (m, executions_of sub)
               else
                 ( m,
                   Option.bind sub.model_executions (fun t -> Hashtbl.find_opt t m)
                   |> Option.value ~default:[] ))
             models
          )

(** The executions promising semantics [semantics] computes for [ctx]. *)
let promising_run (ctx : mordor_ctx) semantics =
  let sub =
    {
      ctx with
      options = { ctx.options with semantics };
      compare_models = [];
      model_admissions = None;
      executions = None;
    }
  in
  let%lwt sub = Promising.step_calculate_executions (Lwt.return sub) in
    Lwt.return (executions_of sub)

(** [step_calculate_executions ?track ?after_justifications lwt_ctx] is sMRD's
    [Elaborations.step_generate_justifications] followed by
    [Executions.step_calculate_dependencies], or {!Promising}'s step for PS1.0
    and PS2.0, as [ctx.options.semantics] says. [after_justifications] runs
    between sMRD's two steps, where the justifications are known; [track] is
    {!Promising.step_calculate_executions}'s.

    The compared models are then matched against the primary's executions:
    coherence models by sMRD as ever when sMRD is primary, and otherwise by
    outcome, as above. *)
let step_calculate_executions ?track ?(after_justifications = Fun.id)
    (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let%lwt ctx = lwt_ctx in
  let primary_run ctx =
    match ctx.options.semantics with
    | Smrd ->
        Lwt.return ctx
        |> Elaborations.step_generate_justifications
        |> after_justifications
        |> Executions.step_calculate_dependencies
    | Promising1 | Promising2 ->
        Promising.step_calculate_executions ?track (Lwt.return ctx)
  in
  let primary = ctx.options.semantics in
  let compared =
    List.filter
      (fun m -> semantics_of_model_name m <> Some primary)
      ctx.compare_models
  in
  let promising, coherence = List.partition is_promising compared in
    if promising = [] && (primary = Smrd || coherence = []) then primary_run ctx
    else begin
      (* sMRD checks the coherence models itself when it is primary. *)
      ctx.compare_models <- (if primary = Smrd then coherence else []);
      let%lwt ctx = primary_run ctx in
      let structure = Option.get ctx.structure in
      let executions = executions_of ctx in
      let admissions =
        Option.value ctx.model_admissions ~default:(Hashtbl.create 16)
      in
      let admit (e : Types.symbolic_execution) model =
        Hashtbl.replace admissions e.id
          (Option.value (Hashtbl.find_opt admissions e.id) ~default:[] @ [ model ])
      in
      (* [model] admits a primary execution when one of [others] can end
         with its outcome, or it can end with one of theirs. *)
      let match_outcomes model ~primary_symbolic others =
        List.iter
          (fun (e : Types.symbolic_execution) ->
            let admitted =
              e.aborted = None
              && List.exists
                   (fun (o : Types.symbolic_execution) ->
                     o.aborted = None
                     &&
                     if primary_symbolic then
                       Assertion.admits_outcome structure e (outcome_of o)
                     else Assertion.admits_outcome structure o (outcome_of e)
                   )
                   others
            in
              if admitted then admit e model
          )
          executions
      in
      let%lwt () =
        if primary <> Smrd && coherence <> [] then
          let%lwt by_model = smrd_admitted ctx coherence in
            List.iter
              (fun (model, admitted) ->
                match_outcomes model ~primary_symbolic:false admitted
              )
              by_model;
            Lwt.return_unit
        else Lwt.return_unit
      in
      let%lwt () =
        Lwt_list.iter_s
          (fun model ->
            let%lwt others =
              promising_run ctx (Option.get (semantics_of_model_name model))
            in
              match_outcomes model ~primary_symbolic:(primary = Smrd) others;
              Lwt.return_unit
          )
          promising
      in
        ctx.compare_models <- compared;
        ctx.model_admissions <- Some admissions;
        Lwt.return ctx
    end

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
         (semantics_name options.semantics)
         (semantics_name options.semantics)
      )
