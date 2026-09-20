(** Domain-safe landmark wrapper.

    The [Landmarks] library is not domain-safe. [Landmark.enter] and
    [Landmark.exit] push and pop one global node stack ([current_node_ref] in
    landmark.ml), and [Landmark.register] mutates a global weak hashtable and a
    plain [incr] counter. Driven from several domains at once that state is
    corrupted: [OCAML_LANDMARKS=on] together with [--threads 8] aborted on every
    run with [Landmark.LandmarkFailure "Stack underflow"], or with a complaint
    about closing a landmark that was not the one on top of the stack.

    This module confines the profile to the main domain: [enter] and [exit] are
    no-ops on any other, so a worker never touches the shared stack. The pairs
    that do run stay balanced, because both ends ask the same question. With
    [--threads 1] -- the default, and the mode the profiling instructions in
    CLAUDE.md describe -- no domain pool exists and every landmark behaves as
    [Landmark]'s own does.

    What a parallel run loses is the workers' share of the profile. A single
    global call graph could not have described several domains at once anyway;
    reporting per-domain would be a change to landmarks itself. *)

(** [register name] registers a landmark. It must be called from the main
    domain, which in practice means at module initialisation: registration
    writes to landmarks' global tables and cannot be made a no-op elsewhere, as
    the landmark it returns is needed whether or not it is ever entered. *)
let register ?id ?location name =
  if not (Domain.is_main_domain ()) then
    invalid_arg
      ("Landmark_safe.register: "
      ^ name
      ^ " registered outside the main domain; register landmarks at module \
         initialisation"
      );
  Landmark.register ?id ?location name

(** [enter landmark] enters [landmark] on the main domain, and does nothing
    anywhere else. The [profiling] test comes first so that a run without
    [OCAML_LANDMARKS=on] pays exactly what it paid before: one ref read. *)
let enter landmark =
  if Landmark.profiling () && Domain.is_main_domain () then
    Landmark.enter landmark

(** [exit landmark] is the counterpart to {!enter}, no-op under the same
    conditions so that entries and exits pair up on every domain. *)
let exit landmark =
  if Landmark.profiling () && Domain.is_main_domain () then
    Landmark.exit landmark
