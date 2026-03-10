(** Thread-safe logging wrapper.

    [Stdlib.Format] and the [Logs] library are not domain-safe: their
    pretty-printer maintains internal mutable state (including a [Queue] of
    pending formatting tokens) that is corrupted when multiple domains call
    logging functions concurrently.

    This module wraps every [Logs] level with a [Mutex] so that only one domain
    can drive the formatter at a time. The interface is intentionally identical
    to [Logs] so that call sites only need to change [Logs.] to [Logs_safe.]. *)

let mutex = Mutex.create ()

(** [with_lock f] runs [f ()] with the logging mutex held, releasing it even if
    [f] raises. *)
let with_lock f =
  Mutex.lock mutex;
  Fun.protect ~finally:(fun () -> Mutex.unlock mutex) f

let debug msgf =
  if Logs.level () >= Some Logs.Debug then with_lock (fun () -> Logs.debug msgf)

let info msgf =
  if Logs.level () >= Some Logs.Info then with_lock (fun () -> Logs.info msgf)

let warn msgf =
  if Logs.level () >= Some Logs.Warning then with_lock (fun () -> Logs.warn msgf)

let err msgf =
  if Logs.level () >= Some Logs.Error then with_lock (fun () -> Logs.err msgf)

(** [app] corresponds to [Logs.app] (the always-on level). No level check
    needed: [Logs.App] is always enabled. *)
let app msgf = with_lock (fun () -> Logs.app msgf)
