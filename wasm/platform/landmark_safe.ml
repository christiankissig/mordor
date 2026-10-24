(** The browser's {!Landmark_safe}: no profiling, so every landmark is a no-op.
*)

type landmark = unit

let register ?id:_ ?location:_ _ = ()
let enter () = ()
let exit () = ()
