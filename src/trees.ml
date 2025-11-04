open Uset

(* Build tree for program order *)
let build_tree e_set rel =
  let tree = Hashtbl.create 256 in
    USet.iter (fun e -> Hashtbl.add tree e (USet.create ())) e_set;
    USet.iter
      (fun (from, to_) ->
        let set = Hashtbl.find tree from in
          USet.add set to_ |> ignore
      )
      rel;
    tree
