(* Build tree for program order *)
let build_tree e_set rel =
  let tree = Hashtbl.create 256 in
    Uset.iter (fun e -> Hashtbl.add tree e (Uset.create ())) e_set;
    Uset.iter
      (fun (from, to_) ->
        let set = Hashtbl.find tree from in
          Uset.add set to_ |> ignore
      )
      rel;
    tree
