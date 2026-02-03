open Format

(** Generic pretty printer for hashtables *)
let pp_hashtbl pp_key pp_value fmt ht =
  fprintf fmt "@[<hov 2>{";
  let first = ref true in
    Hashtbl.iter
      (fun k v ->
        if not !first then fprintf fmt ",@ " else first := false;
        fprintf fmt "%a -> %a" pp_key k pp_value v
      )
      ht;
    fprintf fmt "}@]"

(** Pretty printer for int lists *)
let pp_int_list fmt lst =
  fprintf fmt "[@[%a@]]"
    (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") pp_print_int)
    lst
