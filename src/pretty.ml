open Format
open Uset

let pp_z fmt z = Format.fprintf fmt "%s" (Z.to_string z)

let pp_int_uset fmt uset =
  Format.fprintf fmt "{%s}"
    (String.concat ", " (List.map string_of_int (USet.to_list uset)))

let pp_int_urel fmt uset =
  Format.fprintf fmt "{%s}"
    (String.concat ", "
       (List.map
          (fun (a, b) -> Printf.sprintf "(%d,%d)" a b)
          (USet.to_list uset)
       )
    )

let pp_string_uset fmt uset =
  Format.fprintf fmt "{%s}"
    (String.concat ", "
       (List.map (fun a -> Printf.sprintf "%s" a) (USet.to_list uset))
    )

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
