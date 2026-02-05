open Format
open Uset

(** Pretty-print an integer *)
let pp_int fmt i = Format.fprintf fmt "%d" i

(** Pretty-print a Z.t integer *)
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

(** Pretty-print a ternary relation (set of triples) *)
let pp_ternary_relation pp_a pp_b pp_c fmt rel =
  Format.fprintf fmt "@[<hv 2>{";
  let first = ref true in
    USet.iter
      (fun (a, b, c) ->
        if !first then first := false else Format.fprintf fmt ";@,";
        Format.fprintf fmt "(@[%a,@ %a,@ %a@])" pp_a a pp_b b pp_c c
      )
      rel;
    Format.fprintf fmt "}@]"

(** Pretty-print a ternary relation with compact notation *)
let pp_ternary_relation_compact pp_a pp_b pp_c fmt rel =
  Format.fprintf fmt "{@[<hov 2>";
  let first = ref true in
    USet.iter
      (fun (a, b, c) ->
        if !first then first := false else Format.fprintf fmt ";@ ";
        Format.fprintf fmt "(%a,%a,%a)" pp_a a pp_b b pp_c c
      )
      rel;
    Format.fprintf fmt "@]}"

let pair_int_uset_to_yojson uset =
  [%to_yojson: (int * int) list] (USet.values uset)

let pair_int_uset_of_yojson json =
  match [%of_yojson: (int * int) list] json with
  | Ok lst -> Ok (USet.of_list lst)
  | Error e -> Error e
