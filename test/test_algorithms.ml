open Alcotest
open Algorithms
open Lwt.Syntax

let test_build_combinations =
 fun () ->
  let listmap = Hashtbl.create 10 in
    Hashtbl.add listmap 1 [ 2; 3; 4 ];
    Hashtbl.add listmap 2 [ 4; 5; 6 ];
    Hashtbl.add listmap 3 [ 6; 7; 8 ];

    let sum combo = List.fold_left (fun a b -> a + b) 0 combo in

    let[@warning "-27"] check_partial combo ?alternatives pair =
      sum (List.map snd combo) + snd pair < 15
    in
    let check_final combo = sum (List.map snd combo) < 15 in
    let combos =
      ListMapCombinationBuilder.build_combinations listmap [ 1; 2; 3 ]
        ~check_partial ~check_final ()
    in
    let combos = List.map (List.map snd) combos in
      check int "Number of combinations" 10 (List.length combos);
      check bool "[2;4;6] is a valid combination" true
        (List.mem [ 2; 4; 6 ] combos);
      check bool "[2;5;7] is a valid combination" true
        (List.mem [ 2; 5; 7 ] combos);
      check bool "[4;6;8] is not a valid combination" false
        (List.mem [ 4; 6; 8 ] combos)

(* Depth-first, then sorted, the combinations are build_combinations', in its
   order; four keys of different widths, so each direction of the order is
   exercised, and a check that prunes. *)
let test_fold_combinations () =
  let listmap = Hashtbl.create 10 in
    Hashtbl.add listmap 1 [ 1; 2; 3 ];
    Hashtbl.add listmap 2 [ 4; 5 ];
    Hashtbl.add listmap 3 [ 6; 7; 8; 9 ];
    Hashtbl.add listmap 4 [ 1; 0 ];
    let[@warning "-27"] check_partial combo ?alternatives (_, v) =
      (v + List.fold_left (fun a (_, b) -> a + b) 0 combo) mod 5 <> 0
    in
    let keys = [ 1; 2; 3; 4 ] in
    let built =
      ListMapCombinationBuilder.build_combinations listmap keys ~check_partial
        ()
    in
    let folded =
      ListMapCombinationBuilder.fold_combinations listmap keys ~check_partial
        (fun acc indices combo -> (indices, combo) :: acc)
        []
      |> List.stable_sort (fun (a, _) (b, _) ->
          ListMapCombinationBuilder.compare_build_order a b
      )
      |> List.map snd
    in
      check bool "some combinations are pruned" true
        (List.length built < 3 * 2 * 4 * 2);
      check
        (list (list (pair int int)))
        "the same combinations in the same order" built folded

let suite =
  ( "Algorithms",
    [
      test_case "build_combinations" `Quick test_build_combinations;
      test_case "fold_combinations" `Quick test_fold_combinations;
    ]
  )
