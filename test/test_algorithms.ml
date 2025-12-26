open Alcotest
open Algorithms
open Lwt.Syntax

(** Helper to run Lwt tests *)
let run_lwt f () = Lwt_main.run (f ())

let test_build_combinations =
  run_lwt (fun () ->
      let listmap = Hashtbl.create 10 in
        Hashtbl.add listmap 1 [ 2; 3; 4 ];
        Hashtbl.add listmap 2 [ 4; 5; 6 ];
        Hashtbl.add listmap 3 [ 6; 7; 8 ];

        let sum combo = List.fold_left (fun a b -> a + b) 0 combo in

        let[@warning "-27"] check_partial_combo combo ?alternatives pair =
          Lwt.return (sum (List.map snd combo) + snd pair < 15)
        in
        let check_final_combo combo =
          Lwt.return (sum (List.map snd combo) < 15)
        in
          let* combos =
            ListMapCombinationBuilder.build_combinations listmap [ 1; 2; 3 ]
              ~check_partial_combo ~check_final_combo ()
          in
          let combos = List.map (List.map snd) combos in
            check int "Number of combinations" 10 (List.length combos);
            check bool "[2;4;6] is a valid combination" true
              (List.mem [ 2; 4; 6 ] combos);
            check bool "[2;5;7] is a valid combination" true
              (List.mem [ 2; 5; 7 ] combos);
            check bool "[4;6;8] is not a valid combination" false
              (List.mem [ 4; 6; 8 ] combos);
            Lwt.return_unit
  )

let suite =
  ( "Algorithms",
    [ test_case "build_combinations" `Quick test_build_combinations ]
  )
