(** Tests for the Büchi arithmetic check on interpreted programs. *)

open Alcotest
open Context
open Types

(* Interpret [program] and return the check's violations, or the failure
   interpretation stopped with. *)
let interpret ?(allow = false) program =
  let ctx = make_context { default_options with allow_non_buechi = allow } () in
    ctx.litmus <- Some program;
    match
      Lwt_main.run
        (Lwt.return ctx |> Parse.step_parse_litmus |> Interpret.step_interpret)
    with
    | ctx -> Ok (Buechi.check (Option.get ctx.structure))
    | exception Failure msg -> Error msg

let reasons = function
  | Ok vs -> List.map (fun v -> v.Buechi.reason) vs
  | Error _ -> [ "failed" ]

(* A product of two read values is outside the fragment, and interpretation
   stops with an error naming it. *)
let test_product_of_reads_fails () =
  match interpret "x := 3; y := 4; r1 := x; r2 := y; z := r1 * r2" with
  | Error msg ->
      let needle = "product of two non-constant terms" in
      let n = String.length needle in
      let rec contains i =
        i + n <= String.length msg
        && (String.sub msg i n = needle || contains (i + 1))
      in
        check bool "names the product" true (contains 0)
  | Ok _ -> fail "interpretation should have failed"

(* With the option the same program interprets, and the check still finds the
   product. *)
let test_allow_downgrades_to_warning () =
  check (list string) "one product"
    [ "product of two non-constant terms" ]
    (reasons
       (interpret ~allow:true "x := 3; y := 4; r1 := x; r2 := y; z := r1 * r2")
    )

(* Division by a read value is outside; division by a constant is inside. *)
let test_division () =
  check (list string) "division by an unknown"
    [ "division by a non-constant term" ]
    (reasons (interpret ~allow:true "x := 3; r1 := x; z := 8 / r1"));
  check (list string) "division by a constant" []
    (reasons (interpret "x := 3; r1 := x; z := r1 / 2"))

(* What the fragment defines: scaling, bitwise operations, a product of
   registers that hold numerals, and division by a truth value. *)
let test_inside_the_fragment () =
  check (list string) "linear and bitwise" []
    (reasons
       (interpret
          "x := 3; r1 := x; z := (r1 * 4) + (r1 & 6); w := (r1 | 1) ^ 2; r2 := \
           5; r3 := 6; v := r2 * r3; u := 1 / (! r1)"
       )
    )

let suite =
  ( "Buechi",
    [
      test_case "product of two reads fails interpretation" `Quick
        test_product_of_reads_fails;
      test_case "--allow-non-buechi downgrades to a warning" `Quick
        test_allow_downgrades_to_warning;
      test_case "division by an unknown, not by a constant" `Quick test_division;
      test_case "scaling, bitwise and finite-range terms pass" `Quick
        test_inside_the_fragment;
    ]
  )
