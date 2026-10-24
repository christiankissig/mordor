(* What MoRDor's hashes make of a fixed set of values, for comparing the
   native build with the browser build (#193). [hashes_native.exe] and
   [hashes.bc.js] both print [main]'s report, and compare.py requires the two
   to be identical.

   A hash that overflows depends on the width of [int], 63 bits natively and 32
   under js_of_ocaml. Through a set's buckets it decides the order the set's
   members come out in, which is how such a hash once reordered the executions
   of LB, 3.SB and IRIW in the browser build. So the report prints orders as
   well as hash values: sets of the kinds of members the analysis keeps, large
   enough for their hashes to overflow. *)

open Types
open Uset

let event label : event =
  {
    label;
    typ = Write;
    id = None;
    loc = Some (EVar "x");
    rval = None;
    wval = Some (ENum (Z.of_int label));
    cond = None;
    rmod = Relaxed;
    wmod = Relaxed;
    fmod = Relaxed;
    volatile = false;
    strong = None;
    is_rdmw = false;
  }

let expr i =
  EBinOp
    ( EVar (Printf.sprintf "r%d" (i mod 7)),
      (if i mod 2 = 0 then "=" else "<"),
      EOr [ ENum (Z.of_int (i * 1000003)); ESymbol (Printf.sprintf "s%d" i) ]
    )

let pairs i = USet.of_list (List.init (1 + (i mod 5)) (fun k -> (i, i + k)))
let line name items = Printf.printf "%s: %s\n" name (String.concat " " items)
let order name show s = line name (List.map show (USet.values s))

let main () =
  let n = 200 in
    order "ints" string_of_int (USet.of_list (List.init n (fun i -> i * 7919)));
    order "pairs"
      (fun (a, b) -> Printf.sprintf "%d,%d" a b)
      (USet.of_list (List.init n (fun i -> (i, n - i))));
    order "strings" Fun.id
      (USet.of_list (List.init n (fun i -> Printf.sprintf "v%d" i)));
    order "lists"
      (fun l -> String.concat "," (List.map string_of_int l))
      (USet.of_list (List.init n (fun i -> List.init (1 + (i mod 4)) (( + ) i))));
    order "exprs" show_expr (USet.of_list (List.init n expr));
    order "sets of pairs"
      (fun s -> string_of_int (USet.size s))
      (USet.of_list (List.init n pairs));
    order "labelled exprs"
      (fun (l, e) -> Printf.sprintf "%d:%s" l (show_expr e))
      (USet.of_list (List.init n (fun i -> (i, expr i))));
    line "conjunction hashes"
      (List.init 20 (fun i ->
           string_of_int (Expr.ConjunctionCacheKey.hash (List.init (i + 1) expr))
       )
      );
    line "justification hashes"
      (List.init 20 (fun i ->
           string_of_int
             (Justifications.Justification.hash
                {
                  p = List.init (i + 1) expr;
                  d = USet.of_list [ Printf.sprintf "s%d" i ];
                  fwd = pairs i;
                  we = pairs (i + 1);
                  w = event i;
                }
             )
       )
      )
