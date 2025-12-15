(** Graph Visualization Module for Symbolic Event Structures using OCamlGraph *)

open Context
open Graph
open Expr
open Types
open Uset
open Lwt.Syntax

module EventStructureViz = struct
  (** Vertex type with event information *)
  module Vertex = struct
    type t = { id : int; event : event; constraints : expr list }

    let compare v1 v2 = compare v1.id v2.id
    let hash v = Hashtbl.hash v.id
    let equal v1 v2 = v1.id = v2.id
  end

  (** Edge label type *)
  type edge_label =
    | PO (* Program Order *)
    | RMW (* Read-Modify-Write *)
    | LO (* Lock Order *)
    | FJ (* Fork-Join *)
    | DP of string
      (* Data Dependency with string representation of relative
    predicates *)
    | PPO of string
    (* Preserved Program Order with string representation of
    relative predicates *)
    | RF of string
  (* Read-From with string representation of relative
    predicates *)

  (** Edge type *)
  module Edge = struct
    type t = edge_label

    let compare = compare
    let default = PO
  end

  (** Create the graph type *)
  module G = Imperative.Digraph.ConcreteLabeled (Vertex) (Edge)

  (** [structure executions] Generate edges for relaxed dependencies in
      execution set for symbolic event structure.

      Performs DNF simplification on predicates to minimize edges. *)
  let generate_relaxed_deps (structure : symbolic_event_structure)
      (executions : symbolic_execution USet.t option) :
      (int * int * Edge.t) USet.t =
    Option.map
      (fun execs ->
        (* Collect edges with predicates *)
        let edge_preds_table = Hashtbl.create 100 in

        USet.iter
          (fun exec ->
            let preds = exec.ex_p in
            let filter_preds src =
              let src_preds =
                Hashtbl.find_opt structure.restrict src
                |> Option.value ~default:[]
              in
                List.filter (fun p -> not (List.mem p src_preds)) preds
            in

            let process_relation rel_type edges =
              USet.iter
                (fun (src, dst) ->
                  let clause = filter_preds src in
                  let key = (src, dst, rel_type) in
                  let existing =
                    Hashtbl.find_opt edge_preds_table key
                    |> Option.value ~default:[]
                  in
                    Hashtbl.replace edge_preds_table key (clause :: existing)
                )
                edges
            in

            process_relation `DP (URelation.transitive_reduction exec.dp);
            process_relation `PPO (URelation.transitive_reduction exec.ppo);
            process_relation `RF (URelation.transitive_reduction exec.rf)
          )
          execs;

        (* Simplify and create edges *)
        let result_edges = ref (USet.create ()) in

        Hashtbl.iter
          (fun (src, dst, rel_type) dnf_clauses ->
            let simplified_dnf = Expr.simplify_dnf dnf_clauses in

            List.iter
              (fun clause ->
                (* Format predicate string *)
                let preds_str =
                  match clause with
                  | [ EBoolean true ] | [] ->
                      "" (* true predicate -> empty string *)
                  | _ ->
                      clause
                      |> List.map Expr.to_string
                      |> String.concat " AND " (* ASCII instead of Unicode *)
                in

                let edge =
                  match rel_type with
                  | `DP -> (src, dst, DP preds_str)
                  | `PPO -> (src, dst, PPO preds_str)
                  | `RF -> (src, dst, RF preds_str)
                in
                  result_edges := USet.add !result_edges edge
              )
              simplified_dnf
          )
          edge_preds_table;

        !result_edges
      )
      executions
    |> Option.value ~default:(USet.create ())

  (** Build graph from event structure *)
  let build_graph (structure : symbolic_event_structure)
      (executions : symbolic_execution USet.t option) : G.t =
    let g = G.create () in

    (* Create vertices *)
    let events = structure.events in
    let vertex_map = Hashtbl.create 100 in
      Hashtbl.iter (fun k _v -> Printf.printf "%d " k) events;
      USet.iter (fun eid -> Printf.printf "%d " eid) structure.e;

      USet.iter
        (fun event_id ->
          let evt = Hashtbl.find events event_id in
          let constraints =
            try Hashtbl.find structure.restrict event_id with Not_found -> []
          in
          let v = { Vertex.id = event_id; event = evt; constraints } in
            G.add_vertex g v;
            Hashtbl.add vertex_map event_id v
        )
        structure.e;

      (* Apply transitive reduction to po *)
      let po_reduced = URelation.transitive_reduction structure.po in

      (* Add program order edges *)
      USet.iter
        (fun (src, dst) ->
          let v_src = Hashtbl.find vertex_map src in
          let v_dst = Hashtbl.find vertex_map dst in
            G.add_edge_e g (G.E.create v_src PO v_dst)
        )
        po_reduced;

      (* Add RMW edges *)
      USet.iter
        (fun (src, dst) ->
          let v_src = Hashtbl.find vertex_map src in
          let v_dst = Hashtbl.find vertex_map dst in
            G.add_edge_e g (G.E.create v_src RMW v_dst)
        )
        structure.rmw;

      (* Add lock order edges *)
      USet.iter
        (fun (src, dst) ->
          let v_src = Hashtbl.find vertex_map src in
          let v_dst = Hashtbl.find vertex_map dst in
            G.add_edge_e g (G.E.create v_src LO v_dst)
        )
        structure.lo;

      (* Add fork-join edges *)
      USet.iter
        (fun (src, dst) ->
          let v_src = Hashtbl.find vertex_map src in
          let v_dst = Hashtbl.find vertex_map dst in
            G.add_edge_e g (G.E.create v_src FJ v_dst)
        )
        structure.fj;

      (* Add relaxed dependency edges from executions *)
      let relaxed_deps = generate_relaxed_deps structure executions in
        USet.iter
          (fun (src, dst, label) ->
            let v_src = Hashtbl.find vertex_map src in
            let v_dst = Hashtbl.find vertex_map dst in
              G.add_edge_e g (G.E.create v_src label v_dst)
          )
          relaxed_deps;

        g

  (** DOT output using OCamlGraph's Graphviz module *)
  module DotOutput = struct
    type t = G.t

    let iter_vertex = G.iter_vertex
    let iter_edges_e = G.iter_edges_e

    module V = Vertex

    module E = struct
      type t = G.E.t

      let compare = G.E.compare
      let src = G.E.src
      let dst = G.E.dst
    end

    let vertex_name v = Printf.sprintf "e%d" v.V.id
    let graph_attributes _ : Graphviz.DotAttributes.graph list = []

    let default_vertex_attributes _ : Graphviz.DotAttributes.vertex list =
      [ `Shape `Box; `Style `Rounded ]

    let vertex_attributes v =
      let evt = v.V.event in

      (* Build label *)
      let label_lines =
        [ Printf.sprintf "e%d: %s" v.V.id (event_type_to_string evt.typ) ]
      in

      let label_lines =
        match evt.loc with
        | Some loc -> label_lines @ [ Expr.to_string loc ]
        | None -> label_lines
      in

      let label_lines =
        match evt.rval with
        | Some rval -> label_lines @ [ Value.to_string rval ]
        | None -> label_lines
      in

      let label_lines =
        match evt.wval with
        | Some wval -> label_lines @ [ Expr.to_string wval ]
        | None -> label_lines
      in

      let label_lines =
        label_lines
        @ [
            Printf.sprintf "φ: %s"
              (String.concat " AND " (List.map Expr.to_string v.V.constraints));
          ]
      in

      let label = String.concat " " label_lines in

      (* Special styling for root node *)
      if v.V.id = 0 then
        [ `Label label; `Shape `Doublecircle; `Color 0x0000FF; `Penwidth 2.0 ]
      else [ `Label label ]

    let default_edge_attributes _ : Graphviz.DotAttributes.edge list = []

    let edge_attributes e =
      let label_txt, color, style, penwidth =
        match G.E.label e with
        | PO -> ("po", 0x000000, `Solid, 1.0)
        | RMW -> ("rmw", 0xFF0000, `Solid, 2.0)
        | LO -> ("lo", 0x0000FF, `Dashed, 1.0)
        | FJ -> ("fj", 0x00FF00, `Dotted, 1.0)
        | DP preds -> ("dp: " ^ preds, 0xFFA500, `Bold, 1.5)
        | PPO preds -> ("ppo: " ^ preds, 0x800080, `Bold, 1.5)
        | RF preds -> ("rf: " ^ preds, 0xA52A2A, `Bold, 1.5)
      in
        [ `Label label_txt; `Color color; `Style style; `Penwidth penwidth ]

    let get_subgraph _ = None
  end

  module DotExport = Graphviz.Dot (DotOutput)

  (** Export to DOT format *)
  let to_dot (g : G.t) : string =
    let buf = Buffer.create 1024 in
    let fmt = Format.formatter_of_buffer buf in
      DotExport.fprint_graph fmt g;
      Format.pp_print_flush fmt ();
      Buffer.contents buf

  (** Proper JSON string escaping *)
  let json_escape s =
    let buf = Buffer.create (String.length s * 2) in
      String.iter
        (fun c ->
          match c with
          | '"' -> Buffer.add_string buf "\\\""
          | '\\' -> Buffer.add_string buf "\\\\"
          | '\b' -> Buffer.add_string buf "\\b"
          | '\012' -> Buffer.add_string buf "\\f"
          | '\n' -> Buffer.add_string buf "\\n"
          | '\r' -> Buffer.add_string buf "\\r"
          | '\t' -> Buffer.add_string buf "\\t"
          | c when int_of_char c < 0x20 ->
              Buffer.add_string buf (Printf.sprintf "\\u%04x" (int_of_char c))
          | c -> Buffer.add_char buf c
        )
        s;
      Buffer.contents buf

  (** Export to JSON format *)
  let to_json (g : G.t) : string =
    let buf = Buffer.create 1024 in

    Buffer.add_string buf "{\n";
    Buffer.add_string buf "  \"nodes\": [\n";

    (* Collect and sort vertices *)
    let vertices = ref [] in
      G.iter_vertex (fun v -> vertices := v :: !vertices) g;
      let vertices =
        List.sort (fun v1 v2 -> compare v1.Vertex.id v2.Vertex.id) !vertices
      in

      List.iteri
        (fun i v ->
          let evt = v.Vertex.event in
          let is_last = i = List.length vertices - 1 in

          Buffer.add_string buf "    {\n";
          Buffer.add_string buf
            (Printf.sprintf "      \"id\": %d,\n" v.Vertex.id);
          Buffer.add_string buf
            (Printf.sprintf "      \"type\": \"%s\",\n"
               (event_type_to_string evt.typ)
            );
          Buffer.add_string buf
            (Printf.sprintf "      \"label\": %d,\n" evt.label);
          Buffer.add_string buf
            (Printf.sprintf "      \"isRoot\": %b" (v.Vertex.id = 0));

          (* Add location if present *)
          ( match evt.loc with
          | Some loc ->
              let loc_str = json_escape (Expr.to_string loc) in
                Buffer.add_string buf
                  (Printf.sprintf ",\n      \"location\": \"%s\"" loc_str)
          | None -> ()
          );

          (* Add constraints if present *)
          if v.Vertex.constraints <> [] then (
            Buffer.add_string buf ",\n      \"constraints\": [";
            List.iteri
              (fun j c ->
                let c_str = json_escape (Expr.to_string c) in
                  Buffer.add_string buf (Printf.sprintf "\"%s\"" c_str);
                  if j < List.length v.Vertex.constraints - 1 then
                    Buffer.add_string buf ", "
              )
              v.Vertex.constraints;
            Buffer.add_string buf "]"
          );

          Buffer.add_string buf
            (Printf.sprintf "\n    }%s\n" (if is_last then "" else ","))
        )
        vertices;

      Buffer.add_string buf "  ],\n";
      Buffer.add_string buf "  \"edges\": [\n";

      (* Collect edges *)
      let edges = ref [] in
        G.iter_edges_e
          (fun e ->
            let src = (G.E.src e).Vertex.id in
            let dst = (G.E.dst e).Vertex.id in
            let edge_type, color =
              match G.E.label e with
              | PO -> ("po", "black")
              | RMW -> ("rmw", "red")
              | LO -> ("lo", "blue")
              | FJ -> ("fj", "green")
              | DP preds -> ("dp - " ^ preds, "orange")
              | PPO preds -> ("ppo - " ^ preds, "purple")
              | RF preds -> ("rf - " ^ preds, "brown")
            in
            (* Escape edge type string which may contain predicates *)
            let edge_type_escaped = json_escape edge_type in
              edges := (src, dst, edge_type_escaped, color) :: !edges
          )
          g;
        let edges = List.rev !edges in

        List.iteri
          (fun i (src, dst, edge_type, color) ->
            let is_last = i = List.length edges - 1 in
              Buffer.add_string buf "    {\n";
              Buffer.add_string buf
                (Printf.sprintf "      \"source\": %d,\n" src);
              Buffer.add_string buf
                (Printf.sprintf "      \"target\": %d,\n" dst);
              Buffer.add_string buf
                (Printf.sprintf "      \"type\": \"%s\",\n" edge_type);
              Buffer.add_string buf
                (Printf.sprintf "      \"color\": \"%s\"\n" color);
              Buffer.add_string buf
                (Printf.sprintf "    }%s\n" (if is_last then "" else ","))
          )
          edges;

        Buffer.add_string buf "  ]\n";
        Buffer.add_string buf "}\n";
        Buffer.contents buf

  (** Write visualization to file *)
  let write_to_file (filename : string) (format : output_mode)
      (structure : symbolic_event_structure)
      (executions : symbolic_execution USet.t option) : string option =
    let g = build_graph structure executions in
      match format with
      | Dot ->
          if filename = "stdout" then (
            let dot_content = to_dot g in
              Printf.printf "%s\n" dot_content;
              flush stdout;
              Some dot_content
          )
          else
            let oc = open_out filename in
              DotExport.output_graph oc g;
              close_out oc;
              Some (to_dot g)
      | Json ->
          let content = to_json g in
            if filename = "stdout" then (
              Printf.printf "%s\n" content;
              flush stdout;
              Some content
            )
            else
              let oc = open_out filename in
                output_string oc content;
                close_out oc;
                Some content
      | _ ->
          Logs.err (fun m ->
              m "Unsupported output format for\n      visualization."
          );
          None
end

let step_visualize_event_structure (lwt_ctx : mordor_ctx Lwt.t) :
    mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in

  match ctx.structure with
  | Some structure ->
      let output =
        EventStructureViz.write_to_file ctx.output_file ctx.output_mode
          structure ctx.executions
      in
        ctx.output <- output;

        Logs.info (fun m ->
            m "Event structure visualization written to %s" ctx.output_file
        );

        Lwt.return ctx
  | _ ->
      Logs.err (fun m ->
          m "Event structure or events not available for visualization."
      );
      Lwt.return ctx
