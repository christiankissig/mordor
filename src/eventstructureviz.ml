(** Graph Visualization Module for Symbolic Event Structures using OCamlGraph *)

open Graph
open Expr
open Types

module EventStructureViz = struct
  (** Output format type *)
  type output_format = DOT | JSON

  (** Format event type as string *)
  let event_type_to_string = function
    | Read -> "R"
    | Write -> "W"
    | RMW -> "RMW"
    | Fence -> "F"
    | Lock -> "Lock"
    | Unlock -> "Unlock"
    | _ -> "Event"

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

  (** Edge type *)
  module Edge = struct
    type t = edge_label

    let compare = compare
    let default = PO
  end

  (** Create the graph type *)
  module G = Imperative.Digraph.ConcreteLabeled (Vertex) (Edge)

  (** Build graph from event structure *)
  let build_graph (ses : symbolic_event_structure)
      (events : (int, event) Hashtbl.t) : G.t =
    let g = G.create () in

    (* Create vertices *)
    let vertex_map = Hashtbl.create 100 in
      Uset.iter
        (fun event_id ->
          let evt = Hashtbl.find events event_id in
          let constraints =
            try Hashtbl.find ses.restrict event_id with Not_found -> []
          in
          let v = { Vertex.id = event_id; event = evt; constraints } in
            G.add_vertex g v;
            Hashtbl.add vertex_map event_id v
        )
        ses.e;

      (* Add program order edges *)
      Uset.iter
        (fun (src, dst) ->
          let v_src = Hashtbl.find vertex_map src in
          let v_dst = Hashtbl.find vertex_map dst in
            G.add_edge_e g (G.E.create v_src PO v_dst)
        )
        ses.po;

      (* Add RMW edges *)
      Uset.iter
        (fun (src, dst) ->
          let v_src = Hashtbl.find vertex_map src in
          let v_dst = Hashtbl.find vertex_map dst in
            G.add_edge_e g (G.E.create v_src RMW v_dst)
        )
        ses.rmw;

      (* Add lock order edges *)
      Uset.iter
        (fun (src, dst) ->
          let v_src = Hashtbl.find vertex_map src in
          let v_dst = Hashtbl.find vertex_map dst in
            G.add_edge_e g (G.E.create v_src LO v_dst)
        )
        ses.lo;

      (* Add fork-join edges *)
      Uset.iter
        (fun (src, dst) ->
          let v_src = Hashtbl.find vertex_map src in
          let v_dst = Hashtbl.find vertex_map dst in
            G.add_edge_e g (G.E.create v_src FJ v_dst)
        )
        ses.fj;

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
        [ Printf.sprintf "E%d: %s" v.V.id (event_type_to_string evt.typ) ]
      in

      let label_lines =
        match evt.loc with
        | Some loc ->
            label_lines @ [ Printf.sprintf "loc: %s" (Expr.to_string loc) ]
        | None -> label_lines
      in

      let label_lines =
        match evt.rval with
        | Some rval ->
            label_lines @ [ Printf.sprintf "rval: %s" (Value.to_string rval) ]
        | None -> label_lines
      in

      let label_lines =
        match evt.wval with
        | Some wval ->
            label_lines @ [ Printf.sprintf "wval: %s" (Expr.to_string wval) ]
        | None -> label_lines
      in

      let label_lines =
        label_lines
        @ List.map
            (fun c -> Printf.sprintf "φ: %s" (Expr.to_string c))
            v.V.constraints
      in

      let label = String.concat "\\n" label_lines in

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
              let loc_str = String.escaped (Expr.to_string loc) in
                Buffer.add_string buf
                  (Printf.sprintf ",\n      \"location\": \"%s\"" loc_str)
          | None -> ()
          );

          (* Add constraints if present *)
          if v.Vertex.constraints <> [] then (
            Buffer.add_string buf ",\n      \"constraints\": [";
            List.iteri
              (fun j c ->
                let c_str = String.escaped (Expr.to_string c) in
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
            in
              edges := (src, dst, edge_type, color) :: !edges
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

  (** Main visualization function *)
  let visualize (format : output_format) (ses : symbolic_event_structure)
      (events : (int, event) Hashtbl.t) : string =
    let g = build_graph ses events in
      match format with
      | DOT -> to_dot g
      | JSON -> to_json g

  (** Write visualization to file *)
  let write_to_file (filename : string) (format : output_format)
      (ses : symbolic_event_structure) (events : (int, event) Hashtbl.t) : unit
      =
    let g = build_graph ses events in
      match format with
      | DOT ->
          let oc = open_out filename in
            DotExport.output_graph oc g;
            close_out oc
      | JSON ->
          let content = to_json g in
          let oc = open_out filename in
            output_string oc content;
            close_out oc

  (** Export graph for further processing *)
  let get_graph (ses : symbolic_event_structure)
      (events : (int, event) Hashtbl.t) : G.t =
    build_graph ses events
end
