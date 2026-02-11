(** {1 Graph Visualization Module for Symbolic Event Structures}

    This module provides visualization capabilities for symbolic event
    structures using the OCamlGraph library. It supports multiple output formats
    (DOT, JSON) and integrates with web servers for real-time graph streaming.

    @author Event Structure Visualization Team
    @version 1.0 *)

open Assertion
open Context
open Graph
open Expr
open Types
open Uset
open Lwt.Syntax

let ( <|> ) opt1 opt2 =
  match opt1 with
  | Some _ -> opt1
  | None -> opt2

(** {1 Type Definitions} *)

module EventStructureViz = struct
  (** {2 Graph Component Types} *)

  (** {3 Vertex Module}

      Represents a node in the event structure graph. Each vertex encapsulates
      an event along with its constraints and optional source code location. *)
  module Vertex = struct
    (** Type representing a vertex in the event structure graph.*)

    type t = {
      id : int;  (** id Unique identifier for the event *)
      event : event;
          (** event The event data structure containing operation details *)
      constraints : expr list;
          (** constraints List of symbolic constraints restricting this event *)
      source_span : source_span option; [@default None]
          (** source_span Optional source code location for debugging *)
    }

    (** [compare v1 v2] compares two vertices by their ID.
        @return Negative if [v1 < v2], zero if equal, positive if [v1 > v2] *)
    let compare v1 v2 = compare v1.id v2.id

    (** [hash v] computes a hash value for vertex [v].
        @return Hash value based on vertex ID *)
    let hash v = Hashtbl.hash v.id

    (** [equal v1 v2] checks if two vertices have the same ID.
        @return [true] if vertices are equal, [false] otherwise *)
    let equal v1 v2 = v1.id = v2.id
  end

  (** {3 Edge Label Types}

      Defines the different kinds of relationships between events in the graph.
  *)

  (** Edge label type representing different kinds of relationships between
      events.

      - [PO]: Program Order - sequential ordering within a thread
      - [RMW]: Read-Modify-Write - atomic operation coupling
      - [LO]: Lock Order - synchronization ordering
      - [FJ]: Fork-Join - thread creation/joining relationships
      - [DP preds]: Data Dependency with predicates
      - [PPO preds]: Preserved Program Order with predicates
      - [RF preds]: Read-From relationship with predicates *)
  type edge_label =
    | PO
    | RMW
    | LO
    | FJ
    | DP of string
    | PPO of string
    | RF of string

  (** {3 Edge Module}

      Module defining edge properties for graph construction. *)
  module Edge = struct
    (** Edge type alias for edge labels *)
    type t = edge_label

    (** [compare e1 e2] compares two edges.
        @return Standard comparison result *)
    let compare = compare

    (** Default edge label (Program Order) *)
    let default = PO
  end

  (** {3 Graph Type}

      The main graph data structure built using OCamlGraph's imperative digraph.
  *)
  module G = Imperative.Digraph.ConcreteLabeled (Vertex) (Edge)

  (** {2 JSON Serialization Types}

      Types for converting graphs to JSON format for web transmission. *)

  (** JSON representation of a graph node.

      This structure contains all information needed to render a node in a
      web-based visualization, including the event data, source location, and
      constraint information.*)

  type json_node = {
    id : int;  (** id Unique event identifier *)
    type_ : string; [@key "type"]
        (** type_ Event type (e.g., "Read", "Write", "Fence") *)
    label : int;  (** label Event label number *)
    isRoot : bool;  (** isRoot Whether this is the root/initial event *)
    location : string option; [@default None]
        (** location Optional memory location string *)
    value : string option; [@default None]
        (** value Optional read/write value *)
    constraints : string list; [@default []]
        (** constraints List of constraint strings *)
    source_start_line : int option; [@default None]
        (** source_start_line Optional starting line in source code *)
    source_start_col : int option; [@default None]
        (** source_start_col Optional starting column in source code *)
    source_end_line : int option; [@default None]
        (** source_end_line Optional ending line in source code *)
    source_end_col : int option; [@default None]
        (** source_end_col Optional ending column in source code *)
  }
  [@@deriving yojson]

  (** JSON representation of a graph edge. *)

  type json_edge = {
    source : int;  (** source Source vertex ID *)
    target : int;  (** target Target vertex ID *)
    type_ : string; [@key "type"]
        (** type_ Edge type string (e.g., "po", "rf", "dp") *)
  }
  [@@deriving yojson]

  (** JSON representation of a complete graph. *)
  type json_graph = {
    nodes : json_node list;  (** nodes List of all nodes in the graph *)
    edges : json_edge list;  (** edges List of all edges in the graph *)
  }
  [@@deriving yojson]

  (** Message wrapper for streaming graph data via web server. *)

  type graph_message = {
    type_ : string; [@key "type"]  (** type_ Message type identifier *)
    graph : json_graph;  (** graph The graph data *)
    index : int option; [@default None]
        (** index Optional execution index number *)
    preds : string option; [@default None]
        (** preds Optional predicate string *)
    is_valid : bool option; [@default None]
        (** is_valid Optional validity status *)
    undefined_behaviour : Yojson.Safe.t option; [@default None]
        (** undefined_behaviour Optional undefined behaviour information *)
  }
  [@@deriving yojson]

  (** {1 Graph Construction Functions} *)

  (** {2 Graph Construction Helpers}

      Low-level functions for creating and populating graph structures. *)

  (** [create_vertex event_id structure source_spans] creates a vertex from an
      event ID and structure information.

      @param event_id The unique identifier of the event
      @param structure The symbolic event structure containing event data
      @param source_spans Hash table mapping event IDs to source locations
      @return A fully populated vertex record
      @raise Not_found if event_id is not in the structure *)
  let create_vertex (event_id : int) (structure : symbolic_event_structure)
      (source_spans : (int, source_span) Hashtbl.t) : Vertex.t =
    let evt = Hashtbl.find structure.events event_id in
    let constraints =
      try Hashtbl.find structure.restrict event_id with Not_found -> []
    in
    let source_span = Hashtbl.find_opt source_spans event_id in
      { Vertex.id = event_id; event = evt; constraints; source_span }

  (** [add_vertices_to_graph g event_ids structure source_spans] adds all
      specified events as vertices to the graph.

      @param g The graph to add vertices to (modified in place)
      @param event_ids Set of event IDs to add as vertices
      @param structure The symbolic event structure
      @param source_spans Hash table of source code locations
      @return Hash table mapping event IDs to their vertex objects *)
  let add_vertices_to_graph (g : G.t) (event_ids : int USet.t)
      (structure : symbolic_event_structure)
      (source_spans : (int, source_span) Hashtbl.t) : (int, Vertex.t) Hashtbl.t
      =
    let vertex_map = Hashtbl.create 100 in
      USet.iter
        (fun event_id ->
          let v = create_vertex event_id structure source_spans in
            G.add_vertex g v;
            Hashtbl.add vertex_map event_id v
        )
        event_ids;
      vertex_map

  (** [add_edges_from_relation g vertex_map relation edge_label] adds edges to
      the graph from a binary relation.

      This is a generic function for adding any type of edge. It looks up source
      and target vertices in the vertex map and creates edges with the specified
      label.

      @param g The graph to add edges to (modified in place)
      @param vertex_map Hash table mapping event IDs to vertices
      @param relation Set of (source, target) pairs
      @param edge_label The label to apply to all edges
      @raise Not_found if a source or target ID is not in vertex_map *)
  let add_edges_from_relation (g : G.t) (vertex_map : (int, Vertex.t) Hashtbl.t)
      (relation : (int * int) USet.t) (edge_label : edge_label) : unit =
    USet.iter
      (fun (src, dst) ->
        let v_src = Hashtbl.find vertex_map src in
        let v_dst = Hashtbl.find vertex_map dst in
          G.add_edge_e g (G.E.create v_src edge_label v_dst)
      )
      relation

  (** {2 Relaxed Dependency Processing}

      Functions for computing and simplifying relaxed memory model dependencies
      (data dependencies, preserved program order, and read-from relations). *)

  (** [filter_predicates_for_event structure src preds] filters out predicates
      that are already enforced by the structure's restrictions.

      @param structure The symbolic event structure
      @param src The source event ID
      @param preds List of predicates to filter
      @return
        Filtered list containing only predicates not in structure restrictions
  *)
  let filter_predicates_for_event (structure : symbolic_event_structure)
      (src : int) (preds : expr list) : expr list =
    let src_preds =
      Hashtbl.find_opt structure.restrict src |> Option.value ~default:[]
    in
      List.filter (fun p -> not (List.mem p src_preds)) preds

  (** [format_predicate_string clause] converts a list of predicates to a
      human-readable string for edge labels.

      @param clause List of predicate expressions
      @return
        Empty string for trivially true predicates, otherwise predicates joined
        with " AND " *)
  let format_predicate_string (clause : expr list) : string =
    match clause with
    | [ EBoolean true ] | [] -> "" (* True predicate -> empty string *)
    | _ -> clause |> List.map Expr.to_string |> String.concat " AND "

  (** [generate_relaxed_deps structure executions] generates relaxed dependency
      edges from a set of executions with DNF simplification.

      This function collects dependency, preserved program order, and read-from
      edges from all executions, groups them by (source, target, type), performs
      DNF simplification on the associated predicates, and produces a minimal
      set of labeled edges.

      @param structure The symbolic event structure
      @param executions Optional set of symbolic executions
      @return Set of (source_id, target_id, edge_label) tuples *)
  let generate_relaxed_deps (structure : symbolic_event_structure)
      (executions : symbolic_execution USet.t option) :
      (int * int * Edge.t) USet.t =
    match executions with
    | None -> USet.create ()
    | Some execs ->
        (* Collect edges with predicates in a hash table *)
        let edge_preds_table = Hashtbl.create 100 in

        (* Process each execution *)
        USet.iter
          (fun exec ->
            let preds = exec.ex_p in
            let filter_preds src =
              filter_predicates_for_event structure src preds
            in

            (* Helper to process a relation type *)
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

            (* Process each relation type with transitive reduction *)
            process_relation `DP (URelation.transitive_reduction exec.dp);
            process_relation `PPO (URelation.transitive_reduction exec.ppo);
            process_relation `RF (URelation.transitive_reduction exec.rf);
            process_relation `RMW (URelation.transitive_reduction exec.rmw)
          )
          execs;

        (* Simplify predicates and create final edges *)
        let result_edges = ref (USet.create ()) in
          Hashtbl.iter
            (fun (src, dst, rel_type) dnf_clauses ->
              let simplified_dnf = Expr.simplify_dnf dnf_clauses in

              List.iter
                (fun clause ->
                  let preds_str = format_predicate_string clause in
                  let edge =
                    match rel_type with
                    | `DP -> (src, dst, DP preds_str)
                    | `PPO -> (src, dst, PPO preds_str)
                    | `RF -> (src, dst, RF preds_str)
                    | `RMW -> (src, dst, RMW)
                  in
                    result_edges := USet.add !result_edges edge
                )
                simplified_dnf
            )
            edge_preds_table;

          !result_edges

  (** {2 Main Graph Construction}

      High-level functions for building different types of graphs from event
      structures. *)

  (** [build_graph structure executions] builds a complete graph from an event
      structure including all edge types.

      This function is primarily used by the CLI. It creates a graph containing
      all events and edges including:
      - Program order (PO) edges with transitive reduction
      - Read-modify-write (RMW) edges
      - Lock order (LO) edges
      - Fork-join (FJ) edges
      - Relaxed dependency edges (DP, PPO, RF) computed from executions

      @param structure The symbolic event structure
      @param executions
        Optional set of symbolic executions for computing relaxed dependencies
      @return A complete graph with all vertices and edges *)
  let build_graph (structure : symbolic_event_structure)
      (executions : symbolic_execution USet.t option) : G.t =
    let g = G.create () in
    let source_spans = Hashtbl.create 0 in
    (* No source spans for CLI *)

    (* Add vertices *)
    let vertex_map =
      add_vertices_to_graph g structure.e structure source_spans
    in

    (* Add program order edges (with transitive reduction) *)
    let po_reduced = URelation.transitive_reduction structure.po in
      add_edges_from_relation g vertex_map po_reduced PO;

      (* Add other structural edges *)
      add_edges_from_relation g vertex_map structure.lo LO;
      add_edges_from_relation g vertex_map structure.fj FJ;

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

  (** [build_event_structure_graph structure source_spans] builds an event
      structure graph with only program order edges.

      This simplified graph is used by the web server to show the basic event
      structure before dependency analysis. It includes all events but only PO
      edges.

      @param structure The symbolic event structure
      @param source_spans Hash table mapping event IDs to source locations
      @return A graph with only PO edges *)
  let build_event_structure_graph (structure : symbolic_event_structure)
      (source_spans : (int, source_span) Hashtbl.t) : G.t =
    let g = G.create () in

    (* Add vertices *)
    let vertex_map =
      add_vertices_to_graph g structure.e structure source_spans
    in

    (* Add only program order edges (with transitive reduction) *)
    let po_reduced = URelation.transitive_reduction structure.po in
      add_edges_from_relation g vertex_map po_reduced PO;

      g

  (** [build_execution_graph structure exec source_spans po_relation] builds a
      graph for a single symbolic execution.

      This function creates a graph containing only the events that participate
      in the given execution, along with their PO edges and the execution's
      dependency edges (DP, PPO, RF). This is used for visualizing individual
      executions in the web interface.

      @param structure The symbolic event structure
      @param exec The symbolic execution to visualize
      @param source_spans Hash table of source code locations
      @param po_relation Pre-computed program order relation (already reduced)
      @return A graph containing only events in this execution *)
  let build_execution_graph (structure : symbolic_event_structure)
      (exec : symbolic_execution) (source_spans : (int, source_span) Hashtbl.t)
      (po_relation : (int * int) USet.t) : G.t =
    let g = G.create () in

    (* Collect event IDs that are in this execution *)
    let exec_events = Hashtbl.create 100 in

    let mark_events_in_relation relation =
      USet.iter
        (fun (src, dst) ->
          Hashtbl.replace exec_events src ();
          Hashtbl.replace exec_events dst ()
        )
        relation
    in

    mark_events_in_relation exec.dp;
    mark_events_in_relation exec.ppo;
    mark_events_in_relation exec.rf;

    (* Create vertices only for events in this execution *)
    let vertex_map = Hashtbl.create 100 in
      Hashtbl.iter
        (fun event_id () ->
          let v = create_vertex event_id structure source_spans in
            G.add_vertex g v;
            Hashtbl.add vertex_map event_id v
        )
        exec_events;

      (* Add PO edges (only for events in execution) *)
      USet.iter
        (fun (src, dst) ->
          if Hashtbl.mem exec_events src && Hashtbl.mem exec_events dst then
            let v_src = Hashtbl.find vertex_map src in
            let v_dst = Hashtbl.find vertex_map dst in
              G.add_edge_e g (G.E.create v_src PO v_dst)
        )
        po_relation;

      (* Add relaxed dependency edges *)
      let add_dep_edges relation label_fn =
        USet.iter
          (fun (src, dst) ->
            if Hashtbl.mem exec_events src && Hashtbl.mem exec_events dst then
              let v_src = Hashtbl.find vertex_map src in
              let v_dst = Hashtbl.find vertex_map dst in
              let preds_str = format_predicate_string exec.ex_p in
                G.add_edge_e g (G.E.create v_src (label_fn preds_str) v_dst)
          )
          (URelation.transitive_reduction relation)
      in

      add_dep_edges exec.dp (fun p -> DP p);
      add_dep_edges exec.ppo (fun p -> PPO p);
      add_dep_edges exec.rf (fun p -> RF p);
      add_dep_edges exec.rmw (fun _ -> RMW);

      g

  (** {1 Export Functions (DOT and JSON)} *)

  (** {2 DOT Format Export}

      Functions for exporting graphs to Graphviz DOT format for visualization.
  *)

  (** Module implementing DOT output formatting for graphs.

      This module conforms to the OCamlGraph Graphviz interface and defines how
      vertices and edges should be rendered in DOT format. *)
  module DotOutput = struct
    type t = G.t

    module V = Vertex

    module E = struct
      type t = G.E.t

      let compare = G.E.compare
      let src = G.E.src
      let dst = G.E.dst
    end

    (** [iter_vertex f g] iterates function [f] over all vertices in graph [g]
    *)
    let iter_vertex = G.iter_vertex

    (** [iter_edges_e f g] iterates function [f] over all edges in graph [g] *)
    let iter_edges_e = G.iter_edges_e

    (** [vertex_name v] generates the DOT identifier for a vertex.
        @param v The vertex
        @return String in format "eN" where N is the event ID *)
    let vertex_name v = Printf.sprintf "e%d" v.V.id

    (** [graph_attributes g] returns global graph attributes.
        @param g The graph
        @return Empty list (no global attributes) *)
    let graph_attributes _ : Graphviz.DotAttributes.graph list = []

    (** [default_vertex_attributes g] returns default styling for all vertices.
        @param g The graph
        @return List of default vertex attributes *)
    let default_vertex_attributes _ : Graphviz.DotAttributes.vertex list =
      [ `Shape `Box; `Style `Rounded ]

    (** [build_vertex_label v] constructs a multi-line label for a vertex.

        The label includes:
        - Event ID and type
        - Location (if present)
        - Read value (if present)
        - Write value (if present)
        - Condition (if present)
        - Constraints

        @param v The vertex to label
        @return Formatted label string *)
    let build_vertex_label (v : Vertex.t) : string =
      let evt = v.V.event in
      let lines =
        ref [ Printf.sprintf "e%d: %s" v.V.id (show_event_type evt.typ) ]
      in

      (* Add location if present *)
      ( match evt.loc with
      | Some loc -> lines := !lines @ [ Expr.to_string loc ]
      | None -> ()
      );

      (* Add read value if present *)
      ( match evt.rval with
      | Some rval -> lines := !lines @ [ Value.to_string rval ]
      | None -> ()
      );

      (* Add write value if present *)
      ( match evt.wval with
      | Some wval -> lines := !lines @ [ Expr.to_string wval ]
      | None -> ()
      );

      (* Add condition if present *)
      ( match evt.cond with
      | Some cond ->
          lines := !lines @ [ Printf.sprintf "cond: %s" (Expr.to_string cond) ]
      | None -> ()
      );

      (* Add constraints *)
      lines :=
        !lines
        @ [
            Printf.sprintf "φ: %s"
              (String.concat " AND " (List.map Expr.to_string v.V.constraints));
          ];

      String.concat " " !lines

    (** [vertex_attributes v] returns DOT attributes for a specific vertex.

        Root nodes (ID = 0) receive special styling with double circles and blue
        coloring.

        @param v The vertex
        @return List of DOT attributes *)
    let vertex_attributes v =
      let label = build_vertex_label v in
        (* Special styling for root node *)
        if v.V.id = 0 then
          [ `Label label; `Shape `Doublecircle; `Color 0x0000FF; `Penwidth 2.0 ]
        else [ `Label label ]

    (** [default_edge_attributes g] returns default edge attributes.
        @param g The graph
        @return Empty list *)
    let default_edge_attributes _ : Graphviz.DotAttributes.edge list = []

    (** [edge_attributes e] returns DOT attributes for a specific edge based on
        its type.

        Different edge types receive distinct colors and styles:
        - PO: Black, solid
        - RMW: Red, solid, thick
        - LO: Blue, dashed
        - FJ: Green, dotted
        - DP: Orange, bold
        - PPO: Purple, bold
        - RF: Brown, bold

        @param e The edge
        @return List of DOT attributes including label, color, style, and width
    *)
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

    (** [get_subgraph v] determines subgraph membership for a vertex.
        @param v The vertex
        @return None (no subgraphs used) *)
    let get_subgraph _ = None
  end

  (** DOT export module instantiated with our output configuration *)
  module DotExport = Graphviz.Dot (DotOutput)

  (** [to_dot g] exports a graph to DOT format string.

      @param g The graph to export
      @return DOT format representation as a string *)
  let to_dot (g : G.t) : string =
    let buf = Buffer.create 1024 in
    let fmt = Format.formatter_of_buffer buf in
      DotExport.fprint_graph fmt g;
      Format.pp_print_flush fmt ();
      Buffer.contents buf

  (** {2 JSON Format Export}

      Functions for converting graphs to JSON format for web-based
      visualization. *)

  (** [vertex_to_json_node v] converts a vertex to its JSON representation.

      This function extracts all relevant information from the vertex and event
      structure, converting expression and value types to their string
      representations. The [label] field is taken directly from [evt.label]
      without transformation.

      @param v The vertex to convert
      @return A {!json_node} record ready for serialization *)
  let vertex_to_json_node (v : Vertex.t) : json_node =
    let evt = v.Vertex.event in

    let location =
      match evt.loc with
      | Some loc -> Some (Expr.to_string loc)
      | None -> None
    in

    let value =
      Option.map Value.to_string evt.rval
      <|> Option.map Expr.to_string evt.wval
      <|> Option.map Expr.to_string evt.cond
    in

    let constraints =
      if v.Vertex.constraints <> [] then
        List.map Expr.to_string v.Vertex.constraints
      else []
    in

    let source_start_line, source_start_col, source_end_line, source_end_col =
      match v.Vertex.source_span with
      | Some span ->
          ( Some span.start_line,
            Some span.start_col,
            Some span.end_line,
            Some span.end_col
          )
      | None -> (None, None, None, None)
    in

    {
      id = v.Vertex.id;
      type_ = show_event_type evt.typ;
      label = evt.label;
      (* Direct assignment from event.label *)
      isRoot = v.Vertex.id = 0;
      location;
      value;
      constraints;
      source_start_line;
      source_start_col;
      source_end_line;
      source_end_col;
    }

  (** [edge_label_to_string label] converts an edge label to its JSON string
      representation.

      For dependency edges (DP, PPO, RF), if predicates are present they are
      appended after a hyphen separator.

      @param label The edge label to convert
      @return String representation (e.g., "po", "dp - x > 0") *)
  let edge_label_to_string (label : edge_label) : string =
    match label with
    | PO -> "po"
    | RMW -> "rmw"
    | LO -> "lo"
    | FJ -> "fj"
    | DP preds -> if preds = "" then "dp" else "dp - " ^ preds
    | PPO preds -> if preds = "" then "ppo" else "ppo - " ^ preds
    | RF preds -> if preds = "" then "rf" else "rf - " ^ preds

  (** [sort_edges_po_first edges] sorts edges to place program order edges
      first.

      This ensures PO edges appear first in the JSON output for consistent
      visualization rendering.

      @param edges List of edges as (src, dst, type_str, label) tuples
      @return Sorted edge list with PO edges first *)
  let sort_edges_po_first (edges : (int * int * string * edge_label) list) :
      (int * int * string * edge_label) list =
    List.sort
      (fun (_, _, _, label1) (_, _, _, label2) ->
        match (label1, label2) with
        | PO, PO -> 0
        | PO, _ -> -1
        | _, PO -> 1
        | _ -> 0
      )
      edges

  (** [to_json g] converts a graph to JSON string representation.

      This function processes the entire graph, converting all vertices to JSON
      nodes and all edges to JSON edge records. Vertices are sorted by ID and
      edges are sorted with PO edges first. The resulting JSON conforms to the
      {!json_graph} schema.

      @param g The graph to convert
      @return JSON string representation of the graph *)
  let to_json (g : G.t) : string =
    (* Collect and sort vertices by ID *)
    let vertices = ref [] in
      G.iter_vertex (fun v -> vertices := v :: !vertices) g;
      let vertices =
        List.sort (fun v1 v2 -> compare v1.Vertex.id v2.Vertex.id) !vertices
      in

      (* Convert vertices to JSON nodes *)
      let nodes = List.map vertex_to_json_node vertices in

      (* Collect edges *)
      let edges = ref [] in
        G.iter_edges_e
          (fun e ->
            let src = (G.E.src e).Vertex.id in
            let dst = (G.E.dst e).Vertex.id in
            let label = G.E.label e in
            let edge_type = edge_label_to_string label in
              edges := (src, dst, edge_type, label) :: !edges
          )
          g;

        (* Sort edges (PO first) *)
        let edges = sort_edges_po_first !edges in

        (* Convert to JSON edge format *)
        let json_edges =
          List.map
            (fun (src, dst, edge_type, _) ->
              { source = src; target = dst; type_ = edge_type }
            )
            edges
        in

        let graph = { nodes; edges = json_edges } in
          Yojson.Safe.to_string (json_graph_to_yojson graph)

  (** {1 File Output}

      Functions for writing graphs to files or stdout. *)

  (** [write_to_file filename format structure executions] writes a
      visualization to a file or stdout.

      This function builds the complete graph and exports it in the specified
      format. If filename is "stdout", output goes to standard output instead of
      a file.

      @param filename Output filename or "stdout"
      @param format Output format ({!Dot} or {!Json})
      @param structure The symbolic event structure to visualize
      @param executions Optional set of executions for computing dependencies
      @return [Some content] with the generated output, or [None] on error *)
  let write_to_file (filename : string) (format : output_mode)
      (structure : symbolic_event_structure)
      (executions : symbolic_execution USet.t option) : string option =
    let g = build_graph structure executions in

    match format with
    | Dot ->
        let dot_content = to_dot g in
          if filename = "stdout" then (
            Printf.printf "%s\n" dot_content;
            flush stdout;
            Some dot_content
          )
          else
            let oc = open_out filename in
              DotExport.output_graph oc g;
              close_out oc;
              Some dot_content
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
        Logs.err (fun m -> m "Unsupported output format for visualization.");
        None
end

(** {1 Lwt Step Functions}

    Pipeline step functions for integrating visualization with the web server
    using Lwt for asynchronous I/O. *)

(** [step_visualize_event_structure lwt_ctx] generates and writes an event
    structure visualization to a file.

    This step function is used in the CLI pipeline. It creates the graph
    visualization and writes it to the output file specified in the context.

    @param lwt_ctx Lwt-wrapped Mordor context containing structure and settings
    @return Updated context with output field set to the generated content *)
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
  | None ->
      Logs.err (fun m ->
          m "Event structure or events not available for visualization."
      );
      Lwt.return ctx

(** [step_send_event_structure_graph ~send_data lwt_ctx] sends the event
    structure graph (with PO edges only) via the web server.

    This step function is called after interpretation to send the initial graph
    structure to the web client. It includes all events but only program order
    edges.

    @param send_data Function to send JSON data to the client
    @param lwt_ctx Lwt-wrapped Mordor context
    @return Updated context (unchanged) *)
let step_send_event_structure_graph ~(send_data : string -> unit Lwt.t)
    (lwt_ctx : mordor_ctx Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in

  let source_spans =
    Option.value ctx.source_spans ~default:(Hashtbl.create 0)
  in

  match ctx.structure with
  | Some structure ->
      (* Build and send the event structure graph *)
      let es_graph =
        EventStructureViz.build_event_structure_graph structure source_spans
      in
      let es_json = EventStructureViz.to_json es_graph in

      (* Wrap in graph message *)
      let message =
        EventStructureViz.
          {
            type_ = "event_structure";
            graph =
              Yojson.Safe.from_string es_json
              |> json_graph_of_yojson
              |> Result.get_ok;
            index = None;
            preds = None;
            is_valid = None;
            undefined_behaviour = None;
          }
      in
      let es_message =
        Yojson.Safe.to_string (EventStructureViz.graph_message_to_yojson message)
      in
        let* () = send_data es_message in
          Logs.info (fun m -> m "Event structure graph sent after interpret");
          Lwt.return ctx
  | None ->
      Logs.err (fun m ->
          m "Event structure not available for visualization after interpret."
      );
      Lwt.return ctx

(** [send_single_execution_graph ~send_data ~build_exec_graph checked_executions
     i exec] sends a single execution graph as a JSON message.

    @param send_data Function to send JSON data to the client
    @param build_exec_graph Function to build a graph for the given execution
    @param checked_executions Hash table of checked execution info for validity
    @param i Index of the execution (0-based)
    @param exec The symbolic execution to visualize *)
let send_single_execution_graph ~send_data ~build_exec_graph checked_executions
    i exec =
  let exec_graph = build_exec_graph exec in
  let graph_json = EventStructureViz.to_json exec_graph in
  let graph_obj =
    Yojson.Safe.from_string graph_json
    |> EventStructureViz.json_graph_of_yojson
    |> Result.get_ok
  in

  let exec_info_opt : execution_info option =
    Hashtbl.find_opt checked_executions exec.id
  in
  let exec_preds_string =
    String.concat ", " (List.map Expr.to_string exec.ex_p)
  in
  let is_valid : bool option =
    match exec_info_opt with
    | Some info -> Some info.satisfied
    | None -> None
  in
  let undefined_behaviour =
    Option.map (fun info -> ub_reasons_to_yojson info.ub_reasons) exec_info_opt
  in

  (* Create and send message *)
  let message =
    EventStructureViz.
      {
        type_ = "execution";
        graph = graph_obj;
        index = Some (i + 1);
        preds = Some exec_preds_string;
        is_valid;
        undefined_behaviour;
      }
  in
  let exec_message =
    Yojson.Safe.to_string (EventStructureViz.graph_message_to_yojson message)
  in
    send_data exec_message

(** [step_send_execution_graphs lwt_ctx ~send_data] sends individual execution
    graphs via the web server.

    This step function is called after dependency calculation to stream each
    execution's graph to the web client. Each execution is sent as a separate
    message, followed by a completion message with the total count.

    For each execution, the message includes:
    - The execution graph (events and edges)
    - The execution index (1-based)
    - The predicate string
    - Validity status (if available)
    - Undefined behaviour information (if available)

    @param lwt_ctx Lwt-wrapped Mordor context
    @param send_data Function to send JSON data to the client
    @return Updated context (unchanged) *)
let step_send_execution_graphs (lwt_ctx : mordor_ctx Lwt.t)
    ~(send_data : string -> unit Lwt.t) : mordor_ctx Lwt.t =
  let* ctx = lwt_ctx in

  let source_spans =
    Option.value ctx.source_spans ~default:(Hashtbl.create 0)
  in

  match ctx.structure with
  | Some structure ->
      (* Process executions *)
      let* () =
        (* Get PO relation for execution graphs *)
        let po_reduced = URelation.transitive_reduction structure.po in
        let build_exec_graph exec =
          EventStructureViz.build_execution_graph structure exec source_spans
            po_reduced
        in

        match ctx.executions with
        | Some execs ->
            let exec_list = USet.to_list execs in
            let exec_count = List.length exec_list in

            (* Build checked executions lookup table *)
            let checked_executions =
              Hashtbl.create
                (ctx.checked_executions
                |> Option.value ~default:[]
                |> List.length
                )
            in
              ( match ctx.checked_executions with
              | Some exec_infos ->
                  List.iter
                    (fun info ->
                      Hashtbl.add checked_executions info.exec_id info
                    )
                    exec_infos
              | None -> ()
              );

              (* Send each execution graph *)
              Lwt_list.iteri_s
                (send_single_execution_graph ~send_data ~build_exec_graph
                   checked_executions
                )
                exec_list
        | None ->
            (* No executions *)
            Lwt.return_unit
      in

      Logs.info (fun m -> m "Execution graphs sent after dependency calculation");
      Lwt.return ctx
  | None ->
      Logs.err (fun m ->
          m "Event structure not available for execution graph streaming."
      );
      Lwt.return ctx
