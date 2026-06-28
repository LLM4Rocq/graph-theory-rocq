(** * Cycle.foundations.connectivity — shared multigraph connectivity vocabulary

    The GENERAL (carrier-agnostic) multigraph CONNECTIVITY layer of cycle theory,
    factored out of the conjecture files U6 / U10 / D1 (which all rebuilt the same
    primitives independently).  Everything here is plain [mgraph] vocabulary built
    on top of base's edge/walk API ([edges_at], [incident], [source]/[target],
    [eseparates], [uwalk]); no flow-, cycle-cover-, face- or D1-specific notions
    live here (those stay in their conjecture files).

    Contents (dependency-ordered):
      - degrees:        [mdeg], [subdeg], [subgraph_kregular];
      - connectivity:   [walk_in], [mconnected], [connected_del_edges],
                        [connected_del_verts], [two_connected], [edge_connected],
                        [H_inc], [subgraph_connected];
      - circuits:       [is_circuit];
      - cuts / bridges: [cut], [is_bridge], [bridgeless];
      - 2-edge-conn.:   [two_edge_connected].

    IMPORT ORDER: [mgraph] is imported BEFORE [base], because coq-graph-theory's
    [mgraph] ships a DIRECTED [line_graph] that would otherwise shadow base's
    undirected one (base re-exports the line/total-graph vocabulary).  [base]
    provides the [mgraph] notation ([graph unit unit]), [uwalk], [edges_at],
    [incident], [source]/[target], [eseparates]. *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Degrees and subgraph degrees *)

(** Multigraph degree of [v]: number of incident edges. *)
Definition mdeg (G : mgraph) (v : G) : nat := #|edges_at v|.

(** Degree of [v] inside the subgraph given by edge set [H]. *)
Definition subdeg (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|edges_at v :&: H|.

(** [k]-regular subgraph: every vertex has [H]-degree [0] or [k]
    (so its support is a disjoint union of [k]-regular pieces). *)
Definition subgraph_kregular (G : mgraph) (H : {set edge G}) (k : nat) : Prop :=
  forall v : G, subdeg H v = 0 \/ subdeg H v = k.

(** ** Connectivity at the multigraph level (via [uwalk]) *)

(** Walk restricted to edges of [H]. *)
Definition walk_in (G : mgraph) (H : {set edge G}) (x y : G) (w : seq (edge G)) : bool :=
  uwalk x y w && all (fun e => e \in H) w.

(** Whole-graph (vertex) connectivity. *)
Definition mconnected (G : mgraph) : Prop :=
  forall x y : G, exists w, uwalk x y w.

(** Connectivity using only edges OUTSIDE the edge set [S] (i.e. of [G - E(S)]). *)
Definition connected_del_edges (G : mgraph) (S : {set edge G}) : Prop :=
  forall x y : G, exists w, uwalk x y w /\ all (fun e => e \notin S) w.

(** Connectivity after deleting the vertex set [Z] (walks avoiding [Z]). *)
Definition connected_del_verts (G : mgraph) (Z : {set G}) : Prop :=
  forall x y : G, x \notin Z -> y \notin Z ->
    exists w, uwalk x y w /\ all (fun e => (source e \notin Z) && (target e \notin Z)) w.

(** 2-(vertex-)connected: at least 3 vertices, and connected after deleting any one. *)
Definition two_connected (G : mgraph) : Prop :=
  (3 <= #|G|)%N /\ forall z : G, connected_del_verts [set z].

(** [k]-edge-connected: deleting fewer than [k] edges keeps the graph connected. *)
Definition edge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, (#|E| < k)%N -> connected_del_edges E.

(** A subgraph [H] is incident at [x]: some [H]-edge meets [x]. *)
Definition H_inc (G : mgraph) (H : {set edge G}) (x : G) : bool :=
  [exists e, (e \in H) && incident x e].

(** A subgraph [H] is connected: any two [H]-incident vertices are joined by an
    [H]-walk. *)
Definition subgraph_connected (G : mgraph) (H : {set edge G}) : Prop :=
  forall x y : G, H_inc H x -> H_inc H y -> exists w, walk_in H x y w.

(** ** Circuits *)

(** A circuit (single cycle): a nonempty, connected, 2-regular edge set. *)
Definition is_circuit (G : mgraph) (C : {set edge G}) : Prop :=
  [/\ C != set0, subgraph_kregular C 2 & subgraph_connected C].

(** ** Edge cuts and bridges *)

(** The edge cut of a vertex set [S]: edges with exactly one endpoint in [S]. *)
Definition cut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** [e] is a bridge: every walk between its endpoints uses [e]. *)
Definition is_bridge (G : mgraph) (e : edge G) : Prop :=
  eseparates (source e) (target e) [set e].

Definition bridgeless (G : mgraph) : Prop :=
  forall e : edge G, ~ is_bridge e.

(** ** Two-edge-connectivity *)

(** 2-edge-connected = connected and bridgeless. *)
Definition two_edge_connected (G : mgraph) : Prop :=
  mconnected G /\ bridgeless G.
