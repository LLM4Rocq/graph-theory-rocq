(** * Cycle.conjectures.U6 — milestone U6 (namespace Cycle, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of eleven open problems of cycle theory: cycle double covers,
    edge-decompositions, eulerian decompositions, cycle covers, oddness and
    faithful covers.

    CARRIER: every row is an undirected MULTIGRAPH statement, so the carrier is
    coq-graph-theory's [mgraph] = [graph unit unit].  Subgraphs / cycles /
    matchings / covers are all represented as EDGE SETS [{set edge G}] (or
    sequences of them, for multisets of cycles).  This is the faithful object
    level for cycle theory: a "cycle" is a connected 2-regular edge set
    (a circuit), a "cycle double cover" a list of circuits hitting each edge
    exactly twice, etc.

    IMPORT ORDER: [mgraph] is imported BEFORE [base], because coq-graph-theory's
    [mgraph] ships a DIRECTED [line_graph] that would otherwise shadow base's
    undirected one (base re-exports the line/total-graph vocabulary).  We need
    the raw multigraph edge API: [edge G], [source]/[target] (= [endpoint]),
    [incident], [edges_at], [edges], [walk], [eseparates].

    CORE API used (verified on switch `digraph`, Rocq 9.1.1 + coq-graph-theory):
      - [edge G] : finType of edges; [source e]/[target e] : G endpoints;
      - [incident x e] : bool; [edges_at x] : {set edge G};
      - [edges x y] : {set edge G} the edges between x and y;
      - [walk x y w] : closed/open edge-walk predicate (w : seq (edge G));
      - [eseparates x y E] : every [x]–[y] walk meets the edge set [E];
      - [partition P D] : mathcomp partition of a finite set.

    AREA primitives introduced here (cycle-theory specific; would only migrate to
    graph-theory-base if a 2nd area needs them): [subdeg], [mdeg], [cubic],
    [bridgeless], [is_circuit], [even_subgraph], [cdc], [two_factor], [oddness_le],
    [faithful_cover], [admissible], transition systems and compatible
    decompositions.  [eulerian] and [edge_connected] are general graph notions
    (tagged [@MOVE-to-base] candidates). *)

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

(** A 2-factor: a SPANNING 2-regular subgraph (every vertex has degree 2). *)
Definition two_factor (G : mgraph) (F : {set edge G}) : Prop :=
  forall v : G, subdeg F v = 2.

(** An even subgraph ("binary cycle" / element of the cycle space):
    every vertex has even subgraph-degree. *)
Definition even_subgraph (G : mgraph) (C : {set edge G}) : Prop :=
  forall v : G, ~~ odd (subdeg C v).

(** ** Connectivity at the multigraph level (via [walk]) *)

(** Walk restricted to edges of [H]. *)
Definition walk_in (G : mgraph) (H : {set edge G}) (x y : G) (w : seq (edge G)) : bool :=
  walk x y w && all (fun e => e \in H) w.

(** Whole-graph (vertex) connectivity. *)
Definition mconnected (G : mgraph) : Prop :=
  forall x y : G, exists w, walk x y w.

(** Connectivity using only edges OUTSIDE the edge set [S] (i.e. of [G - E(S)]). *)
Definition connected_del_edges (G : mgraph) (S : {set edge G}) : Prop :=
  forall x y : G, exists w, walk x y w /\ all (fun e => e \notin S) w.

(** Connectivity after deleting the vertex set [Z] (walks avoiding [Z]). *)
Definition connected_del_verts (G : mgraph) (Z : {set G}) : Prop :=
  forall x y : G, x \notin Z -> y \notin Z ->
    exists w, walk x y w /\ all (fun e => (source e \notin Z) && (target e \notin Z)) w.

(** 2-(vertex-)connected: at least 3 vertices, and connected after deleting any one. *)
Definition two_connected (G : mgraph) : Prop :=
  (3 <= #|G|)%N /\ forall z : G, connected_del_verts [set z].

(** [k]-edge-connected: deleting fewer than [k] edges keeps the graph connected.
    [@MOVE-to-base]: general graph notion, migrate to graph-theory-base when a
    second area needs it. *)
Definition edge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, (#|E| < k)%N -> connected_del_edges E.

(** A subgraph [H] is connected: any two [H]-incident vertices are joined by an
    [H]-walk. *)
Definition H_inc (G : mgraph) (H : {set edge G}) (x : G) : bool :=
  [exists e, (e \in H) && incident x e].

Definition subgraph_connected (G : mgraph) (H : {set edge G}) : Prop :=
  forall x y : G, H_inc H x -> H_inc H y -> exists w, walk_in H x y w.

(** ** Circuits and acyclicity *)

(** A circuit (single cycle): a nonempty, connected, 2-regular edge set. *)
Definition is_circuit (G : mgraph) (C : {set edge G}) : Prop :=
  [/\ C != set0, subgraph_kregular C 2 & subgraph_connected C].

(** Acyclic: contains no circuit. *)
Definition acyclic (G : mgraph) (H : {set edge G}) : Prop :=
  forall C : {set edge G}, C \subset H -> ~ is_circuit C.

(** A path subgraph: nonempty, connected, acyclic, max degree ≤ 2. *)
Definition is_path (G : mgraph) (P : {set edge G}) : Prop :=
  [/\ P != set0, subgraph_connected P, acyclic P & forall v : G, (subdeg P v <= 2)%N].

(** A matching: every vertex meets at most one matching edge. *)
Definition is_matching (G : mgraph) (M : {set edge G}) : Prop :=
  forall v : G, (subdeg M v <= 1)%N.

(** A spanning tree (as an edge set): spanning + connected + acyclic.  Spanning
    is automatic from [walk]-connectivity over ALL vertices (an isolated vertex
    has no nontrivial walk to the others). *)
Definition spanning_connected (G : mgraph) (T : {set edge G}) : Prop :=
  forall x y : G, exists w, walk x y w /\ all (fun e => e \in T) w.

Definition spanning_tree (G : mgraph) (T : {set edge G}) : Prop :=
  spanning_connected T /\ acyclic T.

(** ** Bridges, cubic, eulerian *)

(** [e] is a bridge: every walk between its endpoints uses [e]. *)
Definition is_bridge (G : mgraph) (e : edge G) : Prop :=
  eseparates (source e) (target e) [set e].

Definition bridgeless (G : mgraph) : Prop :=
  forall e : edge G, ~ is_bridge e.

(** Cubic: loopless and 3-regular. *)
Definition cubic (G : mgraph) : Prop :=
  loopless G /\ forall v : G, mdeg v = 3.

(** Simple multigraph: loopless and at most one edge between any pair. *)
Definition simple_mgraph (G : mgraph) : Prop :=
  loopless G /\ forall x y : G, (#|edges x y| <= 1)%N.

(** Eulerian: connected with all degrees even.
    [@MOVE-to-base]: general graph notion, migrate to graph-theory-base when a
    second area needs it. *)
Definition eulerian (G : mgraph) : Prop :=
  mconnected G /\ forall v : G, ~~ odd (mdeg v).

(** An eulerian tour: a closed walk traversing every edge exactly once. *)
Definition is_eulerian_tour (G : mgraph) (w : seq (edge G)) : Prop :=
  (exists x : G, walk x x w) /\ (forall e : edge G, count (pred1 e) w = 1).

(** ** Edge partitions and decompositions *)

(** A list of edge sets partitions ALL edges: each edge in exactly one part. *)
Definition edge_partitionT (G : mgraph) (D : seq {set edge G}) : Prop :=
  forall e : edge G, count (fun C : {set edge G} => e \in C) D = 1.

(** A list of edge sets partitions the edges of [H]: each edge of [H] in exactly
    one part, each non-[H] edge in none. *)
Definition edge_partition_of (G : mgraph) (H : {set edge G}) (D : seq {set edge G}) : Prop :=
  forall e : edge G, count (fun C : {set edge G} => e \in C) D = ((e \in H) : nat).

(** Decomposition of [H] into circuits. *)
Definition cycle_decomposition_of (G : mgraph) (H : {set edge G})
    (D : seq {set edge G}) : Prop :=
  (forall C, C \in D -> is_circuit C) /\ edge_partition_of H D.

(** Decomposition of the WHOLE edge set into circuits. *)
Definition cycle_decomposition (G : mgraph) (D : seq {set edge G}) : Prop :=
  (forall C, C \in D -> is_circuit C) /\ edge_partitionT D.

(** Decomposition into paths. *)
Definition path_decomposition (G : mgraph) (D : seq {set edge G}) : Prop :=
  (forall P, P \in D -> is_path P) /\ edge_partitionT D.

(** ** Cycle covers *)

(** A cycle double cover: a list of circuits with every edge covered exactly twice. *)
Definition cdc (G : mgraph) (L : seq {set edge G}) : Prop :=
  (forall C, C \in L -> is_circuit C) /\
  (forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2).

(** A faithful cover for an edge weighting [p]: circuits covering [e] exactly [p e] times. *)
Definition faithful_cover (G : mgraph) (p : edge G -> nat) (L : seq {set edge G}) : Prop :=
  (forall C, C \in L -> is_circuit C) /\
  (forall e : edge G, count (fun C : {set edge G} => e \in C) L = p e).

(** The edge cut of a vertex set [S]: edges with exactly one endpoint in [S]. *)
Definition cut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].

(** Admissible weighting: across every cut, the total is even and no single edge
    exceeds the sum of the others (i.e. 2·p(e) ≤ p(δ(S))). *)
Definition admissible (G : mgraph) (p : edge G -> nat) : Prop :=
  forall (S : {set G}) (e : edge G), e \in cut S ->
    (2 * p e <= \sum_(f in cut S) p f)%N /\ ~~ odd (\sum_(f in cut S) p f).

(** ** Transition systems and compatible decompositions *)

(** A 2-transition system: at every vertex [v], [P v] partitions the incident
    edges into transitions, each of size exactly 2. *)
Definition transition2_system (G : mgraph) (P : G -> {set {set edge G}}) : Prop :=
  (forall v : G, partition (P v) (edges_at v)) /\
  (forall (v : G) (T : {set edge G}), T \in P v -> #|T| = 2).

(** A cycle decomposition is compatible with [P] if no circuit uses a transition
    of [P] (at each vertex its two circuit-edges are not a [P]-transition). *)
Definition compatible_decomposition (G : mgraph) (P : G -> {set {set edge G}})
    (D : seq {set edge G}) : Prop :=
  cycle_decomposition D /\
  (forall C, C \in D -> forall v : G, (edges_at v :&: C) \notin P v).

(** Two edges are consecutive in the cyclic tour [w]. *)
Definition cyc_pairs (G : mgraph) (w : seq (edge G)) : seq (edge G * edge G) :=
  zip w (rot 1 w).

Definition two_consecutive (G : mgraph) (w : seq (edge G)) (C : {set edge G}) : bool :=
  has (fun p => (p.1 \in C) && (p.2 \in C)) (cyc_pairs w).

(** Oddness ≤ [k]: some 2-factor decomposes into circuits, at most [k] of them odd. *)
Definition oddness_le (G : mgraph) (k : nat) : Prop :=
  exists (F : {set edge G}) (D : seq {set edge G}),
    [/\ two_factor F, cycle_decomposition_of F D & (count (fun C : {set edge G} => odd #|C|) D <= k)%N].

(** ================================================================= *)
(** ** Row 1 — Cycle double covers containing a predefined 2-regular subgraph *)
(** OPEN.

    Source: "Let G be a 2-connected cubic graph and let S be a 2-regular subgraph
    such that G−E(S) is connected.  Then G has a cycle double cover which contains
    S (i.e. all cycles of S)." *)
Definition cycle_double_covers_containing_predefined_2_regular_statement : Prop :=
  forall (G : mgraph) (S : {set edge G}),
    (0 < #|G|)%N -> cubic G -> two_connected G ->
    subgraph_kregular S 2 -> connected_del_edges S ->
    exists L : seq {set edge G},
      cdc L /\
      exists D : seq {set edge G},
        cycle_decomposition_of S D /\ {subset D <= L}.

(** ** Row 2 — 3-Decomposition Conjecture *)
(** OPEN.

    Source: "Every connected cubic graph G has a decomposition into a spanning
    tree, a family of cycles and a matching." *)
Definition three_decomposition_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic G -> mconnected G ->
    exists T F M : {set edge G},
      [/\ spanning_tree T, subgraph_kregular F 2, is_matching M
        & edge_partitionT [:: T; F; M]].

(** ** Row 3 — Decomposing a connected graph into paths *)
(** OPEN.

    Source: "Every simple connected graph on n vertices can be decomposed into at
    most ½(n+1) paths." *)
Definition decomposing_a_connected_graph_into_paths_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> simple_mgraph G -> mconnected G ->
    exists D : seq {set edge G},
      path_decomposition D /\ (size D <= (#|G| + 1) %/ 2)%N.

(** ** Row 4 — Decomposing an eulerian graph into cycles *)
(** OPEN.

    Source: "Every simple eulerian graph on n vertices can be decomposed into at
    most ½(n−1) cycles." *)
Definition decomposing_an_eulerian_graph_into_cycles_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> simple_mgraph G -> eulerian G ->
    exists D : seq {set edge G},
      cycle_decomposition D /\ (size D <= (#|G| - 1) %/ 2)%N.

(** ** Row 5 — Eulerian decomposition avoiding two consecutive tour edges *)
(** OPEN.

    Source: "Let G be an eulerian graph of minimum degree 4, and let W be an
    eulerian tour of G.  Then G admits a decomposition into cycles none of which
    contains two consecutive edges of W." *)
Definition decomposing_an_eulerian_graph_into_cycles_with_no_tw_statement : Prop :=
  forall (G : mgraph) (w : seq (edge G)),
    (0 < #|G|)%N -> eulerian G -> (forall v : G, (4 <= mdeg v)%N) ->
    is_eulerian_tour w ->
    exists D : seq {set edge G},
      cycle_decomposition D /\ (forall C, C \in D -> ~~ two_consecutive w C).

(** ** Row 6 — Compatible decompositions of eulerian graphs *)
(** OPEN.

    Source: "If G is a 6-edge-connected Eulerian graph and P is a 2-transition
    system for G, then (G,P) has a compatible decomposition." *)
Definition decomposing_eulerian_graphs_statement : Prop :=
  forall (G : mgraph) (P : G -> {set {set edge G}}),
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> edge_connected G 6 -> eulerian G ->
    transition2_system P ->
    exists D : seq {set edge G}, compatible_decomposition P D.

(** ** Row 7 — (5,2)-cycle covers *)
(** OPEN.

    Source: "Every bridgeless graph has a (5,2)-cycle-cover."

    MODELING NOTE: in a (5,2)-cover (and in the k-cycle-double-cover rows 10/11),
    a "cycle" means an EVEN SUBGRAPH (element of the cycle space, a disjoint union
    of circuits), not necessarily a single [is_circuit]; this is the standard
    even-subgraph formulation, so the cover members are typed [even_subgraph]. *)
Definition m_n_cycle_covers_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> bridgeless G ->
    exists L : seq {set edge G},
      [/\ size L = 5,
          (forall C, C \in L -> even_subgraph C)
        & (forall e : edge G, count (fun C : {set edge G} => e \in C) L = 2)].

(** ** Row 8 — Odd cycles and low oddness *)
(** OPEN.

    Source: "If in a bridgeless cubic graph G the cycles of any 2-factor are odd,
    then ω(G) ≤ 2, where ω(G) is the oddness, i.e. the minimum number of odd
    cycles in a 2-factor of G." *)
Definition odd_cycles_and_low_oddness_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> cubic G -> bridgeless G ->
    (forall F : {set edge G}, two_factor F ->
       forall C : {set edge G}, C \subset F -> is_circuit C -> odd #|C|) ->
    oddness_le G 2.

(** ** Row 9 — Faithful cycle covers *)
(** OPEN.

    Source: "If G=(V,E) is a graph, p:E→ℤ is admissible, and p(e) is even for
    every e∈E(G), then (G,p) has a faithful cover." *)
Definition faithful_cycle_covers_statement : Prop :=
  forall (G : mgraph) (p : edge G -> nat),
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> admissible p ->
    (forall e : edge G, ~~ odd (p e)) ->
    exists L : seq {set edge G}, faithful_cover p L.

(** ** Row 10 — Strong 5-cycle double cover conjecture *)
(** OPEN.

    Source: "Let C be a circuit in a bridgeless cubic graph G.  Then there is a
    five cycle double cover of G such that C is a subgraph of one of these five
    cycles." *)
Definition strong_5_cycle_double_cover_statement : Prop :=
  forall (G : mgraph) (C : {set edge G}),
    (0 < #|G|)%N -> cubic G -> bridgeless G -> is_circuit C ->
    exists L : seq {set edge G},
      [/\ size L = 5,
          (forall D, D \in L -> even_subgraph D),
          (forall e : edge G, count (fun D : {set edge G} => e \in D) L = 2)
        & (exists D, D \in L /\ C \subset D)].

(** ** Row 11 — Cycle double cover conjecture *)
(** OPEN.

    Source: "For every graph with no bridge, there is a list of cycles so that
    every edge is contained in exactly two." *)
Definition cycle_double_cover_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> (0 < #|edge G|)%N -> bridgeless G ->
    exists L : seq {set edge G}, cdc L.
