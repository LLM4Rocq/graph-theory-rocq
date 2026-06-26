(** * Chromatic.conjectures.U5 — milestone U5 (namespace Chromatic, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of nine open/partial problems on EDGE and TOTAL colouring: strong
    edge colouring (Erdős–Nešetřil), Seymour's r-graph conjecture, the 3-edge-
    colouring conjecture, Goldberg's conjecture, a hypergraph generalization of
    Vizing's theorem, universal Steiner triple systems, acyclic edge colouring,
    the star chromatic index of (sub)cubic graphs, and Behzad's total colouring
    conjecture.

    CARRIER TYPES (chosen per row.rocq_idiom, NOT a blanket sgraph):
      - Rows 1, 7, 8 (strong / acyclic / star EDGE colouring of SIMPLE graphs):
        carrier [sgraph]; an edge colouring is modelled as a SYMMETRIC function
        [col : G -> G -> 'I_k] on adjacent vertex pairs (a simple graph has at
        most one edge per pair), avoiding a separate edge type.
      - Rows 2, 3, 4, 6, 9 (r-graphs / cubic / multigraph / total colouring):
        carrier [mgraph] = [graph unit unit] (coq-graph-theory multigraphs),
        using the raw [edge]/[source]/[target]/[incident]/[edges_at]/[edge_set]
        API, with edge- and total-chromatic numbers via base's line/total graph.
      - Row 5 (d-uniform hypergraph): a finite incidence record [hypergraph].

    CORE undirected vocabulary + the edge/total-colouring layer come from
    graph-theory-base (GTBase.base): [sgraph], [x -- y], [χ]=[chi_mem],
    ['K_n], [Delta] (Δ for sgraph), [ceil_div], [connected], [ucycleb], and the
    PROMOTED edge/total surface [mgraph] notation, [loopless], [line_graph],
    [total_graph], [chromatic_index] (χ'), [total_chromatic_number] (χ''),
    [edge_colourable], [total_colourable].  These are REUSED verbatim; no base
    primitive is redefined.  coq-graph-theory's [mgraph] module is imported
    BEFORE base (its DIRECTED [line_graph] is then shadowed by base's undirected
    one) to expose the raw multigraph edge API.

    AREA-SPECIFIC primitives introduced here (edge/total-colouring vocabulary):
      - [strong_edge_colourable] (+ [near_edge]/[diff_edge]) : strong chromatic
        index sχ' as colourability (Row 1);
      - [mDelta] : multigraph maximum degree (parallel edges counted) — a
        cross-area primitive shared with U4, tagged [@MOVE-to-base];
      - [regular_m] / [cubic] : multigraph regularity / 3-regularity (same
        degree-with-parallel-edges family as [mDelta], so likewise tagged
        [@MOVE-to-base] for the next multigraph milestone);
      - [msimple] : a simple multigraph (loopless + no parallel edges), used to
        restrict Behzad's conjecture (Row 9) to the SIMPLE-graph setting in
        which it is open (over multigraphs the Δ+2 upper bound is false);
      - [edge_boundary] / [is_r_graph] : edge cut δ(X) and Seymour r-graphs (Row 2);
      - [remove_edge] / [usimple] / [mconnected] / [subdivide_edge_s] /
        [subdivR_s] / [homeomorphic_s] : edge deletion, the underlying simple
        graph, connectivity, single-edge subdivision and the common-subdivision
        homeomorphism used for the homeomorphic cubic reduction (Row 3);
      - [overfull_parameter] : Goldberg's density parameter w(G) (Row 4);
      - [hypergraph] / [uniform_hg] / [simple_hg] / [hg_codegree_le] : finite
        d-uniform hypergraphs and codegree (Row 5);
      - [sts] / [sts_valid] / [sts_edge_colourable] / [is_universal_sts] :
        Steiner triple systems and STS-edge-colouring (Row 6);
      - [acyclic_edge_colouring] (+ [edge_colour_seq]) : Row 7;
      - [star_edge_colouring] : Row 8. *)

(* mgraph imported BEFORE base: coq-graph-theory's mgraph defines a DIRECTED `line_graph`
   (DiGraph, target=source); importing it first lets base's undirected sgraph line_graph/
   total_graph shadow it. We use mgraph for the raw edge/incident/edges_at/source/target API. *)
From GraphTheory Require Import mgraph.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    SHARED AREA PRIMITIVES
    ========================================================================== *)

(** [mDelta] (multigraph maximum degree, parallel edges counted) — PROMOTED to graph-theory-base
    (U4 ∩ U5 triggered the migration); reused here via the base export. *)

(** [r]-regularity / cubicity of a multigraph (degree = #incident edges).
    Same degree-with-parallel-edges family as [mDelta]; promote together.
    [@MOVE-to-base] *)
Definition regular_m (G : mgraph) (r : nat) : Prop := forall v : G, #|edges_at v| = r.
Definition cubic (G : mgraph) : Prop := regular_m G 3.

(** Simple multigraph: loopless and no two distinct edges share an unordered
    endpoint pair (no parallel edges).  [edge_ends e] is the (≤2-element) set of
    endpoints of [e]; injectivity of [edge_ends] on a loopless graph rules out
    parallel edges, so [msimple G] is exactly "G is a simple graph presented as
    a multigraph".  Used to restrict Behzad's conjecture to simple graphs. *)
Definition edge_ends (G : mgraph) (e : edge G) : {set G} :=
  [set source e; target e].
Definition msimple (G : mgraph) : Prop :=
  loopless G /\ injective (@edge_ends G).

(** ** Underlying simple graph, edge deletion, connectivity (for Rows 3, 6) ****)

(** [madj] (base) is the underlying simple adjacency of a multigraph; we package
    it as an [sgraph] to reuse base's [connected]. *)
Lemma madj_sym (G : mgraph) : symmetric (@madj G).
Proof.
move=> x y; rewrite /madj eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[w Hw]; exists w; rewrite andbC.
Qed.
Lemma madj_irrefl (G : mgraph) : irreflexive (@madj G).
Proof. by move=> x; rewrite /madj eqxx. Qed.
Definition usimple (G : mgraph) : sgraph := SGraph (@madj_sym G) (@madj_irrefl G).
Definition mconnected (G : mgraph) : Prop := connected [set: usimple G].

(** Delete one edge (vertex type unchanged). *)
Definition remove_edge (G : mgraph) (e : edge G) : mgraph := remove_edges [set e].

(** ============================================================================
    Row 1 — Strong edge colouring (Erdős–Nešetřil) — PARTIAL.
    "A strong edge-colouring colours edges so every colour class is an INDUCED
    matching (any two vertices on distinct equicoloured edges are non-adjacent);
    sχ'(G) is the minimum number of colours.  Conjecture sχ'(G) ≤ 5Δ²/4 if Δ
    even, (5Δ²−2Δ+1)/4 if Δ odd."  Edges modelled as a symmetric [col] on
    adjacent vertex pairs; two edges {x,y},{u,v} are [near] iff they share a
    vertex or an endpoint of one is adjacent to an endpoint of the other (line-
    graph distance ≤ 1) — a strong colouring keeps NEAR distinct edges apart.
    ========================================================================== *)

Definition diff_edge (G : sgraph) (x y u v : G) : bool :=
  ~~ (((x == u) && (y == v)) || ((x == v) && (y == u))).

Definition near_edge (G : sgraph) (x y u v : G) : bool :=
  [|| x == u, x == v, y == u, y == v, x -- u, x -- v, y -- u | y -- v].

Definition strong_edge_colourable (G : sgraph) (k : nat) : Prop :=
  exists col : G -> G -> 'I_k,
    (forall x y : G, col x y = col y x) /\
    (forall x y u v : G, x -- y -> u -- v ->
        diff_edge x y u v -> near_edge x y u v -> col x y != col u v).

(** Non-triviality guard [0 < Delta G]: for an edgeless graph Delta G = 0, the
    even branch gives bound 0 and the conclusion would demand a TOTAL function
    into the empty ordinal ['I_0] (refutable on any inhabited vertex type).  The
    guard excludes exactly that degenerate edgeless case; sχ'(edgeless)=0 ≤ 0 is
    mathematically trivial and so harmlessly dropped.  For [0 < Delta G] both
    branches are ≥ 1, so the colour type is inhabited. *)
Definition strong_edge_colouring_statement : Prop :=
  forall G : sgraph, 0 < Delta G ->
    strong_edge_colourable G
      (if odd (Delta G)
       then (5 * (Delta G) ^ 2 - 2 * (Delta G) + 1) %/ 4
       else (5 * (Delta G) ^ 2) %/ 4).

(** ============================================================================
    Row 2 — Seymour's r-graph conjecture — OPEN.
    "An r-graph is an r-regular G with |δ(X)| ≥ r for every X ⊆ V(G) of odd
    size.  Conjecture χ'(G) ≤ r+1 for every r-graph G."  δ(X) = edges with
    exactly one endpoint in X.
    ========================================================================== *)

Definition edge_boundary (G : mgraph) (X : {set G}) : {set edge G} :=
  [set e | (source e \in X) (+) (target e \in X)].

Definition is_r_graph (G : mgraph) (r : nat) : Prop :=
  (forall v : G, #|edges_at v| = r) /\
  (forall X : {set G}, odd #|X| -> r <= #|edge_boundary X|).

Definition seymours_r_graph_statement : Prop :=
  forall (r : nat) (G : mgraph), is_r_graph G r -> edge_colourable G r.

(** ============================================================================
    Row 3 — 3-edge-colouring conjecture — OPEN.
    "G connected cubic with |V(G)|>2 admitting a 3-edge-colouring ⇒ ∃ e ∈ E(G)
    such that the cubic graph homeomorphic to G−e has a 3-edge-colouring."  The
    "cubic graph homeomorphic to G−e" is captured by [homeomorphic_s]: H is a
    cubic multigraph whose underlying simple graph is homeomorphic to that of
    G−e, where homeomorphism = common subdivision of underlying simple graphs.
    ========================================================================== *)

(** Single-edge subdivision of a simple graph: replace edge x–y by a new degree-2
    vertex [inr tt] adjacent to x and y. *)
Section SubdivS.
Variables (G : sgraph) (x y : G).
Definition sds_rel : rel (G + unit) :=
  fun a b =>
    match a, b with
    | inl u, inl v => (u -- v) && ~~ (((u == x) && (v == y)) || ((u == y) && (v == x)))
    | inl u, inr _ => (u == x) || (u == y)
    | inr _, inl v => (v == x) || (v == y)
    | inr _, inr _ => false
    end.
Lemma sds_sym : symmetric sds_rel.
Proof.
move=> a b; case: a => [u|[]]; case: b => [v|[]] //=.
rewrite sg_sym; congr (_ && _); congr (~~ _).
by case: (u == x); case: (u == y); case: (v == x); case: (v == y).
Qed.
Lemma sds_irrefl : irreflexive sds_rel.
Proof. by move=> [u|[]] //=; rewrite sgP. Qed.
Definition subdivide_edge_s : sgraph := SGraph sds_sym sds_irrefl.
End SubdivS.

(** [K] is a subdivision of [G]: reachable from [G] by finitely many single-edge
    subdivisions (up to simple-graph isomorphism [≃] = [diso]). *)
Inductive subdivR_s : sgraph -> sgraph -> Prop :=
| subdivR_s_refl (G : sgraph) : subdivR_s G G
| subdivR_s_step (G H K : sgraph) (x y : H) :
    subdivR_s G H -> (subdivide_edge_s x y ≃ K) -> subdivR_s G K.

(** Topological equivalence of simple graphs: a common subdivision. *)
Definition homeomorphic_s (G H : sgraph) : Prop :=
  exists K : sgraph, subdivR_s K G /\ subdivR_s K H.

Definition three_edge_coloring_statement : Prop :=
  forall G : mgraph,
    loopless G -> cubic G -> mconnected G -> 2 < #|G| -> edge_colourable G 3 ->
    exists (e : edge G) (H : mgraph),
      [/\ cubic H,
          homeomorphic_s (usimple (remove_edge e)) (usimple H)
        & edge_colourable H 3].

(** ============================================================================
    Row 4 — Goldberg's conjecture — OPEN.
    "w(G) = max over H ⊆ G of ⌈|E(H)| / ⌊|V(H)|/2⌋⌉.  Every G satisfies
    χ'(G) ≤ max{Δ(G)+1, w(G)}."  The max ranges over induced subgraphs (vertex
    subsets S), with |E(H)| = #|edge_set S|, |V(H)| = #|S|; ⌈·/·⌉ = ceil_div
    (ceil_div a 0 = 0, so the |S|≤1 terms vanish).
    ========================================================================== *)

Definition overfull_parameter (G : mgraph) : nat :=
  \max_(S : {set G}) ceil_div #|edge_set S| (#|S| %/ 2).

Definition goldbergs_statement : Prop :=
  forall G : mgraph,
    chromatic_index G <= maxn (mDelta G).+1 (overfull_parameter G).

(** ============================================================================
    Row 5 — A generalization of Vizing's theorem — OPEN.
    "H a simple d-uniform hypergraph; every set of d−1 points lies in ≤ r edges.
    Then ∃ an (r+d−1)-edge-colouring so that any two edges sharing d−1 vertices
    have distinct colours."
    ========================================================================== *)

Record hypergraph := Hypergraph {
  hv : finType;
  he : finType;
  hinc : he -> {set hv} }.

(** [d]-uniformity: every edge has exactly d points. *)
Definition uniform_hg (H : hypergraph) (d : nat) : Prop :=
  forall e : he H, #|hinc e| = d.
(** Simplicity: distinct edges are distinct point sets. *)
Definition simple_hg (H : hypergraph) : Prop := injective (@hinc H).
(** Codegree ≤ r: every (d−1)-set lies in at most r edges. *)
Definition hg_codegree_le (H : hypergraph) (d r : nat) : Prop :=
  forall T : {set hv H}, #|T| = d.-1 -> #|[set e | T \subset hinc e]| <= r.

Definition a_generalization_of_vizings_theorem_statement : Prop :=
  forall (H : hypergraph) (d r : nat),
    1 <= d -> uniform_hg H d -> simple_hg H -> hg_codegree_le H d r ->
    exists c : he H -> 'I_(r + d - 1),
      forall e e' : he H,
        e != e' -> #|hinc e :&: hinc e'| = d.-1 -> c e != c e'.

(** ============================================================================
    Row 6 — Universal Steiner triple systems — OPEN PROBLEM.
    "Which Steiner triple systems are universal?"  An STS S is universal iff
    every (loopless) cubic graph is S-edge-colourable: edges are coloured by
    points of S so that the three edges at every vertex form a block (triple) of
    S.  We state the associated open proposition — the EXISTENCE of a universal
    STS — the property [is_universal_sts] being the object the classification
    problem asks to characterize.
    ========================================================================== *)

Record sts := STS { sts_pt : finType; sts_blk : {set {set sts_pt}} }.

(** Validity: every block is a triple, and every pair of points lies in a unique
    block. *)
Definition sts_valid (S : sts) : Prop :=
  (forall B : {set sts_pt S}, B \in sts_blk S -> #|B| = 3) /\
  (forall p q : sts_pt S, p != q ->
     exists B : {set sts_pt S},
       [/\ B \in sts_blk S, p \in B, q \in B
         & forall B' : {set sts_pt S},
             B' \in sts_blk S -> p \in B' -> q \in B' -> B' = B]).

(** [G] is S-edge-colourable: a point-colouring of edges whose three values at
    every vertex form a block (forces distinctness, hence properness, on cubic
    G). *)
Definition sts_edge_colourable (G : mgraph) (S : sts) : Prop :=
  exists c : edge G -> sts_pt S,
    forall v : G, [set c e | e in edges_at v] \in sts_blk S.

Definition is_universal_sts (S : sts) : Prop :=
  forall G : mgraph, loopless G -> cubic G -> sts_edge_colourable G S.

Definition universal_steiner_triple_systems_statement : Prop :=
  exists S : sts, sts_valid S /\ is_universal_sts S.

(** ============================================================================
    Row 7 — Acyclic edge colouring — OPEN.
    "Every simple graph with maximum degree Δ has a proper (Δ+2)-edge-colouring
    so that every cycle contains edges of at least three distinct colours."
    Cycle = vertex [ucycle]; the cycle's edge colours are read off consecutive
    pairs.
    ========================================================================== *)

Definition edge_colour_seq (G : sgraph) (k : nat) (col : G -> G -> 'I_k)
    (s : seq G) : seq 'I_k :=
  [seq col p.1 p.2 | p <- zip s (rot 1 s)].

Definition acyclic_edge_colouring (G : sgraph) (k : nat) (col : G -> G -> 'I_k)
    : Prop :=
  [/\ (forall x y : G, col x y = col y x),
      (forall x y z : G, y != z -> x -- y -> x -- z -> col x y != col x z)
    & forall s : seq G, ucycleb (--) s -> 2 < size s ->
        2 < size (undup (edge_colour_seq col s))].

Definition acyclic_edge_coloring_statement : Prop :=
  forall G : sgraph,
    exists col : G -> G -> 'I_(Delta G + 2), acyclic_edge_colouring col.

(** ============================================================================
    Row 8 — Star chromatic index of (sub)cubic graphs — OPEN QUESTION.
    "χ_s'(G) = min colours for a proper edge colouring with no bicoloured path or
    cycle of length four.  Is χ_s'(G) ≤ 6 for every (sub)cubic graph G?"
    Length four = four edges (P5 / C4); proper colouring already forbids equal
    consecutive colours, so bicoloured ⇔ the two ends repeat the first two
    colours.
    ========================================================================== *)

Definition star_edge_colouring (G : sgraph) (k : nat) (col : G -> G -> 'I_k)
    : Prop :=
  [/\ (forall x y : G, col x y = col y x),
      (forall x y z : G, y != z -> x -- y -> x -- z -> col x y != col x z),
      (forall x0 x1 x2 x3 x4 : G,
          x0 -- x1 -> x1 -- x2 -> x2 -- x3 -> x3 -- x4 ->
          uniq [:: x0; x1; x2; x3; x4] ->
          ~ (col x0 x1 = col x2 x3 /\ col x1 x2 = col x3 x4))
    & (forall x0 x1 x2 x3 : G,
          x0 -- x1 -> x1 -- x2 -> x2 -- x3 -> x3 -- x0 ->
          uniq [:: x0; x1; x2; x3] ->
          ~ (col x0 x1 = col x2 x3 /\ col x1 x2 = col x3 x0))].

Definition star_chromatic_index_of_cubic_graphs_statement : Prop :=
  forall G : sgraph, Delta G <= 3 ->
    exists col : G -> G -> 'I_6, star_edge_colouring col.

(** ============================================================================
    Row 9 — Behzad's total colouring conjecture — OPEN.
    "A total colouring assigns colours to vertices AND edges so adjacent
    vertices, adjacent edges, and incident vertex–edge pairs differ; χ''(G) is
    the minimum.  Behzad: χ''(G) = Δ(G)+1 or Δ(G)+2."  Stated as the two-sided
    bound Δ+1 ≤ χ''(G) ≤ Δ+2.

    CARRIER: Behzad's Total Colouring Conjecture is a statement about SIMPLE
    graphs; over multigraphs the Δ+2 upper bound is FALSE (the "fat triangle"
    K3 with p parallel edges per pair is loopless with Δ=2p but χ''≥χ'=3p>2p+2
    for p≥3).  We therefore guard with [msimple G] (loopless + no parallel
    edges) so the statement is exactly the open conjecture, while still reusing
    base's [total_chromatic_number] machinery on [mgraph]. *)

Definition behzads_statement : Prop :=
  forall G : mgraph, msimple G ->
    (mDelta G).+1 <= total_chromatic_number G <= (mDelta G).+2.
