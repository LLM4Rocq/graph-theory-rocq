(** * Chromatic.conjectures.U1 — milestone U1 (namespace Chromatic, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of nine open/partial/solved problems on graph colouring.

    PRE-G3 MODE: [graph-theory-base] is not a live library yet (the repo's
    [base/] directory holds only a README scaffold, no [.v] files), so the CORE
    undirected vocabulary is imported DIRECTLY from coq-graph-theory here.
    Cross-area primitives that should MOVE to graph-theory-base once G3 lands
    are tagged [@MOVE-to-base] below; we make no claim of base reuse yet.

    CORE API used (verified to load on switch `digraph`, Rocq 9.1.1 +
    coq-graph-theory):
      - [G : sgraph]; [x -- y] adjacency; [N(x)] open neighbourhood ({set G});
      - [χ(A)] = [chi_mem (mem A)] : subset-relative chromatic number (nat),
        whole-graph value [χ([set: G])]; the induced subgraph on [A] is the
        carrier, so removing vertices is [χ(A :\: S)];
      - [ω(A)] = [omega_mem (mem A)] : subset-relative clique number (nat);
      - [clique A] : Prop; [connected A] : Prop; ['K_n] = [complete n] : sgraph;
      - [F ≃ G] = [diso F G] : Type (isomorphism data — wrapped in [inhabited]
        to land in Prop);
      - [ucycle (--) c] / [ucycleb (--) c] : (boolean) cycle predicate on
        [c : seq G] (a cycle = closed walk with distinct vertices). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Shared AREA primitives *)

(** [@MOVE-to-base] Maximum degree Δ(G).  For the empty graph this is 0; the
    rows that use it (Borodin–Kostochka, Reed) carry an explicit non-triviality
    guard. *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** [@MOVE-to-base] Pure arithmetic helper: ⌈a/b⌉ (with the mathcomp
    convention ⌈a/0⌉ = 0).  Graph-free and cross-area (used by Melnikov, Row 8,
    and conceptually Reed); it is a base/arithmetic candidate, not row-local. *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** [@MOVE-to-base] Common-neighbourhood set of two vertices. *)
Definition common_nbr (G : sgraph) (u v : G) : {set G} := N(u) :&: N(v).

(** [@MOVE-to-base] [d]-regularity: every vertex has degree exactly [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** [@MOVE-to-base] Girth ≥ [g]: every GENUINE cycle has length at least [g]
    (acyclic graphs satisfy this for every [g]).

    NB: the [2 < size c] guard is load-bearing, not decoration.  In mathcomp
    [ucycle (--) [::]] reduces to [true] (an empty closed walk), and for an
    edge [x -- y] the 2-tuple [[x; y]] is also a [ucycle]; without the guard
    [girth_geq G g] would be REFUTED by [c := [::]] for every [g ≥ 1] (size 0)
    and capped at [g ≤ 2] for every graph carrying an edge, making it
    unsatisfiable for [g ≥ 3] and turning Row 4 into a false statement.  In a
    simple graph every genuine cycle has [3 ≤ size c], so restricting the bound
    to [2 < size c] is exactly "girth ≥ g" and keeps the predicate satisfiable
    (e.g. forests/edgeless graphs satisfy it for all [g]). *)
Definition girth_geq (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> g <= size c.

(** ** Row 1 — Double-critical graph conjecture
    PARTIAL (verified for k ≤ 5; open for k ≥ 6).

    Source: "A connected simple graph G is double-critical if removing any pair
    of adjacent vertices lowers the chromatic number by two.  Conjecture: K_n
    is the only n-chromatic double-critical graph."

    New AREA primitive: [double_critical]. *)
Definition double_critical (G : sgraph) : Prop :=
  forall x y : G, x -- y -> χ([set: G] :\: [set x; y]) + 2 = χ([set: G]).

Definition double_critical_graph_statement : Prop :=
  forall (G : sgraph) (n : nat),
    0 < #|G| -> connected [set: G] -> double_critical G ->
    χ([set: G]) = n -> inhabited (G ≃ 'K_n).

(** ** Row 2 — Three-chromatic (0,2)-graphs
    OPEN.

    Source: "Are there any (0,2)-graphs with chromatic number exactly three?
    A (0,2)-graph: every two distinct vertices have either 0 or exactly 2
    common neighbours."

    New AREA primitive: the (0,2) property [zero_two_graph]. *)
Definition zero_two_graph (G : sgraph) : Prop :=
  forall u v : G, u != v ->
    #|common_nbr u v| = 0 \/ #|common_nbr u v| = 2.

Definition three_chromatic_0_2_graphs_statement : Prop :=
  exists G : sgraph, zero_two_graph G /\ χ([set: G]) = 3.

(** ** Row 3 — Cycles in graphs of large chromatic number
    PARTIAL (special cases proven; general open).

    Source: "If chi(G)>k, then G contains at least (k+1)(k-1)!/2 cycles of
    length 0 mod k."

    New AREA primitives: [n_cycles_len] (count of cycles of a fixed length)
    and [count_cycles_mod].  A cycle of length [L] is encoded as a closed walk
    [t : L.-tuple G] satisfying [ucycleb]; each undirected cycle is counted
    [2L] times (L rotations × 2 orientations), so we divide by [2 * L].  The
    statement is the conjecture multiplied through by 2 (so [(k+1)(k-1)!/2 ≤ c]
    becomes [(k+1)(k-1)! ≤ 2c], avoiding the halving).

    The [2 < L] filter restricts the count to GENUINE cycles: in a simple graph
    a closed walk with [size ≤ 2] is the empty walk ([ucycleb [::]] reduces to
    [true]) or a single edge ([ucycleb [x; y]] reduces to [x -- y]), neither of
    which is a cycle.  The [2 < k] guard pins the conjecture to its meaningful
    open regime: for [k = 1] take [G := 'K_2] ([χ = 2 > 1] but no genuine
    cycle, so the count is 0 and [2 * 0! = 2 ≤ 0] is FALSE), and for [k = 2]
    take a 5-cycle ([χ = 3 > 2], no even genuine cycle, count 0, again false).
    With [2 < k] the smallest [L] with [k %| L] and [0 < L] is [L = k ≥ 3], so
    the [2 < L] guard is automatically met and the [size 2] edge artefact never
    contributes. *)
Definition n_cycles_len (G : sgraph) (L : nat) : nat :=
  #|[set t : L.-tuple G | ucycleb (--) (val t)]| %/ (2 * L).

Definition count_cycles_mod (G : sgraph) (k : nat) : nat :=
  \sum_(L < #|G|.+1 | (2 < L) && (k %| L)) n_cycles_len G L.

Definition cycles_in_graphs_of_large_chromatic_number_statement : Prop :=
  forall (k : nat) (G : sgraph),
    2 < k -> k < χ([set: G]) ->
    (k.+1) * (k.-1)`! <= 2 * count_cycles_mod G k.

(** ** Row 4 — High-girth low-degree 4-chromatic graphs
    OPEN.

    Source: "Do there exist 4-regular 4-chromatic graphs of arbitrarily high
    girth?"

    Uses AREA primitives [regular] and [girth_geq]. *)
Definition high_girth_low_degree_4_chromatic_graphs_statement : Prop :=
  forall g : nat, exists G : sgraph,
    [/\ regular G 4, χ([set: G]) = 4 & girth_geq G g].

(** ** Row 5 — Erdős–Faber–Lovász conjecture
    SOLVED for all large n (Kang–Kelly–Kühn–Methuku–Osthus, 2023); stated here
    as a Definition only.

    Source: "If G is a simple graph which is the union of k pairwise
    edge-disjoint complete graphs, each with k vertices, then chi(G) = k."

    New AREA primitive: [edge_disjoint_clique_union].  "Pairwise edge-disjoint"
    is encoded as: distinct cliques share at most one vertex (two shared
    vertices would be a shared edge). *)
Definition edge_disjoint_clique_union (G : sgraph) (k : nat) : Prop :=
  exists cliqs : 'I_k -> {set G},
    [/\ (forall i, #|cliqs i| = k),
        (forall i, clique (cliqs i)),
        (forall i j, i != j -> #|cliqs i :&: cliqs j| <= 1),
        (forall x : G, exists i, x \in cliqs i)
      & (forall x y : G, x -- y -> exists i, (x \in cliqs i) && (y \in cliqs i))].

Definition erdos_faber_lovasz_statement : Prop :=
  forall (k : nat) (G : sgraph),
    edge_disjoint_clique_union G k -> χ([set: G]) = k.

(** ** Row 6 — Borodin–Kostochka conjecture
    OPEN.

    Source: "Every graph with maximum degree Delta >= 9 has chromatic number at
    most max{Delta-1, omega}." *)
Definition the_borodin_kostochka_statement : Prop :=
  forall G : sgraph,
    9 <= Delta G -> χ([set: G]) <= maxn (Delta G - 1) ω([set: G]).

(** ** Row 7 — Vertex colouring of graph fractional powers
    PARTIAL (special cases proven; general open).

    Source: "G^{m/n} := (G^{1/n})^m, where G^{1/n} is the n-subdivision
    (replace each edge by a path of length n) and G^m the m-th power (join
    vertices at distance <= m).  Conjecture: for connected G with Delta(G)>=3
    and integer m>1, for any n>m, chi(G^{m/n}) = omega(G^{m/n})."

    New AREA primitives: [graph_power], [subdivision], [frac_power].  Both
    constructions are produced as genuine [sgraph]s; their edge relations are
    made symmetric/irreflexive by construction (an OR with the reversed
    relation), so the [sgraph] proofs are immediate.

    [@MOVE-to-base] [graph_power], [subdivision] and [frac_power] are pure,
    colouring-free [sgraph] constructions (m-th power and n-subdivision of an
    arbitrary graph) reused across structural/topological areas; they are base
    candidates once G3 lands, tracked here only because base does not exist
    yet.  NB on the boundary: [subdivision G n] degenerates to an edgeless
    graph for [n ≤ 1] (no internal vertices); Row 7's guard [1 < m < n] keeps
    [n ≥ 3], but a future base move should document/repair the [n ≤ 1] corner. *)

(** *** The m-th power G^m *)
Section Power.
Variables (G : sgraph) (m : nat).

(** Closed [k]-ball around [x]: vertices reachable from [x] in ≤ [k] steps. *)
Fixpoint ball (k : nat) (x : G) : {set G} :=
  if k is k'.+1 then ball k' x :|: \bigcup_(z in ball k' x) N(z)
  else [set x].

Definition reach_le (x y : G) : bool := y \in ball m x.

(** Adjacency of the power graph: distinct vertices within distance [m]
    (the OR makes symmetry free; reachability is already symmetric). *)
Definition pow_rel : rel G :=
  fun x y => (x != y) && (reach_le x y || reach_le y x).

Lemma pow_sym : symmetric pow_rel.
Proof. by move=> x y; rewrite /pow_rel eq_sym orbC. Qed.

Lemma pow_irrefl : irreflexive pow_rel.
Proof. by move=> x; rewrite /pow_rel eqxx. Qed.

Definition graph_power : sgraph := SGraph pow_sym pow_irrefl.
End Power.

(** *** The n-subdivision G^{1/n} *)
Section Subdivision.
Variables (G : sgraph) (n : nat).

(** Canonically oriented edges (each undirected edge once, low endpoint first
    in the finType enumeration order). *)
Definition oedge (p : G * G) : bool :=
  (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N.

Local Notation EdgeT := {p : G * G | oedge p}.

Definition lo (e : EdgeT) : G := (val e).1.
Definition hi (e : EdgeT) : G := (val e).2.

(** Vertices of the n-subdivision: original vertices, plus [n-1] internal
    vertices per edge. *)
Definition SubVert : Type := (G + (EdgeT * 'I_n.-1))%type.

(** Oriented raw relation: endpoint [lo e] meets internal position [0],
    endpoint [hi e] meets internal position [n-2], consecutive internal
    positions of one edge are adjacent.  Symmetrized below. *)
Definition sub_r0 (x y : SubVert) : bool :=
  match x, y with
  | inl _, inl _ => false
  | inl a, inr (e, i) =>
      ((a == lo e) && (val i == 0)) || ((a == hi e) && (val i == n.-1.-1))
  | inr _, inl _ => false
  | inr (e, i), inr (e', j) => (e == e') && ((val i).+1 == val j)
  end.

Definition sub_rel (x y : SubVert) : bool := sub_r0 x y || sub_r0 y x.

Lemma sub_sym : symmetric sub_rel.
Proof. by move=> x y; rewrite /sub_rel orbC. Qed.

Lemma sub_irrefl : irreflexive sub_rel.
Proof.
move=> x; rewrite /sub_rel orbb; case: x => [a|[e i]] //=.
by rewrite eqxx /= (gtn_eqF (ltnSn _)).
Qed.

Definition subdivision : sgraph := SGraph sub_sym sub_irrefl.
End Subdivision.

(** The fractional power G^{m/n} = (G^{1/n})^m. *)
Definition frac_power (G : sgraph) (m n : nat) : sgraph :=
  graph_power (subdivision G n) m.

Definition vertex_coloring_of_graph_fractional_powers_statement : Prop :=
  forall (G : sgraph) (m n : nat),
    connected [set: G] -> 3 <= Delta G -> 1 < m -> m < n ->
    χ([set: frac_power G m n]) = ω([set: frac_power G m n]).

(** ** Row 8 — Melnikov's valency-variety problem
    OPEN.

    Source: "The valency-variety w(G) of a graph G is the number of different
    degrees in G.  Is the chromatic number of any graph G with at least two
    vertices greater than ceil( floor(w(G)/2) / (|V(G)| - w(G)) )?"

    New AREA primitive: [valency_variety] (number of distinct vertex degrees). *)
Definition valency_variety (G : sgraph) : nat :=
  size (undup [seq #|N(x)| | x <- enum [set: G]]).

Definition melnikovs_valency_variety_statement : Prop :=
  forall G : sgraph, 2 <= #|G| ->
    ceil_div (valency_variety G %/ 2) (#|G| - valency_variety G)
      < χ([set: G]).

(** ** Row 9 — Reed's ω, Δ and χ conjecture
    OPEN.

    Source: "Conjecture: chi(G) <= ceil( (1/2)(Delta(G)+1) + (1/2)omega(G) )
    for every graph G."  Stated in the doubled, subtraction-free form
    [2·chi ≤ (Δ+1) + ω + 1]. *)
Definition reeds_omega_delta_and_chi_statement : Prop :=
  forall G : sgraph, 0 < #|G| ->
    2 * χ([set: G]) <= Delta G + 1 + ω([set: G]) + 1.
