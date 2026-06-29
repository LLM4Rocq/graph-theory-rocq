(** * Extremal.conjectures.D2chr — milestone D2chr (namespace Extremal, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of ten open/partial problems on FRACTIONAL, CIRCULAR and LIST
    colouring and the fractional Hadwiger number.

    CORE undirected vocabulary comes from graph-theory-base (GTBase.base):
    [sgraph], [x -- y], [N], [χ]=[chi_mem], [Delta] (Δ), [connected], [triangle_free],
    [complete]=['K_n], [graph_power], [is_choice_number], [wagner_planar] (the
    combinatorial Wagner planarity façade: no K5 / K3,3 minor).  [GraphTheory.minor]
    supplies [minor G H] ("H is a minor of G") for the Hadwiger rows.  [all_algebra]
    supplies [int]/[absz], [rat] (for χ_f, χ_c, had_f, the choosability threshold),
    and [rcfType]/[matrix] (for the R^3 orthogonality graph).  The shared circular
    layer ([pq_colouring], [is_circular_chromatic], parametric in an abstract
    [adj : V -> V -> bool]) lives in [Extremal.foundations.circular_colouring].

    CARRIER TYPES (per row.rocq_idiom):
      - [sgraph] for the fractional/list/circular rows on finite graphs (1,2,3,5,6,7,8);
      - finite [{ffun 'I_n -> 'I_n}] matchings + sign function for the perfect-matching
        weight row (4);
      - the infinite geometric graph on [{ }'rV[R]_3] (R : rcfType), perpendicularity
        adjacency, for the orthogonality row (9).

    PARTIAL / abstraction notes:
      - Row 1 [is_fractional_hadwiger] gives the LP relaxation of the (clique-minor)
        Hadwiger number — a faithful but definitional choice of the fractional value.
      - Row 2 (mixing) is PARTIAL: the genuine object M_c(G) is a REAL number and the
        question is whether it is rational; with no real-number / recolouring-dynamics
        layer we model the recolouring graph by single-vertex moves under [connect] and
        state the existence of a RATIONAL attained mixing threshold (the cleanest
        faithful core of "is M_c(G) always rational?").
      - Row 9 quantifies over every real-closed field [R : rcfType] (the reals R are one
        instance); the vertices are nonzero 3-vectors with perpendicularity adjacency,
        the natural representative model of the lines-through-the-origin graph. *)

From GTBase Require Export base.
From GraphTheory Require Import minor.
From Extremal.foundations Require Export circular_colouring.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ** Row 1 — Fractional Hadwiger conjecture (OPEN).
    "For every graph G: (a) χ_f(G) ≤ had(G); (b) χ(G) ≤ had_f(G); (c) χ_f(G) ≤ had_f(G)."

    AREA primitives:
      - [bfold_colouring]/[is_fractional_chromatic] : χ_f via (a:b)-colourings (each
        vertex an b-subset of an a-palette, adjacent vertices disjoint); χ_f = inf a/b,
        attained (rational for finite G);
      - [is_hadwiger] : had(G) = largest h with a K_h minor (via base [minor]);
      - [frac_clique_minor]/[is_fractional_hadwiger] : had_f(G) = the LP relaxation —
        rational weights on connected, pairwise-adjacent branch sets, each vertex
        covered with total weight ≤ 1, maximise the total weight (0/1 weights recover
        a clique minor, so the optimum is had_f ≥ had). *)
Definition bfold_colouring (G : sgraph) (a b : nat) (f : G -> {set 'I_a}) : Prop :=
  (forall v, #|f v| = b) /\ (forall x y : G, x -- y -> [disjoint f x & f y]).

Definition is_fractional_chromatic (G : sgraph) (r : rat) : Prop :=
  (exists a b : nat, (0 < b)%N /\ (exists f, @bfold_colouring G a b f) /\ r = a%:Q / b%:Q) /\
  (forall a b : nat, (0 < b)%N -> (exists f, @bfold_colouring G a b f) -> r <= a%:Q / b%:Q).

Definition is_hadwiger (G : sgraph) (h : nat) : Prop :=
  minor G 'K_h /\ (forall h', minor G 'K_h' -> (h' <= h)%N).

Definition frac_clique_minor (G : sgraph) (n : nat)
    (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r : rat) : Prop :=
  [/\ (forall i, 0 <= w i),
      (forall i, connected (B i)),
      (forall i j, i != j -> exists x y : G, [/\ x \in B i, y \in B j & x -- y]),
      (forall v : G, (\sum_(i | v \in B i) w i <= 1)%R)
    & r = \sum_i w i].

Definition is_fractional_hadwiger (G : sgraph) (r : rat) : Prop :=
  (exists (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat), frac_clique_minor B w r) /\
  (forall (n : nat) (B : 'I_n -> {set G}) (w : 'I_n -> rat) (r' : rat),
     frac_clique_minor B w r' -> r' <= r).

Definition fractional_hadwiger_statement : Prop :=
  forall (G : sgraph) (xf hf : rat) (h : nat),
    (0 < #|G|)%N ->
    is_fractional_chromatic G xf -> is_hadwiger G h -> is_fractional_hadwiger G hf ->
    [/\ xf <= h%:Q,
        (χ([set: G]))%:Q <= hf
      & xf <= hf ].

(** ** Row 2 — Is the colouring-mixing threshold M_c(G) always rational? (OPEN; PARTIAL).
    The recolouring graph on the [(p,q)]-colourings (single-vertex moves); [circ_mixing]
    says it is connected (all valid colourings reachable). M_c(G) is the INFIMUM p/q over
    mixing pairs; the statement asserts this infimum is RATIONAL for every G — the
    faithful core of the rationality question (NO attainment is required: [r] is modelled
    as the greatest lower bound, not as an attained minimum). *)

(** [pqb G p q c] is the decidable (boolean) reflection of the shared Prop-level
    [pq_colouring (fun x y => x -- y) p q (fun v => c v : nat)] (foundations): the
    [c v < p] clause is discharged by the ['I_p] carrier, and the [q <= |.| <= p-q]
    edge condition is the same notion, recast over [{ffun G -> 'I_p}] because
    [connect]/[rel] require a boolean adjacency. *)
Definition pqb (G : sgraph) (p q : nat) (cf : {ffun G -> 'I_p}) : bool :=
  [forall x : G, [forall y : G, (x -- y) ==>
     ((q <= absz (Posz (cf x) - Posz (cf y)))%N &&
      (absz (Posz (cf x) - Posz (cf y)) <= p - q)%N)]].

Definition recolour_adj (G : sgraph) (p q : nat) : rel {ffun G -> 'I_p} :=
  fun c c' => [&& @pqb G p q c, @pqb G p q c' & #|[set v | c v != c' v]| == 1%N].

Definition circ_mixing (G : sgraph) (p q : nat) : Prop :=
  forall c c' : {ffun G -> 'I_p},
    @pqb G p q c -> @pqb G p q c' -> connect (@recolour_adj G p q) c c'.

(** A NON-TRIVIAL mixing pair: a genuine circular regime [2*q <= p] (every edge of a
    nonempty graph forces [p >= 2q]) in which an actual valid colouring exists AND the
    recolouring graph is connected.  The colourability + [2*q <= p] guards block the
    spurious empty-palette pair [p = 0] (under which [pqb] holds vacuously) from
    dragging the infimum down to a meaningless [0]. *)
Definition mixing_pair (G : sgraph) (p q : nat) : Prop :=
  [/\ (0 < q)%N, (2 * q <= p)%N, (exists c : {ffun G -> 'I_p}, @pqb G p q c)
    & circ_mixing G p q].

(** [r = M_c(G)] as the INFIMUM (greatest lower bound) of the ratios [p/q] over mixing
    pairs: [r] is a lower bound (clause 1) and the greatest such (clause 2).  Then
    [exists r : rat, is_colouring_mixing_threshold G r] holds exactly when this real
    infimum is rational — faithfully "is M_c(G) always rational?", with no spurious
    attainment. *)
Definition is_colouring_mixing_threshold (G : sgraph) (r : rat) : Prop :=
  (forall p q : nat, mixing_pair G p q -> r <= p%:Q / q%:Q) /\
  (forall s : rat,
     (forall p q : nat, mixing_pair G p q -> s <= p%:Q / q%:Q) -> s <= r).

Definition mixing_circular_colourings_0_statement : Prop :=
  forall G : sgraph, exists r : rat, is_colouring_mixing_threshold G r.

(** ** Row 3 — List chromatic number vs maximum degree of bipartite graphs (OPEN).
    "There is a constant c with χ_ℓ(G) ≤ c·log Δ for every bipartite G of max degree Δ."
    The logarithm is removed by exponentiating: [ch ≤ c·log₂ Δ ⟺ 2^ch ≤ Δ^c].
    [bipartite] = 2-colourable (χ ≤ 2); the guard [2 ≤ Δ] excludes the degenerate
    small-degree regime where log Δ vanishes.

    [@MOVE-to-base] [bipartite] is a generic cross-area chromatic primitive (not yet in
    GTBase.base); migrate it to base when a 2nd area needs it. *)
Definition bipartite (G : sgraph) : Prop := (χ([set: G]) <= 2)%N.

Definition list_chromatic_number_and_maximum_degree_of_bipartit_statement : Prop :=
  exists c : nat,
    forall (G : sgraph) (m : nat),
      bipartite G -> (2 <= Delta G)%N -> is_choice_number G m ->
      (2 ^ m <= (Delta G) ^ c)%N.

(** ** Row 4 — Monochromatic colorings inherited from perfect matchings (OPEN).
    "For which (n,d) is there a bi-colored graph on n vertices and d colors such that all
    d monochromatic colorings have unit weight and every other coloring cancels?"

    AREA primitives [bicolored_unit] / [coloring_weight]: the bicoloring is a sign
    function [sgn] on vertex pairs; a perfect matching is a fixed-point-free involution
    [m]; [match_weight] = ∏_{i < m i} sgn i (m i); [coloring_weight c] = the signed sum,
    over perfect matchings whose every matched pair is monochromatic under [c], of
    [match_weight].  [bicolored_unit n d]: a sign function exists for which every constant
    (monochromatic) colouring has weight 1 and every non-constant colouring has weight 0.
    The "for which (n,d)" question is encoded as the existence of at least one nontrivial
    [(n,d)] with this property (the full characterisation of the admissible set is the
    open content). *)
Definition pmatch (n : nat) (m : {ffun 'I_n -> 'I_n}) : bool :=
  [forall i, (m (m i) == i) && (m i != i)].

Definition match_weight (n : nat) (sgn : 'I_n -> 'I_n -> int) (m : {ffun 'I_n -> 'I_n}) : int :=
  \prod_(i : 'I_n | (i < m i)%N) sgn i (m i).

Definition coloring_weight (n d : nat) (sgn : 'I_n -> 'I_n -> int) (c : 'I_n -> 'I_d) : int :=
  \sum_(m : {ffun 'I_n -> 'I_n} | pmatch m && [forall i, c (m i) == c i]) match_weight sgn m.

Definition bicolored_unit (n d : nat) : Prop :=
  exists sgn : 'I_n -> 'I_n -> int,
    (* bi-coloured: [sgn] is a genuine 2-valued sign, not an arbitrary weight *)
    (forall i j : 'I_n, sgn i j = 1 \/ sgn i j = -1) /\
    (forall (k : 'I_d) (c : 'I_n -> 'I_d),
        (forall i, c i = k) -> @coloring_weight n d sgn c = (1 : int)) /\
    (forall c : 'I_n -> 'I_d,
        ~ (exists k : 'I_d, forall i, c i = k) -> @coloring_weight n d sgn c = (0 : int)).

Definition monochromatic_vertex_colorings_inherited_from_perfec_statement : Prop :=
  exists n d : nat, (2 <= d)%N /\ (0 < n)%N /\ bicolored_unit n d.

(** ** Row 5 — Choosability of graph powers (Noel, 2013) (OPEN).
    "Does there exist f(k)=o(k²) with ch(G²) ≤ f(χ(G²)) for every graph G?"
    [graph_power G 2] = G²; [is_o_ksq] is the ε–N rendering of o(k²):
    for every c>0, eventually [c·f(k) ≤ k²] (i.e. f(k)/k² → 0). *)
Definition is_o_ksq (f : nat -> nat) : Prop :=
  forall c : nat, (0 < c)%N -> exists N, forall k, (N <= k)%N -> (c * f k <= k * k)%N.

Definition choosability_of_graph_powers_statement : Prop :=
  exists f : nat -> nat, is_o_ksq f /\
    forall (G : sgraph) (chG m : nat),
      χ([set: graph_power G 2]) = chG ->
      is_choice_number (graph_power G 2) m ->
      (m <= f chG)%N.

(** ** Row 6 — Circular choosability of planar graphs (OPEN; best bound asked).
    Following the source: a [t]-[(p,q)]-list-assignment gives each vertex a list
    [L v ⊆ {0,…,p-1}] with [|L v| ≥ t·q]; [G] is [t]-[(p,q)]-choosable if every such
    [L] admits a [(p,q)]-colouring picking [c v ∈ L v]; [G] is circularly [t]-choosable
    if [t]-[(p,q)]-choosable for all [p,q]; cch(G) = inf{t ≥ 1 : circularly t-choosable}.
    The Problem ("best upper bound over planar graphs") is the LEAST [B] bounding cch on
    every (Wagner-)planar graph. *)
Definition t_pq_choosable (G : sgraph) (t : rat) (p q : nat) : Prop :=
  forall L : G -> {set 'I_p},
    (forall v, t * q%:Q <= (#|L v|)%:Q) ->
    exists c : G -> 'I_p,
      pq_colouring (fun x y : G => x -- y) p q (fun v => (c v : nat)) /\
      (forall v, c v \in L v).

Definition circularly_t_choosable (G : sgraph) (t : rat) : Prop :=
  forall p q : nat, (0 < q)%N -> t_pq_choosable G t p q.

Definition is_circular_choosability (G : sgraph) (b : rat) : Prop :=
  [/\ (1 <= b)%R,
      (forall t : rat, b < t -> circularly_t_choosable G t)
    & (forall t : rat, 1 <= t -> circularly_t_choosable G t -> b <= t)].

Definition circular_choosability_of_planar_graphs_statement : Prop :=
  exists B : rat,
    (forall (G : sgraph) (b : rat),
        wagner_planar G -> is_circular_choosability G b -> b <= B) /\
    (forall B' : rat,
        (forall (G : sgraph) (b : rat),
            wagner_planar G -> is_circular_choosability G b -> b <= B') ->
        B <= B').

(** ** Row 7 — Star chromatic index of complete graphs (OPEN).
    "Is χ'_s(K_n) linear in n, i.e. O(n)?"  A star edge colouring is a proper edge
    colouring (adjacent edges differ) with NO bichromatic path or cycle on 4 edges
    (the colour set on the 4 edges has size ≥ 3).  [is_star_chromatic_index] is the least
    number of colours; the statement is the eventual linear bound [k ≤ c·n].

    BASE-REUSE NOTE: base's edge-colouring layer (line_graph / chromatic_index χ' /
    edge_colourable) exposes only a colour COUNT, not a colour assignment; the star
    constraints (no bichromatic P4/C4) need the explicit colour FUNCTION [f] on edges,
    so base's χ' cannot express them and a local [proper_ec] is required.  The genuinely
    new star primitives below carry a [@MOVE-to-base] tag for future migration. *)
Definition proper_ec (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  (forall x y : G, f x y = f y x) /\
  (forall x y z : G, x -- y -> x -- z -> y != z -> f x y != f x z).

Definition no_bichromatic_P4 (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  forall a b c d e : G,
    uniq [:: a; b; c; d; e] -> a -- b -> b -- c -> c -- d -> d -- e ->
    (2 < #|[set f a b; f b c; f c d; f d e]|)%N.

Definition no_bichromatic_C4 (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  forall a b c d : G,
    uniq [:: a; b; c; d] -> a -- b -> b -- c -> c -- d -> d -- a ->
    (2 < #|[set f a b; f b c; f c d; f d a]|)%N.

(** [@MOVE-to-base] [star_edge_colouring] / [is_star_chromatic_index] extend base's
    edge-colouring layer with the star (no bichromatic P4/C4) constraints; migrate to
    base when a 2nd area needs the star chromatic index. *)
Definition star_edge_colouring (G : sgraph) (C : finType) (f : G -> G -> C) : Prop :=
  [/\ proper_ec f, no_bichromatic_P4 f & no_bichromatic_C4 f].

Definition star_edge_k_colourable (G : sgraph) (k : nat) : Prop :=
  exists f : G -> G -> 'I_k, star_edge_colouring f.

Definition is_star_chromatic_index (G : sgraph) (k : nat) : Prop :=
  star_edge_k_colourable G k /\
  (forall k', star_edge_k_colourable G k' -> (k <= k')%N).

Definition star_chromatic_index_of_complete_graphs_statement : Prop :=
  exists c N : nat,
    forall (n k : nat),
      (N <= n)%N -> is_star_chromatic_index (complete n) k -> (k <= c * n)%N.

(** ** Row 8 — Circular chromatic number of triangle-free planar cubic graphs (OPEN).
    "Does every triangle-free planar graph of maximum degree 3 have χ_c ≤ 20/7?"
    χ_c via the shared [is_circular_chromatic]; planarity via base [wagner_planar]. *)
Definition circular_chromatic_number_of_triangle_free_planar_gr_statement : Prop :=
  forall (G : sgraph) (r : rat),
    triangle_free G -> wagner_planar G -> (Delta G <= 3)%N ->
    is_circular_chromatic (fun x y : G => x -- y) r -> r <= 20%:Q / 7%:Q.

(** ** Row 9 — Circular colouring of the orthogonality graph (OPEN; PARTIAL/geometric).
    O has vertex set the lines through the origin in R^3, two adjacent iff perpendicular;
    Problem: is χ_c(O) = 4?  Modelled, over any real-closed field [R], on nonzero
    3-vectors with perpendicularity ([dot product = 0]) adjacency — the natural
    representative model of the lines graph; the shared [is_circular_chromatic] applies
    unchanged to this INFINITE vertex type. *)
Definition perp (R : rcfType) (u v : 'rV[R]_3) : bool :=
  [&& (u != 0), (v != 0) & ((u *m v^T) 0 0 == 0)].

Definition circular_colouring_the_orthogonality_graph_statement : Prop :=
  forall R : rcfType, is_circular_chromatic (@perp R) 4%:Q.
