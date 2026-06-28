(** * Cycle.conjectures.D1 — milestone D1 (namespace Cycle, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of fifteen open problems of FLOW theory: nowhere-zero flows,
    circular flow numbers, bidirected flows, group/B-flows, the flow polynomial,
    modular orientations, local tensions on embedded graphs, cycle-continuous
    maps and an edge-disjoint-paths approximation question.

    CARRIER per row (chosen from each row's rocq_idiom, NOT a blanket sgraph):
      - Most flow rows are undirected MULTIGRAPH statements, carrier
        coq-graph-theory's [mgraph] = [graph unit unit].  Edges carry an
        intrinsic reference orientation ([source]/[target]); a nowhere-zero
        r-flow is a real/integer edge weighting that may be negative (this
        absorbs the choice of orientation), with [1 <= |phi e| <= r-1] and
        Kirchhoff conservation [out-sum = in-sum] at every vertex.
      - Bouchet's row carries two endpoint SIGN functions on top of [mgraph]
        (a bidirected graph).
      - The cycle-continuous row carries [nat -> sgraph] (an infinite family of
        SIMPLE graphs) with the binary cycle space on its 2-element edge sets.
      - The local-tensions row carries [mgraph] + a rotation system
        [{perm (edge G * bool)}] (a combinatorial surface embedding).
      - The group/B-flow row carries two [finGroupType]s and Cayley graphs.
      - The real-roots row uses [{poly int}] and roots in any [rcfType].
      - The unit-vector row uses [ 'rV[R]_3 ] over any [rcfType] R (S^2).

    IMPORT ORDER: [mgraph] (and [sgraph], [treewidth]) are imported BEFORE
    [base] (base ships an undirected line_graph that the multigraph one would
    otherwise shadow); the mathcomp algebra/fingroup layer is imported AFTER
    [base] so its canonical [int]/[rat]/order instances win (importing it before
    [base] makes ring numerals lose their order instance).  The shared
    multigraph vocabulary ([mdeg], [cut], [bridgeless], [mconnected],
    [edge_connected], [is_circuit], ...) mirrors cycle-theory U6 but is INLINED
    here (kept self-contained rather than importing U6).

    AREA primitives introduced here (flow-theory specific): all the flow
    families ([iconservative]/[rconservative]/[int_bounded]/[has_nz_kflow]/
    [has_nz_kflow_del]/[has_nz_rflow]/[circular_flow_number_le]), [is_2t1_graph],
    [mreg], [mDelta]/[is_class1], the bidirected primitives ([is_sign]/[bnet]/
    [has_nz_biflow]), [petersen]/[mg_minor], [imbalance], [nullity]/[flow_poly]/
    [flow_poly_eval], the embedded-graph primitives ([faces]/[fbound]/
    [contractible]/[edge_width_geq]/[local_tension]), Cayley graphs + [Bflow],
    the cycle space ([sedge]/[in_cycle_space]/[cycle_continuous]) and the
    edge-disjoint-paths primitives ([routes]/[edp_feasible]/[frac_feasible]/
    [mtreewidth_le]).  [two_edge_connected] is tagged [@MOVE-to-base]. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import mgraph sgraph treewidth.
From GTBase Require Import base.
From mathcomp Require Import all_algebra all_fingroup.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(** ================================================================= *)
(** ** Reused multigraph vocabulary (self-contained, mirroring U6) *)

(** Multigraph degree, edge cut, connectivity, edge-connectivity, bridges.
    [@MOVE-to-base]: mdeg/mreg/mDelta are genuinely new multigraph primitives
    (base only ships sgraph-level [Delta]/[regular]); tagged for migration to
    base once a second area needs the multigraph degree vocabulary. *)
Definition mdeg (G : mgraph) (v : G) : nat := #|edges_at v|.
Definition cut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e | (source e \in S) (+) (target e \in S)].
Definition mconnected (G : mgraph) : Prop :=
  forall x y : G, exists w, uwalk x y w.
Definition connected_del_edges (G : mgraph) (S : {set edge G}) : Prop :=
  forall x y : G, exists w, uwalk x y w /\ all (fun e => e \notin S) w.
Definition edge_connected (G : mgraph) (k : nat) : Prop :=
  forall E : {set edge G}, (#|E| < k)%N -> connected_del_edges E.
Definition is_bridge (G : mgraph) (e : edge G) : Prop :=
  eseparates (source e) (target e) [set e].
Definition bridgeless (G : mgraph) : Prop := forall e : edge G, ~ is_bridge e.

(** Circuits (single cycles) as edge sets. *)
Definition subdeg (G : mgraph) (H : {set edge G}) (v : G) : nat :=
  #|edges_at v :&: H|.
Definition subgraph_kregular (G : mgraph) (H : {set edge G}) (k : nat) : Prop :=
  forall v : G, subdeg H v = 0 \/ subdeg H v = k.
Definition walk_in (G : mgraph) (H : {set edge G}) (x y : G)
    (w : seq (edge G)) : bool := uwalk x y w && all (fun e => e \in H) w.
Definition H_inc (G : mgraph) (H : {set edge G}) (x : G) : bool :=
  [exists e, (e \in H) && incident x e].
Definition subgraph_connected (G : mgraph) (H : {set edge G}) : Prop :=
  forall x y : G, H_inc H x -> H_inc H y -> exists w, walk_in H x y w.
Definition is_circuit (G : mgraph) (C : {set edge G}) : Prop :=
  [/\ C != set0, subgraph_kregular C 2 & subgraph_connected C].

(** ================================================================= *)
(** ** Shared flow infrastructure (mgraph, intrinsic [source]/[target]) *)

(** Kirchhoff conservation for an integer / rational edge weighting: the total
    weight on the edges leaving [v] equals the total weight on the edges
    entering [v] (loops cancel, negative weights reverse the reference
    orientation). *)
Definition iconservative (G : mgraph) (phi : edge G -> int) : Prop :=
  forall v : G, \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e.

Definition rconservative (G : mgraph) (phi : edge G -> rat) : Prop :=
  forall v : G, \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e.

(** Nowhere-zero [k]-bounds for an integer flow: [1 <= |phi e| <= k-1]. *)
Definition int_bounded (G : mgraph) (k : nat) (phi : edge G -> int) : Prop :=
  forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= (k.-1)%:R)%R.

(** [G] has a nowhere-zero [k]-flow (integer formulation). *)
Definition has_nz_kflow (G : mgraph) (k : nat) : Prop :=
  exists phi : edge G -> int, iconservative phi /\ int_bounded k phi.

(** [G \ A] (delete the edge set [A]) has a nowhere-zero [k]-flow: a flow
    supported off [A], conservative on the whole vertex set. *)
Definition has_nz_kflow_del (G : mgraph) (A : {set edge G}) (k : nat) : Prop :=
  exists phi : edge G -> int,
    [/\ iconservative phi,
        (forall e : edge G, e \in A -> phi e = 0)
      & (forall e : edge G, e \notin A ->
           (1 <= `|phi e|)%R /\ (`|phi e| <= (k.-1)%:R)%R)].

(** Nowhere-zero real [r]-flow (rational values suffice and are faithful): a
    rational conservative weighting with [1 <= |phi e| <= r-1]. *)
Definition has_nz_rflow (G : mgraph) (r : rat) : Prop :=
  exists phi : edge G -> rat,
    rconservative phi /\
    (forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= r - 1)%R).

(** Circular flow number bound [F_c(G) <= c]: since the set of feasible [r] is
    an up-set, [F_c(G) = inf {r | G has a nz r-flow} <= c] iff [G] has a
    nowhere-zero [r]-flow for every rational [r > c]. *)
Definition circular_flow_number_le (G : mgraph) (c : rat) : Prop :=
  forall r : rat, (c < r)%R -> has_nz_rflow G r.

(** ** [(2t+1)]-graphs and regularity (multigraph degree [mdeg] from U6) *)

(** [d]-regular multigraph.  [@MOVE-to-base] (see mdeg note above). *)
Definition mreg (G : mgraph) (d : nat) : Prop := forall v : G, mdeg v = d.

(** A [(2t+1)]-graph: [(2t+1)]-regular and every odd vertex set has an edge cut
    of size at least [2t+1]. *)
Definition is_2t1_graph (G : mgraph) (t : nat) : Prop :=
  mreg G (2 * t + 1)%N /\
  (forall X : {set G}, odd #|X| -> (2 * t + 1 <= #|cut X|)%N).

(** Maximum multigraph degree and the class-1 property (χ'(G) = Δ(G)).
    [@MOVE-to-base] (see mdeg note above). *)
Definition mDelta (G : mgraph) : nat := \max_(v : G) mdeg v.
Definition is_class1 (G : mgraph) : Prop := chromatic_index G = mDelta G.

(** 2-edge-connected = connected and bridgeless.  [@MOVE-to-base]. *)
Definition two_edge_connected (G : mgraph) : Prop :=
  mconnected G /\ bridgeless G.

(** ================================================================= *)
(** ** Row 1 — Circular flow numbers of [(2t+1)]-graphs *)
(** OPEN.

    Source: "A [(2t+1)]-graph is [(2t+1)]-regular with [|∂_G(X)| >= 2t+1] for
    every odd [X].  If [t > 1] and [G] is a [(2t+1)]-graph then
    [F_c(G) <= 2 + 2/t]." *)
Definition circular_flow_numbers_of_r_graphs_statement : Prop :=
  forall (t : nat) (G : mgraph),
    (1 < t)%N -> (0 < #|G|)%N -> is_2t1_graph G t ->
    circular_flow_number_le G (2%:R + 2%:R / t%:R).

(** ================================================================= *)
(** ** Bidirected graphs and Bouchet's 6-flow conjecture *)

Definition is_sign (s : int) : bool := (s == 1) || (s == -1).

(** Bidirected graph = an [mgraph] with a sign [±1] at each endpoint of each
    edge ([ss] at the [source]-end, [st] at the [target]-end). *)
Definition is_bidirected (G : mgraph) (ss st : edge G -> int) : Prop :=
  forall e : edge G, is_sign (ss e) /\ is_sign (st e).

(** Bidirected vertex balance: the signed sum of incident edge weights at [v]. *)
Definition bnet (G : mgraph) (ss st : edge G -> int) (phi : edge G -> int)
    (v : G) : int :=
  \sum_(e | source e == v) ss e * phi e + \sum_(e | target e == v) st e * phi e.

(** [G] (with signature [ss],[st]) has a nowhere-zero [k]-flow. *)
Definition has_nz_biflow (G : mgraph) (ss st : edge G -> int) (k : nat) : Prop :=
  exists phi : edge G -> int,
    (forall v : G, bnet ss st phi v = 0) /\
    (forall e : edge G, (1 <= `|phi e|)%R /\ (`|phi e| <= (k.-1)%:R)%R).

(** ** Row 2 — Bouchet's 6-flow conjecture *)
(** OPEN.

    Source: "Every bidirected graph with a nowhere-zero [k]-flow for some [k]
    has a nowhere-zero 6-flow." *)
Definition bouchets_6_flow_statement : Prop :=
  forall (G : mgraph) (ss st : edge G -> int),
    (0 < #|edge G|)%N -> is_bidirected ss st ->
    (exists k : nat, has_nz_biflow ss st k) -> has_nz_biflow ss st 6.

(** ================================================================= *)
(** ** Cycle space of a simple graph and cycle-continuous maps *)

(** The (2-element) edge set of a simple graph, as a set of vertex pairs. *)
Definition sedge (G : sgraph) : {set {set G}} :=
  [set e : {set G} | [exists x, [exists y, (x -- y) && (e == [set x; y])]]].

(** Binary cycle space: an even subgraph (every vertex has even degree). *)
Definition in_cycle_space (G : sgraph) (C : {set {set G}}) : Prop :=
  C \subset sedge G /\
  (forall v : G, ~~ odd #|[set e in C | v \in e]|).

(** A cycle-continuous map [f : E(G) -> E(H)]: it sends edges to edges and the
    pre-image of every cycle-space element of [H] is a cycle-space element
    of [G]. *)
Definition cycle_continuous (G H : sgraph) (f : {set G} -> {set H}) : Prop :=
  (forall e : {set G}, e \in sedge G -> f e \in sedge H) /\
  (forall C : {set {set H}}, in_cycle_space C ->
     in_cycle_space [set e in sedge G | f e \in C]).

(** ** Row 3 — Antichains in the cycle-continuous order *)
(** OPEN (Problem).

    Source: "Does there exist an infinite set of graphs [{G_1,G_2,...}] so that
    there is no cycle-continuous mapping between [G_i] and [G_j] whenever
    [i != j]?"  (Each member has at least one edge, to exclude the degenerate
    edgeless family.) *)
Definition antichains_in_the_cycle_continuous_order_statement : Prop :=
  exists Gs : nat -> sgraph,
    (forall i : nat, sedge (Gs i) != set0) /\
    (forall i j : nat, i <> j ->
       ~ exists f : {set (Gs i)} -> {set (Gs j)}, cycle_continuous f).

(** ================================================================= *)
(** ** Edge-connectivity flows: 3-flow, 4-flow, 5-flow *)

(** ** Row 4 — Tutte's 3-flow conjecture *)
(** OPEN.

    Source: "Every 4-edge-connected graph has a nowhere-zero 3-flow." *)
Definition three_flow_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> edge_connected G 4 -> has_nz_kflow G 3.

(** Minor model of a simple graph [H] inside a multigraph [G]: disjoint
    nonempty connected branch sets, one per vertex of [H], joined by an edge of
    [G] whenever the corresponding vertices are adjacent in [H]. *)
Definition mg_branch_connected (G : mgraph) (A : {set G}) : Prop :=
  forall x y : G, x \in A -> y \in A ->
    exists w : seq (edge G),
      uwalk x y w /\ all (fun e => (source e \in A) && (target e \in A)) w.

Definition mg_minor (G : mgraph) (H : sgraph) : Prop :=
  exists phi : H -> {set G},
    [/\ (forall x : H, phi x != set0),
        (forall x y : H, x != y -> [disjoint phi x & phi y]),
        (forall x : H, mg_branch_connected (phi x))
      & (forall x y : H, x -- y -> exists e : edge G,
           ((source e \in phi x) && (target e \in phi y)) ||
           ((source e \in phi y) && (target e \in phi x)))].

(** The Petersen graph on [ 'I_10 ]: outer 5-cycle [0..4], spokes [i ~ i+5],
    inner pentagram on [5..9]. *)
Definition pedges : seq (nat * nat) :=
  [:: (0,1); (1,2); (2,3); (3,4); (4,0);
      (0,5); (1,6); (2,7); (3,8); (4,9);
      (5,7); (7,9); (9,6); (6,8); (8,5) ]%N.
Definition pconn (a b : nat) : bool := ((a, b) \in pedges) || ((b, a) \in pedges).
Definition padj (x y : 'I_10) : bool := (x != y) && pconn (val x) (val y).

Lemma padj_sym : symmetric padj.
Proof. by move=> x y; rewrite /padj /pconn eq_sym orbC. Qed.

Lemma padj_irrefl : irreflexive padj.
Proof. by move=> x; rewrite /padj eqxx. Qed.

Definition petersen : sgraph := SGraph padj_sym padj_irrefl.

(** ** Row 6 — Tutte's 4-flow conjecture *)
(** OPEN.

    Source: "Every bridgeless graph with no Petersen minor has a nowhere-zero
    4-flow." *)
Definition four_flow_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> bridgeless G -> ~ mg_minor G petersen ->
    has_nz_kflow G 4.

(** ** Row 7 — Tutte's 5-flow conjecture *)
(** OPEN.

    Source: "Every bridgeless graph has a nowhere-zero 5-flow." *)
Definition five_flow_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> bridgeless G -> has_nz_kflow G 5.

(** ================================================================= *)
(** ** Unit-vector (S^2) flows *)

Section UnitVector.
Variable R : rcfType.

(** A unit vector of [R^3] (a point of [S^2]). *)
Definition sphere_vec (x : 'rV[R]_3) : bool := \sum_(i < 3) (x ord0 i) ^+ 2 == 1.

(** Vector flow conservation (Kirchhoff, componentwise). *)
Definition vconservative (G : mgraph) (phi : edge G -> 'rV[R]_3) : Prop :=
  forall v : G, \sum_(e | source e == v) phi e = \sum_(e | target e == v) phi e.

End UnitVector.

(** ** Row 8 — Unit-vector flows (primary conjecture) *)
(** OPEN.

    Source: "For every bridgeless graph [G] there is a flow
    [phi : E(G) -> S^2 = {x in R^3 : |x| = 1}]."  (Stated over an arbitrary
    real-closed field [R]; the original is the case [R = ℝ].  Unit vectors are
    nowhere zero, so this is exactly a nowhere-zero [S^2]-flow.) *)
Definition unit_vector_flows_statement : Prop :=
  forall (R : rcfType) (G : mgraph),
    (0 < #|edge G|)%N -> bridgeless G ->
    exists phi : edge G -> 'rV[R]_3,
      (forall e : edge G, sphere_vec (phi e)) /\ vconservative phi.

(** Companion conjecture: a [{-4..4}\{0}]-valued antipodally-odd labelling of
    [S^2] whose great-circle equilateral triples ([a+b+c=0]) sum to zero. *)
Definition unit_vector_flows_q_statement : Prop :=
  forall R : rcfType, exists q : 'rV[R]_3 -> int,
    [/\ (forall x, sphere_vec x -> (q x != 0) && (`|q x| <= 4)%R),
        (forall x, sphere_vec x -> q (- x) = - q x)
      & (forall a b c, sphere_vec a -> sphere_vec b -> sphere_vec c ->
           a + b + c = 0 -> q a + q b + q c = 0)].

(** ================================================================= *)
(** ** Row 9 — 5-local-tensions on embedded graphs *)
(** OPEN.

    Source: "There exists a fixed constant [c] so that every embedded (loopless)
    graph with edge-width [>= c] has a 5-local-tension."

    A surface embedding is modelled as a rotation system: a permutation [sigma]
    of the darts ([edge G * bool]; the involution [dflip] pairs the two darts of
    an edge).  Faces are the orbits of [sigma o dflip].  A cycle is contractible
    when its edge set lies in the GF(2)-span of the facial boundaries; the
    edge-width is the length of a shortest noncontractible circuit. *)

Section Embedding.
Variable G : mgraph.

Definition dart := (edge G * bool)%type.
Definition dflip (d : dart) : dart := (d.1, ~~ d.2).

Lemma dflip_inj : injective dflip.
Proof. by move=> [e b] [e' b'] [] -> /negb_inj ->. Qed.

Definition dalpha : {perm dart} := perm dflip_inj.

Variable sigma : {perm dart}.

(** Faces = orbits of [sigma o dflip]. *)
Definition facemap : {perm dart} := (sigma * dalpha)%g.
Definition faces : {set {set dart}} := porbits facemap.

(** Direction sign of a dart relative to the reference orientation. *)
Definition dsign (d : dart) : int := if d.2 then 1 else -1.

(** Boundary of a face [O] as a GF(2) edge vector: the edges with exactly one
    dart in [O]. *)
Definition fbound (O : {set dart}) : {set edge G} :=
  [set e : edge G | ((e, true) \in O) (+) ((e, false) \in O)].

(** GF(2) symmetric difference and contractible cycles (sums of face
    boundaries). *)
Definition symd (A B : {set edge G}) : {set edge G} := (A :|: B) :\: (A :&: B).
Definition contractible (C : {set edge G}) : Prop :=
  exists g : {set dart} -> bool,
    C = \big[symd/set0]_(O in faces | g O) fbound O.

(** Edge-width [>= c]: every noncontractible circuit has at least [c] edges. *)
Definition edge_width_geq (c : nat) : Prop :=
  forall C : {set edge G}, is_circuit C -> ~ contractible C -> (c <= #|C|)%N.

(** A nowhere-zero [k]-local-tension: an integer edge weighting with
    [1 <= |t e| <= k-1] whose signed sum around every face is zero. *)
Definition local_tension (k : nat) (t : edge G -> int) : Prop :=
  (forall e : edge G, (1 <= `|t e|)%R /\ (`|t e| <= (k.-1)%:R)%R) /\
  (forall O : {set dart}, O \in faces -> \sum_(d in O) dsign d * t d.1 = 0).

Definition has_5_local_tension : Prop := exists t, local_tension 5 t.

End Embedding.

Definition five_local_tensions_statement : Prop :=
  exists c : nat,
    forall (G : mgraph) (sigma : {perm (edge G * bool)}),
      loopless G -> edge_width_geq sigma c -> has_5_local_tension sigma.

(** ================================================================= *)
(** ** Row 10 — Jaeger's modular orientation conjecture *)
(** OPEN.

    Source: "Every [4k]-edge-connected graph can be oriented so that
    indegree(v) - outdegree(v) ≡ 0 (mod [2k+1]) for every vertex [v]."

    An orientation [o : edge G -> bool] keeps ([true]) or reverses ([false])
    each edge's reference direction. *)
Definition otail (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then source e else target e.
Definition ohead (G : mgraph) (o : edge G -> bool) (e : edge G) : G :=
  if o e then target e else source e.
Definition imbalance (G : mgraph) (o : edge G -> bool) (v : G) : int :=
  ((#|[set e | ohead o e == v]|)%:R - (#|[set e | otail o e == v]|)%:R)%R.

Definition jaegers_modular_orientation_statement : Prop :=
  forall (k : nat) (G : mgraph),
    (0 < #|edge G|)%N -> (0 < k)%N -> edge_connected G (4 * k)%N ->
    exists o : edge G -> bool,
      forall v : G, exists q : int, imbalance o v = ((2 * k + 1)%N)%:R * q.

(** ================================================================= *)
(** ** Flow polynomial *)

(** Component relation of a spanning subgraph [(V, S)] and its component count. *)
Definition erel (G : mgraph) (S : {set edge G}) : rel G :=
  fun x y => [exists e, (e \in S) &&
    (((source e == x) && (target e == y)) ||
     ((source e == y) && (target e == x)))].
Definition ncomp (G : mgraph) (S : {set edge G}) : nat := n_comp (erel S) [set: G].

(** Cycle-space dimension (nullity) of [(V, S)]: [|S| - |V| + c(S)]. *)
Definition nullity (G : mgraph) (S : {set edge G}) : nat :=
  (#|S| + ncomp S - #|G|)%N.

(** Flow polynomial [Phi(G,x) = sum_{S ⊆ E} (-1)^{|E\S|} x^{nullity S}]: for
    integer [k] it counts nowhere-zero [k]-flows. *)
Definition flow_poly_eval (G : mgraph) (x : rat) : rat :=
  \sum_(S : {set edge G}) (-1) ^+ (#|edge G| - #|S|) * x ^+ nullity S.
Definition flow_poly (G : mgraph) : {poly int} :=
  \sum_(S : {set edge G}) (-1) ^+ (#|edge G| - #|S|) *: 'X^(nullity S).

(** ** Row 11 — Half-integral flow-polynomial values *)
(** OPEN.

    Source: "[Phi(G,5.5) > 0] for every 2-edge-connected graph [G]." *)
Definition half_integral_flow_polynomial_values_statement : Prop :=
  forall G : mgraph,
    (0 < #|G|)%N -> two_edge_connected G ->
    (0 < flow_poly_eval G (11%:R / 2%:R))%R.

(** ** Row 13 — Real roots of the flow polynomial *)
(** OPEN.

    Source: "All real roots of nonzero flow polynomials are at most 4." *)
Definition real_roots_of_the_flow_polynomial_statement : Prop :=
  forall G : mgraph, flow_poly G != 0 ->
    forall (F : rcfType) (z : F),
      root (map_poly (fun n : int => n%:~R : F) (flow_poly G)) z -> (z <= 4%:R)%R.

(** ================================================================= *)
(** ** Group / B-flows and the Cayley homomorphism problem *)

Section CayleyGraph.
Variables (M : finGroupType) (B : {set M}).

Definition cradj (x y : M) : bool :=
  (x != y) && (((x^-1 * y)%g \in B) || ((y^-1 * x)%g \in B)).

Lemma cradj_sym : symmetric cradj.
Proof. by move=> x y; rewrite /cradj eq_sym orbC. Qed.

Lemma cradj_irrefl : irreflexive cradj.
Proof. by move=> x; rewrite /cradj eqxx. Qed.

Definition cayley : sgraph := SGraph cradj_sym cradj_irrefl.

End CayleyGraph.

(** A [B]-flow of [G] in the abelian group [M]: each edge weight lies in [B] and
    the group-products around each vertex balance. *)
Definition Bflow (M : finGroupType) (G : mgraph) (B : {set M})
    (phi : edge G -> M) : Prop :=
  (forall e : edge G, phi e \in B) /\
  (forall v : G, (\prod_(e | source e == v) phi e)%g
               = (\prod_(e | target e == v) phi e)%g).

(** ** Row 12 — A homomorphism problem for flows *)
(** OPEN.

    Source: "Let [M,M'] be abelian groups and [B ⊆ M], [B' ⊆ M'] with [B=-B],
    [B'=-B'].  If there is a homomorphism [Cayley(M,B) -> Cayley(M',B')], then
    every graph with a [B]-flow has a [B']-flow." *)
Definition a_homomorphism_problem_for_flows_statement : Prop :=
  forall (M M' : finGroupType) (B : {set M}) (B' : {set M'}),
    abelian [set: M] -> abelian [set: M'] ->
    B = [set (x^-1)%g | x in B] -> B' = [set (x^-1)%g | x in B'] ->
    (* [base.is_hom] qualified explicitly: both base's sgraph hom and
       mgraph's [is_hom] are in scope; the qualifier makes the intended
       sgraph homomorphism robust to import-order edits. *)
    (exists f : cayley B -> cayley B', base.is_hom f) ->
    forall G : mgraph,
      (exists phi : edge G -> M, Bflow B phi) ->
      (exists psi : edge G -> M', Bflow B' psi).

(** ================================================================= *)
(** ** Row 14 — Circular flow number of regular class-1 graphs *)
(** OPEN (partial: known for some regularities).

    Source: "Let [t >= 1] and [G] a [(2t+1)]-regular graph.  If [G] is class 1
    then [F_c(G) <= 2 + 2/t]." *)
Definition circular_flow_number_of_regular_class_1_graphs_statement : Prop :=
  forall (t : nat) (G : mgraph),
    (1 <= t)%N -> (0 < #|G|)%N -> mreg G (2 * t + 1)%N -> is_class1 G ->
    circular_flow_number_le G (2%:R + 2%:R / t%:R).

(** ================================================================= *)
(** ** Row 15 — Three 4-flows conjecture *)
(** OPEN.

    Source: "For every bridgeless graph [G] there exist disjoint
    [A_1,A_2,A_3] ⊆ E(G) with union [E(G)] so that [G \ A_i] has a
    nowhere-zero 4-flow for each [i]." *)
Definition three_4_flows_statement : Prop :=
  forall G : mgraph,
    (0 < #|edge G|)%N -> bridgeless G ->
    exists A1 A2 A3 : {set edge G},
      [/\ [disjoint A1 & A2], [disjoint A1 & A3], [disjoint A2 & A3],
          A1 :|: A2 :|: A3 = [set: edge G]
        & [/\ has_nz_kflow_del A1 4, has_nz_kflow_del A2 4
            & has_nz_kflow_del A3 4]].

(** ================================================================= *)
(** ** Row 5 — Approximation ratio for k-outerplanar / treewidth graphs *)
(** OPEN (Problem).

    Source: "Is the approximation ratio for Maximum Edge-Disjoint Paths (MaxEDP)
    or Maximum Integer Multiflow (MaxIMF) bounded by a constant in k-outerplanar
    or tree-width graphs?"  Formalized (planarity-free) as a bounded
    integrality gap on the bounded-treewidth class: for each treewidth bound
    [w] there is a constant [c] so that any fractional multiflow value is within
    a factor [c] of some integral edge-disjoint routing. *)

(** [P] contains an [s]-[t] walk (routes the demand [(s,t)]). *)
Definition routes (G : mgraph) (P : {set edge G}) (s t : G) : Prop :=
  exists w : seq (edge G), uwalk s t w /\ all (fun e => e \in P) w.

(** An integral edge-disjoint routing of distinct demands of [dem]. *)
Definition edp_feasible (G : mgraph) (dem : seq (G * G))
    (L : seq ((G * G) * {set edge G})) : Prop :=
  uniq (map (fun t => t.1) L) /\
  (forall t, t \in L -> t.1 \in dem /\ routes t.2 t.1.1 t.1.2) /\
  (forall t s, t \in L -> s \in L -> t <> s -> [disjoint t.2 & s.2]).

(** A fractional multiflow: weighted demand-paths obeying unit edge capacities. *)
Definition frac_feasible (G : mgraph) (dem : seq (G * G))
    (L : seq (((G * G) * {set edge G}) * rat)) : Prop :=
  (forall t, t \in L ->
     [/\ t.1.1 \in dem, (0 <= t.2)%R & routes t.1.2 t.1.1.1 t.1.1.2]) /\
  (forall e : edge G, (\sum_(t <- L | e \in t.1.2) t.2 <= 1)%R).
Definition frac_value (G : mgraph)
    (L : seq (((G * G) * {set edge G}) * rat)) : rat := \sum_(t <- L) t.2.

(** Treewidth [<= w] of the underlying simple graph of [G]. *)
Definition vskel_rel (G : mgraph) (x y : G) : bool :=
  (x != y) && [exists e, ((source e == x) && (target e == y)) ||
                          ((source e == y) && (target e == x))].

Lemma vskel_sym (G : mgraph) : symmetric (@vskel_rel G).
Proof.
move=> x y; rewrite /vskel_rel eq_sym; congr (_ && _).
by apply/existsP/existsP=> -[e He]; exists e; rewrite orbC.
Qed.

Lemma vskel_irrefl (G : mgraph) : irreflexive (@vskel_rel G).
Proof. by move=> x; rewrite /vskel_rel eqxx. Qed.

Definition vskel (G : mgraph) : sgraph := SGraph (@vskel_sym G) (@vskel_irrefl G).

Definition mtreewidth_le (G : mgraph) (w : nat) : Prop :=
  exists (T : forest) (D : T -> {set vskel G}), sdecomp T (vskel G) D /\ (width D <= w)%N.

Definition approximation_ratio_for_k_outerplanar_graphs_statement : Prop :=
  forall w : nat, exists c : rat, (1 <= c)%R /\
    forall (G : mgraph) (dem : seq (G * G)),
      mtreewidth_le G w ->
      forall L : seq (((G * G) * {set edge G}) * rat),
        frac_feasible dem L ->
        exists L' : seq ((G * G) * {set edge G}),
          edp_feasible dem L' /\ (frac_value L <= c * (size L')%:R)%R.
