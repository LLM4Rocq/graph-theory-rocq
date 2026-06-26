(** * Hom.conjectures.U3 — milestone U3 (namespace Hom, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of ten open / solved / disproved problems in graph
    HOMOMORPHISM theory: tensor-product chromatic number (Hedetniemi),
    homomorphisms to odd cycles, cores of Cayley / strongly-regular graphs,
    endomorphism counts of trees, longest cycles/paths, fractional powers and
    the weak pentagon problem.

    CARRIER TYPES are chosen per row from the source statement: most rows live
    over [sgraph] (simple finite graphs); the Cayley-graph row lives over the
    finite group [{ffun 'I_k -> M}] (the [k]-th power of an abelian group [M]).

    Imports.  [GTBase.base] is the SOLE graph import: it re-exports the
    coq-graph-theory undirected vocabulary ([sgraph], [x -- y], [N(x)], [χ],
    [ω], [α], [clique], [connected], ['K_n], ['K_n,m], [≃]/[diso], [ucycle],
    [path]) AND owns the cross-area primitives reused here verbatim:
    [tensor_product] (×, the product Hedetniemi is about), [homs_to]/[is_hom]
    (graph homomorphism), [is_core] (graph core), [girth_geq], [regular] (whence
    cubic = [regular _ 3]), [common_nbr], [Delta] (Δ).  [mathcomp fingroup] is
    additionally imported for the abelian-group / Cayley-graph row only (it is
    NOT graph vocabulary, so it does not duplicate base's surface).

    AREA-SPECIFIC new primitives introduced below (none belongs in base yet —
    each is specific to homomorphism statements): [cycle_graph]/[C5]
    (odd-cycle targets), [path_graph], [star_graph], [bipartite_rel],
    [triangle_free], [k_connected], [longest_cycle], [chord], [is_path],
    [longest_path], [hom_ffun]/[endo_count], [hom_equiv], [strongly_regular],
    [pcayley]/[pconn_set].  [graph_power]/[subdivision]/[frac_power] are the
    pure colouring-free [sgraph] constructions promoted from chromatic-theory/U1
    (tagged [@MOVE-to-base]: base candidates once a 2nd area needs them). *)

From GTBase Require Export base.
From mathcomp Require Import fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Area constructions: cycle / path / star graphs *)

(** The [n]-vertex cycle graph [C_n] on ['I_n]: distinct [i],[j] are adjacent
    iff one is the cyclic successor of the other (mod [n]).  The [i != j] guard
    makes the relation irreflexive for every [n] (including the degenerate
    [n ≤ 2]); for [n ≥ 3] this is the genuine cycle.  [C5] = [cycle_graph 5]
    is Hedetniemi/pentagon's target; [cycle_graph (2*k+1)] is the odd cycle
    [C_{2k+1}]. *)
Section CycleGraph.
Variable n : nat.
Definition cyc_rel (i j : 'I_n) : bool :=
  (i != j) && (((val i).+1 %% n == val j) || ((val j).+1 %% n == val i)).
Lemma cyc_sym : symmetric cyc_rel.
Proof. by move=> i j; rewrite /cyc_rel eq_sym orbC. Qed.
Lemma cyc_irrefl : irreflexive cyc_rel.
Proof. by move=> i; rewrite /cyc_rel eqxx. Qed.
Definition cycle_graph : sgraph := SGraph cyc_sym cyc_irrefl.
End CycleGraph.

Definition C5 : sgraph := cycle_graph 5.

(** The [n]-vertex path graph [P_n] on ['I_n]: [i],[j] adjacent iff their
    indices are consecutive integers (no modular wrap, so it is a path, not a
    cycle). *)
Section PathGraph.
Variable n : nat.
Definition pth_rel (i j : 'I_n) : bool :=
  ((val i).+1 == val j) || ((val j).+1 == val i).
Lemma pth_sym : symmetric pth_rel.
Proof. by move=> i j; rewrite /pth_rel orbC. Qed.
Lemma pth_irrefl : irreflexive pth_rel.
Proof. by move=> i; rewrite /pth_rel orbb (gtn_eqF (ltnSn _)). Qed.
Definition path_graph : sgraph := SGraph pth_sym pth_irrefl.
End PathGraph.

(** The [n]-vertex star graph [K_{1,n-1}] (one centre, [n-1] leaves) — a tree.
    Uses base's re-exported ['K_1, m] notation ([= KB 1 m]) rather than the bare
    [KB] constant, to stay on the documented base vocabulary surface. *)
Definition star_graph (n : nat) : sgraph := 'K_1, n.-1.

(** ** Row 1 — Hedetniemi's conjecture
    DISPROVED (Shitov 2019: there exist finite G,H with χ(G×H) < min(χG,χH)).
    Stated here as the historical EQUALITY (statement-only); its refutation is
    optional applications/ work, out of scope for this milestone.

    Source: "If G,H are simple finite graphs, then χ(G × H) = min{χ(G),χ(H)}.
    Here G × H is the tensor (direct / categorical) product."

    Uses base's [tensor_product] (×) verbatim. *)
Definition hedetniemis_statement : Prop :=
  forall G H : sgraph,
    χ([set: tensor_product G H]) = minn (χ([set: G])) (χ([set: H])).

(** ** Row 2 — The pentagon problem
    OPEN.

    Source: "Let G be a 3-regular graph that contains no cycle of length
    shorter than g.  Is it true that for large enough g there is a
    homomorphism G → C_5?"

    Cubic = [regular G 3]; "no cycle shorter than g" = [girth_geq G g];
    homomorphism to [C5] = [homs_to G C5] (all from base + area [C5]). *)
Definition pentagon_statement : Prop :=
  exists g : nat, forall G : sgraph,
    regular G 3 -> girth_geq G g -> homs_to G C5.

(** ** Row 3 — Chords of longest cycles
    OPEN.

    Source: "If G is a 3-connected graph, every longest cycle in G has a chord."

    [k_connected G k]: more than [k] vertices, and deleting any set of fewer
    than [k] vertices leaves the rest connected (standard vertex
    [k]-connectivity, stated self-containedly via [connected (~: S)]).
    [longest_cycle G c]: [c] is a genuine cycle ([ucycle], [2 < size]) of
    maximum length.  [chord G c]: an edge [x -- y] joining two cycle vertices
    that are NOT cyclically consecutive in [c] — consecutivity is exactly
    membership in [zip c (rot 1 c)], the list of cycle edges. *)
(* [k_connected] now from graph-theory-base (uses [set: G] :\: S = ~: S). *)

Definition longest_cycle (G : sgraph) (c : seq G) : Prop :=
  [/\ ucycle (--) c, 2 < size c &
      forall c' : seq G, ucycle (--) c' -> size c' <= size c].

Definition chord (G : sgraph) (c : seq G) : Prop :=
  exists x y : G,
    [/\ x \in c, y \in c, x -- y,
        (x, y) \notin zip c (rot 1 c) & (y, x) \notin zip c (rot 1 c)].

Definition chords_of_longest_cycles_statement : Prop :=
  forall G : sgraph, k_connected G 3 ->
    forall c : seq G, longest_cycle c -> chord c.

(** ** Row 4 — Cores of Cayley graphs
    OPEN.

    Source: "Let M be an abelian group.  Is the core of a Cayley graph (on
    some power of M) a Cayley graph (on some power of M)?"

    CARRIER: the [k]-th power of [M] is the finite type [{ffun 'I_k -> M}],
    carrying the pointwise group structure of [M].  Its Cayley graph with
    connection set [S] ([pcayley S]) makes distinct [f],[g] adjacent iff the
    pointwise "difference" [pdiff f g = (i ↦ f i · (g i)⁻¹) ∈ S] (symmetrised
    so the [sgraph] laws hold for any [S]; the genuine Cayley graph is
    recovered when [S] is a [pconn_set] — identity-free, inverse-closed).  We
    use [M]'s group operations directly (M : finGroupType), which sidesteps
    needing a packed finGroupType instance for [{ffun 'I_k -> M}].  "The core of
    G is a Cayley graph on a power of M" is stated without a core OPERATOR as:
    there is a power [m] and connection set [S'] whose Cayley graph is a core
    ([is_core]) and is homomorphically equivalent to G ([hom_equiv]) — i.e. it
    IS the core of G up to isomorphism. *)
Section Cayley.
Variables (M : finGroupType) (k : nat).
Implicit Types (f g : {ffun 'I_k -> M}) (S : {set {ffun 'I_k -> M}}).

(** Pointwise group structure on the power [M^k = {ffun 'I_k -> M}]. *)
Definition pone : {ffun 'I_k -> M} := [ffun _ => 1%g].
Definition pinv f : {ffun 'I_k -> M} := [ffun i => (f i)^-1%g].
Definition pdiff f g : {ffun 'I_k -> M} := [ffun i => (f i * (g i)^-1)%g].

Definition pcayley_rel (S : {set {ffun 'I_k -> M}}) : rel {ffun 'I_k -> M} :=
  fun f g => (f != g) && ((pdiff f g \in S) || (pdiff g f \in S)).
Lemma pcayley_sym S : symmetric (pcayley_rel S).
Proof. by move=> f g; rewrite /pcayley_rel eq_sym orbC. Qed.
Lemma pcayley_irrefl S : irreflexive (pcayley_rel S).
Proof. by move=> f; rewrite /pcayley_rel eqxx. Qed.
Definition pcayley S : sgraph := SGraph (pcayley_sym S) (pcayley_irrefl S).

(** A valid Cayley connection set on the power: identity-free, inverse-closed. *)
Definition pconn_set S : Prop :=
  (pone \notin S) /\ (forall f, f \in S -> pinv f \in S).
End Cayley.

(** Homomorphic equivalence: homomorphisms both ways.  A generic cross-area
    companion to base's [homs_to]/[is_core], already reused by Rows 4 and 6 here
    ([@MOVE-to-base]: migrate to base alongside [homs_to]/[is_core] once a 2nd
    area needs it, so it is never redefined). *)
Definition hom_equiv (G H : sgraph) : Prop := homs_to G H /\ homs_to H G.

Definition cores_of_cayley_graphs_statement : Prop :=
  forall M : finGroupType, abelian [set: M] ->
  forall (k : nat) (S : {set {ffun 'I_k -> M}}), pconn_set S ->
    exists (m : nat) (S' : {set {ffun 'I_m -> M}}),
      [/\ pconn_set S', is_core (pcayley S') & hom_equiv (pcayley S) (pcayley S')].

(** ** Row 5 — Chromatic number of the 3/3-power of a graph
    OPEN.

    Source: "G^{m/n} := (G^{1/n})^m (the m-power of the n-subdivision).
    Conjecture: for G with Δ(G) ≥ 2, χ(G^{3/3}) ≤ 2Δ(G) + 1."

    [graph_power]/[subdivision]/[frac_power] are the pure [sgraph]
    constructions promoted verbatim from chromatic-theory/U1 ([@MOVE-to-base]
    candidates).  [G^{3/3}] = [frac_power G 3 3] = [graph_power (subdivision G 3) 3]. *)

(** *** Powers / subdivisions / fractional powers — PROMOTED to graph-theory-base.
    [graph_power], [subdivision], [frac_power] now live in base/ (used by both U1 and U3),
    reused here via the base import; no local definitions remain. *)

Definition chromatic_number_of_frac_3_3_power_of_graph_statement : Prop :=
  forall G : sgraph, 2 <= Delta G ->
    χ([set: frac_power G 3 3]) <= 2 * Delta G + 1.

(** ** Row 6 — Cores of strongly-regular graphs
    OPEN.

    Source: "Does every strongly regular graph have either itself or a complete
    graph as a core?"

    [strongly_regular G]: there are parameters [k],[l],[m] with [G] [k]-regular,
    every adjacent pair sharing [l] common neighbours and every non-adjacent
    distinct pair sharing [m].  The conjecture: the core of [G] is either [G]
    itself ([is_core G]) or a complete graph (G is hom-equivalent to ['K_n],
    whose core is ['K_n]). *)
Definition srg (G : sgraph) (k l m : nat) : Prop :=
  [/\ regular G k,
      (forall x y : G, x -- y -> #|common_nbr x y| = l)
    & (forall x y : G, x != y -> ~~ x -- y -> #|common_nbr x y| = m)].

Definition strongly_regular (G : sgraph) : Prop :=
  exists k l m : nat, srg G k l m.

Definition cores_of_strongly_regular_graphs_statement : Prop :=
  forall G : sgraph, strongly_regular G ->
    is_core G \/ exists n : nat, hom_equiv G 'K_n.

(** ** Row 7 — Mapping planar graphs to odd cycles
    OPEN. PLANARITY G2-GATE: coq-graph-theory-planar / coq-fourcolor are NOT
    installed, so planarity is carried as a DISCHARGED SECTION HYPOTHESIS
    [Variable is_planar : sgraph -> Prop] — the statement is stated RELATIVE to
    a FIXED planarity predicate, which the section then discharges, so the final
    constant has type [(sgraph -> Prop) -> Prop] (never a top-level
    Parameter/Axiom — keeps the file axiom-free).

    IMPORTANT (faithfulness fix): [is_planar] must NOT be an inner
    [forall is_planar : sgraph -> Prop, ...].  As a positive (hypothesis-side)
    occurrence, an inner universal could be instantiated at [fun _ => True],
    which DROPS the planarity hypothesis and yields the STRICTLY STRONGER (and
    false) planarity-free claim.  A section [Variable] (discharged to an explicit
    argument) constrains nothing artificially: instantiating the resulting
    [(sgraph -> Prop) -> Prop] at the GENUINE planarity predicate — once the
    planar layer lands — recovers exactly the conjecture.  Until then the row is
    reported compile_blocked: with an arbitrary [is_planar] it type-checks but is
    not yet the genuine planar conjecture.

    Source: "Every planar graph of girth ≥ 4k has a homomorphism to C_{2k+1}."

    Target odd cycle [C_{2k+1}] = [cycle_graph (2*k+1)]; girth via [girth_geq]. *)
Section MappingPlanar.
Variable is_planar : sgraph -> Prop.

Definition mapping_planar_graphs_to_odd_cycles_statement : Prop :=
  forall (G : sgraph) (k : nat),
    0 < k -> is_planar G -> girth_geq G (4 * k) ->
    homs_to G (cycle_graph (2 * k + 1)).
End MappingPlanar.

(** ** Row 8 — Three longest paths share a vertex
    OPEN.

    Source: "Do any three longest paths in a connected graph have a vertex in
    common?"

    A path is a duplicate-free walk [is_path s] ([uniq] + consecutive
    adjacency); [longest_path s] is one of maximum length.  The [0 < #|G|]
    guard rules out the empty graph (whose only path is [[::]], for which "a
    common vertex" is vacuously impossible). *)
Definition is_path (G : sgraph) (s : seq G) : bool :=
  uniq s && (if s is x :: p then path (--) x p else true).

Definition longest_path (G : sgraph) (s : seq G) : Prop :=
  is_path s /\ forall t : seq G, is_path t -> size t <= size s.

Definition do_any_three_longest_paths_in_a_connected_graph_have_statement : Prop :=
  forall G : sgraph, 0 < #|G| -> connected [set: G] ->
    forall s1 s2 s3 : seq G,
      longest_path s1 -> longest_path s2 -> longest_path s3 ->
      exists v : G, [/\ v \in s1, v \in s2 & v \in s3].

(** ** Row 9 — Extremal number of tree endomorphisms
    OPEN.

    Source: "An endomorphism of a graph is an edge-preserving self-map of the
    vertex set.  Among all n-vertex trees, the star has the most endomorphisms
    and the path has the least."

    [hom_ffun f]: [f : {ffun G -> G}] is an endomorphism; [endo_count G] counts
    them.  Compared against the [n]-vertex [path_graph] (least) and
    [star_graph] (most).

    [hom_ffun] is the BOOLEAN REFLECTION of base's Prop-valued [is_hom] (a
    boolean predicate is required to index the cardinal [#|[set f | ...]|],
    which the Prop-valued [is_hom] cannot serve directly); the two notions
    provably coincide — see [hom_ffunP] in grounding_U3.v
    ([reflect (is_hom f) (hom_ffun f)]).  It is therefore a reflection of
    base's homomorphism vocabulary, not an independent redefinition. *)
Definition hom_ffun (G : sgraph) (f : {ffun G -> G}) : bool :=
  [forall x, forall y, (x -- y) ==> (f x -- f y)].

Definition endo_count (G : sgraph) : nat :=
  #|[set f : {ffun G -> G} | hom_ffun f]|.

Definition extremal_problem_on_the_number_of_tree_endomorphism_statement : Prop :=
  forall (n : nat) (T : sgraph),
    0 < n -> is_tree [set: T] -> #|T| = n ->
    (endo_count (path_graph n) <= endo_count T)
      /\ (endo_count T <= endo_count (star_graph n)).

(** ** Row 10 — The weak pentagon problem
    OPEN.

    Source: "If G is a cubic graph not containing a triangle, then the edges of
    G can be coloured by five colours so that the complement of every colour
    class is bipartite."

    [triangle_free]: no three mutually adjacent vertices.  An edge 5-colouring
    is a symmetric [col : G -> G -> 'I_5]; the complement of colour class [c] is
    the relation [x -- y && col x y != c], required [bipartite_rel] (admits a
    2-colouring [G -> bool] separating its edges). *)
(* [triangle_free] now from graph-theory-base (identical definition). *)

Definition bipartite_rel (G : sgraph) (r : rel G) : Prop :=
  exists f : G -> bool, forall x y : G, r x y -> f x != f y.

Definition weak_pentagon_statement : Prop :=
  forall G : sgraph, regular G 3 -> triangle_free G ->
    exists col : G -> G -> 'I_5,
      (forall x y : G, col x y = col y x) /\
      forall c : 'I_5,
        @bipartite_rel G (fun x y => (x -- y) && (col x y != c)).
