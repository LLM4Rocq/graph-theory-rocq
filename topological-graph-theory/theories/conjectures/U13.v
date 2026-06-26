(** * Topological.conjectures.U13 — milestone U13 (namespace Topological, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of four planar / topological-graph-theory problems.

    PLANARITY G2-GATE.  [coq-graph-theory-planar] / [coq-fourcolor] are NOT
    installed on this switch, so there is no [planar : sgraph -> Prop] in scope.
    Every row of THIS milestone is intrinsically about planar graphs
    (manifest [requires_planarity = true] for all four slugs).  Per plan §3 the
    planarity predicate is therefore discharged INTO each statement as a
    universally-quantified ORACLE [is_planar : sgraph -> Prop] — never a
    top-level Parameter/Axiom (which would contaminate Print Assumptions).  The
    file type-checks and is axiom-free, but the rows are honestly marked
    [compile_blocked]: their MATHEMATICAL content is faithful only when
    [is_planar] is instantiated with the real planarity predicate from the
    planar/fourcolor stack (plan gate G2).  Once G2 lands, replace the leading
    [forall (is_planar : sgraph -> Prop)] by the concrete predicate.

    CORE API reused (switch `digraph`, Rocq 9.1.1 + coq-graph-theory + base):
      - [G : sgraph]; [x -- y] adjacency; [N(x)] open neighbourhood;
      - [is_forest S] : Prop  (coq-graph-theory sgraph) — the induced subgraph
        on [S : {set G}] is a forest (acyclic);  this IS the "induced forest"
        primitive, so no new primitive is introduced for row 1;
      - [χ(A)] : nat — subset-relative chromatic number, whole-graph [χ([set:G])];
      - [Delta G] : nat (base) — sgraph maximum degree Δ ("max-degree");
      - [graph_power G 2] : sgraph (base) — the square G² ("graph-square"):
        distinct vertices at distance ≤ 2 are adjacent.
    Thus "graph-square" = [graph_power _ 2] and "max-degree" = [Delta] are
    REUSED from base verbatim.  Two genuinely-new primitives are introduced:
      - [union_of_two_planar] (row 2) is AREA-SPECIFIC (intrinsically planar /
        thickness-2), so it stays local;
      - [k_degenerate_on] / [k_degenerate] (row 4) are a generic structural /
        sparsity notion that is plausibly CROSS-AREA, so they are tagged
        [@MOVE-to-base] and should migrate to base once a second area needs
        degeneracy. *)

From GTBase Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Row 1 — Large induced forest in a planar graph
    PARTIAL (partial lower bounds proven; the conjectured 1/2 fraction is open).
    G2-GATE (planarity).

    Source (Conjecture): "Every planar graph on n vertices has an induced forest
    with at least n/2 vertices."

    Carrier: [sgraph].  "induced forest" = [is_forest S] (coq-graph-theory):
    the induced subgraph on the vertex set [S] is acyclic.  The bound
    |S| ≥ n/2 is stated multiplied through as [#|G| <= 2 * #|S|] to avoid the
    nat division. *)
Definition large_induced_forest_in_a_planar_graph_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G ->
    exists S : {set G}, is_forest S /\ (#|G| <= 2 * #|S|)%N.

(** ** Row 2 — Earth–Moon problem (thickness-2 chromatic number)
    OPEN (the maximum is known to lie between 9 and 12).
    G2-GATE (planarity).

    Source (Problem): "What is the maximum number of colours needed to colour
    countries such that no two countries sharing a common border have the same
    colour in the case where each country consists of one region on earth and
    one region on the moon?"

    The map-colouring formulation is, via duality, the chromatic number of a
    graph that is the edge-UNION of two planar graphs on a common vertex set
    (a thickness-≤ 2 graph).  The open Problem "what is the maximum?" is stated
    as: there is a value [m] that is simultaneously an UPPER BOUND on χ over all
    such graphs and ACHIEVED by one of them — i.e. the maximum exists and equals
    [m].

    NON-VACUITY GUARD (faithfulness): the ACHIEVED clause is an existential over
    biplanar graphs, so under the degenerate oracle [is_planar := fun _ => False]
    (where [union_of_two_planar] is unsatisfiable) it would make the whole Prop
    FALSE for reasons unrelated to the mathematics — i.e. refutable, not merely
    over-strong.  We therefore guard the statement on the existence of at least
    one biplanar graph: [(exists G0, union_of_two_planar is_planar G0) -> …].
    Once G2 instantiates [is_planar] with the real planarity predicate the guard
    is automatically discharged (planar graphs exist), so the guard adds nothing
    mathematically yet keeps the pre-G2 statement self-contained (non-refutable).

    New AREA primitive: [union_of_two_planar] (edge-union of two [is_planar]
    graphs on the vertex set of [G]).  Each planar layer is reconstructed as an
    [sgraph] over the SAME vertex type [G] from a symmetric irreflexive edge
    relation, so [is_planar] applies to it and χ([set:G]) is the union's
    chromatic number. *)
Definition union_of_two_planar
    (is_planar : sgraph -> Prop) (G : sgraph) : Prop :=
  exists (e1 e2 : rel G)
         (s1 : symmetric e1) (i1 : irreflexive e1)
         (s2 : symmetric e2) (i2 : irreflexive e2),
    [/\ is_planar (SGraph s1 i1),
        is_planar (SGraph s2 i2)
      & forall x y : G, (x -- y) = e1 x y || e2 x y ].

Definition earth_moon_statement : Prop :=
  forall (is_planar : sgraph -> Prop),
    (exists G0 : sgraph, union_of_two_planar is_planar G0) ->
    exists m : nat,
      (forall G : sgraph, union_of_two_planar is_planar G -> (χ([set: G]) <= m)%N)
   /\ (exists G : sgraph, union_of_two_planar is_planar G /\ χ([set: G]) = m).

(** ** Row 3 — Colouring the square of a planar graph (Wegner)
    OPEN.
    G2-GATE (planarity).

    Source (Conjecture): "Let G be a planar graph of maximum degree Δ.  The
    chromatic number of its square is at most 7 if Δ = 3, at most Δ+5 if
    4 ≤ Δ ≤ 7, at most ⌊3Δ/2⌋+1 if Δ ≥ 8."

    Carrier: [sgraph].  "graph-square" = [graph_power G 2] (base); χ of the
    square = [χ([set: graph_power G 2])]; "max-degree" Δ = [Delta G] (base).
    The three regimes are stated as a guarded conjunction. *)
Definition colouring_the_square_of_a_planar_graph_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G -> (0 < #|G|)%N ->
    [/\ ( Delta G = 3 -> (χ([set: graph_power G 2]) <= 7)%N ),
        ( (4 <= Delta G)%N -> (Delta G <= 7)%N ->
            (χ([set: graph_power G 2]) <= Delta G + 5)%N )
      & ( (8 <= Delta G)%N ->
            (χ([set: graph_power G 2]) <= (3 * Delta G)./2 + 1)%N ) ].

(** ** Row 4 — Degenerate colourings of planar graphs
    OPEN.
    G2-GATE (planarity).

    Source: "A graph G is k-degenerate if every subgraph of G has a vertex of
    degree ≤ k.  Conjecture: Every simple planar graph has a 5-coloring so that
    for 1 ≤ k ≤ 4, the union of any k color classes induces a (k−1)-degenerate
    graph."

    Carrier: [sgraph].  New AREA primitives:
      - [k_degenerate_on G W k] : the induced subgraph on [W : {set G}] is
        k-degenerate — every NONEMPTY subset [S ⊆ W] has a vertex whose degree
        WITHIN [S] (i.e. [#|N(x) :&: S|]) is ≤ k.  (Quantifying over induced
        subgraphs suffices for degeneracy.)
      - [k_degenerate G k := k_degenerate_on [set:G] k] : whole-graph form,
        matching the source's definition of k-degenerate.  Not used by the
        four [_statement]s here (only [k_degenerate_on] is); it is EXPORTED as
        public milestone API for downstream reuse.
    [@MOVE-to-base]: [k_degenerate_on] / [k_degenerate] are a generic graph-
    sparsity primitive, not planarity-specific; migrate to base when a second
    area needs degeneracy.
    A 5-colouring is a vertex map [col : G -> 'I_5] that is proper; the "union
    of k colour classes" picked by a palette [T : {set 'I_5}] with |T| = k is
    the vertex set [[set v | col v \in T]], which must be (k−1)-degenerate for
    1 ≤ k ≤ 4. *)
Definition k_degenerate_on (G : sgraph) (W : {set G}) (k : nat) : Prop :=
  forall S : {set G},
    S \subset W -> S != set0 ->
    exists x : G, x \in S /\ (#|N(x) :&: S| <= k)%N.

Definition k_degenerate (G : sgraph) (k : nat) : Prop :=
  k_degenerate_on [set: G] k.
Arguments k_degenerate_on {G} W k.

Definition degenerate_colorings_of_planar_graphs_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G ->
    exists col : G -> 'I_5,
      (forall x y : G, x -- y -> col x != col y)
   /\ (forall T : {set 'I_5},
         (1 <= #|T|)%N -> (#|T| <= 4)%N ->
         k_degenerate_on [set v : G | col v \in T] (#|T| - 1)).
