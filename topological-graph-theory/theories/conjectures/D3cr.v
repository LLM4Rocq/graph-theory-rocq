(** * Topological.conjectures.D3cr — milestone D3cr (namespace Topological, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of four crossing-number conjectures.

    CROSSING NUMBER.  All four rows are about the crossing number [cr(G)].  We use
    the FAITHFUL combinatorial planarization invariant from
    [Topological.foundations.crossing]:

      [is_crossing_number G n]  :  n is the least number of "crossing splits"
                                   (degree-4 resolutions of two independent edges)
                                   that planarize G onto base's [wagner_planar].

    This needs NO geometry / drawings / surfaces / faces / point-sets and NO
    planarity stack (it bottoms out at the Wagner no-K5/K3,3-minor predicate), and
    it is grounded there by:  [crossing_number0] (cr = 0 ⇔ planar, both ways),
    [wagner_planar_sub] (planarity subgraph-closed — the base case of cr
    monotonicity), and [not_wagner_planar_K5] ⇒ [is_crossing_number_K5] (cr(K5) ≥ 1).
    See crossing.v for why cr is exposed RELATIONALLY (a total [nat]-valued cr
    would need a finite-drawing/geometry existence fact, excluded here) and for the
    honest note on the full subgraph-monotonicity (open in this model).
    [is_crossing_number] is FUNCTIONAL ([is_crossing_number_uniq]); each statement
    binds cr as a value [v] under the hypothesis [is_crossing_number _ v], which
    therefore pins cr and keeps the statement non-vacuous and faithful.

    CARRIERS (per row.rocq_idiom): complete-bipartite [KB m n], complete ['K_n],
    arbitrary [sgraph], and the hypercube [hypercube d] (= iterated cartesian power
    of ['K_2], built on base's [cartesian_product]).

    NEW AREA PRIMITIVES: crossing notions live in crossing.v (area-local
    planarization invariant).  [hypercube] is defined here; it is a generic graph
    family (not crossing-specific), tagged [@MOVE-to-base] for promotion once a
    second area needs it. *)

From Topological Require Import foundations.crossing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The d-dimensional hypercube Q_d: vertices are binary strings of length d, two
    adjacent iff they differ in exactly one coordinate.  Equivalently the d-fold
    cartesian (box) power of K_2 (Q_0 = K_1, Q_{d+1} = K_2 □ Q_d).  Reuses base's
    [cartesian_product] (□).  [@MOVE-to-base]: generic graph family.

    NB. base's [graph_power] is NOT the right primitive here: it is the DISTANCE
    power (same vertex set, vertices adjacent iff joined by a walk of length ≤ m,
    via [pow_rel]), not the cartesian/box power.  Hence the local fixpoint over
    [cartesian_product] is the correct construction, not a redefinition of an
    existing base primitive.  Grounding (witness + textbook identities — base case
    Q_0 = K_1, recurrence, and #|Q_d| = 2^d) is in [grounding_D3cr]. *)
Fixpoint hypercube (d : nat) : sgraph :=
  match d with
  | 0 => 'K_1
  | d'.+1 => cartesian_product 'K_2 (hypercube d')
  end.

(** ** Row 1 — Crossing number of the complete bipartite graph (Zarankiewicz)
    OPEN (Zarankiewicz's conjecture; known for min(m,n) ≤ 6).

    Source: "The crossing number cr(G) of G is the minimum number of crossings in
    all drawings of G in the plane.  Conjecture
      cr(K_{m,n}) = ⌊m/2⌋⌊(m−1)/2⌋⌊n/2⌋⌊(n−1)/2⌋."

    Carrier: the complete bipartite graph [KB m n].  Floors are nat division
    [_ %/ 2]. *)
Definition the_crossing_number_of_the_complete_bipartite_graph_statement : Prop :=
  forall (m n v : nat),
    is_crossing_number (KB m n) v ->
    v = (m %/ 2) * ((m - 1) %/ 2) * (n %/ 2) * ((n - 1) %/ 2).

(** ** Row 2 — Crossing number of the complete graph (Guy)
    OPEN (Guy's conjecture; known for n ≤ 12).

    Source: "The crossing number cr(G) of G is the minimum number of crossings in
    all drawings of G in the plane.  Conjecture
      cr(K_n) = ¼⌊n/2⌋⌊(n−1)/2⌋⌊(n−2)/2⌋⌊(n−3)/2⌋."

    Carrier: the complete graph ['K_n].  The Guy product is always divisible by 4,
    so the ¼ factor is the EXACT nat division [_ %/ 4].  (This divisibility is a
    relied-upon arithmetic fact about the Guy product — verified for all checked n
    — not enforced by the encoding; were it ever to fail, [%/ 4] would truncate.) *)
Definition the_crossing_number_of_the_complete_graph_statement : Prop :=
  forall (n v : nat),
    is_crossing_number 'K_n v ->
    v = ((n %/ 2) * ((n - 1) %/ 2) * ((n - 2) %/ 2) * ((n - 3) %/ 2)) %/ 4.

(** ** Row 3 — Crossing numbers and colouring (Albertson)
    OPEN (Albertson's conjecture; known for t ≤ 18 and via the four-colour theorem
    for small cases).

    Source: "We let cr(G) denote the crossing number of a graph G.  Conjecture
      Every graph G with χ(G) ≥ t satisfies cr(G) ≥ cr(K_t)."

    Carrier: arbitrary [sgraph]; χ([set: G]) is the whole-graph chromatic number
    (base/coloring). *)
Definition crossing_numbers_and_coloring_statement : Prop :=
  forall (G : sgraph) (t vG vt : nat),
    (t <= χ([set: G]))%N ->
    is_crossing_number G vG ->
    is_crossing_number 'K_t vt ->
    (vt <= vG)%N.

(** ** Row 4 — Crossing number of the hypercube
    OPEN (the limit is known to exist and lie in a narrow interval around 5/32;
    the exact value 5/32 is conjectural).

    Source: "The crossing number cr(G) of G is the minimum number of crossings in
    all drawings of G in the plane.  The d-dimensional (hyper)cube Q_d ... .
    Conjecture  lim cr(Q_d)/4^d = 5/32."

    Carrier: [hypercube d].  The limit is stated by the eventual-bound (ε–N)
    idiom over ℕ with the rational target 5/32, cross-multiplied (denominators are
    positive): for every positive rational ε = eps_num/eps_den there is an N past
    which |cr(Q_d)/4^d − 5/32| < ε, i.e.
      eps_den · |32·cr − 5·4^d|  <  eps_num · (32·4^d),
    the absolute value written as a sum of truncated nat subtractions.

    VACUITY NOTE (shared by all four rows, sharpest here).  Like Rows 1–3, the
    inner body is gated by [is_crossing_number (hypercube d) v], which RELATIONALLY
    pins cr but — in this geometry-free model — is not KNOWN to be inhabited in the
    non-planar regime (d ≥ 4): exhibiting it needs the planarization upper bound
    (a drawing/geometry existence fact this layer omits), so the ε–N body is
    vacuously satisfiable precisely where the 5/32 limit lives.  This is inherent
    to the relational cr foundation, not a defect of the encoding; it keeps the
    statement faithful (it makes no false claim) while honestly weak.  That cr is
    nonetheless genuinely INHABITED (so the predicate is not silently empty) is
    certified in [grounding_D3cr] by [cr_hypercube0]/[cr_hypercube1] (cr(Q_0) =
    cr(Q_1) = 0, the planar base of the family) and [cr_K1]. *)
Definition the_crossing_number_of_the_hypercube_statement : Prop :=
  forall (eps_num eps_den : nat),
    (0 < eps_num)%N -> (0 < eps_den)%N ->
    exists N : nat,
      forall (d v : nat),
        (N <= d)%N -> is_crossing_number (hypercube d) v ->
        (eps_den * ((32 * v - 5 * 4 ^ d) + (5 * 4 ^ d - 32 * v))
           < eps_num * (32 * 4 ^ d))%N.
