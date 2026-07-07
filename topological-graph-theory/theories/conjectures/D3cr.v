(** * Topological.conjectures.D3cr — milestone D3cr (namespace Topological, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of four crossing-number conjectures.

    CROSSING NUMBER.  All four rows are about the crossing number [cr(G)].  We use
    the axiom-free combinatorial split-planarization proxy from
    [Topological.foundations.crossing]:

      [is_crossing_number G n]  :  n is the least number of "crossing splits"
                                   (degree-4 resolutions of two independent edges)
                                   that planarize G onto base's [wagner_planar].

    This needs NO geometry / drawings / surfaces / faces / point-sets and NO
    planarity stack (it bottoms out at the Wagner no-K5/K3,3-minor predicate), and
    it is grounded there by:  [crossing_number0] (split-cr = 0 ⇔ planar, both ways),
    [wagner_planar_sub] (planarity subgraph-closed — the base case of cr
    monotonicity), and [not_wagner_planar_K5] ⇒ [is_crossing_number_K5] (cr(K5) ≥ 1).
    See crossing.v for why cr is exposed RELATIONALLY (a total [nat]-valued cr
    would need a finite-drawing/geometry existence fact, excluded here) and for the
    honest note on the full subgraph-monotonicity (open in this model).
    [is_crossing_number] is FUNCTIONAL ([is_crossing_number_uniq]).

    STATUS.  The rows are stated in DIRECT, NON-VACUOUS form, but are recorded as
    PARTIAL after the #5/#6 readback review: the [xsplit] model lacks local
    drawing rotation/alternation data at crossing vertices, so equivalence to the
    usual drawing crossing number is not yet validated.  Rows 1–2 assert
    [is_crossing_number <carrier> <formula>] outright — the conjectured split
    value both achievable and minimal, no inhabitance gate (the former
    [forall v, is_crossing_number _ v -> v = _] shape was vacuity-conditional).
    Row 3 uses the sub-level comparison of minima ([forall k achievable for G,
    exists j <= k achievable for K_t] — robust to the exactly-k non-monotonicity
    of [crossing_planar_in]); Row 4 states the 5/32 limit two-sidedly on the
    achievable counts.  No totality theorem is needed: each existence half is part
    of the conjecture's own claim.

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
    [_ %/ 2].

    WAVE-2 FORM (direct, NON-VACUOUS): asserts that the Zarankiewicz product IS
    the crossing number — both achievability of that many crossings (the known
    Zarankiewicz drawing) and minimality (the open part) are part of the
    conjecture's own claim, so no separate totality theorem is needed.  The
    former relational form [forall v, is_crossing_number _ v -> v = _] was
    vacuity-conditional on inhabitance. *)
Definition the_crossing_number_of_the_complete_bipartite_graph_statement : Prop :=
  forall m n : nat,
    is_crossing_number (KB m n)
      ((m %/ 2) * ((m - 1) %/ 2) * (n %/ 2) * ((n - 1) %/ 2)).

(** ** Row 2 — Crossing number of the complete graph (Guy)
    OPEN (Guy's conjecture; known for n ≤ 12).

    Source: "The crossing number cr(G) of G is the minimum number of crossings in
    all drawings of G in the plane.  Conjecture
      cr(K_n) = ¼⌊n/2⌋⌊(n−1)/2⌋⌊(n−2)/2⌋⌊(n−3)/2⌋."

    Carrier: the complete graph ['K_n].  The Guy product is always divisible by 4,
    so the ¼ factor is the EXACT nat division [_ %/ 4].  (This divisibility is a
    relied-upon arithmetic fact about the Guy product — verified for all checked n
    — not enforced by the encoding; were it ever to fail, [%/ 4] would truncate.)

    WAVE-2 FORM (direct, NON-VACUOUS): asserts the Guy value IS the crossing
    number (achievability = Guy's construction + minimality = the open part). *)
Definition the_crossing_number_of_the_complete_graph_statement : Prop :=
  forall n : nat,
    is_crossing_number 'K_n
      (((n %/ 2) * ((n - 1) %/ 2) * ((n - 2) %/ 2) * ((n - 3) %/ 2)) %/ 4).

(** ** Row 3 — Crossing numbers and colouring (Albertson)
    OPEN (Albertson's conjecture; known for t ≤ 18 and via the four-colour theorem
    for small cases).

    Source: "We let cr(G) denote the crossing number of a graph G.  Conjecture
      Every graph G with χ(G) ≥ t satisfies cr(G) ≥ cr(K_t)."

    Carrier: arbitrary [sgraph]; χ([set: G]) is the whole-graph chromatic number
    (base/coloring).

    WAVE-2 FORM (sub-level, NON-VACUOUS): the source inequality cr(K_t) ≤ cr(G)
    is represented in the split model as "every planarization count achievable
    for G dominates some achievable count for K_t":
    [forall k, crossing_planar_in k G -> exists j <= k, crossing_planar_in
    j 'K_t].  The [exists j <= k] (rather than exactly [k]) is deliberate —
    [crossing_planar_in] counts EXACT split numbers and is not monotone in [k],
    so the sub-level form is the correct encoding of the ≤ comparison of minima.
    It has content for every planarizable G (no inhabitance gate). *)
Definition crossing_numbers_and_coloring_statement : Prop :=
  forall (G : sgraph) (t k : nat),
    (t <= χ([set: G]))%N ->
    crossing_planar_in k G ->
    exists j : nat, (j <= k)%N /\ crossing_planar_in j 'K_t.

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

    WAVE-2 FORM (two-sided, NON-VACUOUS).  The former ε–N body was gated by
    [is_crossing_number (hypercube d) v] and hence vacuity-conditional exactly
    where the limit lives (d ≥ 4).  The direct form asserts, past N, BOTH sides
    of |cr(Q_d)/4^d − 5/32| < ε on the achievable planarization counts:
    - UPPER + achievability: SOME count [k] is achievable with
      [|32k − 5·4^d| < ε·32·4^d]  (in particular cr ≤ k, giving the upper bound;
      the existence half is part of the conjecture's own claim);
    - LOWER: EVERY achievable count [k] satisfies [(5/32 − ε)·4^d < k], written
      additively as [eps_den·5·4^d < eps_den·32·k + eps_num·32·4^d] so no
      truncated subtraction is needed.  (One-sided on purpose: counts above the
      minimum are legitimate, so only the lower bound may quantify over all [k].)
    Together these pin the minimum into the ε-window, i.e. the limit is 5/32.
    Non-vacuity of the family's planar base stays certified in [grounding_D3cr]
    ([cr_hypercube0]/[cr_hypercube1], [cr_K1]). *)
Definition the_crossing_number_of_the_hypercube_statement : Prop :=
  forall (eps_num eps_den : nat),
    (0 < eps_num)%N -> (0 < eps_den)%N ->
    exists N : nat,
      forall d : nat,
        (N <= d)%N ->
        (exists k : nat,
            crossing_planar_in k (hypercube d) /\
            (eps_den * ((32 * k - 5 * 4 ^ d) + (5 * 4 ^ d - 32 * k))
               < eps_num * (32 * 4 ^ d))%N) /\
        (forall k : nat,
            crossing_planar_in k (hypercube d) ->
            (eps_den * (5 * 4 ^ d)
               < eps_den * (32 * k) + eps_num * (32 * 4 ^ d))%N).
