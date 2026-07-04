(** * Infinite.conjectures.D4inf5 — colouring the odd-distance graph (PARTIAL).

    The Odd Distance Graph O has vertex set ℝ² with two points adjacent iff their
    distance is an odd integer.  We ask whether χ(O) = ∞.

    Carrier: an [iGraph] on [R * R] over an abstract REAL-CLOSED field [R]
    ([rcfType], not axiom-laden Stdlib [Reals]); the edge is sqrt-free —
    [∃ m, odd m ∧ (Δx)² + (Δy)² = (m:R)²].

    PARTIAL (two labelled proxies):
    (1) READING-2.  χ(O) = ∞ is rendered as "the finite subgraphs have unbounded
        chromatic number": for every [n] there is a FINITE point set not properly
        [n]-colourable.  This implies χ(O) = ∞; the converse is De Bruijn–Erdős,
        which needs choice — so this is the choice-free direction, formally
        stronger than (hence a faithful proxy for) the literal χ = ∞.
    (2) FIELD-GENERIC.  Quantifying [forall R : rcfType] is a proxy for the
        specific field ℝ (colourings are second-order, so no Tarski transfer). *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph.
From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section OddDistance.
Variable R : rcfType.
Definition oddpt := (R * R)%type.

(** Two points are at ODD-INTEGER distance (squared, to avoid a square root). *)
Definition odd_dist (p q : oddpt) : Prop :=
  exists m : nat, odd m /\ (p.1 - q.1) ^+ 2 + (p.2 - q.2) ^+ 2 = (m%:R) ^+ 2.

Lemma odd_dist_sym : irel_sym odd_dist.
Proof.
move=> p q [m [Hm E]]; exists m; split=> //.
by rewrite -[q.1 - p.1]opprB sqrrN -[q.2 - p.2]opprB sqrrN.
Qed.

Lemma odd_dist_irr : irel_irr odd_dist.
Proof.
move=> p [m [Hm E]].
have H2 : (m%:R : R) ^+ 2 == 0 by rewrite -E !subrr !expr2 !mulr0 addr0.
move: H2; rewrite expf_eq0 pnatr_eq0 => /andP[_ /eqP m0].
by move: Hm; rewrite m0.
Qed.

Definition OddG : iGraph := Build_iGraph odd_dist_sym odd_dist_irr.

(** A finite point set [S] is properly [n]-colourable in O. *)
Definition n_colorable (S : seq oddpt) (n : nat) : Prop :=
  exists c : oddpt -> 'I_n,
    forall p q, p \in S -> q \in S -> odd_dist p q -> c p <> c q.

End OddDistance.

Arguments odd_dist {R} p q.
Arguments n_colorable {R} S n.

(** ** coloring_the_odd_distance_graph  (Question, OPEN — PARTIAL)

    Reading-2: the odd-distance graph's finite subgraphs have UNBOUNDED chromatic
    number — for every [n] a finite point set fails to be [n]-colourable. *)
Definition coloring_the_odd_distance_graph_statement : Prop :=
  forall (R : rcfType) (n : nat), exists S : seq (R * R), ~ n_colorable S n.
