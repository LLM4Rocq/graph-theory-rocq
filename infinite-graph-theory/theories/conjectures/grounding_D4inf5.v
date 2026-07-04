(** * Grounding for the odd-distance colouring row (the encoding has content). *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph conjectures.D4inf5.
From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The odd-distance relation is NON-TRIVIAL: any point is adjacent to its
    unit-x-shift (distance 1, an odd integer).  So [OddG] is not edgeless. *)
Lemma odd_dist_shift (R : rcfType) (p : R * R) :
  odd_dist p (p.1 + 1, p.2).
Proof.
exists 1%N; split=> //=.
have -> : p.1 - (p.1 + 1) = -1 by rewrite opprD addrA subrr add0r.
by rewrite subrr sqrrN !expr2 !mulr1 mulr0 addr0.
Qed.

(** ['I_1] is a subsingleton (only one colour). *)
Lemma I1_eq (i j : 'I_1) : i = j.
Proof.
apply: val_inj => /=.
have v0 : forall k : 'I_1, nat_of_ord k = 0.
  by move=> k; move: (ltn_ord k); rewrite ltnS leqn0 => /eqP.
by rewrite !v0.
Qed.

(** So a single odd-distance edge is NOT 1-colourable: the colouring guard has
    teeth (the finite-subgraph chromatic-unboundedness statement is non-vacuous —
    for [n = 1] a 2-point set already fails). *)
Lemma not_1_colorable (R : rcfType) (p : R * R) :
  ~ n_colorable [:: p; (p.1 + 1, p.2)] 1.
Proof.
case=> c H; move: (H p (p.1 + 1, p.2)).
rewrite !inE !eqxx ?orbT /= => /(_ isT isT (odd_dist_shift p)) Hne.
by apply: Hne; exact: I1_eq.
Qed.
