(** * Digraph.in_neighbourhood — Lemma H17

    Paper Lemma H17: for x in the Hi band and y in the Lo band of ACₙ, the
    common in-neighbourhood N⁻(x) ∩ N⁻(y) lies in a *single* band — below m
    when val x ≤ val y + m, above m otherwise ([H17_side]). The form consumed
    by the square obstructions (obstructions.v) is [H17_no_mixed]: no Hi
    vertex and Lo vertex can both beat both x and y.

    Membership [z --> v] in ACₙ is used in the equivalent residue form
    [v - z \in ACset] (cf. [AC_arcE]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive substitution.
From Digraph Require Import acn_arc_facts acn_base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section H17.
Variable m' : nat.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).

(** Connection-set elements have value in [1, m+1] ∖ {m}. *)
Lemma gval_bounds (g1 : 'Z_n) : g1 \in ACset m' ->
  [/\ (0 < val g1)%N, (val g1 <= m.+1)%N & val g1 != m].
Proof.
rewrite AC_mem_val => /orP[/andP[pos lt]|/eqP e].
- split=> //; first by rewrite (leq_trans (ltnW lt)) // leqW.
  by rewrite (ltn_eqF lt).
- by rewrite e; split=> //; rewrite gtn_eqF // ltnSn.
Qed.

(** An in-neighbour of an Hi vertex sits in the window [vx−m−1, vx−1]. *)
Lemma H17_xrange (x z : 'Z_n) : (m < val x)%N -> x - z \in ACset m' ->
  (val z < val x)%N /\ (val x <= val z + m.+1)%N.
Proof.
move=> hx hg.
have [g1pos g1ub _] := gval_bounds hg.
have zltx : (val z < val x)%N.
  case: (leqP (val z) (val x)) => [le|gt].
  - rewrite ltn_neqAle le andbT.
    apply/eqP=> e; move: g1pos.
    by rewrite (val_sub_le le) e subnn.
  - have dle : (val z - val x <= m')%N.
      rewrite leq_subLR.
      apply: (leq_trans (_ : (val z <= m.*2)%N)); first by rewrite -ltnS ltn_ord.
      apply: (leq_trans _ (leq_add hx (leqnn m'))).
      by rewrite -[m.*2]/(m'.*2.+2) -[(m'.+2 + m')%N]/(((m' + m').+2)%N) !ltnS addnn.
    have := g1ub; rewrite (val_sub_gt gt) leq_subLR => h.
    have := leq_trans h (leq_add dle (leqnn m.+1)).
    by rewrite !addnS addnn ltnn.
split=> //.
rewrite (val_sub_le (ltnW zltx)) in g1ub.
by move: g1ub; rewrite leq_subLR addnC.
Qed.

(** An in-neighbour of a Lo vertex is either below it or ≥ m positions up. *)
Lemma H17_dichot (y z : 'Z_n) : (0 < val y <= m)%N -> y - z \in ACset m' ->
  (val z < val y)%N \/ (val y + m <= val z)%N.
Proof.
case/andP=> ypos yle hg.
have [g2pos g2ub _] := gval_bounds hg.
case: (leqP (val z) (val y)) => [le|gt]; [left|right].
- rewrite ltn_neqAle le andbT.
  apply/eqP=> e; move: g2pos.
  by rewrite (val_sub_le le) e subnn.
- have := g2ub; rewrite (val_sub_gt gt) leq_subLR => h.
  rewrite -leq_subRL ?(ltnW gt) //.
  rewrite leqNgt; apply/negP=> dlt.
  have := leq_trans h (leq_add (dlt : (val z - val y <= m')%N) (leqnn m'.+2)).
  by rewrite !addnS addnn ltnn.
Qed.

(** H17: the common in-neighbourhood lies in the band determined by x − y. *)
Lemma H17_side (x y z : 'Z_n) :
  (m < val x)%N -> (0 < val y <= m)%N ->
  x - z \in ACset m' -> y - z \in ACset m' ->
  if (val x <= val y + m)%N then (val z < m)%N else (m < val z)%N.
Proof.
move=> hx hy gx gy.
have [zx xzm] := H17_xrange hx gx.
case/andP: (hy) => ypos yle.
case: ifP => [le|gt'].
- case: (H17_dichot hy gy) => [zy|ge].
  + exact: leq_trans zy yle.
  + by have := leq_trans (leq_ltn_trans ge zx) le; rewrite ltnn.
- move/negbT: gt'; rewrite -ltnNge => gt.
  case: (H17_dichot hy gy) => [zy|ge].
  + have : (val x <= val y + m)%N.
      apply: (leq_trans xzm).
      by rewrite addnS -addSn leq_add2r.
    by rewrite leqNgt gt.
  + apply: (leq_trans _ ge).
    by rewrite -add1n leq_add2r.
Qed.

(** The working corollary: an Hi vertex and a Lo vertex can never both beat
    both an Hi vertex x and a Lo vertex y. *)
Lemma H17_no_mixed (x y zH zL : 'Z_n) :
  (m < val x)%N -> (0 < val y <= m)%N ->
  (m < val zH)%N -> (0 < val zL <= m)%N ->
  x - zH \in ACset m' -> y - zH \in ACset m' ->
  x - zL \in ACset m' -> y - zL \in ACset m' -> False.
Proof.
move=> hx hy hzH hzL gxH gyH gxL gyL.
have h1 := H17_side hx hy gxH gyH.
have h2 := H17_side hx hy gxL gyL.
case/andP: hzL => _ zLle.
case: ifP h1 h2 => _ h1 h2.
- by have := ltn_trans hzH h1; rewrite ltnn.
- by have := leq_ltn_trans zLle h2; rewrite ltnn.
Qed.

End H17.
