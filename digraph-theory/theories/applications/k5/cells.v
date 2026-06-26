(** * Digraph.cells — the inner-then-outer key order and the 8 cells

    For T = ACₙ[ACₙ] we order vertices (a,b) by the lexicographic key
    (c(b), c(a), val a, val b), where the *band* c(v) is 1 on Hi = [m+1,2m],
    2 on Lo = [1,m] and 3 on {0} (paper §5). The *cell* of a vertex is
    (c(b), c(a)), encoded as [cidx ∈ [0..8]]; cell 8 = (3,3) is occupied by
    (0,0) alone, so survivors of T − (0,0) occupy cells 0..7.

    The radix lemmas and the band kit ([band], [band1P/2P/3P], [AC_wrapF],
    [band_gap]) live in the shared applications/acn_bands.v (re-exported
    here); this file keeps the T5-specific cell machinery.

    Contents:
    - the realized key order [qk] and its characterization [qkE];
    - the *beat conditions* for clique members ([beat_blocks]/[beat_inner]:
      the higher-key reps beat the lower-key ones, blockwise);
    - the cell Lemma ([cidx_inj_clique]): no backedge inside a cell, so a
      backedge clique has at most one vertex per cell;
    - the cardinality bridge ([card_clique_cidx]): #|K| = Σ cell-occupancy. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive substitution.
From Digraph Require Import acn_arc_facts acn_base.
From Digraph Require Export acn_bands.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Cells.
Variable m' : nat.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').
Local Notation T5 := (lexprod_tournament ACm ACm).

(** ** Cells and the key *)

Definition cidx (w : T5) : nat := (band w.2 - 1) * 3 + (band w.1 - 1).

Lemma cidx_decode (w : T5) :
  band w.2 = ((cidx w) %/ 3).+1 /\ band w.1 = ((cidx w) %% 3).+1.
Proof.
have hb2 : (band w.2 - 1 < 3)%N by rewrite ltn_subLR ?band_ge1 //; exact: band_le3.
have hb1 : (band w.1 - 1 < 3)%N by rewrite ltn_subLR ?band_ge1 //; exact: band_le3.
rewrite /cidx divnMDl // divn_small // addn0 modnMDl modn_small //.
by rewrite !subn1 !(ltn_predK (band_ge1 _)).
Qed.

Lemma cidx_le8 (w : T5) : (cidx w <= 8)%N.
Proof.
rewrite /cidx.
have hb2 : (band w.2 - 1 <= 2)%N by rewrite leq_subLR band_le3.
have hb1 : (band w.1 - 1 <= 2)%N by rewrite leq_subLR band_le3.
apply: (@leq_trans (2 * 3 + 2)%N) => //.
by apply: leq_add => //; rewrite leq_mul2r hb2 orbT.
Qed.

Definition key (w : T5) : nat := ((cidx w) * n + val w.1) * n + val w.2.

Lemma key_inj : injective key.
Proof.
move=> [a b] [a' b'] e.
have [e1 e2] := radix_eq_inv (ltn_ord _) (ltn_ord _) e.
have [_ e3] := radix_eq_inv (ltn_ord _) (ltn_ord _) e1.
by rewrite (val_inj e2 : b = b') (val_inj e3 : a = a').
Qed.

Lemma cidx_mono (w w' : T5) : (cidx w < cidx w')%N -> (key w < key w')%N.
Proof.
move=> h; apply: radix_ltA (ltn_ord _) _.
exact: radix_ltA (ltn_ord _) h.
Qed.

Lemma key_samecell (w w' : T5) : cidx w = cidx w' -> (key w < key w')%N ->
  (val w.1 < val w'.1)%N \/ (w.1 = w'.1 /\ (val w.2 < val w'.2)%N).
Proof.
move=> ec h.
case: (radix_lt_inv (ltn_ord _) (ltn_ord _) h) => [h1|[e1 h2]]; last first.
  case: (radix_eq_inv (ltn_ord _) (ltn_ord _) e1) => _ ea.
  by right; split=> //; exact: val_inj.
case: (radix_lt_inv (ltn_ord _) (ltn_ord _) h1) => [hc|[_ ha]]; last by left.
by move: hc; rewrite ec ltnn.
Qed.

(** ** The realized key order *)

Definition rk := [rel u v : T5 | (key u < key v)%N].
Fact rk_irr : irreflexive rk. Proof. by move=> u /=; rewrite ltnn. Qed.
Fact rk_trans : transitive rk. Proof. by move=> a b c /=; apply: ltn_trans. Qed.
Fact rk_total (u v : T5) : u != v -> rk u v || rk v u.
Proof.
move=> uDv; rewrite /= -neq_ltn.
by apply: contraNneq uDv => /key_inj->.
Qed.

Definition qk : {perm T5} := realize rk.

Lemma qkE (u v : T5) : ltp qk u v = (key u < key v)%N.
Proof. exact: (ltp_realizeE rk_irr rk_trans rk_total). Qed.

(** ** Beat conditions for clique members *)

Section InClique.
Variables (K : {set backedge qk}).
Hypothesis Kcl : forall u v : backedge qk,
  u \in K -> v \in K -> u != v -> u -- v.

Lemma beat_key (u v : backedge qk) : u \in K -> v \in K ->
  (key u < key v)%N -> ((v : T5) --> (u : T5)).
Proof.
move=> uK vK kuv.
have uDv : u != v by apply: contraTneq kuv => ->; rewrite ltnn.
have := Kcl uK vK uDv.
by rewrite backedgeE !qkE kuv (leq_gtF (ltnW kuv)) /= orbF.
Qed.

(** Between different blocks, the beaten block-difference is a connection
    element; inside a block the inner difference is. *)
Lemma beat_blocks (u v : backedge qk) : u \in K -> v \in K ->
  (key u < key v)%N -> (u : T5).1 != (v : T5).1 ->
  ((u : T5).1 : 'Z_n) - ((v : T5).1 : 'Z_n) \in ACset m'.
Proof.
move=> uK vK kuv aDa.
have := beat_key uK vK kuv.
rewrite lexprod_arcE eq_sym (negbTE aDa) andFb orbF => h.
by rewrite -AC_arcE.
Qed.

Lemma beat_inner (u v : backedge qk) : u \in K -> v \in K ->
  (key u < key v)%N -> (u : T5).1 = (v : T5).1 ->
  ((u : T5).2 : 'Z_n) - ((v : T5).2 : 'Z_n) \in ACset m'.
Proof.
move=> uK vK kuv aEa.
have := beat_key uK vK kuv.
rewrite lexprod_arcE -aEa arcxx eqxx /= => h.
by rewrite -AC_arcE.
Qed.

(** ** The cell Lemma: at most one clique vertex per cell *)

Lemma cidx_inj_clique : {in K &, forall u v : backedge qk,
  cidx (u : T5) = cidx (v : T5) -> u = v}.
Proof.
have main (u v : backedge qk) : u \in K -> v \in K ->
    cidx (u : T5) = cidx (v : T5) -> (key u < key v)%N -> False.
  move=> uK vK ec kuv.
  have [d1 d2] := cidx_decode (u : T5).
  have [d1' d2'] := cidx_decode (v : T5).
  case: (key_samecell ec kuv) => [alt|[aE blt]].
  - (* outer values differ: same a-band, forward gap, backedge impossible *)
    have aDa : (u : T5).1 != (v : T5).1.
      by apply: contraTneq alt => ->; rewrite ltnn.
    have hmem := beat_blocks uK vK kuv aDa.
    have ebandA : band ((u : T5).1 : 'Z_n) = band ((v : T5).1 : 'Z_n).
      by rewrite d2 d2' ec.
    have b3 : band ((u : T5).1 : 'Z_n) != 3.
      apply/negP; rewrite band3P => /eqP z1.
      have : band ((v : T5).1 : 'Z_n) == 3 by rewrite -ebandA band3P z1.
      rewrite band3P => /eqP z1'.
      by move: alt; rewrite z1 z1' ltnn.
    have gap := band_gap ebandA b3 alt.
    by move: hmem; rewrite (AC_wrapF alt gap).
  - (* inner values differ: same b-band, forward gap *)
    have hmem := beat_inner uK vK kuv aE.
    have ebandB : band ((u : T5).2 : 'Z_n) = band ((v : T5).2 : 'Z_n).
      by rewrite d1 d1' ec.
    have b3 : band ((u : T5).2 : 'Z_n) != 3.
      apply/negP; rewrite band3P => /eqP z1.
      have : band ((v : T5).2 : 'Z_n) == 3 by rewrite -ebandB band3P z1.
      rewrite band3P => /eqP z1'.
      by move: blt; rewrite z1 z1' ltnn.
    have gap := band_gap ebandB b3 blt.
    by move: hmem; rewrite (AC_wrapF blt gap).
move=> u v uK vK ec.
case: (ltngtP (key u) (key v)) => [lt|gt|e].
- by case: (main _ _ uK vK ec lt).
- by case: (main _ _ vK uK (esym ec) gt).
- exact: key_inj e.
Qed.

(** ** Occupancy and the cardinality bridge *)

Definition occ (i : nat) : bool := [exists u in K, cidx (u : T5) == i].

Lemma occP (i : nat) :
  reflect (exists2 u, u \in K & cidx (u : T5) = i) (occ i).
Proof.
apply: (iffP existsP) => [[u /andP[uK /eqP e]]|[u uK e]]; first by exists u.
by exists u; rewrite uK e eqxx.
Qed.

Lemma card_clique_cidx : #|K| = (\sum_(i < 9) occ i)%N.
Proof.
pose f (u : backedge qk) : 'I_9 := inord (cidx (u : T5)).
have fE u : f u = cidx (u : T5) :> nat.
  by rewrite /f inordK // ltnS cidx_le8.
have finj : {in K &, injective f}.
  move=> u v uK vK e; apply: (cidx_inj_clique uK vK).
  by rewrite -(fE u) -(fE v) e.
rewrite -(card_in_imset finj).
have -> : #|f @: K| = (\sum_(i < 9) (i \in f @: K))%N.
  rewrite -sum1_card big_mkcond /=.
  by apply: eq_bigr => i _; case: (_ \in _).
apply: eq_bigr => i _.
congr nat_of_bool.
apply/imsetP/(occP i) => [[u uK e]|[u uK e]].
- by exists u; rewrite // -(fE u) -e.
- by exists u; rewrite //; apply: ord_inj; rewrite fE e.
Qed.

End InClique.

End Cells.
