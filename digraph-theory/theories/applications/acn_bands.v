(** * Digraph.acn_bands — radix keys and the ACₙ band kit (shared)

    Shared machinery for applications built on the circulant tournament
    ACₙ (n = 2m+1): the k = 5 family ACₙ[ACₙ] (applications/k5/) and the
    k = 4 family ACₙ[C₃] (applications/k4/) both order vertices by a
    radix nat key whose leading digit is a *band* of the ACₙ coordinate.

    Contents (moved verbatim from k5/cells.v, M14 / D13):
    - radix encode/decode lemmas for lexicographic keys
      ([radix_ltA], [radix_lt_inv], [radix_eq_inv]);
    - the band c : 'Z_n → {1,2,3} — 1 on Hi = [m+1,2m], 2 on Lo = [1,m],
      3 on {0} — with its characterizations [band1P]/[band2P]/[band3P],
      bounds [band_ge1]/[band_le3], dichotomy [band12P];
    - [AC_wrapF]: a backward residue over a gap below m is never a
      connection element (no backedge within a monotone <m-interval);
    - [band_gap]: within a (nonzero) band, value gaps stay below m. *)

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

(** ** Radix lemmas for lexicographic keys *)

Lemma radix_ltA (N c c' x x' : nat) :
  (x < N)%N -> (c < c')%N -> (c * N + x < c' * N + x')%N.
Proof.
move=> xN cc.
apply: (@leq_trans (c.+1 * N)%N); first by rewrite mulSn addnC ltn_add2r.
apply: (leq_trans _ (leq_addr x' _)).
by rewrite leq_mul2r cc orbT.
Qed.

Lemma radix_lt_inv (N A B y y' : nat) :
  (y < N)%N -> (y' < N)%N -> (A * N + y < B * N + y')%N ->
  (A < B)%N \/ (A = B /\ (y < y')%N).
Proof.
move=> yN y'N h.
case: (ltngtP A B) => [lt|gt|e]; [by left| |right].
- by have := ltn_trans h (radix_ltA y y'N gt); rewrite ltnn.
- by split => //; move: h; rewrite e ltn_add2l.
Qed.

Lemma radix_eq_inv (N A B y y' : nat) :
  (y < N)%N -> (y' < N)%N -> (A * N + y = B * N + y')%N -> A = B /\ y = y'.
Proof.
move=> yN y'N e.
have e1 : y = y'.
  by move: (congr1 (fun t => (t %% N)%N) e); rewrite !modnMDl !modn_small.
have e2 : A = B.
  move: (congr1 (fun t => (t %/ N)%N) e).
  by rewrite !divnMDl ?divn_small ?addn0 //; case: N yN {y'N e e1}.
by [].
Qed.

Section AcnBands.
Variable m' : nat.
Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).

(** ** Bands *)

Definition band (v : 'Z_n) : nat :=
  if (val v == 0)%N then 3 else if (val v <= m)%N then 2 else 1.

Lemma band1P (v : 'Z_n) : (band v == 1) = (m < val v)%N.
Proof.
rewrite /band; case: (posnP (val v)) => [->|pos] //=.
by case: ifP => h /=; rewrite ltnNge h.
Qed.

Lemma band2P (v : 'Z_n) : (band v == 2) = (0 < val v <= m)%N.
Proof.
rewrite /band; case: (posnP (val v)) => [->|pos] //=.
by case: ifP.
Qed.

Lemma band3P (v : 'Z_n) : (band v == 3) = (val v == 0)%N.
Proof.
by rewrite /band; case: ifP => h //=; case: ifP.
Qed.

Lemma band_ge1 (v : 'Z_n) : (1 <= band v)%N.
Proof. by rewrite /band; case: ifP => // _; case: ifP. Qed.

Lemma band_le3 (v : 'Z_n) : (band v <= 3)%N.
Proof. by rewrite /band; case: ifP => // _; case: ifP. Qed.

(** Two band dichotomies. *)
Lemma band12P (v : 'Z_n) : band v != 3 ->
  (band v == 1) || (band v == 2).
Proof.
have b1 := band_ge1 v; have b2 := band_le3 v.
by move: b1 b2; case: (band v) => [|[|[|[|?]]]].
Qed.

(** Pure-nat helpers (kept 'Z_n-free to avoid dependent-rewrite traps). *)
Let dbl_lt_addr (k x : nat) : (k < x)%N -> (k.*2 < x + k)%N.
Proof. by move=> h; rewrite -addnn ltn_add2r. Qed.

Let lt_addl_pos (k x : nat) : (0 < x)%N -> (k < x + k)%N.
Proof. by move=> h; rewrite -{1}[k]add0n ltn_add2r. Qed.

(** A backward residue over a gap below m is never a connection element. *)
Lemma AC_wrapF (a b : 'Z_n) : (val a < val b)%N -> (val b - val a < m)%N ->
  (a - b \in ACset m') = false.
Proof.
move=> ab gap.
rewrite AC_mem_val (val_sub_gt ab).
have lo : (m.+1 < n - (val b - val a))%N.
  rewrite ltn_subRL.
  apply: (leq_ltn_trans (leq_add (gap : (val b - val a <= m')%N) (leqnn m.+1))).
  by rewrite !addnS addnn ltnSn.
rewrite (leq_gtF (ltnW (ltn_trans (ltnSn m) lo))) andbF.
by rewrite (gtn_eqF lo).
Qed.

(** Within a (nonzero) band, value gaps stay below m. *)
Lemma band_gap (a b : 'Z_n) : band a = band b -> band a != 3 ->
  (val a < val b)%N -> (val b - val a < m)%N.
Proof.
move=> e b3 ab.
case/orP: (band12P b3) => [h1|h2].
- have hb : (m < val b)%N by rewrite -band1P -e.
  have ha : (m < val a)%N by rewrite -band1P.
  have hbu : (val b <= m.*2)%N by rewrite -ltnS ltn_ord.
  rewrite ltn_subLR ?(ltnW ab) //.
  exact: leq_ltn_trans hbu (dbl_lt_addr ha).
- have hb : (0 < val b <= m)%N by rewrite -band2P -e.
  have ha : (0 < val a <= m)%N by rewrite -band2P.
  case/andP: hb => _ hbu; case/andP: ha => hap _.
  rewrite ltn_subLR ?(ltnW ab) //.
  exact: leq_ltn_trans hbu (lt_addl_pos m hap).
Qed.

End AcnBands.
