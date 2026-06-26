(** * Digraph.k4_value — ω̄(ACₙ[C₃]) ≤ 4 (the merged order kv)

    M15 (docs/k34_dossier.md §2, items V0–V7). The witness order is the
    radix key kv (t,h) := (κ(t,h)·n + t)·3 + h, where the merged class
    κ = band t + dband h ∈ {2,…,5} (V0). A backedge clique K has at most
    one vertex per (band, dband) sub-band σ ∈ {0,…,5}
    ([sidx_inj_clique], V1–V4: within a sub-band the t-gap stays below m
    — [AC_wrapF] — or the same block needs the false C₃ arc 2 → 1), so
    #|K| = Σ σ-occupancies ([card_classes_inj], G2). Two exclusions cap
    the sum at 4:
    - [occ24_5F]/[occ24_1F] (V5): if both κ = 4 sub-bands are occupied,
      the pair is forced to {(m,0),(0,i)} ([occ24_block]) and then
      neither (0,0) nor any κ = 3 low fits;
    - [occ5310_F] (V6): (0,0), a κ3 high, a κ3 low and a κ2 member
      force blocks m+1, 1, m+1 and die on the forward arc 1 → m+1.
    Exit: [omegabar_T4] : ω̄(ACₙ[C₃]) = 4 (with M14's lower bound). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive substitution.
From Digraph Require Import acn_arc_facts acn_base acn_bands k4_lower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** ** The inner band on C₃ (h = 0 heavy, h ≠ 0 light) *)

Definition dband (h : C3) : nat := if (val h == 0)%N then 2 else 1.

Lemma dband2P (h : C3) : (dband h == 2) = (val h == 0)%N.
Proof. by rewrite /dband; case: ifP. Qed.

Lemma dband1P (h : C3) : (dband h == 1) = (val h != 0)%N.
Proof. by rewrite /dband; case: ifP. Qed.

Lemma dband_ge1 (h : C3) : (1 <= dband h)%N.
Proof. by rewrite /dband; case: ifP. Qed.

Lemma dband_le2 (h : C3) : (dband h <= 2)%N.
Proof. by rewrite /dband; case: ifP. Qed.

Section K4Value.
Variable m' : nat.
Hypothesis m3 : (3 <= m'.+1)%N.

Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').
Local Notation C3t := (C3 : tournament).
Local Notation T4 := (lexprod_tournament ACm C3t).

(** ** Sub-bands, classes, and the merged key *)

Definition sidx (w : T4) : nat := (dband w.2 - 1) * 3 + (band w.1 - 1).

Lemma sidx_decode (w : T4) :
  dband w.2 = ((sidx w) %/ 3).+1 /\ band w.1 = ((sidx w) %% 3).+1.
Proof.
have hb1 : (band w.1 - 1 < 3)%N.
  by rewrite ltn_subLR ?band_ge1 //; exact: band_le3.
rewrite /sidx divnMDl // divn_small // addn0 modnMDl modn_small //.
by rewrite !subn1 !(ltn_predK (band_ge1 _)) (ltn_predK (dband_ge1 _)).
Qed.

Lemma sidx_le5 (w : T4) : (sidx w <= 5)%N.
Proof.
rewrite /sidx.
have hb2 : (dband w.2 - 1 <= 1)%N by rewrite leq_subLR dband_le2.
have hb1 : (band w.1 - 1 <= 2)%N by rewrite leq_subLR band_le3.
apply: (@leq_trans (1 * 3 + 2)%N) => //.
by apply: leq_add => //; rewrite leq_mul2r hb2 orbT.
Qed.

Definition kappa (w : T4) : nat := band w.1 + dband w.2.

Lemma kappa_sidx (w : T4) : kappa w = ((sidx w) %% 3 + (sidx w) %/ 3).+2.
Proof.
have [d c] := sidx_decode w.
by rewrite /kappa c d addSn addnS.
Qed.

Definition kv (w : T4) : nat := ((kappa w) * n + val w.1) * 3 + val w.2.

Lemma kv_inj : injective kv.
Proof.
move=> [t h] [t' h'] e.
have [e1 e2] := radix_eq_inv (ltn_ord _) (ltn_ord _) e.
have [_ e3] := radix_eq_inv (ltn_ord _) (ltn_ord _) e1.
by rewrite (val_inj e2 : h = h') (val_inj e3 : t = t').
Qed.

Lemma kv_kappa_mono (w w' : T4) :
  (kappa w < kappa w')%N -> (kv w < kv w')%N.
Proof.
move=> h; apply: radix_ltA (ltn_ord _) _.
exact: radix_ltA (ltn_ord _) h.
Qed.

Lemma kv_lt_t (w w' : T4) : kappa w = kappa w' ->
  (val w.1 < val w'.1)%N -> (kv w < kv w')%N.
Proof.
by move=> ek lt; apply: radix_ltA (ltn_ord _) _; rewrite ek ltn_add2l.
Qed.

Lemma kv_samekappa (w w' : T4) : kappa w = kappa w' -> (kv w < kv w')%N ->
  (val w.1 < val w'.1)%N \/ (w.1 = w'.1 /\ (val w.2 < val w'.2)%N).
Proof.
move=> ec h.
case: (radix_lt_inv (ltn_ord _) (ltn_ord _) h) => [h1|[e1 h2]]; last first.
  case: (radix_eq_inv (ltn_ord _) (ltn_ord _) e1) => _ ea.
  by right; split=> //; exact: val_inj.
case: (radix_lt_inv (ltn_ord _) (ltn_ord _) h1) => [hc|[_ ha]]; last by left.
by move: hc; rewrite ec ltnn.
Qed.

(** ** The realized merged order *)

Definition rv := [rel u v : T4 | (kv u < kv v)%N].
Fact rv_irr : irreflexive rv. Proof. by move=> u /=; rewrite ltnn. Qed.
Fact rv_trans : transitive rv. Proof. by move=> a b c /=; apply: ltn_trans. Qed.
Fact rv_total (u v : T4) : u != v -> rv u v || rv v u.
Proof.
move=> uDv; rewrite /= -neq_ltn.
by apply: contraNneq uDv => /kv_inj->.
Qed.

Definition qv : {perm T4} := realize rv.

Lemma qvE (u v : T4) : ltp qv u v = (kv u < kv v)%N.
Proof. exact: (ltp_realizeE rv_irr rv_trans rv_total). Qed.

(** ** Residue arithmetic helpers (pure nat, m-relative) *)

Lemma n_sub_ge_Sm (d : nat) : (d <= m)%N -> (m.+1 <= n - d)%N.
Proof. by move=> dm; rewrite ltn_subRL ltnS -addnn leq_add2r. Qed.

Lemma n_sub_gt_Sm (d : nat) : (d < m)%N -> (m.+1 < n - d)%N.
Proof. by move=> dm; rewrite ltn_subRL addnS ltnS -addnn ltn_add2r. Qed.

Lemma n_sub_eq_Sm (d : nat) : (d <= m.*2)%N -> ((n - d)%N == m.+1) = (d == m)%N.
Proof.
move=> dle; rewrite -(eqn_add2r d) subnK ?(leqW dle) //.
by rewrite -addnn -addSn eqn_add2l eq_sym.
Qed.

Lemma sub_eq_m (a : nat) : (a <= m)%N -> ((m.+1 - a)%N == m) = (a == 1)%N.
Proof.
move=> am; rewrite -(eqn_add2r a) subnK ?(leqW am) //.
by rewrite -[in X in (X == _) = _]addn1 eqn_add2l eq_sym.
Qed.

(** Connection-set refutations by value. *)
Lemma mem_m_F (z : 'Z_n) : val z = m -> (z \in ACset m') = false.
Proof.
by move=> vz; rewrite AC_mem_val vz ltnn andbF (ltn_eqF (ltnSn m)).
Qed.

Lemma mem_mid_F (z : 'Z_n) : (m.+1 < val z)%N -> (z \in ACset m') = false.
Proof.
by move=> h; rewrite (AC_mem_Hi (ltnW h)) (gtn_eqF h).
Qed.

Lemma vals12 (a b : nat) : (a < b)%N -> (b < 3)%N -> a != 0%N ->
  a = 1%N /\ b = 2%N.
Proof. by case: a => [|[|?]] //; case: b => [|[|[|?]]]. Qed.

(** The 64-case occupancy arithmetic behind V5/V6. *)
Let bool_final (o0 o1 o2 o3 o4 o5 : bool) :
  (o2 && o4) ==> (~~ o5 && ~~ o1) ->
  ~~ [&& o5, o3, o1 & o0] ->
  (o0 + o1 + o2 + o3 + o4 + o5 <= 4)%N.
Proof. by case: o0; case: o1; case: o2; case: o3; case: o4; case: o5. Qed.

(** ** Beat conditions for clique members *)

Section InCliqueV.
Variables (K : {set backedge qv}).
Hypothesis Kcl : forall u v : backedge qv,
  u \in K -> v \in K -> u != v -> u -- v.

Lemma beat_kv (u v : backedge qv) : u \in K -> v \in K ->
  (kv (u : T4) < kv (v : T4))%N -> ((v : T4) --> (u : T4)).
Proof.
move=> uK vK kuv.
have uDv : u != v by apply: contraTneq kuv => ->; rewrite ltnn.
have := Kcl uK vK uDv.
by rewrite backedgeE !qvE kuv (leq_gtF (ltnW kuv)) /= orbF.
Qed.

Lemma beat_blocksV (u v : backedge qv) : u \in K -> v \in K ->
  (kv (u : T4) < kv (v : T4))%N -> (u : T4).1 != (v : T4).1 ->
  ((u : T4).1 : 'Z_n) - ((v : T4).1 : 'Z_n) \in ACset m'.
Proof.
move=> uK vK kuv aDa.
have := beat_kv uK vK kuv.
rewrite lexprod_arcE eq_sym (negbTE aDa) andFb orbF => h.
by rewrite -AC_arcE.
Qed.

Lemma beat_innerV (u v : backedge qv) : u \in K -> v \in K ->
  (kv (u : T4) < kv (v : T4))%N -> (u : T4).1 = (v : T4).1 ->
  ((v : T4).2 --> (u : T4).2).
Proof.
move=> uK vK kuv aEa.
have := beat_kv uK vK kuv.
by rewrite lexprod_arcE -aEa arcxx eqxx /=.
Qed.

(** ** The sub-band Lemma: at most one clique vertex per σ (V1–V4) *)

Lemma sidx_inj_clique : {in K &, forall u v : backedge qv,
  sidx (u : T4) = sidx (v : T4) -> u = v}.
Proof.
have main (u v : backedge qv) : u \in K -> v \in K ->
    sidx (u : T4) = sidx (v : T4) -> (kv (u : T4) < kv (v : T4))%N -> False.
  move=> uK vK ec kuv.
  have ek : kappa (u : T4) = kappa (v : T4) by rewrite !kappa_sidx ec.
  have [du cu] := sidx_decode (u : T4).
  have [dv cv] := sidx_decode (v : T4).
  case: (kv_samekappa ek kuv) => [alt|[aE blt]].
  - (* blocks differ: same t-band, forward gap, backedge impossible *)
    have aDa : (u : T4).1 != (v : T4).1.
      by apply: contraTneq alt => ->; rewrite ltnn.
    have hmem := beat_blocksV uK vK kuv aDa.
    have ebandA : band ((u : T4).1) = band ((v : T4).1).
      by rewrite cu cv ec.
    have b3 : band ((u : T4).1) != 3.
      apply/negP; rewrite band3P => /eqP z1.
      have : band ((v : T4).1) == 3 by rewrite -ebandA band3P z1.
      rewrite band3P => /eqP z1'.
      by move: alt; rewrite z1 z1' ltnn.
    have gap := band_gap ebandA b3 alt.
    by move: hmem; rewrite (AC_wrapF alt gap).
  - (* same block: same h-band, the C₃ arc 2 → 1 is missing *)
    have hmem := beat_innerV uK vK kuv aE.
    have edb : dband ((u : T4).2) = dband ((v : T4).2) by rewrite du dv ec.
    case e0 : (val ((u : T4).2) == 0)%N.
    + have dv2 : (val ((v : T4).2) == 0)%N.
        by rewrite -dband2P -edb dband2P e0.
      by move: blt; rewrite (eqP e0) (eqP dv2) ltnn.
    + have hv0 : (val ((v : T4).2) != 0)%N.
        by rewrite -dband1P -edb dband1P e0.
      have [vu1 vv2] := vals12 blt (ltn_ord _) (negbT e0).
      have eu : ((u : T4).2) = (1 : 'Z_3) :> C3 by apply: val_inj; rewrite vu1.
      have ev : ((v : T4).2) = (1 + 1 : 'Z_3) :> C3.
        by apply: val_inj; rewrite vv2.
      by move: hmem; rewrite arcC3E eu ev.
move=> u v uK vK ec.
case: (ltngtP (kv (u : T4)) (kv (v : T4))) => [lt|gt|e].
- by case: (main _ _ uK vK ec lt).
- by case: (main _ _ vK uK (esym ec) gt).
- exact/kv_inj.
Qed.

(** ** Occupancy *)

Definition occv (i : nat) : bool := [exists u in K, sidx (u : T4) == i].

Lemma occvP (i : nat) :
  reflect (exists2 u, u \in K & sidx (u : T4) = i) (occv i).
Proof.
apply: (iffP existsP) => [[u /andP[uK /eqP e]]|[u uK e]]; first by exists u.
by exists u; rewrite uK e eqxx.
Qed.

Lemma card_clique_sidx : #|K| = (\sum_(i < 6) occv i)%N.
Proof.
apply: card_classes_inj; last exact: sidx_inj_clique.
by move=> u _; rewrite ltnS sidx_le5.
Qed.

(** ** V5: both κ = 4 sub-bands occupied forces {(m,0),(0,i)} *)

Lemma occ24_block (u2 u4 : backedge qv) :
  u2 \in K -> u4 \in K -> sidx (u2 : T4) = 2 -> sidx (u4 : T4) = 4 ->
  val ((u4 : T4).1) = m.
Proof.
move=> u2K u4K s2 s4.
have c2 : band ((u2 : T4).1) = 3.
  by case: (sidx_decode (u2 : T4)) => _ ->; rewrite s2.
have d2 : dband ((u2 : T4).2) = 1.
  by case: (sidx_decode (u2 : T4)) => -> _; rewrite s2.
have c4 : band ((u4 : T4).1) = 2.
  by case: (sidx_decode (u4 : T4)) => _ ->; rewrite s4.
have d4 : dband ((u4 : T4).2) = 2.
  by case: (sidx_decode (u4 : T4)) => -> _; rewrite s4.
have t20 : (val ((u2 : T4).1) == 0)%N by rewrite -band3P c2.
have /andP[t4pos t4le] : (0 < val ((u4 : T4).1) <= m)%N by rewrite -band2P c4.
have ek : kappa (u2 : T4) = kappa (u4 : T4) by rewrite /kappa c2 d2 c4 d4.
have lt12 : (val ((u2 : T4).1) < val ((u4 : T4).1))%N by rewrite (eqP t20).
have kuv := kv_lt_t ek lt12.
have aDa : (u2 : T4).1 != (u4 : T4).1.
  by rewrite -(inj_eq val_inj) (eqP t20) eq_sym (gtn_eqF t4pos).
have hmem := beat_blocksV u2K u4K kuv aDa.
have vE : val (((u2 : T4).1 : 'Z_n) - ((u4 : T4).1 : 'Z_n))
          = (n - val ((u4 : T4).1))%N.
  by rewrite (val_sub_gt lt12) (eqP t20) subn0.
have hi : (m.+1 <= val ((((u2 : T4).1 : 'Z_n) - ((u4 : T4).1 : 'Z_n))%R))%N.
  by rewrite vE; exact: (n_sub_ge_Sm t4le).
have t2m : (val ((u4 : T4).1) <= m.*2)%N.
  by rewrite (leq_trans t4le) // -addnn leq_addr.
move: hmem; rewrite (AC_mem_Hi hi) vE (n_sub_eq_Sm t2m).
by move/eqP.
Qed.

Lemma occ24_5F : occv 2 -> occv 4 -> occv 5 = false.
Proof.
case/occvP=> u2 u2K s2; case/occvP=> u4 u4K s4.
apply/negbTE/negP=> /occvP[u5 u5K s5].
have tm := occ24_block u2K u4K s2 s4.
have c5 : band ((u5 : T4).1) = 3.
  by case: (sidx_decode (u5 : T4)) => _ ->; rewrite s5.
have d5 : dband ((u5 : T4).2) = 2.
  by case: (sidx_decode (u5 : T4)) => -> _; rewrite s5.
have c4 : band ((u4 : T4).1) = 2.
  by case: (sidx_decode (u4 : T4)) => _ ->; rewrite s4.
have d4 : dband ((u4 : T4).2) = 2.
  by case: (sidx_decode (u4 : T4)) => -> _; rewrite s4.
have t50 : (val ((u5 : T4).1) == 0)%N by rewrite -band3P c5.
have ka4 : kappa (u4 : T4) = 4 by rewrite /kappa c4 d4.
have ka5 : kappa (u5 : T4) = 5 by rewrite /kappa c5 d5.
have kuv : (kv (u4 : T4) < kv (u5 : T4))%N.
  by apply: kv_kappa_mono; rewrite ka4 ka5.
have mpos : (0 < val ((u4 : T4).1))%N by rewrite tm.
have aDa : (u4 : T4).1 != (u5 : T4).1.
  by rewrite -(inj_eq val_inj) (eqP t50) (gtn_eqF mpos).
have hmem := beat_blocksV u4K u5K kuv aDa.
have le54 : (val ((u5 : T4).1) <= val ((u4 : T4).1))%N by rewrite (eqP t50).
have vE : val (((u4 : T4).1 : 'Z_n) - ((u5 : T4).1 : 'Z_n)) = m.
  by rewrite (val_sub_le le54) (eqP t50) subn0 tm.
by move: hmem; rewrite (mem_m_F vE).
Qed.

Lemma occ24_1F : occv 2 -> occv 4 -> occv 1 = false.
Proof.
case/occvP=> u2 u2K s2; case/occvP=> u4 u4K s4.
apply/negbTE/negP=> /occvP[u1 u1K s1].
have tm := occ24_block u2K u4K s2 s4.
have c2 : band ((u2 : T4).1) = 3.
  by case: (sidx_decode (u2 : T4)) => _ ->; rewrite s2.
have d2 : dband ((u2 : T4).2) = 1.
  by case: (sidx_decode (u2 : T4)) => -> _; rewrite s2.
have c4 : band ((u4 : T4).1) = 2.
  by case: (sidx_decode (u4 : T4)) => _ ->; rewrite s4.
have d4 : dband ((u4 : T4).2) = 2.
  by case: (sidx_decode (u4 : T4)) => -> _; rewrite s4.
have c1 : band ((u1 : T4).1) = 2.
  by case: (sidx_decode (u1 : T4)) => _ ->; rewrite s1.
have d1 : dband ((u1 : T4).2) = 1.
  by case: (sidx_decode (u1 : T4)) => -> _; rewrite s1.
have t20 : (val ((u2 : T4).1) == 0)%N by rewrite -band3P c2.
have /andP[t1pos t1le] : (0 < val ((u1 : T4).1) <= m)%N by rewrite -band2P c1.
have ka1 : kappa (u1 : T4) = 3 by rewrite /kappa c1 d1.
have ka2 : kappa (u2 : T4) = 4 by rewrite /kappa c2 d2.
have ka4 : kappa (u4 : T4) = 4 by rewrite /kappa c4 d4.
case e : (val ((u1 : T4).1) == m)%N.
- (* u1 sits on block m = u4's block; u2 = (0,i) must beat it: m ∈ g fails *)
  have kuv2 : (kv (u1 : T4) < kv (u2 : T4))%N.
    by apply: kv_kappa_mono; rewrite ka1 ka2.
  have aDa : (u1 : T4).1 != (u2 : T4).1.
    by rewrite -(inj_eq val_inj) (eqP t20) (gtn_eqF t1pos).
  have hmem := beat_blocksV u1K u2K kuv2 aDa.
  have le21 : (val ((u2 : T4).1) <= val ((u1 : T4).1))%N by rewrite (eqP t20).
  have vE : val (((u1 : T4).1 : 'Z_n) - ((u2 : T4).1 : 'Z_n)) = m.
    by rewrite (val_sub_le le21) (eqP t20) subn0 (eqP e).
  by move: hmem; rewrite (mem_m_F vE).
- (* u1's block is below m: the backward residue lands in [m+2, 2m] *)
  have t1ltm : (val ((u1 : T4).1) < m)%N by rewrite ltn_neqAle e t1le.
  have kuv : (kv (u1 : T4) < kv (u4 : T4))%N.
    by apply: kv_kappa_mono; rewrite ka1 ka4.
  have lt14 : (val ((u1 : T4).1) < val ((u4 : T4).1))%N by rewrite tm.
  have aDa : (u1 : T4).1 != (u4 : T4).1.
    by rewrite -(inj_eq val_inj) (ltn_eqF lt14).
  have hmem := beat_blocksV u1K u4K kuv aDa.
  have vE : val (((u1 : T4).1 : 'Z_n) - ((u4 : T4).1 : 'Z_n))
            = (n - (m - val ((u1 : T4).1)))%N.
    by rewrite (val_sub_gt lt14) tm.
  have dltm : (m - val ((u1 : T4).1) < m)%N by rewrite ltn_subrL t1pos.
  have hi : (m.+1 < val ((((u1 : T4).1 : 'Z_n) - ((u4 : T4).1 : 'Z_n))%R))%N.
    by rewrite vE; exact: (n_sub_gt_Sm dltm).
  by move: hmem; rewrite (mem_mid_F hi).
Qed.

(** ** V6: the four-class chain (0,0) / high / low / κ2 dies *)

Lemma occ5310_F : occv 5 -> occv 3 -> occv 1 -> occv 0 -> False.
Proof.
case/occvP=> u5 u5K s5; case/occvP=> u3 u3K s3.
case/occvP=> u1 u1K s1; case/occvP=> u0 u0K s0.
have c5 : band ((u5 : T4).1) = 3.
  by case: (sidx_decode (u5 : T4)) => _ ->; rewrite s5.
have d5 : dband ((u5 : T4).2) = 2.
  by case: (sidx_decode (u5 : T4)) => -> _; rewrite s5.
have c3 : band ((u3 : T4).1) = 1.
  by case: (sidx_decode (u3 : T4)) => _ ->; rewrite s3.
have d3 : dband ((u3 : T4).2) = 2.
  by case: (sidx_decode (u3 : T4)) => -> _; rewrite s3.
have c1 : band ((u1 : T4).1) = 2.
  by case: (sidx_decode (u1 : T4)) => _ ->; rewrite s1.
have d1 : dband ((u1 : T4).2) = 1.
  by case: (sidx_decode (u1 : T4)) => -> _; rewrite s1.
have c0 : band ((u0 : T4).1) = 1.
  by case: (sidx_decode (u0 : T4)) => _ ->; rewrite s0.
have d0 : dband ((u0 : T4).2) = 1.
  by case: (sidx_decode (u0 : T4)) => -> _; rewrite s0.
have t50 : (val ((u5 : T4).1) == 0)%N by rewrite -band3P c5.
have t3hi : (m < val ((u3 : T4).1))%N by rewrite -band1P c3.
have /andP[t1pos t1le] : (0 < val ((u1 : T4).1) <= m)%N by rewrite -band2P c1.
have t0hi : (m < val ((u0 : T4).1))%N by rewrite -band1P c0.
have ka5 : kappa (u5 : T4) = 5 by rewrite /kappa c5 d5.
have ka3 : kappa (u3 : T4) = 3 by rewrite /kappa c3 d3.
have ka1 : kappa (u1 : T4) = 3 by rewrite /kappa c1 d1.
have ka0 : kappa (u0 : T4) = 2 by rewrite /kappa c0 d0.
(* (1) (0,0) beats the high: its block is m+1 *)
have t3pos : (0 < val ((u3 : T4).1))%N := leq_ltn_trans (leq0n m) t3hi.
have kuv53 : (kv (u3 : T4) < kv (u5 : T4))%N.
  by apply: kv_kappa_mono; rewrite ka3 ka5.
have aDa53 : (u3 : T4).1 != (u5 : T4).1.
  by rewrite -(inj_eq val_inj) (eqP t50) (gtn_eqF t3pos).
have hmem1 := beat_blocksV u3K u5K kuv53 aDa53.
have le53 : (val ((u5 : T4).1) <= val ((u3 : T4).1))%N by rewrite (eqP t50).
have vE1 : val (((u3 : T4).1 : 'Z_n) - ((u5 : T4).1 : 'Z_n))
           = val ((u3 : T4).1).
  by rewrite (val_sub_le le53) (eqP t50) subn0.
have hi1 : (m.+1 <= val ((((u3 : T4).1 : 'Z_n) - ((u5 : T4).1 : 'Z_n))%R))%N.
  by rewrite vE1 t3hi.
move: hmem1; rewrite (AC_mem_Hi hi1) vE1 => /eqP vb.
(* (2) (0,0) beats the κ2 member: its block is m+1 too *)
have t0pos : (0 < val ((u0 : T4).1))%N := leq_ltn_trans (leq0n m) t0hi.
have kuv05 : (kv (u0 : T4) < kv (u5 : T4))%N.
  by apply: kv_kappa_mono; rewrite ka0 ka5.
have aDa05 : (u0 : T4).1 != (u5 : T4).1.
  by rewrite -(inj_eq val_inj) (eqP t50) (gtn_eqF t0pos).
have hmem2 := beat_blocksV u0K u5K kuv05 aDa05.
have le50 : (val ((u5 : T4).1) <= val ((u0 : T4).1))%N by rewrite (eqP t50).
have vE2 : val (((u0 : T4).1 : 'Z_n) - ((u5 : T4).1 : 'Z_n))
           = val ((u0 : T4).1).
  by rewrite (val_sub_le le50) (eqP t50) subn0.
have hi2 : (m.+1 <= val ((((u0 : T4).1 : 'Z_n) - ((u5 : T4).1 : 'Z_n))%R))%N.
  by rewrite vE2 t0hi.
move: hmem2; rewrite (AC_mem_Hi hi2) vE2 => /eqP ve.
(* (3) the high (m+1,0) beats the low: the low's block is 1 *)
have ek13 : kappa (u1 : T4) = kappa (u3 : T4) by rewrite ka1 ka3.
have lt13 : (val ((u1 : T4).1) < val ((u3 : T4).1))%N.
  by rewrite vb ltnS t1le.
have kuv13 := kv_lt_t ek13 lt13.
have aDa13 : (u1 : T4).1 != (u3 : T4).1.
  by rewrite -(inj_eq val_inj) (ltn_eqF lt13).
have hmem3 := beat_blocksV u1K u3K kuv13 aDa13.
have vE3 : val (((u1 : T4).1 : 'Z_n) - ((u3 : T4).1 : 'Z_n))
           = (n - (m.+1 - val ((u1 : T4).1)))%N.
  by rewrite (val_sub_gt lt13) vb.
have dle : (m.+1 - val ((u1 : T4).1) <= m)%N.
  by rewrite leq_subLR addnC -[m.+1]addn1 leq_add2l t1pos.
have hi3 : (m.+1 <= val ((((u1 : T4).1 : 'Z_n) - ((u3 : T4).1 : 'Z_n))%R))%N.
  by rewrite vE3; exact: (n_sub_ge_Sm dle).
have d2m : (m.+1 - val ((u1 : T4).1) <= m.*2)%N.
  by rewrite (leq_trans dle) // -addnn leq_addr.
move: hmem3.
rewrite (AC_mem_Hi hi3) vE3 (n_sub_eq_Sm d2m) (sub_eq_m t1le) => /eqP va1.
(* (5) the low (1,h) must beat the κ2 member (m+1,f): m ∈ g fails *)
have kuv01 : (kv (u0 : T4) < kv (u1 : T4))%N.
  by apply: kv_kappa_mono; rewrite ka0 ka1.
have aDa01 : (u0 : T4).1 != (u1 : T4).1.
  by rewrite -(inj_eq val_inj) ve va1 gtn_eqF.
have hmem5 := beat_blocksV u0K u1K kuv01 aDa01.
have le10 : (val ((u1 : T4).1) <= val ((u0 : T4).1))%N by rewrite ve va1.
have vE5 : val (((u0 : T4).1 : 'Z_n) - ((u1 : T4).1 : 'Z_n)) = m.
  by rewrite (val_sub_le le10) ve va1 subn1.
by move: hmem5; rewrite (mem_m_F vE5).
Qed.

(** ** Assembly: every backedge-qv clique has at most 4 vertices (V7) *)

Let sum6 : (\sum_(i < 6) occv i
            = occv 0 + occv 1 + occv 2 + occv 3 + occv 4 + occv 5)%N.
Proof. by rewrite !big_ord_recr big_ord0. Qed.

Lemma clique_card_le4 : (#|K| <= 4)%N.
Proof.
rewrite card_clique_sidx sum6.
have h1 : (occv 2 && occv 4) ==> (~~ occv 5 && ~~ occv 1).
  apply/implyP=> /andP[o2 o4].
  by rewrite (occ24_5F o2 o4) (occ24_1F o2 o4).
have h2 : ~~ [&& occv 5, occv 3, occv 1 & occv 0].
  by apply/negP=> /and4P[o5 o3 o1 o0]; have := occ5310_F o5 o3 o1 o0.
exact: bool_final h1 h2.
Qed.

End InCliqueV.

(** ** The value bound *)

Lemma omegab_at_qv_le4 : (omegab_at qv <= 4)%N.
Proof.
rewrite /omegab_at; case: omegaP => K Kmax.
have Kcl : forall u v : backedge qv, u \in K -> v \in K -> u != v -> u -- v.
  by have cl := maxclique_clique Kmax; move=> u v uK vK; exact: cl.
exact: clique_card_le4 Kcl.
Qed.

Theorem omegabar_T4_le4 : (ω̄(T4) <= 4)%N.
Proof. exact: leq_trans (omegabar_min qv) omegab_at_qv_le4. Qed.

Theorem omegabar_T4 : ω̄(T4) = 4.
Proof.
by apply/anti_leq; rewrite omegabar_T4_le4 (omegabar_T4_ge4 m3).
Qed.

End K4Value.
