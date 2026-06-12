(** * Digraph.k4_del — ω̄(ACₙ[C₃] − (0,0)) ≤ 3 (the d_then_c order)

    M16 (docs/k34_dossier.md §3, items D0–D4). On the survivors of
    T4 − (0,0) we use the d_then_c order: the radix key
    kd (t,h) := (σ(t,h)·n + t)·3 + h whose leading digit is the sub-band
    σ = (dband h − 1)·3 + (band t − 1) of k4_value. σ is monotone in the
    dossier's (dband, band) lex pair, so kd realizes exactly the
    dossier's band order B1 < B2 < B3 < B4 < B5 (D0); the deleted (0,0)
    is the absent σ = 5 ([sidx_del_le4]). At most one clique vertex per
    band ([didx_inj_clique], D1 — same mechanism as the value order).
    Three exclusions cap a backedge clique at 3 (D2/D3):
    - [occ023_F] (B1+B3+B4): B3 pins the B1 block at m+1 and forces
      s ≥ m+2; then (s,0) cannot beat (m+1,·);
    - [occ124_F] (B2+B3+B5): B3 forces s' = m, pinning the B2 block at
      m, and the B3-beats-B2 backedge needs m ∈ g — false (D3f(i));
    - [occ0134_F] (B1+B2+B4+B5): the D3e core — the forced shape
      t₁ = s+1, s − t₂ = m makes the two w₅-beats need 1+δ ∈ g and
      m+1+δ ∈ g for δ = s−s' ∈ g; the two branches of δ ∈ g each die.
    Exit: [omegabar_T4del0] : ω̄(T4 − (0,0)) = 3 (with M14's ≥ 3). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical domination.
From Digraph Require Import automorphism product cayley circulant transitive substitution.
From Digraph Require Import acn_arc_facts acn_base acn_bands k4_lower k4_value.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section K4Del.
Variable m' : nat.
Hypothesis m3 : (3 <= m'.+1)%N.

Local Notation m := m'.+1.
Local Notation n := (m.*2.+1).
Local Notation ACm := (AC m').
Local Notation C3t := (C3 : tournament).
Local Notation T4 := (lexprod_tournament ACm C3t).

Let z0 : ACm := (0 : 'Z_n).
Let hz : C3t := (0 : 'Z_3).
Let o00 : T4 := (z0, hz).
Local Notation T4del := (del_tournament o00).

(** The survivor's underlying T4 vertex. *)
Local Notation tv u := ((val (u : T4del)) : T4).

(** ** The d_then_c key *)

Definition kd (w : T4) : nat := ((sidx w) * n + val w.1) * 3 + val w.2.

Lemma kd_inj : injective kd.
Proof.
move=> [t h] [t' h'] e.
have [e1 e2] := radix_eq_inv (ltn_ord _) (ltn_ord _) e.
have [_ e3] := radix_eq_inv (ltn_ord _) (ltn_ord _) e1.
by rewrite (val_inj e2 : h = h') (val_inj e3 : t = t').
Qed.

Lemma kd_sidx_mono (w w' : T4) :
  (sidx w < sidx w')%N -> (kd w < kd w')%N.
Proof.
move=> h; apply: radix_ltA (ltn_ord _) _.
exact: radix_ltA (ltn_ord _) h.
Qed.

Lemma kd_samesidx (w w' : T4) : sidx w = sidx w' -> (kd w < kd w')%N ->
  (val w.1 < val w'.1)%N \/ (w.1 = w'.1 /\ (val w.2 < val w'.2)%N).
Proof.
move=> ec h.
case: (radix_lt_inv (ltn_ord _) (ltn_ord _) h) => [h1|[e1 h2]]; last first.
  case: (radix_eq_inv (ltn_ord _) (ltn_ord _) e1) => _ ea.
  by right; split=> //; exact: val_inj.
case: (radix_lt_inv (ltn_ord _) (ltn_ord _) h1) => [hc|[_ ha]]; last by left.
by move: hc; rewrite ec ltnn.
Qed.

(** ** The realized order on the survivors *)

Let rd := [rel u v : T4del | (kd (tv u) < kd (tv v))%N].

Fact rd_irr : irreflexive rd.
Proof. by move=> u /=; rewrite ltnn. Qed.

Fact rd_trans : transitive rd.
Proof. by move=> a b c /=; apply: ltn_trans. Qed.

Fact rd_total (u v : T4del) : u != v -> rd u v || rd v u.
Proof.
move=> uDv; rewrite /= -neq_ltn.
by apply: contraNneq uDv => /kd_inj/val_inj->.
Qed.

Definition qd : {perm T4del} := realize rd.

Lemma qdE (u v : T4del) : ltp qd u v = (kd (tv u) < kd (tv v))%N.
Proof. exact: (ltp_realizeE rd_irr rd_trans rd_total). Qed.

(** Survivors never occupy the deleted band σ = 5 (D0). *)
Lemma sidx_del_le4 (u : T4del) : (sidx (tv u) <= 4)%N.
Proof.
have := sidx_le5 (tv u).
rewrite leq_eqVlt => /orP[/eqP s5|]; last by rewrite -ltnS.
have c : band ((tv u).1) = 3.
  by case: (sidx_decode (tv u)) => _ ->; rewrite s5.
have d : dband ((tv u).2) = 2.
  by case: (sidx_decode (tv u)) => -> _; rewrite s5.
have t0 : (val ((tv u).1) == 0)%N by rewrite -band3P c.
have h0 : (val ((tv u).2) == 0)%N by rewrite -dband2P d.
have e1 : (tv u).1 = z0 by apply: val_inj; rewrite (eqP t0).
have e2 : (tv u).2 = hz by apply: val_inj; rewrite (eqP h0).
have xeq : tv u = o00 by rewrite [LHS]surjective_pairing e1 e2.
by have := valP u; rewrite !inE xeq eqxx.
Qed.

(** ** Extra residue arithmetic *)

Let n_sub_Sm : (n - m.+1)%N = m.
Proof. by rewrite subSS -addnn addnK. Qed.

Let n_sub_ltm_gtSm (s : nat) : (s < n)%N -> (n - s < m)%N -> (m.+1 < s)%N.
Proof.
move=> sn; rewrite ltn_subLR ?(ltnW sn) //.
by rewrite -addnn -addSn ltn_add2r.
Qed.

(** The 32-case occupancy arithmetic behind D2–D4. *)
Let bool_finalD (o0 o1 o2 o3 o4 : bool) :
  ~~ [&& o0, o2 & o3] ->
  ~~ [&& o1, o2 & o4] ->
  ~~ [&& o0, o1, o3 & o4] ->
  (o0 + o1 + o2 + o3 + o4 <= 3)%N.
Proof. by case: o0; case: o1; case: o2; case: o3; case: o4. Qed.

(** ** Beat conditions for clique members *)

Section InCliqueD.
Variables (K : {set backedge qd}).
Hypothesis Kcl : forall u v : backedge qd,
  u \in K -> v \in K -> u != v -> u -- v.

Lemma beat_kd (u v : backedge qd) : u \in K -> v \in K ->
  (kd (tv u) < kd (tv v))%N -> ((tv v) --> (tv u)).
Proof.
move=> uK vK kuv.
have uDv : u != v by apply: contraTneq kuv => ->; rewrite ltnn.
have := Kcl uK vK uDv.
rewrite backedgeE !qdE kuv (leq_gtF (ltnW kuv)) /= orbF.
by rewrite sub_arcE.
Qed.

Lemma beat_blocksD (u v : backedge qd) : u \in K -> v \in K ->
  (kd (tv u) < kd (tv v))%N -> (tv u).1 != (tv v).1 ->
  ((tv u).1 : 'Z_n) - ((tv v).1 : 'Z_n) \in ACset m'.
Proof.
move=> uK vK kuv aDa.
have := beat_kd uK vK kuv.
rewrite lexprod_arcE eq_sym (negbTE aDa) andFb orbF => h.
by rewrite -AC_arcE.
Qed.

Lemma beat_innerD (u v : backedge qd) : u \in K -> v \in K ->
  (kd (tv u) < kd (tv v))%N -> (tv u).1 = (tv v).1 ->
  ((tv v).2 --> (tv u).2).
Proof.
move=> uK vK kuv aEa.
have := beat_kd uK vK kuv.
by rewrite lexprod_arcE -aEa arcxx eqxx /=.
Qed.

(** ** D1: at most one clique vertex per band *)

Lemma didx_inj_clique : {in K &, forall u v : backedge qd,
  sidx (tv u) = sidx (tv v) -> u = v}.
Proof.
have main (u v : backedge qd) : u \in K -> v \in K ->
    sidx (tv u) = sidx (tv v) -> (kd (tv u) < kd (tv v))%N -> False.
  move=> uK vK ec kuv.
  have [du cu] := sidx_decode (tv u).
  have [dv cv] := sidx_decode (tv v).
  case: (kd_samesidx ec kuv) => [alt|[aE blt]].
  - have aDa : (tv u).1 != (tv v).1.
      by apply: contraTneq alt => ->; rewrite ltnn.
    have hmem := beat_blocksD uK vK kuv aDa.
    have ebandA : band ((tv u).1) = band ((tv v).1) by rewrite cu cv ec.
    have b3 : band ((tv u).1) != 3.
      apply/negP; rewrite band3P => /eqP z1.
      have : band ((tv v).1) == 3 by rewrite -ebandA band3P z1.
      rewrite band3P => /eqP z1'.
      by move: alt; rewrite z1 z1' ltnn.
    have gap := band_gap ebandA b3 alt.
    by move: hmem; rewrite (AC_wrapF alt gap).
  - have hmem := beat_innerD uK vK kuv aE.
    have edb : dband ((tv u).2) = dband ((tv v).2) by rewrite du dv ec.
    case e0 : (val ((tv u).2) == 0)%N.
    + have dv2 : (val ((tv v).2) == 0)%N.
        by rewrite -dband2P -edb dband2P e0.
      by move: blt; rewrite (eqP e0) (eqP dv2) ltnn.
    + have [vu1 vv2] := vals12 blt (ltn_ord _) (negbT e0).
      have eu : ((tv u).2) = (1 : 'Z_3) :> C3 by apply: val_inj; rewrite vu1.
      have ev : ((tv v).2) = (1 + 1 : 'Z_3) :> C3.
        by apply: val_inj; rewrite vv2.
      by move: hmem; rewrite arcC3E eu ev.
move=> u v uK vK ec.
case: (ltngtP (kd (tv u)) (kd (tv v))) => [lt|gt|e].
- by case: (main _ _ uK vK ec lt).
- by case: (main _ _ vK uK (esym ec) gt).
- exact: val_inj (kd_inj e).
Qed.

(** ** Occupancy *)

Definition occd (i : nat) : bool := [exists u in K, sidx (tv u) == i].

Lemma occdP (i : nat) :
  reflect (exists2 u, u \in K & sidx (tv u) = i) (occd i).
Proof.
apply: (iffP existsP) => [[u /andP[uK /eqP e]]|[u uK e]]; first by exists u.
by exists u; rewrite uK e eqxx.
Qed.

Lemma card_clique_didx : #|K| = (\sum_(i < 5) occd i)%N.
Proof.
apply: card_classes_inj; last exact: didx_inj_clique.
by move=> u _; rewrite ltnS sidx_del_le4.
Qed.

(** ** The exclusions *)

(** B1 + B3 + B4: B3 pins the B1 block at m+1 and the B4 block at
    s ≥ m+2; then (s,0) cannot beat (m+1,·). *)
Lemma occ023_F : occd 0 -> occd 2 -> occd 3 -> False.
Proof.
case/occdP=> x xK sx; case/occdP=> z zK sz; case/occdP=> w wK sw.
have cx : band ((tv x).1) = 1.
  by case: (sidx_decode (tv x)) => _ ->; rewrite sx.
have cz : band ((tv z).1) = 3.
  by case: (sidx_decode (tv z)) => _ ->; rewrite sz.
have cw : band ((tv w).1) = 1.
  by case: (sidx_decode (tv w)) => _ ->; rewrite sw.
have t1hi : (m < val ((tv x).1))%N by rewrite -band1P cx.
have tz0 : (val ((tv z).1) == 0)%N by rewrite -band3P cz.
have shi : (m < val ((tv w).1))%N by rewrite -band1P cw.
have t1pos : (0 < val ((tv x).1))%N := leq_ltn_trans (leq0n m) t1hi.
have spos : (0 < val ((tv w).1))%N := leq_ltn_trans (leq0n m) shi.
(* z beats x: the B1 block is m+1 *)
have kxz : (kd (tv x) < kd (tv z))%N by apply: kd_sidx_mono; rewrite sx sz.
have aDxz : (tv x).1 != (tv z).1.
  by rewrite -(inj_eq val_inj) (eqP tz0) (gtn_eqF t1pos).
have hmem1 := beat_blocksD xK zK kxz aDxz.
have lezx : (val ((tv z).1) <= val ((tv x).1))%N by rewrite (eqP tz0).
have vE1 : val ((((tv x).1 : 'Z_n) - ((tv z).1 : 'Z_n))%R)
           = val ((tv x).1).
  by rewrite (val_sub_le lezx) (eqP tz0) subn0.
have hi1 : (m.+1 <= val ((((tv x).1 : 'Z_n) - ((tv z).1 : 'Z_n))%R))%N.
  by rewrite vE1 t1hi.
move: hmem1; rewrite (AC_mem_Hi hi1) vE1 => /eqP vb.
(* w beats z: s >= m+2 *)
have kzw : (kd (tv z) < kd (tv w))%N by apply: kd_sidx_mono; rewrite sz sw.
have aDzw : (tv z).1 != (tv w).1.
  by rewrite -(inj_eq val_inj) (eqP tz0) eq_sym (gtn_eqF spos).
have hmem2 := beat_blocksD zK wK kzw aDzw.
have ltzw : (val ((tv z).1) < val ((tv w).1))%N by rewrite (eqP tz0).
have vE2 : val ((((tv z).1 : 'Z_n) - ((tv w).1 : 'Z_n))%R)
           = (n - val ((tv w).1))%N.
  by rewrite (val_sub_gt ltzw) (eqP tz0) subn0.
have nsle : (n - val ((tv w).1) <= m)%N.
  rewrite leq_subLR.
  apply: (@leq_trans (m.+1 + m)%N); first by rewrite addSn addnn.
  by rewrite leq_add2r shi.
have nsltm : (n - val ((tv w).1) < m)%N.
  move: hmem2; rewrite AC_mem_val vE2 => /orP[/andP[_ //]|/eqP eSm].
  by move: nsle; rewrite eSm ltnn.
have sge : (m.+1 < val ((tv w).1))%N.
  exact: n_sub_ltm_gtSm (ltn_ord _) nsltm.
(* w beats x: the backward residue lands in [m+2, 2m] *)
have kxw : (kd (tv x) < kd (tv w))%N by apply: kd_sidx_mono; rewrite sx sw.
have ltxw : (val ((tv x).1) < val ((tv w).1))%N by rewrite vb.
have aDxw : (tv x).1 != (tv w).1.
  by rewrite -(inj_eq val_inj) (ltn_eqF ltxw).
have hmem3 := beat_blocksD xK wK kxw aDxw.
have vE3 : val ((((tv x).1 : 'Z_n) - ((tv w).1 : 'Z_n))%R)
           = (n - (val ((tv w).1) - m.+1))%N.
  by rewrite (val_sub_gt ltxw) vb.
have dltm : (val ((tv w).1) - m.+1 < m)%N.
  by rewrite ltn_subLR ?(ltnW sge) // addSn addnn ltn_ord.
have hi3 : (m.+1 < val ((((tv x).1 : 'Z_n) - ((tv w).1 : 'Z_n))%R))%N.
  by rewrite vE3; exact: (n_sub_gt_Sm dltm).
by move: hmem3; rewrite (mem_mid_F hi3).
Qed.

(** B2 + B3 + B5: B3 forces s' = m (D3f), pinning the B2 block at m;
    the B3-beats-B2 backedge then needs m ∈ g. *)
Lemma occ124_F : occd 1 -> occd 2 -> occd 4 -> False.
Proof.
case/occdP=> y yK sy; case/occdP=> z zK sz; case/occdP=> w wK sw.
have cy : band ((tv y).1) = 2.
  by case: (sidx_decode (tv y)) => _ ->; rewrite sy.
have cz : band ((tv z).1) = 3.
  by case: (sidx_decode (tv z)) => _ ->; rewrite sz.
have cw : band ((tv w).1) = 2.
  by case: (sidx_decode (tv w)) => _ ->; rewrite sw.
have /andP[t2pos t2le] : (0 < val ((tv y).1) <= m)%N by rewrite -band2P cy.
have tz0 : (val ((tv z).1) == 0)%N by rewrite -band3P cz.
have /andP[s'pos s'le] : (0 < val ((tv w).1) <= m)%N by rewrite -band2P cw.
(* w beats z: s' = m *)
have kzw : (kd (tv z) < kd (tv w))%N by apply: kd_sidx_mono; rewrite sz sw.
have aDzw : (tv z).1 != (tv w).1.
  by rewrite -(inj_eq val_inj) (eqP tz0) eq_sym (gtn_eqF s'pos).
have hmem1 := beat_blocksD zK wK kzw aDzw.
have ltzw : (val ((tv z).1) < val ((tv w).1))%N by rewrite (eqP tz0).
have vE1 : val ((((tv z).1 : 'Z_n) - ((tv w).1 : 'Z_n))%R)
           = (n - val ((tv w).1))%N.
  by rewrite (val_sub_gt ltzw) (eqP tz0) subn0.
have hi1 : (m.+1 <= val ((((tv z).1 : 'Z_n) - ((tv w).1 : 'Z_n))%R))%N.
  by rewrite vE1; exact: (n_sub_ge_Sm s'le).
have s2m : (val ((tv w).1) <= m.*2)%N.
  by rewrite (leq_trans s'le) // -addnn leq_addr.
move: hmem1; rewrite (AC_mem_Hi hi1) vE1 (n_sub_eq_Sm s2m) => /eqP s'm.
(* the B2 block: either it is m (kill via z) or below (kill via w) *)
case et : (val ((tv y).1) == m)%N.
- (* z beats y with value m *)
  have kyz : (kd (tv y) < kd (tv z))%N by apply: kd_sidx_mono; rewrite sy sz.
  have aDyz : (tv y).1 != (tv z).1.
    by rewrite -(inj_eq val_inj) (eqP tz0) (gtn_eqF t2pos).
  have hmem2 := beat_blocksD yK zK kyz aDyz.
  have lezy : (val ((tv z).1) <= val ((tv y).1))%N by rewrite (eqP tz0).
  have vE2 : val ((((tv y).1 : 'Z_n) - ((tv z).1 : 'Z_n))%R) = m.
    by rewrite (val_sub_le lezy) (eqP tz0) subn0 (eqP et).
  by move: hmem2; rewrite (mem_m_F vE2).
- (* w beats y across blocks: residue in [m+2, 2m] *)
  have t2ltm : (val ((tv y).1) < m)%N by rewrite ltn_neqAle et t2le.
  have kyw : (kd (tv y) < kd (tv w))%N by apply: kd_sidx_mono; rewrite sy sw.
  have ltyw : (val ((tv y).1) < val ((tv w).1))%N by rewrite s'm.
  have aDyw : (tv y).1 != (tv w).1.
    by rewrite -(inj_eq val_inj) (ltn_eqF ltyw).
  have hmem3 := beat_blocksD yK wK kyw aDyw.
  have vE3 : val ((((tv y).1 : 'Z_n) - ((tv w).1 : 'Z_n))%R)
             = (n - (m - val ((tv y).1)))%N.
    by rewrite (val_sub_gt ltyw) s'm.
  have dltm : (m - val ((tv y).1) < m)%N by rewrite ltn_subrL t2pos.
  have hi3 : (m.+1 < val ((((tv y).1 : 'Z_n) - ((tv w).1 : 'Z_n))%R))%N.
    by rewrite vE3; exact: (n_sub_gt_Sm dltm).
  by move: hmem3; rewrite (mem_mid_F hi3).
Qed.

(** B1 + B2 + B4 + B5: the D3e core. The pairwise beats force
    s − t₂ = m and t₁ = s + 1; then δ = s − s' ∈ g must satisfy both
    1 + δ ∈ g (w₅ beats the forced B1) and m+1+δ ∈ g mod n (w₅ beats
    the forced B2) — the two branches of δ ∈ g each fail one. *)
Lemma occ0134_F : occd 0 -> occd 1 -> occd 3 -> occd 4 -> False.
Proof.
case/occdP=> x xK sx; case/occdP=> y yK sy.
case/occdP=> w4 w4K sw4; case/occdP=> w5 w5K sw5.
have cx : band ((tv x).1) = 1.
  by case: (sidx_decode (tv x)) => _ ->; rewrite sx.
have cy : band ((tv y).1) = 2.
  by case: (sidx_decode (tv y)) => _ ->; rewrite sy.
have cw4 : band ((tv w4).1) = 1.
  by case: (sidx_decode (tv w4)) => _ ->; rewrite sw4.
have cw5 : band ((tv w5).1) = 2.
  by case: (sidx_decode (tv w5)) => _ ->; rewrite sw5.
have t1hi : (m < val ((tv x).1))%N by rewrite -band1P cx.
have /andP[t2pos t2le] : (0 < val ((tv y).1) <= m)%N by rewrite -band2P cy.
have shi : (m < val ((tv w4).1))%N by rewrite -band1P cw4.
have /andP[s'pos s'le] : (0 < val ((tv w5).1) <= m)%N by rewrite -band2P cw5.
have s'lts : (val ((tv w5).1) < val ((tv w4).1))%N := leq_ltn_trans s'le shi.
(* (a) w5 beats w4: δ = s − s' ∈ g *)
have k45 : (kd (tv w4) < kd (tv w5))%N.
  by apply: kd_sidx_mono; rewrite sw4 sw5.
have aD45 : (tv w4).1 != (tv w5).1.
  by rewrite -(inj_eq val_inj) (gtn_eqF s'lts).
have hmemD := beat_blocksD w4K w5K k45 aD45.
have vED : val ((((tv w4).1 : 'Z_n) - ((tv w5).1 : 'Z_n))%R)
           = (val ((tv w4).1) - val ((tv w5).1))%N.
  by rewrite (val_sub_le (ltnW s'lts)).
move: hmemD; rewrite AC_mem_val vED => vd.
(* (b) w4 beats x: t₁ ≥ s *)
have kxw4 : (kd (tv x) < kd (tv w4))%N.
  by apply: kd_sidx_mono; rewrite sx sw4.
have t1ges : (val ((tv w4).1) <= val ((tv x).1))%N.
  rewrite leqNgt; apply/negP=> ltts.
  have aD : (tv x).1 != (tv w4).1.
    by rewrite -(inj_eq val_inj) (ltn_eqF ltts).
  have hmemB := beat_blocksD xK w4K kxw4 aD.
  have ebnd : band ((tv x).1) = band ((tv w4).1) by rewrite cx cw4.
  have b3 : band ((tv x).1) != 3 by rewrite cx.
  have gap := band_gap ebnd b3 ltts.
  by move: hmemB; rewrite (AC_wrapF ltts gap).
(* (c) w4 beats y: s − t₂ ≥ m and s − t₂ ≠ m+1 *)
have ltyw4 : (val ((tv y).1) < val ((tv w4).1))%N := leq_ltn_trans t2le shi.
have kyw4 : (kd (tv y) < kd (tv w4))%N.
  by apply: kd_sidx_mono; rewrite sy sw4.
have aDyw4 : (tv y).1 != (tv w4).1.
  by rewrite -(inj_eq val_inj) (ltn_eqF ltyw4).
have hmemY := beat_blocksD yK w4K kyw4 aDyw4.
have vEY : val ((((tv y).1 : 'Z_n) - ((tv w4).1 : 'Z_n))%R)
           = (n - (val ((tv w4).1) - val ((tv y).1)))%N.
  by rewrite (val_sub_gt ltyw4).
have st2ge : (m <= val ((tv w4).1) - val ((tv y).1))%N.
  rewrite leqNgt; apply/negP=> lt.
  have hi : (m.+1 < val ((((tv y).1 : 'Z_n) - ((tv w4).1 : 'Z_n))%R))%N.
    by rewrite vEY; exact: (n_sub_gt_Sm lt).
  by move: hmemY; rewrite (mem_mid_F hi).
have neqSm : ((val ((tv w4).1) - val ((tv y).1))%N == m.+1) = false.
  apply/negbTE/negP=> /eqP e.
  have vm : val ((((tv y).1 : 'Z_n) - ((tv w4).1 : 'Z_n))%R) = m.
    by rewrite vEY e n_sub_Sm.
  by move: hmemY; rewrite (mem_m_F vm).
(* (d) y beats x: t₁ − t₂ = m+1 *)
have t2ltt1 : (val ((tv y).1) < val ((tv x).1))%N := leq_ltn_trans t2le t1hi.
have kxy : (kd (tv x) < kd (tv y))%N by apply: kd_sidx_mono; rewrite sx sy.
have aDxy : (tv x).1 != (tv y).1.
  by rewrite -(inj_eq val_inj) (gtn_eqF t2ltt1).
have hmemX := beat_blocksD xK yK kxy aDxy.
have vEX : val ((((tv x).1 : 'Z_n) - ((tv y).1 : 'Z_n))%R)
           = (val ((tv x).1) - val ((tv y).1))%N.
  by rewrite (val_sub_le (ltnW t2ltt1)).
have dge : (m <= val ((tv x).1) - val ((tv y).1))%N.
  exact: leq_trans st2ge (leq_sub2r _ t1ges).
have dE : (val ((tv x).1) - val ((tv y).1))%N = m.+1.
  move: hmemX; rewrite AC_mem_val vEX => /orP[/andP[_ ltm]|/eqP //].
  by move: (leq_ltn_trans dge ltm); rewrite ltnn.
(* (e) s − t₂ = m, hence s = m + t₂ and t₁ = s + 1 *)
have st2le2 : (val ((tv w4).1) - val ((tv y).1) <= m)%N.
  have le1 : (val ((tv w4).1) - val ((tv y).1) <= m.+1)%N.
    by rewrite -dE; exact: (leq_sub2r _ t1ges).
  by move: le1; rewrite leq_eqVlt neqSm /= ltnS.
have st2 : (val ((tv w4).1) - val ((tv y).1))%N = m.
  by apply/anti_leq; rewrite st2le2 st2ge.
have sE : (m + val ((tv y).1))%N = val ((tv w4).1).
  by rewrite -[X in (X + _)%N = _]st2 subnK ?(ltnW ltyw4).
have t1E : (m.+1 + val ((tv y).1))%N = val ((tv x).1).
  by rewrite -[X in (X + _)%N = _]dE subnK ?(ltnW t2ltt1).
have tE : val ((tv x).1) = (val ((tv w4).1)).+1.
  by rewrite -t1E addSn sE.
(* (g) the two branches of δ ∈ g *)
case/orP: vd => [/andP[dpos dltm]|/eqP dSm].
- (* δ < m: w5 must beat the forced B2 — residue m+1+δ ∈ [m+2, 2m] *)
  have s'ltsv : (val ((tv w5).1) < val ((tv w4).1))%N := s'lts.
  have t2lts' : (val ((tv y).1) < val ((tv w5).1))%N.
    rewrite -(ltn_add2l m) sE.
    by move: dltm; rewrite ltn_subLR ?(ltnW s'ltsv) // addnC.
  have kyw5 : (kd (tv y) < kd (tv w5))%N.
    by apply: kd_sidx_mono; rewrite sy sw5.
  have aD : (tv y).1 != (tv w5).1.
    by rewrite -(inj_eq val_inj) (ltn_eqF t2lts').
  have hmemW := beat_blocksD yK w5K kyw5 aD.
  have vEW : val ((((tv y).1 : 'Z_n) - ((tv w5).1 : 'Z_n))%R)
             = (n - (val ((tv w5).1) - val ((tv y).1)))%N.
    by rewrite (val_sub_gt t2lts').
  have d2ltm : (val ((tv w5).1) - val ((tv y).1) < m)%N.
    rewrite ltn_subLR ?(ltnW t2lts') // addnC sE.
    by rewrite -subn_gt0.
  have hi : (m.+1 < val ((((tv y).1 : 'Z_n) - ((tv w5).1 : 'Z_n))%R))%N.
    by rewrite vEW; exact: (n_sub_gt_Sm d2ltm).
  by move: hmemW; rewrite (mem_mid_F hi).
- (* δ = m+1: w5 must beat the forced B1 — value δ+1 = m+2 *)
  have s'let1 : (val ((tv w5).1) <= val ((tv x).1))%N.
    exact: leq_trans s'le (ltnW t1hi).
  have kxw5 : (kd (tv x) < kd (tv w5))%N.
    by apply: kd_sidx_mono; rewrite sx sw5.
  have aD : (tv x).1 != (tv w5).1.
    by rewrite -(inj_eq val_inj) (gtn_eqF (leq_ltn_trans s'le t1hi)).
  have hmemX2 := beat_blocksD xK w5K kxw5 aD.
  have vEX2 : val ((((tv x).1 : 'Z_n) - ((tv w5).1 : 'Z_n))%R) = m.+2.
    by rewrite (val_sub_le s'let1) tE subSn ?(ltnW s'lts) // dSm.
  have hi : (m.+1 < val ((((tv x).1 : 'Z_n) - ((tv w5).1 : 'Z_n))%R))%N.
    by rewrite vEX2.
  by move: hmemX2; rewrite (mem_mid_F hi).
Qed.

(** ** Assembly: every backedge-qd clique has at most 3 vertices (D4) *)

Let sum5 : (\sum_(i < 5) occd i
            = occd 0 + occd 1 + occd 2 + occd 3 + occd 4)%N.
Proof. by rewrite !big_ord_recr big_ord0. Qed.

Lemma clique_card_le3 : (#|K| <= 3)%N.
Proof.
rewrite card_clique_didx sum5.
have h1 : ~~ [&& occd 0, occd 2 & occd 3].
  by apply/negP=> /and3P[o0 o2 o3]; have := occ023_F o0 o2 o3.
have h2 : ~~ [&& occd 1, occd 2 & occd 4].
  by apply/negP=> /and3P[o1 o2 o4]; have := occ124_F o1 o2 o4.
have h3 : ~~ [&& occd 0, occd 1, occd 3 & occd 4].
  by apply/negP=> /and4P[o0 o1 o3 o4]; have := occ0134_F o0 o1 o3 o4.
exact: bool_finalD h1 h2 h3.
Qed.

End InCliqueD.

(** ** The deletion bound *)

Lemma omegab_at_qd_le3 : (omegab_at qd <= 3)%N.
Proof.
rewrite /omegab_at; case: omegaP => K Kmax.
have Kcl : forall u v : backedge qd, u \in K -> v \in K -> u != v -> u -- v.
  by have cl := maxclique_clique Kmax; move=> u v uK vK; exact: cl.
exact: clique_card_le3 Kcl.
Qed.

Theorem omegabar_T4del_le3 : (ω̄(T4del) <= 3)%N.
Proof. exact: leq_trans (omegabar_min qd) omegab_at_qd_le3. Qed.

Theorem omegabar_T4del0 : ω̄(T4del) = 3.
Proof.
apply/anti_leq/andP; split; first exact: omegabar_T4del_le3.
exact: (omegabar_T4del_ge3 m3).
Qed.

End K4Del.
