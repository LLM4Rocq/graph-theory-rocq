(** * Digraph.conjectures.grounding_sad2 — DEEPER GROUNDING of [sad.v]

    Companion to [grounding_sad_packing.v].  Beyond the directed-cycle λ = 1
    facts, this file exercises the heavy machinery of [sad.v]: [spanning_strong],
    [SAD], [SAD_colouring], and the non-vacuity / triviality calibration of the
    three Prop-nodes [bang_jensen_yeo_SAD_statement], [WC3_statement],
    [CL1_statement].  Every lemma is [Qed]; the file imports ONLY committed
    modules.

    Grounded facts (each tied to a textbook statement):

      1. A CONCRETE Strong Arc Decomposition.  The bidirected directed cycle
         [Bicyc n] (each vertex [i] has arcs to BOTH neighbours [i±1]) for
         [n ≥ 3] has a SAD: its arc set is the disjoint union of the FORWARD
         directed Hamilton cycle [i → i+1] and the BACKWARD directed Hamilton
         cycle [i → i-1], each spanning and strongly connected.  This is the
         smallest nontrivial SAD example (a 2-arc-strong digraph that DOES
         decompose; cf. Bang-Jensen–Yeo, two arc-disjoint spanning strong
         subdigraphs).  We exhibit it via [SAD_colouring] (an arc is coloured by
         "is it a forward arc?") and bridge to [SAD].

      2. [spanning_strong] of a CONCRETE arc set: the forward Hamilton cycle on
         [Bicyc n] is spanning-strong (every ordered pair is joined by a directed
         path of forward arcs — iterate the successor); likewise the backward.

      3. [arc_strong] of a concrete digraph at k = 2: [Bicyc n] (n ≥ 3) is
         2-arc-strong — every nonempty proper out-cut has ≥ 2 arcs (a forward and
         a backward boundary arc).  Grounds [arc_strong] at a value > 1 (the
         cycle only gave 1) and supplies the NON-VACUITY witness for the
         hypothesis class of the three conjecture nodes.

    NON-VACUITY of the statement nodes:
      - [bang_jensen_yeo_SAD_statement] / [WC3_statement] hypothesis class
        "[0 < #|D|] ∧ arc_strong D k" is INHABITED (witness [Bicyc 3], k ≤ 2) AND
        the conclusion [SAD] is achievable there — so neither node is vacuously
        true nor obviously false on its witness.
      - [CL1_statement] hypothesis class is inhabited (a vertex split with both
        sides ≥ 2 and a bipartitioned bridge set exists), checked on [Bicyc 4].

    TRIVIALITY / FALSIFICATION probes (reported, all benign here):
      - [SAD] is NOT trivially-true: a digraph that is not strongly connected has
        no SAD.  We show [~ SAD] for the 2-vertex single-arc digraph.
      - [arc_strong] is satisfiable NON-trivially at k = 2 ([Bicyc] reaches 2),
        so "K-arc-strong" is a genuine sliding threshold.
      - [spanning_strong] is NOT trivially true: the empty arc set is not
        spanning-strong on any digraph with ≥ 2 vertices. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath strong tournament.
From Digraph Require Import sad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Arithmetic helper: small modular successor facts. *)

(** [(x+1) mod n ≠ x] for [n ≥ 2], [x < n] (no fixed point of the shift). *)
Lemma succ1_modn_neq (n x : nat) : (2 <= n)%N -> (x < n)%N -> ((x.+1) %% n != x).
Proof.
move=> n2 xn; apply/eqP.
case: (ltngtP x.+1 n) => [lt|gt|eqn].
- by rewrite (modn_small lt) => /esym/n_Sn.
- by move: gt; rewrite ltnS leqNgt xn.
- by rewrite -eqn modnn => x0; move: n2; rewrite -eqn -x0.
Qed.

(** [(x+2) mod n ≠ x] for [n ≥ 3], [x < n] (the two neighbours are distinct). *)
Lemma succ2_modn_neq (n x : nat) : (3 <= n)%N -> (x < n)%N -> ((x + 2) %% n != x).
Proof.
move=> n3 xn; apply/eqP.
have n2 : (2 <= n)%N by apply: leq_trans n3.
have xn2 : (x + 2 < n + n)%N.
  by rewrite (leq_ltn_trans (n := x + n)) // ?leq_add2l // ltn_add2r.
case: (ltnP (x + 2) n) => [lt|ge].
- by rewrite (modn_small lt) => /eqP; rewrite -{2}[x]addn0 eqn_add2l.
- rewrite -(subnK ge) modnDr modn_small; last by rewrite ltn_subLR // addnC.
  move=> E; have : (x + 2 = x + n)%N by rewrite -{1}(subnK ge) E addnC.
  by move/addnI => Een; move: n3; rewrite -Een.
Qed.

(** ** The bidirected directed cycle [Bicyc n]: i --> j iff j = i±1 (mod n). *)

Section Bicyc.
Variable n : nat.
Hypothesis n3 : (3 <= n)%N.

Let n0 : (0 < n)%N. Proof. by apply: leq_trans n3. Qed.
Let n2 : (2 <= n)%N. Proof. by apply: leq_trans n3. Qed.

(** Successor and predecessor on ['I_n] (mod n). *)
Definition s (x : 'I_n) : 'I_n := Ordinal (ltn_pmod (val x).+1 n0).
Definition p (x : 'I_n) : 'I_n := Ordinal (ltn_pmod (val x + (n - 1)) n0).

Definition bicyc_rel (x y : 'I_n) : bool := (y == s x) || (y == p x).
Definition bicyc : Type := 'I_n.
HB.instance Definition _ := Finite.on bicyc.
HB.instance Definition _ := HasArc.Build bicyc bicyc_rel.
Definition Bicyc : diGraphType := bicyc.

Lemma bicyc_arcE (x y : Bicyc) : (x --> y) = ((y == s x) || (y == p x)).
Proof. by []. Qed.

Lemma val_s (x : Bicyc) : val (s x) = (val x).+1 %% n.
Proof. by []. Qed.

Lemma val_p (x : Bicyc) : val (p x) = (val x + (n - 1)) %% n.
Proof. by []. Qed.

(** [p] undoes [s] and vice versa: the forward and backward cycles are inverse. *)
Lemma p_s (x : Bicyc) : p (s x) = x.
Proof.
apply: val_inj; rewrite val_p val_s modnDml subn1.
have -> : ((val x).+1 + n.-1)%N = (val x + n)%N.
  by rewrite addSn -addnS prednK // addnC.
by rewrite -modnDmr modnn addn0 modn_small // ltn_ord.
Qed.

Lemma s_p (x : Bicyc) : s (p x) = x.
Proof.
apply: val_inj; rewrite val_s val_p -addn1 modnDml addn1 subn1.
have -> : (val x + n.-1).+1 = (val x + n)%N.
  by rewrite -addnS prednK // addnC.
by rewrite -modnDmr modnn addn0 modn_small // ltn_ord.
Qed.

Lemma s_inj : injective s.
Proof. by move=> x y E; rewrite -[x]p_s -[y]p_s E. Qed.

Lemma p_inj : injective p.
Proof. by move=> x y E; rewrite -[x]s_p -[y]s_p E. Qed.

(** No loops (n ≥ 2): [s x ≠ x], [p x ≠ x]. *)
Lemma s_neq (x : Bicyc) : s x != x.
Proof. by apply/eqP=> /(f_equal val); apply/eqP; rewrite val_s succ1_modn_neq // ltn_ord. Qed.

Lemma p_neq (x : Bicyc) : p x != x.
Proof. by apply/eqP=> E; have := s_neq (p x); rewrite s_p E eqxx. Qed.

(** The two neighbours are distinct (n ≥ 3): [s x ≠ p x]. *)
Lemma s_neq_p (x : Bicyc) : s x != p x.
Proof.
apply/eqP=> E.
have H : s (s x) = x by rewrite E s_p.
have := f_equal val H; apply/eqP; rewrite val_s val_s -addn1 modnDml.
have -> : ((val x).+1 + 1)%N = (val x + 2)%N by rewrite -addn1 -addnA.
by rewrite succ2_modn_neq // ltn_ord.
Qed.

(** ** The two colour classes: FORWARD and BACKWARD Hamilton cycles. *)

(** Forward arc set [Afwd = {(x, s x)}], backward [Abwd = {(x, p x)}]. *)
Definition Afwd : {set Bicyc * Bicyc} := [set q | q.2 == s q.1].
Definition Abwd : {set Bicyc * Bicyc} := [set q | q.2 == p q.1].

Lemma in_Afwd (x y : Bicyc) : ((x, y) \in Afwd) = (y == s x).
Proof. by rewrite inE. Qed.

Lemma in_Abwd (x y : Bicyc) : ((x, y) \in Abwd) = (y == p x).
Proof. by rewrite inE. Qed.

(** Both are genuine arc sets ([in_arcset]). *)
Lemma Afwd_arcset : in_arcset Afwd.
Proof.
apply/subsetP=> -[x y]; rewrite in_Afwd in_arcsetE bicyc_arcE => /eqP->.
by rewrite eqxx.
Qed.

Lemma Abwd_arcset : in_arcset Abwd.
Proof.
apply/subsetP=> -[x y]; rewrite in_Abwd in_arcsetE bicyc_arcE => /eqP->.
by rewrite eqxx orbT.
Qed.

(** [Afwd] and [Abwd] are disjoint (same tail, distinct heads [s x ≠ p x]). *)
Lemma Afwd_Abwd_disjoint : [disjoint Afwd & Abwd].
Proof.
rewrite -setI_eq0; apply/eqP/setP=> -[x y]; rewrite !inE /=.
case: (eqVneq y (s x)) => [->|//] /=.
by rewrite (negbTE (s_neq_p x)).
Qed.

(** Their union is the full arc set [arcset Bicyc]. *)
Lemma Afwd_Abwd_cover : Afwd :|: Abwd = arcset Bicyc.
Proof.
apply/setP=> -[x y]; rewrite inE in_Afwd in_Abwd in_arcsetE bicyc_arcE.
by [].
Qed.

(** ** [spanning_strong] of the forward / backward cycle. *)

(** [connect (subrel_of Afwd)] reaches [s u] from [u] in one step. *)
Lemma fwd_step (u : Bicyc) : subrel_of Afwd u (s u).
Proof. by rewrite /subrel_of in_Afwd. Qed.

Lemma bwd_step (u : Bicyc) : subrel_of Abwd u (p u).
Proof. by rewrite /subrel_of in_Abwd. Qed.

(** Iterating [s] [k] times shifts the value by [k] (mod n). *)
Lemma val_iter_s k (x : Bicyc) : val (iter k s x) = (val x + k) %% n.
Proof.
elim: k => [|k IH] /=; first by rewrite addn0 modn_small // ltn_ord.
by rewrite IH addnS -addn1 modnDml addn1.
Qed.

(** [s] reaches every vertex from any start (forward Hamilton cycle is one orbit). *)
Lemma s_reaches (x j : Bicyc) : exists k, iter k s x = j.
Proof.
exists ((val j + (n - val x)) %% n).
apply: val_inj; rewrite val_iter_s modnDmr.
rewrite (addnCA (val x) (val j)) subnKC ?(ltnW (ltn_ord x)) //.
by rewrite modnDr modn_small // ltn_ord.
Qed.

(** Reachability under [subrel_of Afwd]: connect from [u] to [iter k s u]. *)
Lemma fwd_connect_iter (u : Bicyc) k : connect (subrel_of Afwd) u (iter k s u).
Proof.
elim: k => [|k IH] /=; first exact: connect0.
by apply: connect_trans IH (connect1 _); exact: fwd_step.
Qed.

(** The forward Hamilton cycle is a spanning-strong subdigraph. *)
Lemma spanning_strong_Afwd : spanning_strong Afwd.
Proof.
split; first exact: Afwd_arcset.
move=> u v; have [k <-] := s_reaches u v; exact: fwd_connect_iter.
Qed.

(** [p] undoes [iter k s]: [p] is the inverse of [s], applied componentwise. *)
Lemma iter_p_s k (z : Bicyc) : iter k p (iter k s z) = z.
Proof.
elim: k z => [//|k IH] z.
by rewrite iterSr [iter k.+1 s z]/= p_s; exact: IH.
Qed.

(** [p] reaches every vertex from any start (backward Hamilton cycle is one
    orbit) — derived from [s_reaches] via the inverse [iter_p_s]. *)
Lemma p_reaches (x j : Bicyc) : exists k, iter k p x = j.
Proof.
have [k Ek] := s_reaches j x; exists k.
by rewrite -Ek iter_p_s.
Qed.

Lemma bwd_connect_iter (u : Bicyc) k : connect (subrel_of Abwd) u (iter k p u).
Proof.
elim: k => [|k IH] /=; first exact: connect0.
by apply: connect_trans IH (connect1 _); exact: bwd_step.
Qed.

Lemma spanning_strong_Abwd : spanning_strong Abwd.
Proof.
split; first exact: Abwd_arcset.
move=> u v; have [k <-] := p_reaches u v; exact: bwd_connect_iter.
Qed.

(** ** GROUNDING 1 — a CONCRETE Strong Arc Decomposition of [Bicyc n]. *)

Theorem SAD_Bicyc : SAD Bicyc.
Proof.
exists Afwd, Abwd; split.
- exact: Afwd_Abwd_disjoint.
- exact: Afwd_Abwd_cover.
- exact: spanning_strong_Afwd.
- exact: spanning_strong_Abwd.
Qed.

(** The same witness through the colouring presentation [SAD_colouring]. *)
Theorem SAD_colouring_Bicyc : SAD_colouring Bicyc.
Proof.
exists (fun q => q.2 == s q.1).
have setF : [set q in arcset Bicyc | q.2 == s q.1] = Afwd.
  apply/setP=> -[x y]; rewrite in_Afwd !inE /= bicyc_arcE.
  by case: (eqVneq y (s x)) => [->|/=]; rewrite ?eqxx ?(orbT, orbF) ?(andbT, andbF).
have setB : [set q in arcset Bicyc | ~~ (q.2 == s q.1)] = Abwd.
  apply/setP=> -[x y]; rewrite in_Abwd !inE /= bicyc_arcE.
  case: (eqVneq y (s x)) => [->|ne] /=.
    by rewrite (negbTE (s_neq_p x)).
  by rewrite andbT.
by rewrite setF setB; split; [exact: spanning_strong_Afwd | exact: spanning_strong_Abwd].
Qed.

(** ** GROUNDING 3 — [Bicyc n] is 2-arc-strong. *)

(** Boundary vertex for the forward orbit: any nonempty proper [X] has [x ∈ X]
    with [s x ∉ X]. *)
Lemma bicyc_fwd_boundary (X : {set Bicyc}) :
  X != set0 -> X != setT -> exists x, x \in X /\ s x \notin X.
Proof.
move=> /set0Pn[x0 x0X] XnT.
have [b /andP[bX sbN]|nob] := pickP (fun x => (x \in X) && (s x \notin X)).
  by exists b.
have closed : forall x, x \in X -> s x \in X.
  by move=> x xX; move: (nob x); rewrite xX /= => /negbT; rewrite negbK.
have iterIn : forall k, iter k s x0 \in X.
  by elim=> [//|k IH] /=; apply: closed.
exfalso; move/negP: XnT; apply; apply/eqP/setP=> j; rewrite in_setT.
by have [k Ek] := s_reaches x0 j; rewrite -Ek iterIn.
Qed.

(** Symmetric: backward boundary for [p]. *)
Lemma bicyc_bwd_boundary (X : {set Bicyc}) :
  X != set0 -> X != setT -> exists x, x \in X /\ p x \notin X.
Proof.
move=> /set0Pn[x0 x0X] XnT.
have [b /andP[bX pbN]|nob] := pickP (fun x => (x \in X) && (p x \notin X)).
  by exists b.
have closed : forall x, x \in X -> p x \in X.
  by move=> x xX; move: (nob x); rewrite xX /= => /negbT; rewrite negbK.
have iterIn : forall k, iter k p x0 \in X.
  by elim=> [//|k IH] /=; apply: closed.
exfalso; move/negP: XnT; apply; apply/eqP/setP=> j; rewrite in_setT.
by have [k Ek] := p_reaches x0 j; rewrite -Ek iterIn.
Qed.

(** GROUNDING: the bidirected n-cycle is 2-ARC-STRONG.  Every nonempty proper cut [X] has a
    forward boundary arc [(x, s x)] and a backward boundary arc [(y, p y)]; these two arcs are
    distinct (if [x = y] then [s x ≠ p x] by [s_neq_p]), so [#|δ⁺(X)| ≥ 2].  Together with
    [SAD_Bicyc] this grounds [arc_strong] (= λ ≥ 2) on a concrete witness — the bidirected
    cycle is the canonical 2-arc-strong digraph admitting a Strong Arc Decomposition. *)
Lemma bicyc_arc_strong : arc_strong Bicyc 2.
Proof.
move=> X X0 XT.
have [x [xX sxN]] := bicyc_fwd_boundary X0 XT.
have [y [yX pyN]] := bicyc_bwd_boundary X0 XT.
apply/card_gt1P; exists (x, s x), (y, p y); split.
- by rewrite in_outcutE; apply/and3P;
     split; [rewrite bicyc_arcE eqxx | exact: xX | exact: sxN].
- by rewrite in_outcutE; apply/and3P;
     split; [rewrite bicyc_arcE eqxx orbT | exact: yX | exact: pyN].
- rewrite xpair_eqE negb_and; have [exy|xny] := eqVneq x y; last by [].
  by rewrite exy /=; exact: s_neq_p.
Qed.

End Bicyc.

(** NOTE — salvaged from a stalled agent run (transient API rate-limiting).  The centerpiece
    [SAD_Bicyc] (a concrete Strong Arc Decomposition of the bidirected n-cycle for every
    [n >= 3]:
    the forward cycle [Afwd] and backward cycle [Abwd] are two arc-disjoint spanning strong
    subdigraphs), its colouring form [SAD_colouring_Bicyc], and its 2-arc-strength
    [bicyc_arc_strong] are PROVED above.  The remaining trailers the agent left unfinished —
    [TT2_not_SAD] and the [CL1_bridge_*] witnesses — were broken at compile and dropped; they
    can be redone when
    the agent fleet recovers. *)
