(** * Packing.conjectures.grounding_U13 — grounding lemmas for milestone U13.

    SIMPLE, Qed-closed sanity results validating the NEW primitive introduced in
    [U13.v]: [is_domination_number] (the relational domination number γ(G), built
    on GraphTheory's [dom.dominating]).  For this primitive we record SATISFIABLE
    witnesses and several textbook identities.  These are statement-VALIDATION
    lemmas, NOT the (open) conjectures themselves.

    The cross-area primitives reused by U13 ([regular], [k_connected],
    [ceil_div], [dom.dominating]) are imported from base / GraphTheory core and
    are validated elsewhere; here we ground only the locally introduced
    [is_domination_number].

    Two tiny concrete carriers supply the witnesses:
      - [En n] : the edgeless ("empty") graph on ['I_n] — γ(En n) = n (every
        vertex must be picked);
      - [Kn n] : the complete graph on ['I_n] — γ(Kn n) = 1 (one vertex
        dominates).

    Row 2 ([domination_in_plane_triangulations_statement]) is PLANARITY-GATED /
    BLOCKED (G2 gate): its "plane triangulation" predicate is an abstract,
    universally quantified placeholder, so there is no genuine geometric content
    to ground.  We therefore ground only the shared [is_domination_number]
    primitive (which Row 2 reuses verbatim). *)

From GTBase Require Import base.
From Packing.conjectures Require Import U13.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Tiny concrete carriers.
    ========================================================================== *)

Section EmptyGraph.
Variable n : nat.
Definition En_rel : rel 'I_n := fun _ _ => false.
Lemma En_sym : symmetric En_rel. Proof. by []. Qed.
Lemma En_irr : irreflexive En_rel. Proof. by []. Qed.
Definition En : sgraph := SGraph En_sym En_irr.
End EmptyGraph.

Lemma En_edge (n : nat) (x y : En n) : (x -- y) = false.
Proof. by []. Qed.

Lemma En_N (n : nat) (v : En n) : N(v) = set0.
Proof. by apply/setP=> u; rewrite !inE; apply: En_edge. Qed.

Section CompleteGraph.
Variable n : nat.
Definition Kn_rel : rel 'I_n := fun x y => x != y.
Lemma Kn_sym : symmetric Kn_rel. Proof. by move=> x y; rewrite /Kn_rel eq_sym. Qed.
Lemma Kn_irr : irreflexive Kn_rel. Proof. by move=> x; rewrite /Kn_rel eqxx. Qed.
Definition Kn : sgraph := SGraph Kn_sym Kn_irr.
End CompleteGraph.

Lemma Kn_edge (n : nat) (x y : Kn n) : (x -- y) = (x != y).
Proof. by []. Qed.

Definition v0 : Kn 3 := @Ordinal 3 0 isT.

(** ============================================================================
    Generic facts about [dom.dominating] used to compute domination numbers.
    ========================================================================== *)

(** textbook: the whole vertex set always dominates. *)
Lemma dominating_setT (G : sgraph) : dom.dominating (setT : {set G}).
Proof.
apply/forallP => v; apply: (subsetP (set_sub_clns setT)); exact: in_setT.
Qed.

(** textbook: a dominating set of a nonempty graph is nonempty. *)
Lemma dominating_gt0 (G : sgraph) (x : G) (D : {set G}) :
  dom.dominating D -> 0 < #|D|.
Proof.
move/forallP/(_ x)/bigcupP => [w wD _]; apply/card_gt0P; by exists w.
Qed.

(** ============================================================================
    [is_domination_number]: textbook identities.
    ========================================================================== *)

(** identity: a domination number is realised by some dominating set. *)
Lemma is_domination_number_inv (G : sgraph) (m : nat) :
  is_domination_number G m -> exists D : {set G}, dom.dominating D /\ #|D| = m.
Proof. by case. Qed.

(** identity: the domination number is WELL-DEFINED (unique). *)
Lemma is_domination_number_uniq (G : sgraph) (m m' : nat) :
  is_domination_number G m -> is_domination_number G m' -> m = m'.
Proof.
case=> [[D [domD cD]] lb] [[D' [domD' cD']] lb'].
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by rewrite -cD'; apply: lb.
- by rewrite -cD; apply: lb'.
Qed.

(** identity: the domination number never exceeds the order (since [setT]
    dominates). *)
Lemma is_domination_number_le_order (G : sgraph) (m : nat) :
  is_domination_number G m -> m <= #|G|.
Proof.
case=> _ lb; have := lb _ (dominating_setT G); by rewrite cardsT.
Qed.

(** ============================================================================
    [is_domination_number]: SATISFIABLE witnesses.
    ========================================================================== *)

(** witness: γ(K_3) = 1 — a single vertex dominates the complete graph. *)
Lemma dominating_v0 : dom.dominating ([set v0] : {set Kn 3}).
Proof.
apply/forallP => v; case: (eqVneq v v0) => [->|ne].
- by apply: (subsetP (set_sub_clns _)); rewrite inE eqxx.
- apply: (mem_clns (u := v0)); first by rewrite inE eqxx.
  by rewrite Kn_edge eq_sym.
Qed.

Lemma is_domination_number_Kn3 : is_domination_number (Kn 3) 1.
Proof.
split.
- by exists [set v0]; rewrite cards1; split=> //; exact: dominating_v0.
- by move=> D dD; apply: (dominating_gt0 v0).
Qed.

(** witness: γ(E_n) = n — the edgeless graph forces every vertex into the
    dominating set. *)
Lemma En_dominating_setT (n : nat) (D : {set En n}) :
  dom.dominating D -> (setT : {set En n}) \subset D.
Proof.
move/forallP => H; apply/subsetP => v _.
have /bigcupP[w wD vN] := H v.
move: vN; rewrite in_cln => /orP[/eqP <- // | H2].
by rewrite En_edge in H2.
Qed.

Lemma is_domination_number_En (n : nat) : is_domination_number (En n) n.
Proof.
split.
- exists setT; split; first exact: dominating_setT.
  by rewrite cardsT card_ord.
- move=> D dD; apply: leq_trans (subset_leq_card (En_dominating_setT dD)).
  by rewrite cardsT card_ord.
Qed.
