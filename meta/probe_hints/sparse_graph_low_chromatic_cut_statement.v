From GTBase Require Export base.
From Chromatic.conjectures Require Import X35.

Set Implicit Arguments.
Unset Strict Implicit.

Section Refute.

Definition noedge : rel bool := fun _ _ => false.
Lemma noedge_sym : symmetric noedge. Proof. by []. Qed.
Lemma noedge_irrefl : irreflexive noedge. Proof. by []. Qed.
Definition E2 : sgraph := SGraph noedge_sym noedge_irrefl.

Lemma E2_card : #|E2| = 2.
Proof. by rewrite /E2 /= card_bool. Qed.

Lemma E2_noedges : x35_edge_set E2 = set0.
Proof.
apply/setP => e; rewrite /x35_edge_set !inE.
apply/negbTE; rewrite negb_exists; apply/forallP => x.
rewrite negb_exists; apply/forallP => y.
by rewrite negb_and; apply/orP; left.
Qed.

Lemma refuted : ~ sparse_graph_low_chromatic_cut_statement.
Proof.
rewrite /sparse_graph_low_chromatic_cut_statement => H.
have hk : 0 < 1 by [].
have hkn : 1 <= #|E2| by rewrite E2_card.
have hsp : (2 * #|x35_edge_set E2| < 2 * 1 * #|E2| - 1 * 2)%N.
  by rewrite E2_noedges cards0 E2_card.
have [X [[Xne _] Hchi]] := H 1 E2 hk hkn hsp.
have [x0 x0X] := set0Pn _ Xne.
have hAne : [set: induced X] != set0.
  by apply/set0Pn; exists (Sub x0 x0X); rewrite inE.
have hw : ω([set: induced X]) < 1.
  exact: leq_ltn_trans (omega_leq_chi _) Hchi.
move: hAne; rewrite -omega_eq0 => hne.
by move: hw; rewrite ltnS leqn0 (negbTE hne).
Qed.

Print Assumptions refuted.

End Refute.
