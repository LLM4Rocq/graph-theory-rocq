From GTBase Require Export base.
From Chromatic.conjectures Require Import X100.

Set Implicit Arguments.

(* Adversarial check: is the statement internally REFUTABLE?
   K_4 (= complete 4) at k=2 forces 4 pairwise-adjacent vertices to have
   pairwise-distinct weights mod 2 -> injective (complete 4) -> 'I_2 -> 4<=2. *)
Lemma X100_refuted : ~ modular_edge_colouring_k_plus_constant_statement.
Proof.
rewrite /modular_edge_colouring_k_plus_constant_statement => H.
have [C /(_ (complete 4)) [col Hcol]] := H 2 (leqnn 2).
pose g (v : complete 4) : 'I_2 :=
  Ordinal (ltn_pmod (x100_modular_weight col v) (ltn0Sn 1)).
have ginj : injective g.
  move=> x y /(congr1 (@nat_of_ord 2)) /= exy.
  case: (eqVneq x y) => // xney.
  by move: (Hcol x y xney); rewrite exy eqxx.
have := leq_card g ginj.
by rewrite !card_ord.
Qed.

Print Assumptions X100_refuted.
