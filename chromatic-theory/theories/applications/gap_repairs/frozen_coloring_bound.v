(** The finite switching bound for actual proper frozen colourings. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_core frozen_coloring_switch.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_fiber.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Counting.
Variables (G : sgraph) (C : finType).
Hypothesis budget : forall x : G, #|fc_closed x| <= #|C|.

Let F : {set fc_coloring G C} := [set f | fc_frozen_proper f].
Let P : {set fc_coloring G C} := [set f | fc_proper f].
Let U : {set fc_coloring G C} := [set f | fc_proper f && ~~ fc_frozen f].

Lemma fc_proper_partition : #|F| + #|U| = #|P|.
Proof.
have fset : F = P :&: [set f | fc_frozen f].
- apply/setP=> f; by rewrite /F /P /fc_frozen_proper !inE.
have uset : U = P :\: [set f | fc_frozen f].
- apply/setP=> f; by rewrite /U /P !inE andbC.
by rewrite fset uset cardsID.
Qed.

Lemma fc_count_with_choice (h : G -> G) :
  (forall v, fc_nontwin v (h v)) -> (#|G| + 4) * #|F| <= 4 * #|P|.
Proof.
move=> hn.
have hedge v : v -- h v by move/andP: (hn v)=> [].
pose D : {set (fc_coloring G C * G)} := setX F [set: G].
pose swap (p : fc_coloring G C * G) := fc_swap p.1 p.2 (h p.2).
have maps p : p \in D -> swap p \in U.
- rewrite /D /setX /F /U !inE andbT /fc_frozen_proper.
  move=> /andP [proper frozen]; apply/andP; split.
  + exact (@fc_swap_proper G C budget p.1 p.2 (h p.2) proper frozen (hedge p.2)).
  + exact (@fc_swap_nonfrozen G C budget p.1 p.2 (h p.2) proper frozen (hn p.2)).
have split_count : #|D| = \sum_(t in U) #|fc_switch_preimages h t|.
- rewrite -sum1_card (partition_big swap (mem U)) //.
  apply: eq_bigr=> t _.
  rewrite -sum1dep_card.
  apply: eq_bigl=> p.
  by rewrite /D /setX /F /fc_switch_preimages /swap !inE andbT.
have many : #|D| <= #|U| * 4.
- rewrite split_count -sum_nat_const; apply: leq_sum=> t.
  rewrite /U inE=> /andP [_ nt].
  exact (@fc_switch_fiber_bound G C budget h hedge t nt).
have many' := leq_add many (leqnn (4 * #|F|)).
rewrite /D cardsX cardsT mulnC in many'.
rewrite -mulnDl [#|U| * 4]mulnC (addnC (4 * #|U|)) -mulnDr
  fc_proper_partition in many'.
exact: many'.
Qed.

Theorem fc_frozen_count_bound : connected [set: G] -> ~ clique [set: G] ->
  (#|G| + 4) * #|[set f : fc_coloring G C | fc_frozen_proper f]| <=
  4 * #|[set f : fc_coloring G C | fc_proper f]|.
Proof.
move=> conn nc.
have exists_h (v : G) : exists w, fc_nontwin v w.
- apply/existsP; exact (@fc_nontwin_exists G conn nc v).
pose h v := xchoose (exists_h v).
apply: (fc_count_with_choice (h := h))=> v.
exact: xchooseP (exists_h v).
Qed.

Corollary fc_frozen_count_quantitative : connected [set: G] ->
  ~ clique [set: G] -> forall k, 4 * k <= #|G| ->
  k * #|[set f : fc_coloring G C | fc_frozen_proper f]| <=
  #|[set f : fc_coloring G C | fc_proper f]|.
Proof.
move=> conn nc k kn.
have big := fc_frozen_count_bound conn nc.
have lekn : 4 * k <= #|G| + 4 := leq_trans kn (leq_addr 4 #|G|).
have small := leq_mul lekn (leqnn #|F|).
have result := leq_trans small big.
by move: result; rewrite -mulnA leq_pmul2l.
Qed.

End Counting.

Print Assumptions fc_frozen_count_bound.
Print Assumptions fc_frozen_count_quantitative.
