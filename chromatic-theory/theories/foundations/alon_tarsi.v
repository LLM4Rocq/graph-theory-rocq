(** * Complementation pairs Eulerian subgraphs of opposite parity.

    For an Eulerian finite arc set with an odd number of arcs, the
    complement of each Eulerian subgraph is Eulerian and has opposite
    parity. This gives a bijection between the two parity classes.

    The definitions match the Eulerian-subgraph characterization of an
    Alon--Tarsi orientation in arXiv:2209.09107v2, Introduction. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AlonTarsi.
Variable V : finType.
Implicit Types A B : {set V * V}.

Definition at_outdegree A (v : V) := #|[set w | (v, w) \in A]|.
Definition at_indegree A (v : V) := #|[set w | (w, v) \in A]|.
Definition at_eulerian A :=
  [forall v, at_outdegree A v == at_indegree A v].
Definition at_eulerian_subgraphs A :=
  [set B : {set V * V} | (B \subset A) && at_eulerian B].
Definition at_even_eulerian A :=
  [set B in at_eulerian_subgraphs A | ~~ odd #|B|].
Definition at_odd_eulerian A :=
  [set B in at_eulerian_subgraphs A | odd #|B|].
Definition at_alon_tarsi A :=
  #|at_even_eulerian A| != #|at_odd_eulerian A|.

Lemma at_outdegree_difference A B v : B \subset A ->
  at_outdegree (A :\: B) v = at_outdegree A v - at_outdegree B v.
Proof.
move=> /subsetP hsub; rewrite /at_outdegree.
have he : [set w | (v, w) \in A :\: B] =
          [set w | (v, w) \in A] :\: [set w | (v, w) \in B].
  by apply/setP=> w; rewrite !inE.
rewrite he; apply: cardsDS; apply/subsetP=> w.
by rewrite !inE; exact: hsub.
Qed.
Lemma at_indegree_difference A B v : B \subset A ->
  at_indegree (A :\: B) v = at_indegree A v - at_indegree B v.
Proof.
move=> /subsetP hsub; rewrite /at_indegree.
have he : [set w | (w, v) \in A :\: B] =
          [set w | (w, v) \in A] :\: [set w | (w, v) \in B].
  by apply/setP=> w; rewrite !inE.
rewrite he; apply: cardsDS; apply/subsetP=> w.
by rewrite !inE; exact: hsub.
Qed.
Lemma at_eulerian_difference A B :
  at_eulerian A -> B \subset A -> at_eulerian B -> at_eulerian (A :\: B).
Proof.
move=> /forallP hA hsub /forallP hB; apply/forallP=> v.
rewrite at_outdegree_difference // at_indegree_difference //.
by rewrite (eqP (hA v)) (eqP (hB v)) eqxx.
Qed.
Lemma at_complement_involution A B :
  B \subset A -> A :\: (A :\: B) = B.
Proof.
move=> hsub; rewrite setDDr setDv set0U.
exact/setIidPr.
Qed.
Lemma at_complement_parity A B :
  odd #|A| -> B \subset A -> odd #|A :\: B| = ~~ odd #|B|.
Proof.
move=> hodd hsub.
by rewrite (cardsDS hsub) oddB ?(subset_leq_card hsub) // hodd addTb.
Qed.

Lemma at_complement_even_odd A B :
  at_eulerian A -> odd #|A| ->
  B \in at_even_eulerian A -> A :\: B \in at_odd_eulerian A.
Proof.
move=> hA hodd; rewrite /at_even_eulerian /at_odd_eulerian !inE.
move=> /andP[/andP[hsub hB] hpar].
rewrite subsetDl (at_eulerian_difference hA hsub hB) /=.
by rewrite at_complement_parity.
Qed.
Lemma at_complement_odd_even A B :
  at_eulerian A -> odd #|A| ->
  B \in at_odd_eulerian A -> A :\: B \in at_even_eulerian A.
Proof.
move=> hA hodd; rewrite /at_even_eulerian /at_odd_eulerian !inE.
move=> /andP[/andP[hsub hB] hpar].
rewrite subsetDl (at_eulerian_difference hA hsub hB) /=.
by rewrite at_complement_parity // negbK.
Qed.

Theorem at_odd_eulerian_parity_equality A :
  at_eulerian A -> odd #|A| ->
  #|at_even_eulerian A| = #|at_odd_eulerian A|.
Proof.
move=> hA hodd.
pose complement B := A :\: B.
have hsub B : B \in at_eulerian_subgraphs A -> B \subset A.
  by rewrite inE=> /andP[].
have hEsub B : B \in at_even_eulerian A -> B \subset A.
  by rewrite inE=> /andP[/hsub h _].
have hE : {in at_even_eulerian A &, injective complement}.
  move=> B C hB hC he.
  have hc := congr1 complement he.
  by rewrite /complement !at_complement_involution ?hEsub in hc.
have him : complement @: at_even_eulerian A = at_odd_eulerian A.
  apply/setP=> B; apply/imsetP/idP.
  - move=> [C hC ->]; exact: at_complement_even_odd hA hodd hC.
  - move=> hB; exists (complement B).
    + exact: at_complement_odd_even hA hodd hB.
    + symmetry; apply: at_complement_involution.
      by move: hB; rewrite inE=> /andP[/hsub h _].
by rewrite -(card_in_imset hE) him.
Qed.

Corollary at_odd_eulerian_not_alon_tarsi A :
  at_eulerian A -> odd #|A| -> ~~ at_alon_tarsi A.
Proof.
move=> hA hodd; rewrite /at_alon_tarsi.
by rewrite (at_odd_eulerian_parity_equality hA hodd) eqxx.
Qed.

Lemma at_empty_eulerian : at_eulerian set0.
Proof.
apply/forallP=> v; rewrite /at_outdegree /at_indegree.
have ho : [set w : V | (v, w) \in (set0 : {set V * V})] = set0.
  by apply/setP=> w; rewrite !inE.
have hi : [set w : V | (w, v) \in (set0 : {set V * V})] = set0.
  by apply/setP=> w; rewrite !inE.
by rewrite ho hi eqxx.
Qed.
Lemma at_empty_eulerian_subgraphs : at_eulerian_subgraphs set0 = [set set0].
Proof.
apply/setP=> B; rewrite /at_eulerian_subgraphs !inE subset0.
case hB: (B == set0)=> //=.
by move/eqP: hB=> ->; rewrite at_empty_eulerian.
Qed.
Lemma at_empty_even_eulerian : at_even_eulerian set0 = [set set0].
Proof.
apply/setP=> B; rewrite /at_even_eulerian at_empty_eulerian_subgraphs !inE.
case hB: (B == set0)=> //=.
by move/eqP: hB=> ->; rewrite cards0.
Qed.
Lemma at_empty_odd_eulerian : at_odd_eulerian set0 = set0.
Proof.
apply/setP=> B; rewrite /at_odd_eulerian at_empty_eulerian_subgraphs !inE.
case hB: (B == set0)=> //=.
by move/eqP: hB=> ->; rewrite cards0.
Qed.
Corollary at_empty_alon_tarsi : at_alon_tarsi set0.
Proof.
by rewrite /at_alon_tarsi at_empty_even_eulerian at_empty_odd_eulerian cards1 cards0.
Qed.

End AlonTarsi.

Print Assumptions at_odd_eulerian_not_alon_tarsi.
Print Assumptions at_empty_alon_tarsi.
