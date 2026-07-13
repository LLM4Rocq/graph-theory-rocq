From GTBase Require Export base.
From Chromatic.conjectures Require Import X83.

Set Implicit Arguments.

Lemma refuted : ~ aravind_rainbow_induced_chromatic_path_statement.
Proof.
rewrite /aravind_rainbow_induced_chromatic_path_statement => H.
have Hcard : 0 < #|complete 2| by rewrite card_ord.
have Htf : triangle_free (complete 2).
  move => x y z.
  by case: x => [[|[|x]] hx];
     case: y => [[|[|y]] hy];
     case: z => [[|[|z]] hz].
have [p [Hsize [Hind Huniq]]] := H (complete 2) unit (fun _ => tt) Hcard Htf.
have Hclq : clique [set: complete 2] by move => x y _ _ xy; exact: xy.
have Hchi : χ([set: complete 2]) = 2.
  by rewrite chi_clique // cardsT card_ord.
move: Hsize; rewrite Hchi => Hsize2.
clear Hind.
move: Hsize2 Huniq.
by case: p => [|a [|b p]] //= _.
Qed.

Print Assumptions refuted.
