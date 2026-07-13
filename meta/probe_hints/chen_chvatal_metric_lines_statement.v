From mathcomp Require Import all_ssreflect.
From GTMisc.conjectures Require Import X55.

Lemma refuted : ~ chen_chvatal_metric_lines_statement.
Proof.
rewrite /chen_chvatal_metric_lines_statement => H.
pose d (x y : unit) := 0.
have Hd : x55_metric d.
  rewrite /x55_metric /d; split; last split.
  - by move=> [] []; split.
  - by [].
  - by [].
have Hlines : x55_lines d = set0.
  apply/setP => L; rewrite !inE.
  apply/idP => /existsP[a] /existsP[b] /andP[ab _].
  by case: a b ab => [] [].
case: (H unit d Hd) => [[a [b [ab _]]] | Hle].
- by case: a b ab => [] [].
- move: Hle; rewrite Hlines cards0 leqn0.
  by rewrite card_unit.
Qed.

Print Assumptions refuted.
