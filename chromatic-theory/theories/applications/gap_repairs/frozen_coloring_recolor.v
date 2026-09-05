(** Closed-neighbourhood saturation is exactly isolation in the graph of
    proper colourings joined by changing one vertex. No degree assumption is
    needed for this equivalence. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_core frozen_coloring_switch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Recolor.
Variables (G : sgraph) (C : finType).
Implicit Types (f g : fc_coloring G C) (v : G) (c : C).

Definition fc_recolor f v c : fc_coloring G C :=
  [ffun u => if u == v then c else f u].
Definition fc_recolor_step f g : bool :=
  [exists v : G, (f v != g v) &&
    [forall u : G, (u == v) || (f u == g u)]].
Definition fc_isolated f : bool :=
  [forall g : fc_coloring G C, fc_proper g ==> ~~ fc_recolor_step f g].

Lemma fc_recolor_missing_proper f v c : fc_proper f ->
  c \notin f @: fc_closed v -> fc_proper (fc_recolor f v c).
Proof.
move=> /forallP Hp miss.
have absent u : u \in fc_closed v -> c != f u.
- move=> uv; apply/eqP=> eqcu; by move: miss; rewrite eqcu (imset_f f uv).
apply/forallP=> x; apply/forallP=> y; apply/implyP=> xy.
rewrite /fc_recolor !ffunE.
case xv: (x == v); case yv: (y == v).
- by move/eqP: xv=> -> in xy; move/eqP: yv=> -> in xy; rewrite sg_irrefl in xy.
- move/eqP: xv=> -> in xy *; exact: absent (fc_closed_edge xy).
- move/eqP: yv=> -> in xy *; rewrite eq_sym.
  apply: absent; apply: fc_closed_edge; by rewrite sg_sym.
exact: (implyP (forallP (Hp x) y) xy).
Qed.

Lemma fc_recolor_missing_step f v c : c \notin f @: fc_closed v ->
  fc_recolor_step f (fc_recolor f v c).
Proof.
move=> miss; apply/existsP; exists v; apply/andP; split.
- rewrite /fc_recolor ffunE eqxx; apply/eqP=> eqfc.
  have present : c \in f @: fc_closed v.
  + apply/imsetP; exists v; [exact: fc_closed_refl | by rewrite eqfc].
  by move: miss; rewrite present.
- apply/forallP=> u; rewrite /fc_recolor ffunE.
  by case uv: (u == v); rewrite ?eqxx ?orbT.
Qed.

Lemma fc_frozen_isolated f : fc_frozen f -> fc_isolated f.
Proof.
move=> /forallP Hf; apply/forallP=> g; apply/implyP=> /forallP Hg.
apply/negP=> /existsP [v /andP [change /forallP Hstep]].
move/imsetP: (forallP (Hf v) (g v))=> [u uv equ].
have uneq : u != v.
- apply/eqP=> eq_uv; subst u; by move: change; rewrite equ eqxx.
have vu : v -- u by move: uv; rewrite fc_closedE (negbTE uneq).
have sameu : f u = g u.
- move: (Hstep u); rewrite (negbTE uneq) /=; exact/eqP.
have neqgu := implyP (forallP (Hg v) u) vu.
by move: neqgu; rewrite -sameu -equ eqxx.
Qed.

Lemma fc_isolated_frozen f : fc_proper f -> fc_isolated f -> fc_frozen f.
Proof.
move=> Hp /forallP Hi; apply/forallP=> v; apply/forallP=> c.
apply: contraTT (Hi (fc_recolor f v c)) => miss.
apply/negP=> /implyP H.
have prop := fc_recolor_missing_proper Hp miss.
have step := fc_recolor_missing_step miss.
by move: (H prop); rewrite step.
Qed.

Theorem fc_frozen_isolated_iff f : fc_proper f ->
  fc_frozen f = fc_isolated f.
Proof.
move=> Hp; apply/idP/idP; first exact: fc_frozen_isolated.
exact: fc_isolated_frozen Hp.
Qed.

End Recolor.
