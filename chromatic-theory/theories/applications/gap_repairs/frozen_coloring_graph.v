From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph dom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_core.

Lemma fc_all_twins_complete (G : sgraph) (v : G) :
  connected [set: G] ->
  (forall w : G, v -- w -> fc_closed v = fc_closed w) ->
  clique [set: G].
Proof.
move=> conn twins.
have closedN : closed (@sedge G) (fc_closed v).
  apply: intro_closed; first exact: sconnect_sym.
  move=> x y xy hx; move: hx; rewrite /fc_closed !inE.
  case/orP=> [/eqP xv | vx].
  - have xy' : x -- y := xy.
    subst x; by rewrite xy' orbT.
  - have xy' : x -- y := xy.
    have hy : y \in fc_closed x by rewrite /fc_closed !inE xy' orbT.
    rewrite -(twins x vx) in hy.
    by move: hy; rewrite /fc_closed !inE.
have allN (x : G) : x \in fc_closed v.
  have he := closed_connect closedN (connectedTE conn v x).
  by rewrite -he /fc_closed !inE eqxx.
move=> x y _ _ xNy.
have hx : fc_closed x = fc_closed v.
  move: (allN x); rewrite /fc_closed !inE => /orP[/eqP -> | vx].
  - done.
  - symmetry; exact: twins x vx.
have hy : y \in fc_closed x by rewrite hx; exact: allN.
by move: hy; rewrite /fc_closed !inE eq_sym (negbTE xNy).
Qed.

Lemma fc_nontwin_exists (G : sgraph) :
  connected [set: G] -> ~ clique [set: G] ->
  forall v : G, [exists w : G, fc_nontwin v w].
Proof.
move=> conn nc v; case H: [exists w : G, fc_nontwin v w]=> //.
exfalso; apply: nc; apply: (@fc_all_twins_complete G v conn).
move=> w vw; apply/eqP.
have nex : [forall w : G, ~~ fc_nontwin v w] by rewrite -negb_exists H.
by move: (forallP nex w); rewrite /fc_nontwin vw /= negbK.
Qed.
