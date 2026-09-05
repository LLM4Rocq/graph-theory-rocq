(** Greedy existence of a proper colouring with an inhabited palette
    large enough for every closed neighbourhood. *)
From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma fc_palette_spare (G : sgraph) (C : finType)
    (f : fc_coloring G C) (x : G) (S : {set G}) :
  #|fc_closed x| <= #|C| -> exists c : C, c \notin f @: (N(x) :&: S).
Proof.
move=> budget.
have nd : #|N(x)| < #|C|.
  by move: budget; rewrite /fc_closed cardsU1 inE sg_irrefl /= add1n.
have small : #|f @: (N(x) :&: S)| < #|C|.
  apply: (leq_ltn_trans (leq_imset_card f (N(x) :&: S))).
  exact: (leq_ltn_trans (subset_leq_card (subsetIl _ _)) nd).
have nz : 0 < #|~: (f @: (N(x) :&: S))|.
  by rewrite cardsCs setCK subn_gt0.
have [c hc] := card_gt0P nz.
by exists c; move: hc; rewrite inE.
Qed.

Lemma fc_partial_coloring (G : sgraph) (C : finType) (c0 : C) :
  (forall x : G, #|fc_closed x| <= #|C|) ->
  forall s : seq G, exists f : fc_coloring G C,
    forall x y, x \in s -> y \in s -> x -- y -> f x != f y.
Proof.
move=> budget; elim=> [|v s [f hf]].
  exists [ffun _ => c0]; by move=> x y; rewrite in_nil.
have [c hc] := fc_palette_spare f [set x | x \in s] (budget v).
pose g := [ffun x => if x == v then c else f x].
exists g; move=> x y; rewrite !inE=> xs ys xy.
have spare (z : G) : z \in s -> v -- z -> c != f z.
  move=> zs vz; apply/negP=> /eqP cfz.
  have memc : c \in f @: (N(v) :&: [set x | x \in s]).
    apply/imsetP; exists z; first by rewrite !inE vz zs.
    exact: cfz.
  by move: hc; rewrite memc.
rewrite /g !ffunE.
case xv: (x == v); case yv: (y == v).
- have /eqP xvE := xv; have /eqP yvE := yv.
  subst x; subst y; by rewrite sg_irrefl in xy.
- have /eqP xvE := xv; subst x.
  rewrite yv /= in ys; exact: spare ys xy.
- have /eqP yvE := yv; subst y.
  rewrite xv /= in xs; rewrite eq_sym.
  apply: (spare x xs).
  by rewrite sg_sym.
- rewrite xv /= in xs; rewrite yv /= in ys; exact: hf xs ys xy.
Qed.

Lemma fc_proper_exists (G : sgraph) (C : finType) (c0 : C) :
  (forall x : G, #|fc_closed x| <= #|C|) ->
  exists f : fc_coloring G C, fc_proper f.
Proof.
move=> budget.
have [f hf] := fc_partial_coloring c0 budget (enum G).
exists f; apply/forallP=> x; apply/forallP=> y; apply/implyP=> xy.
apply: hf xy; exact: mem_enum.
Qed.
