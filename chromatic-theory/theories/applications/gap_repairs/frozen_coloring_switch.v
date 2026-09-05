From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Switch.
Variables (G : sgraph) (C : finType).
Implicit Types (f : fc_coloring G C) (x y z : G).

Lemma fc_closedE x y : (y \in fc_closed x) = (y == x) || (x -- y).
Proof. by rewrite /fc_closed !inE. Qed.
Lemma fc_closed_refl x : x \in fc_closed x.
Proof. by rewrite fc_closedE eqxx. Qed.
Lemma fc_closed_sym x y : (y \in fc_closed x) = (x \in fc_closed y).
Proof. by rewrite !fc_closedE eq_sym sg_sym. Qed.
Lemma fc_closed_edge x y : x -- y -> y \in fc_closed x.
Proof. by move=> xy; rewrite fc_closedE xy orbT. Qed.
Lemma fc_edge_neq x y : x -- y -> x != y.
Proof. apply: contraTneq => ->; by rewrite sg_irrefl. Qed.

Lemma fc_frozen_at_image f x : fc_frozen_at f x -> f @: fc_closed x = [set: C].
Proof. move/forallP=> H; apply/setP=> c; by rewrite inE H. Qed.

Hypothesis budget : forall x : G, #|fc_closed x| <= #|C|.

Lemma fc_frozen_at_inj f x : fc_frozen_at f x ->
  {in fc_closed x &, injective f}.
Proof.
move=> H; apply/imset_injP/eqP; apply/eqP; rewrite eqn_leq.
have full := fc_frozen_at_image H.
rewrite full cardsT; apply/andP; split; last exact: budget.
by rewrite -cardsT -full leq_imset_card.
Qed.

Lemma fc_frozen_inj f : fc_frozen f -> forall x,
  {in fc_closed x &, injective f}.
Proof. move/forallP=> H x; exact: fc_frozen_at_inj (H x). Qed.

Lemma fc_swapE f x y z :
  fc_swap f x y z = if z == x then f y else if z == y then f x else f z.
Proof. by rewrite /fc_swap ffunE. Qed.
Lemma fc_swap_left f x y : fc_swap f x y x = f y.
Proof. by rewrite fc_swapE eqxx. Qed.
Lemma fc_swap_right f x y : fc_swap f x y y = f x.
Proof. rewrite fc_swapE eqxx; by case: eqP=> [->|yx]. Qed.
Lemma fc_swap_other f x y z : z != x -> z != y -> fc_swap f x y z = f z.
Proof. by move=> zx zy; rewrite fc_swapE (negbTE zx) (negbTE zy). Qed.
Lemma fc_swapC f x y : fc_swap f x y = fc_swap f y x.
Proof.
apply/ffunP=> z.
case zx: (z == x); first by move/eqP: zx=> ->; rewrite fc_swap_left fc_swap_right.
case zy: (z == y); first by move/eqP: zy=> ->; rewrite fc_swap_left fc_swap_right.
by rewrite !fc_swapE zx zy.
Qed.
Lemma fc_swapK x y : involutive (fun f => fc_swap f x y).
Proof.
move=> f; apply/ffunP=> z; rewrite fc_swapE fc_swap_left fc_swap_right.
case: eqP=> [->|zx] //; case: eqP=> [->|zy] //.
by rewrite fc_swap_other //; apply/eqP.
Qed.

Lemma fc_swap_at_edge f x y z : fc_frozen f ->
  x -- y -> x -- z -> fc_swap f x y x != fc_swap f x y z.
Proof.
move=> Hf xy xz; have injf := @fc_frozen_inj f Hf x.
have zx : z != x by rewrite eq_sym; exact: fc_edge_neq xz.
rewrite fc_swap_left fc_swapE (negbTE zx).
case zy: (z == y).
- apply/eqP=> eqfyx.
  have yx := injf y x (fc_closed_edge xy) (fc_closed_refl x) eqfyx.
  by move: xy; rewrite yx sg_irrefl.
- apply/eqP=> eqfyz.
  have yz := injf y z (fc_closed_edge xy) (fc_closed_edge xz) eqfyz.
  by move: zy; rewrite yz eqxx.
Qed.

Lemma fc_swap_proper f x y : fc_proper f -> fc_frozen f ->
  x -- y -> fc_proper (fc_swap f x y).
Proof.
move=> /forallP Hp Hf xy.
apply/forallP=> u; apply/forallP=> v; apply/implyP=> uv.
case ux: (u == x); first by move/eqP: ux=> -> in uv *; exact: fc_swap_at_edge Hf xy uv.
case uy: (u == y).
- move/eqP: uy=> -> in uv *; rewrite fc_swapC.
  apply: fc_swap_at_edge Hf _ uv; by rewrite sg_sym.
case vx: (v == x).
- move/eqP: vx=> -> in uv *; rewrite eq_sym.
  apply: fc_swap_at_edge Hf xy _; by rewrite sg_sym.
case vy: (v == y).
- move/eqP: vy=> -> in uv *; rewrite fc_swapC eq_sym.
  apply: fc_swap_at_edge Hf _ _; by rewrite sg_sym.
rewrite !fc_swapE ux uy vx vy.
exact: (implyP (forallP (Hp u) v) uv).
Qed.

Lemma fc_swap_frozen_at_same f x y z : fc_frozen_at f z ->
  (x \in fc_closed z) = (y \in fc_closed z) ->
  fc_frozen_at (fc_swap f x y) z.
Proof.
move=> /forallP Hf same; apply/forallP=> c.
move/imsetP: (Hf c)=> [u uz ->].
case ux: (u == x).
- move/eqP: ux=> -> in uz *; apply/imsetP; exists y.
  + by rewrite -same.
  + by rewrite fc_swap_right.
case uy: (u == y).
- move/eqP: uy=> -> in uz *; apply/imsetP; exists x.
  + by rewrite same.
  + by rewrite fc_swap_left.
apply/imsetP; exists u=> //; by rewrite fc_swapE ux uy.
Qed.

Lemma fc_swap_missing f x y z : fc_frozen_at f z -> f x != f y ->
  x \in fc_closed z -> y \notin fc_closed z ->
  f x \notin (fc_swap f x y) @: fc_closed z.
Proof.
move=> Hf neqf xz yz; apply/negP=> /imsetP [u uz eqfx].
have injf := @fc_frozen_at_inj f z Hf.
case ux: (u == x).
- move/eqP: ux=> -> in eqfx; rewrite fc_swap_left in eqfx.
  by move: neqf; rewrite eqfx eqxx.
case uy: (u == y).
- move/eqP: uy=> -> in uz; by move: yz; rewrite uz.
rewrite fc_swapE ux uy in eqfx.
have xu := injf x u xz uz eqfx.
by move: ux; rewrite xu eqxx.
Qed.

Lemma fc_swap_frozen_at f x y z : fc_frozen_at f z -> f x != f y ->
  fc_frozen_at (fc_swap f x y) z =
  ((x \in fc_closed z) == (y \in fc_closed z)).
Proof.
move=> Hf neqf.
case xz: (x \in fc_closed z); case yz: (y \in fc_closed z).
- apply: fc_swap_frozen_at_same Hf _.
  by rewrite xz yz.
- apply/negbTE/negP=> /forallP Hs.
  have missing := fc_swap_missing Hf neqf xz (negbT yz).
  by move: missing; rewrite Hs.
- apply/negbTE/negP=> Hs.
  have neqfy : f y != f x by rewrite eq_sym.
  have missing := fc_swap_missing Hf neqfy yz (negbT xz).
  rewrite -fc_swapC in missing.
  by move: missing; rewrite (forallP Hs).
- apply: fc_swap_frozen_at_same Hf _.
  by rewrite xz yz.
Qed.

Lemma fc_swap_frozen_at_left f x y : fc_frozen f -> x -- y ->
  fc_frozen_at (fc_swap f x y) x.
Proof.
move=> /forallP Hf xy; apply: fc_swap_frozen_at_same (Hf x) _.
by rewrite fc_closed_refl fc_closed_edge.
Qed.

Lemma fc_swap_frozen_at_right f x y : fc_frozen f -> x -- y ->
  fc_frozen_at (fc_swap f x y) y.
Proof.
move=> Hf xy; rewrite fc_swapC; apply: fc_swap_frozen_at_left Hf _.
by rewrite sg_sym.
Qed.

Lemma fc_swap_nonfrozen f x y : fc_proper f -> fc_frozen f ->
  fc_nontwin x y -> ~~ fc_frozen (fc_swap f x y).
Proof.
move=> /forallP Hp Hf /andP [xy nontwin].
have neqf : f x != f y := implyP (forallP (Hp x) y) xy.
apply/negP=> /forallP Hs.
have same : fc_closed x = fc_closed y.
- apply/setP=> z.
  have frozenz := forallP Hf z.
  have eqmem : (x \in fc_closed z) == (y \in fc_closed z).
  + by rewrite -(fc_swap_frozen_at frozenz neqf); exact: Hs.
  move/eqP: eqmem; by rewrite (fc_closed_sym z x) (fc_closed_sym z y).
by move: nontwin; rewrite same eqxx.
Qed.

End Switch.
