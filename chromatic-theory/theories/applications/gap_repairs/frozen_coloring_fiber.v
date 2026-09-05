From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.
From Chromatic.applications.gap_repairs Require Import frozen_coloring_core frozen_coloring_switch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Fiber.
Variables (G : sgraph) (C : finType).
Implicit Types (f t : fc_coloring G C) (x y z u v : G).

Lemma fc_fiber_missing f x y (Z : {set G}) c :
  x \in Z -> y \notin Z -> c \in f @: Z ->
  c \notin (fc_swap f x y) @: Z -> f x = c.
Proof.
move=> xZ yZ /imsetP[u uZ fu] missing.
case ux: (u == x); first by move/eqP: ux=> <-; rewrite fu.
have uy : u != y by apply/eqP=> eu; move: yZ; rewrite -eu uZ.
have bad : c \in (fc_swap f x y) @: Z.
  apply/imsetP; exists u=> //.
  by rewrite fc_swap_other // ?ux // fu.
by move: missing; rewrite bad.
Qed.

Lemma fc_swap_duplicate f x y (Z : {set G}) :
  {in Z &, injective f} -> x \in Z -> y \notin Z -> f x != f y ->
  f y \in f @: Z ->
  exists w, [ /\ w \in Z, w != x & fc_swap f x y w = fc_swap f x y x].
Proof.
move=> injf xZ yZ xy /imsetP[w wZ fw].
have wx : w != x by apply/eqP=> e; move: xy; rewrite -e -fw eqxx.
have wy : w != y by apply/eqP=> eu; move: yZ; rewrite -eu wZ.
exists w; split=> //; by rewrite fc_swap_other // fc_swap_left fw.
Qed.

Lemma fc_swap_duplicate_cover f x y w (Z : {set G}) :
  {in Z &, injective f} -> x \in Z -> y \notin Z ->
  w \in Z -> w != x -> fc_swap f x y w = fc_swap f x y x ->
  forall u v, u \in Z -> v \in Z -> u != v ->
    fc_swap f x y u = fc_swap f x y v -> u \in [set x; w].
Proof.
move=> injf xZ yZ wZ wx equal u v uZ vZ uv eq.
have wy : w != y by apply/eqP=> eu; move: yZ; rewrite -eu wZ.
have uy : u != y by apply/eqP=> eu; move: yZ; rewrite -eu uZ.
have vy : v != y by apply/eqP=> eu; move: yZ; rewrite -eu vZ.
case ux: (u == x); first by rewrite !inE ux.
have ux' : u != x by rewrite ux.
case vx: (v == x).
  move/eqP: vx=> -> in eq.
  have fu_fw : f u = f w.
    by rewrite -(fc_swap_other f ux' uy) -(fc_swap_other f wx wy) equal.
  have -> := injf u w uZ wZ fu_fw.
  by rewrite !inE eqxx orbT.
have vx' : v != x by rewrite vx.
have euv : u = v by apply: (injf u v uZ vZ); rewrite -(fc_swap_other f ux' uy) -(fc_swap_other f vx' vy).
by move: uv; rewrite euv eqxx.
Qed.


Hypothesis budget : forall x : G, #|fc_closed x| <= #|C|.
Variable h : G -> G.
Hypothesis hedge : forall x : G, x -- h x.

Definition fc_switch_preimages t : {set (fc_coloring G C * G)} :=
  [set p | fc_frozen_proper p.1 && (fc_swap p.1 p.2 (h p.2) == t)].
Definition fc_inside z (p : fc_coloring G C * G) :=
  if p.2 \in fc_closed z then p.2 else h p.2.
Definition fc_outside z (p : fc_coloring G C * G) :=
  if p.2 \in fc_closed z then h p.2 else p.2.

Lemma fc_preimage_normalized t z p :
  ~~ fc_frozen_at t z -> p \in fc_switch_preimages t ->
  [ /\ fc_frozen p.1, fc_inside z p \in fc_closed z,
       fc_outside z p \notin fc_closed z,
       fc_inside z p -- fc_outside z p &
       fc_swap p.1 (fc_inside z p) (fc_outside z p) = t].
Proof.
move=> nt; rewrite /fc_switch_preimages inE /fc_frozen_proper.
move=> /andP [/andP [proper frozen] /eqP swapped].
have neq : p.1 p.2 != p.1 (h p.2).
  exact: implyP (forallP (forallP proper p.2) (h p.2)) (hedge p.2).
have different : (p.2 \in fc_closed z) != (h p.2 \in fc_closed z).
  by rewrite -(fc_swap_frozen_at budget (forallP frozen z) neq) swapped.
rewrite /fc_inside /fc_outside.
case xZ: (p.2 \in fc_closed z); case yZ: (h p.2 \in fc_closed z);
  rewrite xZ yZ in different; try by [].
split=> //; first by rewrite xZ.
  + by rewrite sg_sym; exact: hedge.
  + by rewrite fc_swapC.
Qed.

Lemma fc_preimage_outside_color t z p c :
  ~~ fc_frozen_at t z -> p \in fc_switch_preimages t ->
  c \notin t @: fc_closed z -> t (fc_outside z p) = c.
Proof.
move=> nt pin missing.
case: (fc_preimage_normalized nt pin)=> frozen xZ yZ xy swapped.
have cf : c \in p.1 @: fc_closed z := forallP (forallP frozen z) c.
have eqc : p.1 (fc_inside z p) = c.
  apply: fc_fiber_missing xZ yZ cf _; by rewrite swapped.
by rewrite -swapped fc_swap_right.
Qed.

Lemma fc_preimage_local_inj t z p :
  ~~ fc_frozen_at t z -> p \in fc_switch_preimages t ->
  {in fc_closed (fc_inside z p) &, injective t}.
Proof.
move=> nt pin.
case: (fc_preimage_normalized nt pin)=> frozen xZ yZ xy swapped.
apply: (@fc_frozen_at_inj G C budget t (fc_inside z p)).
by rewrite -swapped; exact: fc_swap_frozen_at_left frozen xy.
Qed.


Lemma fc_root_recover z p :
  p.2 = if p.2 == fc_inside z p then fc_inside z p else fc_outside z p.
Proof.
case mem: (p.2 \in fc_closed z); rewrite /fc_inside /fc_outside mem.
- by rewrite eqxx.
- by case: eqP.
Qed.

Lemma fc_preimage_same_inside t z p q c :
  ~~ fc_frozen_at t z -> p \in fc_switch_preimages t ->
  q \in fc_switch_preimages t -> c \notin t @: fc_closed z ->
  fc_inside z p = fc_inside z q ->
  (p.2 == fc_inside z p) = (q.2 == fc_inside z q) -> p = q.
Proof.
move=> nt pin qin missing inside tags.
case: (fc_preimage_normalized nt pin)=> fp xp yp edgep swapp.
case: (fc_preimage_normalized nt qin)=> fq xq yq edgeq swapq.
have colp := fc_preimage_outside_color nt pin missing.
have colq := fc_preimage_outside_color nt qin missing.
have injp := fc_preimage_local_inj nt pin.
have outside : fc_outside z p = fc_outside z q.
  apply: (injp (fc_outside z p) (fc_outside z q)).
  - exact: fc_closed_edge edgep.
  - rewrite inside; exact: fc_closed_edge edgeq.
  - by rewrite colp colq.
have roots : p.2 = q.2.
  by rewrite [p.2](fc_root_recover z p) [q.2](fc_root_recover z q) tags inside outside.
have colors : p.1 = q.1.
  apply: (can_inj (fc_swapK (fc_inside z p) (fc_outside z p))).
  by rewrite swapp inside outside swapq.
apply/eqP; change ((p.1 == q.1) && (p.2 == q.2)).
by rewrite colors roots !eqxx.
Qed.

Lemma fc_preimage_inside_cover t z p :
  ~~ fc_frozen_at t z -> p \in fc_switch_preimages t ->
  exists w, forall q, q \in fc_switch_preimages t ->
    fc_inside z q \in [set fc_inside z p; w].
Proof.
move=> nt pin.
case: (fc_preimage_normalized nt pin)=> frozen xZ yZ xy swapped.
have injf := @fc_frozen_inj G C budget p.1 frozen z.
have neqf : p.1 (fc_inside z p) != p.1 (fc_outside z p).
  move: pin; rewrite /fc_switch_preimages inE /fc_frozen_proper.
  move=> /andP [/andP [proper _] _].
  exact: implyP (forallP (forallP proper _) _) xy.
have fy : p.1 (fc_outside z p) \in p.1 @: fc_closed z.
  exact: forallP (forallP frozen z) _.
case: (fc_swap_duplicate injf xZ yZ neqf fy)=> w [wZ wx ew].
exists w=> q qin.
case: (fc_preimage_normalized nt qin)=> frozenq xq yq xyq swappedq.
have injq := @fc_frozen_inj G C budget q.1 frozenq z.
have neqfq : q.1 (fc_inside z q) != q.1 (fc_outside z q).
  move: qin; rewrite /fc_switch_preimages inE /fc_frozen_proper.
  move=> /andP [/andP [proper _] _].
  exact: implyP (forallP (forallP proper _) _) xyq.
have fyq : q.1 (fc_outside z q) \in q.1 @: fc_closed z.
  exact: forallP (forallP frozenq z) _.
case: (fc_swap_duplicate injq xq yq neqfq fyq)=> v [vZ vx ev].
apply: (fc_swap_duplicate_cover injf xZ yZ wZ wx ew xq vZ).
- by rewrite eq_sym.
- by rewrite swapped -swappedq ev.
Qed.


Lemma fc_switch_fiber_bound t : ~~ fc_frozen t ->
  #|fc_switch_preimages t| <= 4.
Proof.
move=> /forallPn [z nt].
case empty: (fc_switch_preimages t == set0).
  by move/eqP: empty=> ->; rewrite cards0.
have nonempty : fc_switch_preimages t != set0 by rewrite empty.
case/set0Pn: nonempty=> p pin.
case: (fc_preimage_inside_cover nt pin)=> w cover.
move/forallPn: (nt)=> [c missing].
pose code (q : fc_coloring G C * G) :=
  (fc_inside z q == fc_inside z p, q.2 == fc_inside z q).
have injcode : {in fc_switch_preimages t &, injective code}.
  move=> a b ain bin same.
  have first : (fc_inside z a == fc_inside z p) =
               (fc_inside z b == fc_inside z p) := congr1 (fun x : bool * bool => x.1) same.
  have second : (a.2 == fc_inside z a) =
                (b.2 == fc_inside z b) := congr1 (fun x : bool * bool => x.2) same.
  have inside : fc_inside z a = fc_inside z b.
    move: (cover a ain) (cover b bin); rewrite !inE.
    case ax: (fc_inside z a == fc_inside z p);
      case bx: (fc_inside z b == fc_inside z p);
      rewrite ax bx in first; try by [].
    - by move/eqP: ax=> ->; move/eqP: bx=> ->.
    - by move=> /eqP -> /eqP ->.
  exact: fc_preimage_same_inside nt ain bin missing inside second.
have bound := leq_card_in code (fc_switch_preimages t) injcode.
by move: bound; rewrite card_prod !card_bool.
Qed.

End Fiber.

Print Assumptions fc_switch_fiber_bound.
