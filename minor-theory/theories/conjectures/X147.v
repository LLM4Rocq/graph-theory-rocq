(** * Minor.conjectures.X147 -- v2 fat-minor/quasi-isometry row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X147 vocabulary ***********************************************)

Definition x147_c_fat_minor (G H : sgraph) (c : nat) : Prop :=
  exists branch : H -> {set G},
    (forall h : H, branch h != set0) /\
    (forall h : H, connected (branch h)) /\
    (forall h1 h2 : H, h1 != h2 -> branch h1 :&: branch h2 = set0) /\
    (forall h1 h2 : H, h1 -- h2 ->
      exists x y : G, [/\ x \in branch h1, y \in branch h2 & x -- y]) /\
    (forall h1 h2 : H, h1 != h2 -> ~~ (h1 -- h2) ->
      forall x y : G, x \in branch h1 -> y \in branch h2 -> c <= @graph_dist G x y).

Definition x147_quasi_isometric_to_H_minor_free
    (G H : sgraph) (L C : nat) : Prop :=
  exists Q : sgraph,
    ~ minor Q H /\
    exists (f : G -> Q) (g : Q -> G),
      (forall x y : G,
        @graph_dist Q (f x) (f y) <= L * @graph_dist G x y + C) /\
      (forall x y : Q,
        @graph_dist G (g x) (g y) <= L * @graph_dist Q x y + C) /\
      (forall y : Q, exists x : G, @graph_dist Q (f x) y <= C) /\
      (forall x : G, exists y : Q, @graph_dist G (g y) x <= C).

(** ** X147 statements *****************************************************)

(** Georgakopoulos-Papasoglu: for every graph H and fatness c, H-c-fat-minor-free
    graphs are quasi-isometric, with constants depending on H,c, to H-minor-free
    graphs. *)
Definition georgakopoulos_papasoglu_fat_minor_quasi_isometry_statement : Prop :=
  forall (H : sgraph) (c : nat),
    exists L C : nat,
      forall G : sgraph,
        ~ x147_c_fat_minor G H c ->
        x147_quasi_isometric_to_H_minor_free G H L C.
