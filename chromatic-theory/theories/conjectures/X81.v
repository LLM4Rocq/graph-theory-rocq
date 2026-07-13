(** * Chromatic.conjectures.X81 -- v2 proper-orientation bipartite row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X81 vocabulary ************************************************)

Definition x81_orientation_of (G : sgraph) (D : rel G) : Prop :=
  (forall x y : G, D x y -> x -- y) /\
  forall x y : G, x -- y -> (D x y) (+) (D y x).

Definition x81_indegree (G : sgraph) (D : rel G) (v : G) : nat :=
  #|[set u : G | D u v]|.

Definition x81_proper_orientation (G : sgraph) (D : rel G) : Prop :=
  forall x y : G, x -- y -> x81_indegree D x != x81_indegree D y.

Definition x81_proper_orientation_bound (G : sgraph) (k : nat) : Prop :=
  exists D : rel G,
    x81_orientation_of D /\
    x81_proper_orientation D /\
    forall v : G, x81_indegree D v <= k.

(** ** X81 statements ******************************************************)

(** Studies slice: Araujo-Cohen-de Rezende-Havet-Moura proper orientation
    number problem for bipartite graphs. *)
Definition bipartite_proper_orientation_half_delta_constant_statement : Prop :=
  exists C : nat,
    forall G : sgraph,
      bipartite G ->
      exists k : nat,
        x81_proper_orientation_bound G k /\
        2 * k <= Delta G + 2 * C.
