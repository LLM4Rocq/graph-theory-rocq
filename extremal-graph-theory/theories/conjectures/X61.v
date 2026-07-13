(** * Extremal.conjectures.X61 -- v2 finite induced-saturation exceptions row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X49 X60.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X61 vocabulary ************************************************)

Definition x61_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x61_neither_clique_nor_stable (H : sgraph) : Prop :=
  (exists a b : H, a != b /\ ~~ (a -- b)) /\
  (exists a b : H, a != b /\ a -- b).

Definition x61_induced_saturated (H G : sgraph) : Prop :=
  x61_induced_free G H /\
  (forall a b : G,
    a != b ->
    ~~ (a -- b) ->
    x61_induced_free (@x49_add_edge_graph G a b) H -> False) /\
  forall e : {set G},
    e \in x60_edge_set G ->
    x61_induced_free (@x60_delete_edge_graph G e) H -> False.

Definition x61_infinite_family (F : sgraph -> Prop) : Prop :=
  forall n : nat, exists H : sgraph, F H /\ n <= #|H|.

(** ** X61 statements ******************************************************)

(** arXiv:2506.08810, Problem 21: infinitely many finite graphs, neither
    cliques nor independent sets, should have no finite induced-saturated host. *)
Definition infinite_family_without_finite_induced_saturation_statement : Prop :=
  exists F : sgraph -> Prop,
    x61_infinite_family F /\
    forall H : sgraph,
      F H ->
      x61_neither_clique_nor_stable H /\
      forall G : sgraph, ~ x61_induced_saturated H G.
