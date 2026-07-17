(** * GTMisc.conjectures.X145 -- v2 asymptotic dimension of planar graphs row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X145 vocabulary ***********************************************)

Definition x145_set_diameter_at_most (G : sgraph) (S : {set G}) (D : nat) : Prop :=
  forall x y : G, x \in S -> y \in S -> @graph_dist G x y <= D.

Definition x145_cover (G : sgraph) (I : finType) (U : I -> {set G}) : Prop :=
  forall v : G, exists i : I, v \in U i.

Definition x145_r_multiplicity_at_most
    (G : sgraph) (I : finType) (U : I -> {set G}) (r k : nat) : Prop :=
  forall v : G,
    #|[set i : I | [exists x in U i, @graph_dist G v x <= r]]| <= k.

Definition x145_class_asymptotic_dimension_at_most
    (C : sgraph -> Prop) (k : nat) : Prop :=
  forall r : nat,
    exists D : nat,
      forall G : sgraph,
        C G ->
        exists (I : finType) (U : I -> {set G}),
          x145_cover U /\
          (forall i : I, x145_set_diameter_at_most (U i) D) /\
          x145_r_multiplicity_at_most U r k.+1.

(** ** X145 statements *****************************************************)

(** Fujiwara-Papasoglu: the class of planar graphs has asymptotic dimension at
    most two, rendered by uniformly bounded covers with r-multiplicity at most
    three. *)
Definition fujiwara_papasoglu_planar_asymptotic_dimension_two_statement : Prop :=
  x145_class_asymptotic_dimension_at_most wagner_planar 2.
