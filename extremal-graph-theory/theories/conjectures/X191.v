(** * Extremal.conjectures.X191 -- v2 dense H-free clique-blowup error row *)

From GTBase Require Export base.
From GraphTheory Require Import minor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X191 vocabulary ***********************************************)

Definition x191_clique_blowup_rel (m t : nat) : rel ('I_m * 'I_t) :=
  fun x y => x.1 != y.1.

Definition x191_clique_blowup (m t : nat) : sgraph :=
  @fg_mk_sgraph ('I_m * 'I_t)%type (@x191_clique_blowup_rel m t).

Definition x191_copy_count (P G : sgraph) : nat :=
  #|[set f : {ffun P -> G} |
      [forall x : P, [forall y : P, (f x == f y) ==> (x == y)]] &&
      [forall x : P, [forall y : P, (x -- y) ==> (f x -- f y)]]]|.

Definition x191_spanning_subgraph_of (F G : sgraph) : Prop :=
  exists emb : F -> G,
    bijective emb /\
    forall x y : F, x -- y -> emb x -- emb y.

Definition x191_dense_H_free_clique_blowup_extremal
    (H G F : sgraph) (m t : nat) : Prop :=
  x191_spanning_subgraph_of F G /\
  ~ minor F H /\
  (forall F' : sgraph,
    x191_spanning_subgraph_of F' G ->
    ~ minor F' H ->
    x191_copy_count (x191_clique_blowup m t) F' <=
      x191_copy_count (x191_clique_blowup m t) F).

Definition x191_delete_edges (F : sgraph) (X : {set {set F}}) : sgraph :=
  @fg_mk_sgraph F (fun x y => (x -- y) && ([set x; y] \notin X)).

Definition x191_subquadratic_deletion_to_partite
    (F : sgraph) (parts delta_num delta_den : nat) : Prop :=
  exists C : nat,
    forall n : nat,
      #|F| = n ->
      exists X : {set {set F}},
        #|X| ^ delta_den <= C * n ^ (2 * delta_den - delta_num) + C /\
        χ([set: x191_delete_edges X]) <= parts.

(** ** X191 statements *****************************************************)

(** Alon-Shikhelman informal conjecture: the [o(n^2)] deletion error term in
    Proposition 1.4 can be improved to [O(n^(2-delta(H)))]. *)
Definition dense_H_free_clique_blowup_subquadratic_error_statement : Prop :=
  forall H : sgraph,
    exists delta_num delta_den C N : nat,
      [/\ 0 < delta_num, delta_num <= delta_den &
        forall (G F : sgraph) (m t : nat),
          N <= #|G| ->
          x191_dense_H_free_clique_blowup_extremal H G F m t ->
          x191_subquadratic_deletion_to_partite F (χ([set: H]) - 1) delta_num delta_den].
