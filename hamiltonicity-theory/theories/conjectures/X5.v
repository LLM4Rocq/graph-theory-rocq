(** * Hamilton.conjectures.X5 -- v2 milestone X5, clean TSP-walk row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local Hamiltonicity vocabulary **************************************)

Definition x5_tsp_walk (G : sgraph) (w : seq G) : Prop :=
  exists x p,
    [/\ w = x :: p,
        path (--) x p,
        last x p = x
      & forall v : G, v \in w].

Definition x5_tsp_walk_length (G : sgraph) (w : seq G) : nat :=
  if w is _ :: p then size p else 0.

Definition x5_degree_two_count (G : sgraph) : nat :=
  #|[set v : G | #|N(v)| == 2]|.

(** ** X5 statements *******************************************************)

(** arXiv:1608.07568. *)
Definition subcubic_two_connected_tsp_walk_bound_statement : Prop :=
  forall (n : nat) (G : sgraph),
    #|G| = n ->
    k_connected G 2 ->
    Delta G <= 3 ->
    exists w : seq G,
      x5_tsp_walk w /\
      4 * x5_tsp_walk_length w <= 5 * n + x5_degree_two_count G - 4.
