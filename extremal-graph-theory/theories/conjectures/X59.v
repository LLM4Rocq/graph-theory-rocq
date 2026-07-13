(** * Extremal.conjectures.X59 -- v2 C4-free dense subgraph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X59 vocabulary ************************************************)

Fixpoint x59_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x59_poly_eval q x else 0.

Definition x59_subgraph_of (H G : sgraph) : Prop :=
  exists f : H -> G,
    injective f /\
    forall x y : H, x -- y -> f x -- f y.

Definition x59_has_cycle_length (G : sgraph) (n : nat) : Prop :=
  exists c : seq G, ucycle (--) c /\ size c = n.

(** ** X59 statements ******************************************************)

(** arXiv:2307.08361, polynomial average-degree threshold for C4-free
    subgraphs. *)
Definition c4_free_subgraph_polynomial_average_degree_statement : Prop :=
  exists p : seq nat,
    forall (k : nat) (G : sgraph),
      average_degree_geq G (x59_poly_eval p k) 1 ->
      exists H : sgraph,
        x59_subgraph_of H G /\
        ~ x59_has_cycle_length H 4 /\
        average_degree_geq H k 1.
