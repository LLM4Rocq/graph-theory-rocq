(** * Extremal.conjectures.X30 -- v2 triangle-free induced-bipartite row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X30 vocabulary ************************************************)

Definition x30_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition x30_induced_min_degree_log_at_least
    (G : sgraph) (S : {set G}) (cnum cden d : nat) : Prop :=
  forall v : induced S, cden * #|N(v)| >= cnum * trunc_log 2 d.

Definition x30_bipartite_induced_log_min_degree
    (G : sgraph) (cnum cden d : nat) : Prop :=
  exists S : {set G},
    S != set0 /\
    bipartite (induced S) /\
    x30_induced_min_degree_log_at_least S cnum cden d.

(** ** X30 statements ******************************************************)

(** arXiv:1802.03727, Conjecture 1.5 logarithmic bipartite induced subgraph. *)
Definition triangle_free_min_degree_log_bipartite_induced_statement : Prop :=
  exists cnum cden : nat,
    0 < cnum /\ 0 < cden /\
    forall (d : nat) (G : sgraph),
      2 <= d ->
      0 < #|G| ->
      triangle_free G ->
      x30_min_degree_at_least G d ->
      x30_bipartite_induced_log_min_degree G cnum cden d.
