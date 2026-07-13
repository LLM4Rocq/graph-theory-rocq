(** * Extremal.conjectures.X13 -- v2 induced-subgraph rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X13 vocabulary ************************************************)

Definition x13_min_degree_at_least (G : sgraph) (d : nat) : Prop :=
  forall v : G, d <= #|N(v)|.

Definition x13_unbounded (f : nat -> nat) : Prop :=
  forall b : nat, exists d0 : nat, forall d : nat, d0 <= d -> b <= f d.

Definition x13_complete_subgraph_size_at_least (G : sgraph) (m : nat) : Prop :=
  exists S : {set G}, m <= #|S| /\ clique S.

Definition x13_induced_min_degree_at_least
    (G : sgraph) (S : {set G}) (d : nat) : Prop :=
  forall v : induced S, d <= #|N(v)|.

Definition x13_bipartite_induced_min_degree_at_least
    (G : sgraph) (d : nat) : Prop :=
  exists S : {set G},
    S != set0 /\
    bipartite (induced S) /\
    x13_induced_min_degree_at_least S d.

(** ** X13 statements ******************************************************)

(** arXiv:1802.03727, Conjecture 1.4. *)
Definition min_degree_forces_large_clique_or_bipartite_induced_statement : Prop :=
  exists x2 x3 : nat -> nat,
    x13_unbounded x2 /\ x13_unbounded x3 /\
    (forall d : nat, 0 < x2 d /\ 0 < x3 d) /\
    forall (d : nat) (G : sgraph),
      0 < d -> 0 < #|G| ->
      x13_min_degree_at_least G d ->
      x13_complete_subgraph_size_at_least G (x2 d) \/
      x13_bipartite_induced_min_degree_at_least G (x3 d).

(** arXiv:1802.03727, Conjecture 1.6. *)
Definition large_girth_min_degree_bipartite_induced_statement : Prop :=
  exists d0 g0 : nat,
    0 < d0 /\ 0 < g0 /\
    forall G : sgraph,
      0 < #|G| ->
      girth_geq G g0 ->
      x13_min_degree_at_least G d0 ->
      x13_bipartite_induced_min_degree_at_least G 3.
