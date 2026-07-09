(** * Minor.conjectures.X5 -- v2 milestone X5, clean minor-structural rows *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** X5 statements *******************************************************)

(** arXiv:1907.12999. *)
Definition hadwiger_independence_minor_statement : Prop :=
  forall (t n : nat) (G : sgraph),
    0 < t -> #|G| = n -> ~ minor G 'K_(t.+1) ->
    n <= t * α(G).

(** arXiv:2204.10119, Question 1.5. *)
Definition six_regular_has_k6_minor_statement : Prop :=
  forall G : sgraph,
    0 < #|G| -> regular G 6 -> minor G 'K_6.

(** arXiv:2204.10119, Question 1.6. *)
Definition min_degree_six_max_degree_eight_k6_minor_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    (forall v : G, 6 <= #|N(v)|) ->
    Delta G <= 8 ->
    minor G 'K_6.

(** arXiv:2204.10119, bipartite "six replaced by five" variant. *)
Definition bipartite_min_degree_five_k6_minor_statement : Prop :=
  forall G : sgraph,
    0 < #|G| -> bipartite G ->
    (forall v : G, 5 <= #|N(v)|) ->
    minor G 'K_6.

(** arXiv:2204.10119, average-degree K5 variant. *)
Definition bipartite_average_degree_five_max_six_k5_minor_statement : Prop :=
  forall G : sgraph,
    0 < #|G| -> bipartite G ->
    average_degree_geq G 5 1 ->
    Delta G <= 6 ->
    minor G 'K_5.

(** Studies slice: clique-minor conjecture for bounded independence. *)
Definition bounded_independence_clique_minor_statement : Prop :=
  forall (r n : nat) (G : sgraph),
    0 < r -> #|G| = n -> α(G) <= r ->
    minor G 'K_(ceil_div n r).
