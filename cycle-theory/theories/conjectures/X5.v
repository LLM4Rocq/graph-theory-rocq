(** * Cycle.conjectures.X5 -- v2 milestone X5, clean simple-cycle rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local simple-graph cycle vocabulary *********************************)

Definition x5_edge_count (G : sgraph) : nat :=
  #|[set p : G * G |
      (p.1 -- p.2) && ((enum_rank p.1) < (enum_rank p.2))%N]|.

Definition x5_vertices_of_seq (G : sgraph) (c : seq G) : {set G} :=
  [set v : G | v \in c].

Definition x5_cycle_family_disjoint
    (G : sgraph) (k : nat) (cs : 'I_k -> seq G) : Prop :=
  forall i j : 'I_k, i != j ->
    [disjoint x5_vertices_of_seq (cs i) & x5_vertices_of_seq (cs j)].

(** ** X5 statements *******************************************************)

(** Erdos Problems #64. *)
Definition min_degree_three_power_two_cycle_statement : Prop :=
  forall G : sgraph,
    0 < #|G| ->
    (forall v : G, 3 <= #|N(v)|) ->
    exists (k : nat) (c : seq G),
      2 <= k /\ ucycle (--) c /\ size c = 2 ^ k.

(** Erdos Problems #577. *)
Definition min_degree_half_disjoint_four_cycles_statement : Prop :=
  forall (k : nat) (G : sgraph),
    #|G| = 4 * k ->
    (forall v : G, 2 * k <= #|N(v)|) ->
    exists cs : 'I_k -> seq G,
      (forall i : 'I_k, ucycle (--) (cs i) /\ size (cs i) = 4) /\
      x5_cycle_family_disjoint cs.

(** Erdos Problems #916. *)
Definition cycle_with_external_three_neighbours_statement : Prop :=
  forall (n : nat) (G : sgraph),
    2 <= n ->
    #|G| = n ->
    x5_edge_count G = 2 * n - 2 ->
    exists (c : seq G) (v : G),
      ucycle (--) c /\
      2 < size c /\
      v \notin c /\
      3 <= #|N(v) :&: x5_vertices_of_seq c|.
