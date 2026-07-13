(** * GTMisc.conjectures.X87 -- v2 ordered-graph speed-gap row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X87 vocabulary ************************************************)

Definition x87_edge_fun (n : nat) := {ffun 'I_n * 'I_n -> bool}.

Definition x87_edge (n : nat) (E : x87_edge_fun n) (i j : 'I_n) : bool :=
  E (i, j).

Definition x87_sgraph_edge (n : nat) (E : x87_edge_fun n) : bool :=
  [forall i : 'I_n, ~~ x87_edge E i i] &&
  [forall i : 'I_n, [forall j : 'I_n, x87_edge E i j == x87_edge E j i]].

Definition x87_ordered_class := forall n : nat, x87_edge_fun n -> bool.

Definition x87_order_preserving (m n : nat) (f : 'I_m -> 'I_n) : Prop :=
  forall i j : 'I_m, (i < j)%N -> (f i < f j)%N.

Definition x87_induced_edge
    (m n : nat) (E : x87_edge_fun n) (f : 'I_m -> 'I_n)
    : x87_edge_fun m :=
  [ffun p : 'I_m * 'I_m => x87_edge E (f p.1) (f p.2)].

Definition x87_hereditary (C : x87_ordered_class) : Prop :=
  forall (m n : nat) (E : x87_edge_fun n) (f : 'I_m -> 'I_n),
    injective f ->
    x87_order_preserving f ->
    C n E ->
    C m (x87_induced_edge E f).

Definition x87_speed (C : x87_ordered_class) (n : nat) : nat :=
  #|[set E : x87_edge_fun n | x87_sgraph_edge E && C n E]|.

Definition x87_is_hereditary_ordered_graph_speed (speed : nat -> nat) : Prop :=
  exists C : x87_ordered_class,
    x87_hereditary C /\ forall n : nat, speed n = x87_speed C n.

Definition x87_at_most_exponential (speed : nat -> nat) : Prop :=
  exists c N : nat, forall n : nat, N <= n -> speed n <= 2 ^ (c * n).

Definition x87_at_least_half_factorial (speed : nat -> nat) : Prop :=
  forall q : nat,
    3 <= q ->
    exists N : nat,
      forall n : nat,
        N <= n ->
        n ^ ((n * (q - 2)) %/ (2 * q)) <= speed n.

(** ** X87 statements ******************************************************)

(** Studies slice: Balogh-Bollobas-Morris speed-gap conjecture for hereditary
    classes of totally ordered graphs.  Ordered graphs are represented on the
    canonical ordered vertex set 'I_n, so the speed counts ordered isomorphism
    types by their unique increasing relabelling. *)
Definition hereditary_ordered_graph_speed_gap_statement : Prop :=
  forall speed : nat -> nat,
    x87_is_hereditary_ordered_graph_speed speed ->
    x87_at_most_exponential speed \/ x87_at_least_half_factorial speed.
