(** * Extremal.conjectures.X85 -- v2 average-degree cycle-count row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X84.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X85 vocabulary ************************************************)

Definition x85_average_degree_at_most (G : sgraph) (d : nat) : Prop :=
  \sum_(v : G) #|N(v)| <= d * #|G|.

Definition x85_average_degree_exact (G : sgraph) (d : nat) : Prop :=
  average_degree_geq G d 1 /\ x85_average_degree_at_most G d.

Definition x85_log_corrected_exponential_bound
    (c den n d cycles : nat) : Prop :=
  (den ^ n) * cycles <= (d + c * trunc_log 2 d) ^ n.

(** ** X85 statements ******************************************************)

(** Studies slice: Arman-Tsaturian conjecture on the number of cycles in a
    graph of average degree d.  The O(log d / d) multiplicative error is encoded
    as a logarithmic additive correction inside the nth power; [den] is the
    fixed denominator representing the exponential constant in the asymptotic
    envelope. *)
Definition arman_tsaturian_average_degree_cycle_count_statement : Prop :=
  exists c den N : nat,
    [/\ 0 < c, 1 < den
      & forall (n d : nat) (G : sgraph),
          N <= d ->
          #|G| = n ->
          x85_average_degree_exact G d ->
          x85_log_corrected_exponential_bound
            c den n d (x84_cycle_count G)].
