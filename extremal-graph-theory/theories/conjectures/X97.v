(** * Extremal.conjectures.X97 -- v2 maximum-independent-set hitting row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X97 vocabulary ************************************************)

Definition x97_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x != y -> ~~ (x -- y).

Definition x97_maximum_independent_set (G : sgraph) (S : {set G}) : Prop :=
  x97_stable_set S /\
  forall T : {set G}, x97_stable_set T -> #|T| <= #|S|.

Definition x97_hits_all_maximum_independent_sets
    (G : sgraph) (X : {set G}) : Prop :=
  forall S : {set G},
    x97_maximum_independent_set S ->
    ~~ [disjoint X & S].

Definition x97_hitting_number_at_most (G : sgraph) (k : nat) : Prop :=
  exists X : {set G},
    #|X| <= k /\ x97_hits_all_maximum_independent_sets X.

(** ** X97 statements ******************************************************)

(** Studies slice: Bollobas-Erdos-Tuza conjecture that, for every fixed
    positive density of a maximum independent set, the transversal number of
    all maximum independent sets is o(n). *)
Definition bollobas_erdos_tuza_independent_set_hitting_statement : Prop :=
  forall delta_num delta_den eps_num eps_den : nat,
    0 < delta_num ->
    0 < delta_den ->
    0 < eps_num ->
    0 < eps_den ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        delta_den * α([set: G]) >= delta_num * n ->
        exists eta : nat,
          x97_hitting_number_at_most G eta /\
          eps_den * eta <= eps_num * n.
