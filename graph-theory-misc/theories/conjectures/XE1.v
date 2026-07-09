(** * GTMisc.conjectures.XE1 -- Erdős open clean rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition xe1_coprime_adj (n : nat) (x y : 'I_n) : bool :=
  (x != y) && coprime (val x).+1 (val y).+1.

Definition xe1_rel_cycle (V : finType) (r : rel V) (c : seq V) : Prop :=
  ucycle r c /\ 2 < size c.

Definition xe1_all_small_odd_coprime_cycles (n : nat) (A : {set 'I_n}) : Prop :=
  forall ell : nat,
    odd ell -> 3 <= ell -> ell <= n %/ 3 + 1 ->
    exists c : seq 'I_n,
      xe1_rel_cycle (@xe1_coprime_adj n) c /\
      size c = ell /\
      forall x : 'I_n, x \in c -> x \in A.

Definition xe1_complete_tripartite_1_l_l (n ell : nat) (A : {set 'I_n}) : Prop :=
  exists X Y Z : {set 'I_n},
    X \subset A /\
    Y \subset A /\
    Z \subset A /\
    [disjoint X & Y] /\
    [disjoint X :|: Y & Z] /\
    #|X| = 1 /\
    #|Y| = ell /\
    #|Z| = ell /\
    forall x y : 'I_n,
      ((x \in X) && (y \in Y :|: Z) ||
       (x \in Y) && (y \in X :|: Z) ||
       (x \in Z) && (y \in X :|: Y)) ->
      xe1_coprime_adj x y.

(** Erdős Problems #883. *)
Definition erdos_883_statement : Prop :=
  (forall n : nat, forall A : {set 'I_n},
      #|A| > n %/ 2 + n %/ 3 - n %/ 6 ->
      xe1_all_small_odd_coprime_cycles A) /\
  (forall ell : nat, 1 <= ell ->
      exists N : nat,
        forall n : nat, N <= n ->
        forall A : {set 'I_n},
          #|A| > n %/ 2 + n %/ 3 - n %/ 6 ->
          xe1_complete_tripartite_1_l_l ell A).
