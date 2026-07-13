(** * Packing.conjectures.X18 -- v2 fair representation continuation rows *)

From GTBase Require Export base.
From Packing.conjectures Require Import X15.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X18 vocabulary ************************************************)

Definition x18_path_rel (n : nat) : rel 'I_n :=
  fun i j => (i != j) && (((val i).+1 == val j) || ((val j).+1 == val i)).

Lemma x18_path_sym (n : nat) : symmetric (@x18_path_rel n).
Proof.
by move=> i j; rewrite /x18_path_rel eq_sym orbC.
Qed.

Lemma x18_path_irrefl (n : nat) : irreflexive (@x18_path_rel n).
Proof. by move=> i; rewrite /x18_path_rel eqxx. Qed.

Definition x18_path_graph (n : nat) : sgraph :=
  SGraph (@x18_path_sym n) (@x18_path_irrefl n).

Definition x18_vertex_partition
    (G : sgraph) (m : nat) (V : 'I_m -> {set G}) : Prop :=
  (forall v : G, [exists i : 'I_m, v \in V i]) /\
  forall i j : 'I_m, i != j -> [disjoint V i & V j].

Definition x18_independent_set (G : sgraph) (S : {set G}) : Prop :=
  forall u v : G, u \in S -> v \in S -> u -- v -> False.

Definition x18_perfect_matching (G : sgraph) (M : {set {set G}}) : Prop :=
  x15_matching M /\
  forall v : G, #|[set e in M | v \in e]| = 1.

(** ** X18 statements ******************************************************)

(** arXiv:1611.03196, Conjecture 1.6. *)
Definition path_partition_independent_set_balance_statement : Prop :=
  forall (n m : nat) (V : 'I_m -> {set x18_path_graph n}),
    x18_vertex_partition V ->
    exists (S : {set x18_path_graph n}) (b : 'I_m -> nat),
      x18_independent_set S /\
      (forall i : 'I_m, 2 * (#|S :&: V i| + b i) >= #|V i|)%N /\
      (2 * \sum_(i : 'I_m) b i <= m)%N /\
      forall i : 'I_m, b i <= 1.

(** arXiv:1611.03196, Conjecture 1.9. *)
Definition knn_fair_perfect_matching_statement : Prop :=
  forall (n m : nat) (E : 'I_m -> {set {set KB n n}}) (j : 'I_m),
    0 < n ->
    x15_edge_partition E ->
    exists F : {set {set KB n n}},
      x18_perfect_matching F /\
      (forall i : 'I_m, i != j -> (#|E i| %/ n <= #|F :&: E i|)%N) /\
      (#|E j| %/ n - 1 <= #|F :&: E j|)%N.

(** Studies slice: Brualdi-Stein special case. *)
Definition brualdi_stein_partial_transversal_statement : Prop :=
  forall (n : nat) (E : 'I_n -> {set {set KB n n}}),
    0 < n ->
    x15_edge_partition E ->
    (forall i : 'I_n, #|E i| = n) ->
    exists M : {set {set KB n n}},
      x15_matching M /\
      (n.-1 <= #|M|)%N /\
      forall i : 'I_n, #|M :&: E i| <= 1.
