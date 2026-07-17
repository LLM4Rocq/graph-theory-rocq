(** * GTMisc.conjectures.X144 -- v2 pure pairs in perfect graphs row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X144 vocabulary ***********************************************)

Definition x144_perfect_graph (G : sgraph) : Prop :=
  forall S : {set G}, χ([set: induced S]) = ω([set: induced S]).

Definition x144_complete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> a -- b.

Definition x144_anticomplete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> ~~ (a -- b).

Definition x144_pure_pair (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  A != set0 /\
  B != set0 /\
  (x144_complete_between A B \/ x144_anticomplete_between A B).

(** ** X144 statements *****************************************************)

(** Fox: every sufficiently large n-vertex perfect graph has a pure pair whose
    two sides both have size at least n^(1-o(1)).  The asymptotic lower bound is
    encoded in the standard rational-epsilon form: for every 0<e1/e2<1, for all
    sufficiently large n, both sizes are at least n^(1-e1/e2). *)
Definition fox_pure_pair_perfect_graphs_statement : Prop :=
  forall e1 e2 : nat,
    0 < e1 ->
    e1 < e2 ->
    exists N : nat,
      forall (n : nat) (G : sgraph),
        N <= n ->
        #|G| = n ->
        x144_perfect_graph G ->
        exists A B : {set G},
          x144_pure_pair A B /\
          n ^ (e2 - e1) <= #|A| ^ e2 /\
          n ^ (e2 - e1) <= #|B| ^ e2.

