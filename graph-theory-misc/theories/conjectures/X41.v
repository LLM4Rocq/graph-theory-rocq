(** * GTMisc.conjectures.X41 -- v2 sparse pure-pair row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X41 vocabulary ************************************************)

Definition x41_induced_H_free (H G : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x41_complete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> a -- b.

Definition x41_anticomplete_between (G : sgraph) (A B : {set G}) : Prop :=
  forall a b : G, a \in A -> b \in B -> ~~ (a -- b).

Definition x41_pure_pair (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  A != set0 /\
  B != set0 /\
  (x41_complete_between A B \/ x41_anticomplete_between A B).

(** ** X41 statements ******************************************************)

(** Studies slice: Conlon-Fox-Sudakov sparse linear pure-pair conjecture. *)
Definition sparse_linear_pure_pair_statement : Prop :=
  forall H : sgraph, exists eps_num eps_den : nat,
    0 < eps_num /\
    eps_num <= eps_den /\
    forall G : sgraph,
      1 < #|G| ->
      x41_induced_H_free H G ->
      exists A B : {set G},
        x41_pure_pair A B /\
        eps_den ^ eps_den * #|A| ^ eps_den >= eps_num ^ eps_den * #|G| ^ eps_num /\
        eps_den * #|B| >= eps_num * #|G|.
