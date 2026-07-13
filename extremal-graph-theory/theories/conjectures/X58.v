(** * Extremal.conjectures.X58 -- v2 epsilon-bounded pure pair row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X58 vocabulary ************************************************)

Definition x58_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall a b : G, a \in A -> b \in B -> a -- b -> False.

Definition x58_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x58_epsilon_bounded
    (G : sgraph) (eps_num eps_den : nat) : Prop :=
  eps_den * Delta G < eps_num * #|G|.

(** ** X58 statements ******************************************************)

(** arXiv:1810.00058, Conjecture 1.4: epsilon-bounded H-free graphs contain
    a linear anticomplete pair. *)
Definition epsilon_bounded_h_free_anticomplete_pair_statement : Prop :=
  forall H : sgraph,
    exists eps_num eps_den : nat,
      0 < eps_num /\ eps_num <= eps_den /\
      forall G : sgraph,
        1 < #|G| ->
        x58_induced_free G H ->
        x58_epsilon_bounded G eps_num eps_den ->
        exists A B : {set G},
          x58_anticomplete A B /\
          eps_num ^ eps_den * #|G| ^ eps_num <= eps_den ^ eps_den * #|A| ^ eps_den /\
          eps_num * #|G| <= eps_den * #|B|.
