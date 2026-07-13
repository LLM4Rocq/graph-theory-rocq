(** * Extremal.conjectures.X57 -- v2 sparse strong EH row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X57 vocabulary ************************************************)

Definition x57_anticomplete (G : sgraph) (A B : {set G}) : Prop :=
  [disjoint A & B] /\
  forall a b : G, a \in A -> b \in B -> a -- b -> False.

Definition x57_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

Definition x57_sparse_strong_eh_property (H : sgraph) : Prop :=
  exists eps_num eps_den : nat,
    0 < eps_num /\ eps_num <= eps_den /\
    forall G : sgraph,
      2 <= #|G| ->
      x57_induced_free G H ->
      (exists v : G, eps_num * #|G| <= eps_den * #|N(v)|) \/
      (exists A B : {set G},
        x57_anticomplete A B /\
        eps_num * #|G| <= eps_den * #|A| /\
        eps_num * #|G| <= eps_den * #|B|).

(** ** X57 statements ******************************************************)

(** arXiv:1810.00811, Conjecture 1.5: sparse strong EH-property exactly for
    forests. *)
Definition sparse_strong_eh_iff_forest_statement : Prop :=
  forall H : sgraph,
    x57_sparse_strong_eh_property H <-> is_forest [set: H].
