(** * Hypergraph.conjectures.X137 -- v2 Erdos-Rado sunflower row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X137 vocabulary ***********************************************)

Definition x137_uniform (T : finType) (F : {set {set T}}) (r : nat) : Prop :=
  forall A : {set T}, A \in F -> #|A| = r.

Definition x137_sunflower (T : finType) (petals : seq {set T}) : Prop :=
  exists core : {set T},
    forall A B : {set T},
      A \in petals -> B \in petals -> A != B -> A :&: B = core.

(** ** X137 statements *****************************************************)

(** Erdos-Rado sunflower conjecture: for every uniformity [r] there is a
    constant [C(r)] such that every r-uniform family with more than [C^k] members
    contains a k-sunflower. *)
Definition erdos_rado_sunflower_statement : Prop :=
  forall r : nat,
    exists C : nat,
      forall (k : nat) (T : finType) (F : {set {set T}}),
        2 <= k ->
        x137_uniform F r ->
        C ^ k < #|F| ->
        exists petals : seq {set T},
          [/\ size petals = k,
              uniq petals,
              (forall A : {set T}, A \in petals -> A \in F) &
              x137_sunflower petals].

