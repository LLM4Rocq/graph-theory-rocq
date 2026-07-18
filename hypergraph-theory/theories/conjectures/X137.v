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

(** Erdos-Rado sunflower conjecture: for every petal count [k] there is a
    constant [C(k)] such that every r-uniform family with more than [C^r]
    members contains a k-sunflower.  The constant depends on the PETAL COUNT
    and the exponent is the SET SIZE r; the opposite binder assignment
    (C depending on r, exponent k) is a consequence of the 1960 Erdos-Rado
    sunflower LEMMA and carries none of the open content (audit fix
    2026-07-18, meta/BLOCKED_RETARGETING_AUDIT.md, fresh-rows section). *)
Definition erdos_rado_sunflower_statement : Prop :=
  forall k : nat,
    2 <= k ->
    exists C : nat,
      forall (r : nat) (T : finType) (F : {set {set T}}),
        x137_uniform F r ->
        C ^ r < #|F| ->
        exists petals : seq {set T},
          [/\ size petals = k,
              uniq petals,
              (forall A : {set T}, A \in petals -> A \in F) &
              x137_sunflower petals].

