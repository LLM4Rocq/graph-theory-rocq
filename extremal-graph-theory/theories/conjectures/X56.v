(** * Extremal.conjectures.X56 -- v2 C8 Erdos-Hajnal row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X56 vocabulary ************************************************)

Definition x56_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> x -- y -> False.

Definition x56_homogeneous_set (G : sgraph) (S : {set G}) : Prop :=
  clique S \/ x56_stable_set S.

Definition x56_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma x56_complement_sym (G : sgraph) : symmetric (@x56_complement_rel G).
Proof. by move=> x y; rewrite /x56_complement_rel eq_sym sgP. Qed.

Lemma x56_complement_irrefl (G : sgraph) : irreflexive (@x56_complement_rel G).
Proof. by move=> x; rewrite /x56_complement_rel eqxx. Qed.

Definition x56_complement (G : sgraph) : sgraph :=
  SGraph (@x56_complement_sym G) (@x56_complement_irrefl G).

Definition x56_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

(** ** X56 statements ******************************************************)

(** arXiv:2102.04994, the Erdos-Hajnal question for {C8, complement C8}. *)
Definition c8_complement_c8_erdos_hajnal_statement : Prop :=
  exists c : nat,
    0 < c /\
    forall G : sgraph,
      0 < #|G| ->
      x56_induced_free G (cycle_graph 8) ->
      x56_induced_free G (x56_complement (cycle_graph 8)) ->
      exists S : {set G},
        x56_homogeneous_set S /\
        #|G| <= (#|S|) ^ c.
