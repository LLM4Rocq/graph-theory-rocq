(** * Minor.conjectures.X42 -- v2 bounded treewidth forbidden-subgraph row *)

From GTBase Require Export base.
From Minor.conjectures Require Import X27.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X42 vocabulary ************************************************)

Definition x42_diamond_rel (u v : bool + bool) : bool :=
  match u, v with
  | inl a, inl b => a != b
  | inl _, inr _ => true
  | inr _, inl _ => true
  | inr _, inr _ => false
  end.

Lemma x42_diamond_sym : symmetric x42_diamond_rel.
Proof. by move=> [a|a] [b|b] //=; rewrite eq_sym. Qed.

Lemma x42_diamond_irrefl : irreflexive x42_diamond_rel.
Proof. by move=> [a|a] //=; rewrite eqxx. Qed.

Definition x42_diamond : sgraph := SGraph x42_diamond_sym x42_diamond_irrefl.

Definition x42_induced_free (G H : sgraph) : Prop :=
  forall S : {set G}, ~ inhabited (induced S ≃ H).

(** ** X42 statements ******************************************************)

(** arXiv:2001.01607, bounded treewidth for even-hole/K4/diamond-free graphs. *)
Definition even_hole_k4_diamond_free_bounded_treewidth_statement : Prop :=
  exists c : nat,
    forall G : sgraph,
      x27_even_hole_free G ->
      x42_induced_free G 'K_4 ->
      x42_induced_free G x42_diamond ->
      x27_treewidth_at_most G c.
