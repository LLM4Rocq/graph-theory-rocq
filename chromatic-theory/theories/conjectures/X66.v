(** * Chromatic.conjectures.X66 -- v2 good trees disjoint-union row *)

From GTBase Require Export base.
From Chromatic.conjectures Require Import U8 X3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X66 vocabulary ************************************************)

Definition x66_disjoint_union_rel (G H : sgraph) : rel (G + H) :=
  fun x y =>
    match x, y with
    | inl a, inl b => a -- b
    | inr a, inr b => a -- b
    | _, _ => false
    end.

Lemma x66_disjoint_union_sym (G H : sgraph) :
  symmetric (@x66_disjoint_union_rel G H).
Proof. by move=> [a|a] [b|b] //=; rewrite sgP. Qed.

Lemma x66_disjoint_union_irrefl (G H : sgraph) :
  irreflexive (@x66_disjoint_union_rel G H).
Proof. by move=> [a|a] //=; rewrite sg_irrefl. Qed.

Definition x66_disjoint_union (G H : sgraph) : sgraph :=
  SGraph (@x66_disjoint_union_sym G H) (@x66_disjoint_union_irrefl G H).

Definition x66_good (H : sgraph) : Prop :=
  x3_polynomially_chi_bounded (fun G : sgraph => ~ has_induced H G).

(** ** X66 statements ******************************************************)

(** arXiv:2202.09118, open problem: if two trees are good, then their
    disjoint union is good. *)
Definition good_trees_disjoint_union_good_statement : Prop :=
  forall H1 H2 : sgraph,
    is_tree [set: H1] ->
    is_tree [set: H2] ->
    x66_good H1 ->
    x66_good H2 ->
    x66_good (x66_disjoint_union H1 H2).
