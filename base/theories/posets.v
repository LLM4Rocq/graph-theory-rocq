(** * GTBase.posets -- finite posets, cover graphs, and order dimension *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record finite_poset := FinitePoset {
  poset_sort :> finType;
  poset_le : rel poset_sort;
  poset_refl : reflexive poset_le;
  poset_antisym : antisymmetric poset_le;
  poset_trans : transitive poset_le
}.
Arguments poset_le _ _ _ : clear implicits.

Definition poset_lt (P : finite_poset) (x y : P) : bool :=
  poset_le P x y && (x != y).

Definition poset_chain (P : finite_poset) (A : {set P}) : Prop :=
  forall x y : P, x \in A -> y \in A -> poset_le P x y || poset_le P y x.

Definition poset_height_at_most (P : finite_poset) (h : nat) : Prop :=
  forall A : {set P}, poset_chain A -> #|A| <= h.

Definition poset_cover_rel (P : finite_poset) (x y : P) : bool :=
  [&& poset_le P x y, x != y &
      [forall z : P,
        (poset_le P x z && poset_le P z y) ==> ((z == x) || (z == y))]].
Arguments poset_cover_rel _ _ _ : clear implicits.

Definition poset_cover_adj (P : finite_poset) : rel P :=
  fun x y => (x != y) && (poset_cover_rel P x y || poset_cover_rel P y x).
Arguments poset_cover_adj _ _ _ : clear implicits.

Lemma poset_cover_adj_sym (P : finite_poset) : symmetric (poset_cover_adj P).
Proof. by move=> x y; rewrite /poset_cover_adj eq_sym orbC. Qed.

Lemma poset_cover_adj_irrefl (P : finite_poset) : irreflexive (poset_cover_adj P).
Proof. by move=> x; rewrite /poset_cover_adj eqxx. Qed.

Definition poset_cover_graph (P : finite_poset) : sgraph :=
  SGraph (@poset_cover_adj_sym P) (@poset_cover_adj_irrefl P).

(** A realizer is a family of linear extensions whose intersection is exactly
    the poset order. *)
Definition is_linear_order (X : finType) (l : rel X) : Prop :=
  [/\ reflexive l, antisymmetric l, transitive l & total l].

Definition order_extends (X : finType) (le l : rel X) : Prop :=
  forall x y : X, le x y -> l x y.

Definition realizer (X : finType) (le : rel X) (ls : seq (rel X)) : Prop :=
  (forall i : nat, i < size ls ->
     is_linear_order (nth (fun _ _ => false) ls i) /\
     order_extends le (nth (fun _ _ => false) ls i)) /\
  (forall x y : X, le x y <->
     (forall i : nat, i < size ls -> (nth (fun _ _ => false) ls i) x y)).

Definition poset_dimension_at_most (P : finite_poset) (d : nat) : Prop :=
  exists ls : seq (rel P), size ls <= d /\ realizer (poset_le P) ls.

(** A concrete one-point poset witness. *)
Definition unit_poset_le : rel unit := fun _ _ => true.

Lemma unit_poset_le_refl : reflexive unit_poset_le.
Proof. by []. Qed.

Lemma unit_poset_le_antisym : antisymmetric unit_poset_le.
Proof. by move=> [] []. Qed.

Lemma unit_poset_le_trans : transitive unit_poset_le.
Proof. by []. Qed.

Definition unit_poset : finite_poset :=
  FinitePoset unit_poset_le_refl unit_poset_le_antisym unit_poset_le_trans.
