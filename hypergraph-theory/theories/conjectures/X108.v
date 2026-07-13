(** * Hypergraph.conjectures.X108 -- v2 3-uniform Burr-Erdos row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X108 vocabulary ***********************************************)

Definition x108_uniform (T : finType) (E : {set {set T}}) (r : nat) : Prop :=
  forall e : {set T}, e \in E -> #|e| = r.

Definition x108_degree_in
    (T : finType) (E : {set {set T}}) (W : {set T}) (v : T) : nat :=
  #|[set e in E | (v \in e) && (e \subset W)]|.

Definition x108_d_degenerate (T : finType) (E : {set {set T}}) (d : nat) : Prop :=
  forall W : {set T},
    W != set0 ->
    exists v : T, v \in W /\ x108_degree_in E W v <= d.

Definition x108_image_edge
    (T U : finType) (f : T -> U) (e : {set T}) : {set U} :=
  [set y : U | [exists x : T, (x \in e) && (y == f x)]].

Definition x108_monochromatic_copy
    (T : finType) (E : {set {set T}}) (N : nat)
    (col : {set 'I_N} -> bool) : Prop :=
  exists (colour : bool) (f : T -> 'I_N),
    injective f /\
    forall e : {set T},
      e \in E -> col (x108_image_edge f e) = colour.

Definition x108_two_colour_ramsey_at_most
    (T : finType) (E : {set {set T}}) (N : nat) : Prop :=
  forall col : {set 'I_N} -> bool, x108_monochromatic_copy E col.

(** ** X108 statements *****************************************************)

(** Studies slice: Burr-Erdos conjecture for 3-uniform hypergraphs: bounded
    degeneracy should force linear two-colour Ramsey number. *)
Definition three_uniform_degenerate_hypergraph_ramsey_linear_statement : Prop :=
  forall d : nat,
    exists c : nat,
      forall (T : finType) (E : {set {set T}}),
        x108_uniform E 3 ->
        x108_d_degenerate E d ->
        x108_two_colour_ramsey_at_most E (c * #|T|).
