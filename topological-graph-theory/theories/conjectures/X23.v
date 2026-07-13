(** * Topological.conjectures.X23 -- v2 planar colouring layout rows *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X23 vocabulary ************************************************)

Definition x23_genuine_path (G : sgraph) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q => uniq p /\ path (--) x q
  end.

Definition x23_nonrepetitive_colouring
    (G : sgraph) (k : nat) (col : G -> 'I_k) : Prop :=
  forall (p : seq G) (h : nat),
    x23_genuine_path p ->
    size p = 2 * h ->
    0 < h ->
    map col (take h p) != map col (take h (drop h p)).

Definition x23_edge_colour_rel
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : rel G :=
  fun x y => (x -- y) && (col [set x; y] == i).

Lemma x23_edge_colour_sym
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  symmetric (x23_edge_colour_rel col i).
Proof.
by move=> x y; rewrite /x23_edge_colour_rel sg_sym setUC.
Qed.

Lemma x23_edge_colour_irrefl
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) :
  irreflexive (x23_edge_colour_rel col i).
Proof. by move=> x; rewrite /x23_edge_colour_rel sg_irrefl. Qed.

Definition x23_colour_graph
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : sgraph :=
  SGraph (x23_edge_colour_sym col i) (x23_edge_colour_irrefl col i).

Definition x23_linear_forest_colour
    (G : sgraph) (q : nat) (col : {set G} -> 'I_q) (i : 'I_q) : Prop :=
  is_forest [set: x23_colour_graph col i] /\
  Delta (x23_colour_graph col i) <= 2.

Definition x23_linear_arboricity_at_most (G : sgraph) (q : nat) : Prop :=
  exists col : {set G} -> 'I_q,
    forall i : 'I_q, x23_linear_forest_colour col i.

Definition x23_linear_arboricity (G : sgraph) (q : nat) : Prop :=
  x23_linear_arboricity_at_most G q /\
  forall q' : nat, x23_linear_arboricity_at_most G q' -> q <= q'.

(** ** X23 statements ******************************************************)

(** Studies slice: Alon-Grytczuk-Haluszczak-Riordan nonrepetitive colouring. *)
Definition planar_bounded_nonrepetitive_chromatic_statement : Prop :=
  exists k : nat,
    0 < k /\
    forall G : sgraph,
      wagner_planar G ->
      exists col : G -> 'I_k, x23_nonrepetitive_colouring col.

(** Studies slice: planar linear arboricity conjecture. *)
Definition planar_linear_arboricity_statement : Prop :=
  forall G : sgraph,
    wagner_planar G ->
    5 <= Delta G ->
    x23_linear_arboricity G (ceil_div (Delta G) 2).
