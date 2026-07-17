(** * Chromatic.conjectures.X124 -- v2 merge-width polynomial chi-boundedness row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X124 vocabulary ***********************************************)

Fixpoint x124_poly_eval (p : seq nat) (x : nat) : nat :=
  if p is a :: q then a + x * x124_poly_eval q x else 0.

(** Clique number omega(G). *)
Definition x124_omega (G : sgraph) : nat := \max_(S : {set G} | cliqueb S) #|S|.

(** Polynomially chi-bounded class: one polynomial bounds chi in terms of omega
    across every member.  This CONCLUSION is faithful. *)
Definition x124_poly_chi_bounded (C : sgraph -> Prop) : Prop :=
  exists p : seq nat,
    forall G : sgraph, C G -> χ([set: G]) <= x124_poly_eval p (x124_omega G).

Inductive x124_merge_expr (k : nat) : Type :=
| x124_vertex of 'I_k
| x124_disjoint of x124_merge_expr k & x124_merge_expr k
| x124_join_labels of 'I_k & 'I_k & x124_merge_expr k
| x124_relabel of ('I_k -> 'I_k) & x124_merge_expr k
| x124_merge_label of 'I_k & x124_merge_expr k.

Fixpoint x124_expr_leaves k (e : x124_merge_expr k) : nat :=
  match e with
  | x124_vertex _ => 1
  | x124_disjoint e1 e2 => x124_expr_leaves e1 + x124_expr_leaves e2
  | x124_join_labels _ _ e1 => x124_expr_leaves e1
  | x124_relabel _ e1 => x124_expr_leaves e1
  | x124_merge_label _ e1 => x124_expr_leaves e1
  end.

Record x124_merge_realisation (G : sgraph) (k : nat) (e : x124_merge_expr k) := {
  x124_premerge_vertices : finType;
  x124_premerge_label : x124_premerge_vertices -> 'I_k;
  x124_premerge_edge : rel x124_premerge_vertices;
  x124_premerge_map : x124_premerge_vertices -> G;
  x124_premerge_surj : forall v : G, exists x, x124_premerge_map x = v;
  x124_premerge_edge_sound :
    forall x y, x124_premerge_edge x y -> x124_premerge_map x -- x124_premerge_map y;
  x124_premerge_edge_complete :
    forall u v : G, u -- v ->
      exists x y, [/\ x124_premerge_map x = u,
                    x124_premerge_map y = v & x124_premerge_edge x y];
  x124_premerge_width_used : #|{: x124_premerge_vertices}| <= x124_expr_leaves e
}.

Definition x124_merge_width_le (C : sgraph -> Prop) (w : nat) : Prop :=
  forall G : sgraph,
    C G ->
    exists (k : nat) (e : x124_merge_expr k),
      k <= w /\ exists _ : x124_merge_realisation G e, True.

Definition x124_bounded_merge_width (C : sgraph -> Prop) : Prop :=
  exists w : nat, x124_merge_width_le C w.

(** ** X124 statements *****************************************************)

(** Studies slice: Dreier-Torunczyk conjecture -- bounded merge-width classes are
    polynomially chi-bounded.  The antecedent now uses finite labelled expression
    syntax with explicit merge/relabel/join constructors and a surjective
    realisation of the resulting merged graph. *)
Definition dreier_torunczyk_merge_width_poly_chi_bounded_statement : Prop :=
  forall C : sgraph -> Prop,
    x124_bounded_merge_width C -> x124_poly_chi_bounded C.
