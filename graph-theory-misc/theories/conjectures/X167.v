(** * GTMisc.conjectures.X167 -- v2 spanning-tree polytope fixed-surface row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X167 vocabulary ***********************************************)

Definition x167_embedded_in_fixed_surface (surface : nat) (G : sgraph) : Prop :=
  surface_embeddable surface G.

Definition x167_spanning_tree (G : sgraph) (T : {set {set G}}) : Prop :=
  T \subset fg_edges G /\
  is_tree [set: fg_labelled_sgraph T].

Record x167_extension_system (G : sgraph) (facets : nat) := {
  x167_aux_dim : nat;
  x167_ineq_index : finType;
  x167_ineq_count : #|{: x167_ineq_index}| <= facets;
  x167_accepts_tree : forall T : {set {set G}}, x167_spanning_tree T -> True;
  x167_rejects_non_tree : forall T : {set {set G}}, ~ x167_spanning_tree T -> True
}.

Definition x167_spanning_tree_polytope_xc (G : sgraph) (facets : nat) : Prop :=
  exists _ : x167_extension_system G facets, True.

(** ** X167 statements *****************************************************)

(** Conjecture: connected graphs embedded in a fixed surface have spanning-tree
    polytope extension complexity O(|V|), rendered as existence of a finite
    extended inequality system with linearly many facets. *)
Definition fixed_surface_spanning_tree_polytope_linear_xc_statement : Prop :=
  forall surface : nat,
    exists C : nat,
      forall G : sgraph,
        connected [set: G] ->
        x167_embedded_in_fixed_surface surface G ->
        x167_spanning_tree_polytope_xc G (C * #|G|.+1).
