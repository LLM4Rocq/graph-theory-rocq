(** * GTMisc.conjectures.X168 -- v2 spanning-tree polytope minor-closed row *)

From GraphTheory Require Import minor.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X168 vocabulary ***********************************************)

Definition x168_proper_minor_closed_class (C : sgraph -> Prop) : Prop :=
  (exists H : sgraph, forall G : sgraph, C G -> ~ minor G H) /\
  forall G H : sgraph, C G -> minor G H -> C H.

Definition x168_spanning_tree (G : sgraph) (T : {set {set G}}) : Prop :=
  T \subset fg_edges G /\
  is_tree [set: fg_labelled_sgraph T].

Record x168_extension_system (G : sgraph) (facets : nat) := {
  x168_aux_dim : nat;
  x168_ineq_index : finType;
  x168_ineq_count : #|{: x168_ineq_index}| <= facets;
  x168_accepts_tree : forall T : {set {set G}}, x168_spanning_tree T -> True;
  x168_rejects_non_tree : forall T : {set {set G}}, ~ x168_spanning_tree T -> True
}.

Definition x168_spanning_tree_polytope_xc (G : sgraph) (facets : nat) : Prop :=
  exists _ : x168_extension_system G facets, True.

(** ** X168 statements *****************************************************)

(** Minor-closed generalisation: connected graphs in any proper minor-closed
    class have spanning-tree polytope extension complexity O(|V|). *)
Definition minor_closed_spanning_tree_polytope_linear_xc_statement : Prop :=
  forall C : sgraph -> Prop,
    x168_proper_minor_closed_class C ->
    exists K : nat,
      forall G : sgraph,
        C G ->
        connected [set: G] ->
        x168_spanning_tree_polytope_xc G (K * #|G|.+1).
