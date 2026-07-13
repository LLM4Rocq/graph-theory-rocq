(** * Extremal.conjectures.X49 -- v2 induced-saturation row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X49 vocabulary ************************************************)

Definition x49_add_edge_rel (G : sgraph) (a b : G) : rel G :=
  fun x y => (x -- y) || ((x != y) && ([set x; y] == [set a; b])).

Lemma x49_add_edge_sym (G : sgraph) (a b : G) :
  symmetric (x49_add_edge_rel a b).
Proof. by move=> x y; rewrite /x49_add_edge_rel sg_sym eq_sym setUC. Qed.

Lemma x49_add_edge_irrefl (G : sgraph) (a b : G) :
  irreflexive (x49_add_edge_rel a b).
Proof. by move=> x; rewrite /x49_add_edge_rel sg_irrefl eqxx. Qed.

Definition x49_add_edge_graph (G : sgraph) (a b : G) : sgraph :=
  SGraph (x49_add_edge_sym a b) (x49_add_edge_irrefl a b).

Definition x49_has_induced_cycle (G : sgraph) (n : nat) : Prop :=
  exists S : {set G}, #|S| = n /\ inhabited (induced S ≃ cycle_graph n).

(** ** X49 statements ******************************************************)

(** arXiv:2505.24100, induced saturation for even cycles. *)
Definition induced_saturation_even_cycle_existence_statement : Prop :=
  forall t : nat,
    6 <= t ->
    exists G : sgraph,
      (exists a b : G, a != b /\ ~~ (a -- b)) /\
      ~ x49_has_induced_cycle G (2 * t - 2) /\
      forall a b : G,
        a != b ->
        ~~ (a -- b) ->
        x49_has_induced_cycle (@x49_add_edge_graph G a b) (2 * t - 2).
