(** * Extremal.conjectures.X143 -- v2 forcing graph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X143 vocabulary ***********************************************)

Definition x143_contains_cycle (G : sgraph) : Prop :=
  exists c : seq G, ucycle (--) c /\ 2 < size c.

Definition x143_hom_count (A G : sgraph) : nat :=
  #|[set f : {ffun A -> G} |
      [forall x : A, [forall y : A, (x -- y) ==> (f x -- f y)]]]|.

Definition x143_edge_density_num (G : sgraph) : nat := 2 * fg_edge_count G.
Definition x143_edge_density_den (G : sgraph) : nat := #|G| * #|G|.

Definition x143_density_converges
    (num den : sgraph -> nat) (target_num target_den : nat)
    (Gs : nat -> sgraph) : Prop :=
  forall a b : nat, 0 < a -> a <= b ->
    eventually (fun n =>
      b * (target_den * num (Gs n)) <=
        (b * target_num + a * target_num) * den (Gs n)).

Definition x143_quasirandom_sequence (Gs : nat -> sgraph) : Prop :=
  forall H : sgraph,
    exists p q : nat, 0 < q /\
      x143_density_converges
        (fun G => x143_hom_count H G)
        (fun G => #|G| ^ #|H|)
        p q Gs.

Definition x143_forcing_graph (G : sgraph) : Prop :=
  forall (Gs : nat -> sgraph) (p q : nat),
    0 < q ->
    x143_density_converges x143_edge_density_num x143_edge_density_den p q Gs ->
    x143_density_converges
      (fun H => x143_hom_count G H)
      (fun H => #|H| ^ #|G|)
      (p ^ fg_edge_count G) (q ^ fg_edge_count G) Gs ->
    x143_quasirandom_sequence Gs.

(** ** X143 statements *****************************************************)

(** Skokan-Thoma forcing conjecture: a graph is forcing iff it is bipartite and
    contains a cycle.  Forcing is stated through finite hom-density convergence
    over graph sequences. *)
Definition skokan_thoma_forcing_graph_characterisation_statement : Prop :=
  forall A : sgraph,
    x143_forcing_graph A <-> bipartite A /\ x143_contains_cycle A.
