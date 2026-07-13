(** * GTMisc.conjectures.X29 -- v2 normal graph row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X29 vocabulary ************************************************)

Definition x29_complement_rel (G : sgraph) : rel G :=
  fun x y => (x != y) && ~~ (x -- y).

Lemma x29_complement_sym (G : sgraph) : symmetric (@x29_complement_rel G).
Proof. by move=> x y; rewrite /x29_complement_rel eq_sym sg_sym. Qed.

Lemma x29_complement_irrefl (G : sgraph) : irreflexive (@x29_complement_rel G).
Proof. by move=> x; rewrite /x29_complement_rel eqxx. Qed.

Definition x29_complement (G : sgraph) : sgraph :=
  SGraph (@x29_complement_sym G) (@x29_complement_irrefl G).

Definition x29_stable_set (G : sgraph) (S : {set G}) : Prop :=
  forall x y : G, x \in S -> y \in S -> ~~ (x -- y).

Definition x29_clique_cover (G : sgraph) (C : seq {set G}) : Prop :=
  (forall K : {set G}, K \in C -> clique K) /\
  forall v : G, exists K : {set G}, K \in C /\ v \in K.

Definition x29_stable_cover (G : sgraph) (S : seq {set G}) : Prop :=
  (forall I : {set G}, I \in S -> x29_stable_set I) /\
  forall v : G, exists I : {set G}, I \in S /\ v \in I.

Definition x29_normal_graph (G : sgraph) : Prop :=
  exists (C S : seq {set G}),
    x29_clique_cover C /\
    x29_stable_cover S /\
    forall (K I : {set G}), K \in C -> I \in S -> K :&: I != set0.

Definition x29_has_induced_cycle (G : sgraph) (n : nat) : Prop :=
  exists S : {set G},
    #|S| = n /\ inhabited (induced S ≃ cycle_graph n).

(** ** X29 statements ******************************************************)

(** Studies slice: de Simone-Korner normal graph conjecture. *)
Definition no_c5_c7_complement_c7_normal_graph_statement : Prop :=
  forall G : sgraph,
    ~ x29_has_induced_cycle G 5 ->
    ~ x29_has_induced_cycle G 7 ->
    ~ x29_has_induced_cycle (x29_complement G) 7 ->
    x29_normal_graph G.
