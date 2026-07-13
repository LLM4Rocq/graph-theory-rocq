(** * Hypergraph.conjectures.X72 -- v2 Ryser cover-gap row *)

From GTBase Require Export base.
From Hypergraph.conjectures Require Import X6.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X72 vocabulary ************************************************)

Definition x72_intersecting (T : finType) (E : {set {set T}}) : Prop :=
  forall e f : {set T}, e \in E -> f \in E -> e :&: f != set0.

Definition x72_vertex_cover (T : finType) (E : {set {set T}}) (X : {set T})
  : Prop :=
  forall e : {set T}, e \in E -> ~~ [disjoint X & e].

Definition x72_transversal_number
    (T : finType) (E : {set {set T}}) (tau : nat) : Prop :=
  (exists X : {set T}, x72_vertex_cover E X /\ #|X| = tau) /\
  forall X : {set T}, x72_vertex_cover E X -> tau <= #|X|.

(** ** X72 statements ******************************************************)

(** Studies slice: Abu-Khazneh-Barat-Pokrovskiy-Szabo question asking for a
    universal constant K such that every r admits an intersecting r-partite
    r-uniform hypergraph with cover number at least r-K. *)
Definition ryser_intersecting_partite_cover_gap_statement : Prop :=
  exists K : nat,
    forall r : nat,
      1 <= r ->
      exists (T : finType) (part : T -> 'I_r) (E : {set {set T}}) (tau : nat),
        [/\ E != set0,
            @x6_r_partite_uniform T r part E,
            x72_intersecting E,
            x72_transversal_number E tau
          & r <= tau + K].
