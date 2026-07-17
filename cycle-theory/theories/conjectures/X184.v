(** * Cycle.conjectures.X184 -- v2 antisymmetric Z5-flow row *)

From GraphTheory Require Import mgraph.
From GTBase Require Import base.
From Cycle.conjectures Require Import D1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X184 vocabulary ***********************************************)

Definition x184_out_cut (G : mgraph) (S : {set G}) : {set edge G} :=
  [set e : edge G | (source e \in S) && (target e \notin S)].

Definition x184_directed_k_edge_connected (G : mgraph) (k : nat) : Prop :=
  forall S : {set G},
    S != set0 -> S != [set: G] -> k <= #|x184_out_cut S|.

Definition x184_z5_antisymmetric_flow (G : mgraph) : Prop :=
  exists phi : edge G -> 'I_5,
    (forall e : edge G, phi e != ord0) /\
    forall v : G,
      ((\sum_(e : edge G | source e == v) val (phi e)) %% 5 =
       (\sum_(e : edge G | target e == v) val (phi e)) %% 5).

(** ** X184 statements *****************************************************)

(** Esperet-de Joannis de Verclos-Le-Thomasse: there is a constant [k] such
    that every directed [k]-edge-connected graph has a [Z_5]-antisymmetric flow. *)
Definition z5_antisymmetric_flow_edge_connectivity_statement : Prop :=
  exists k : nat,
    forall G : mgraph,
      x184_directed_k_edge_connected G k ->
      x184_z5_antisymmetric_flow G.
