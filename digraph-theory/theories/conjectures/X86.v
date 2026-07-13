(** * Digraph.conjectures.X86 -- v2 arc-disjoint branchings row *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented strong.
From Digraph.conjectures Require Import dichromatic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X86 vocabulary ************************************************)

Definition x86_real_sel (D : diGraphType) (f : D -> {set D}) : Prop :=
  forall u v : D, v \in f u -> u --> v.

Definition x86_inside (D : diGraphType) (S : {set D}) (f : D -> {set D}) : Prop :=
  forall u v : D, v \in f u -> u \in S /\ v \in S.

Definition x86_arc_disjoint
    (D : diGraphType) (f g : D -> {set D}) : Prop :=
  forall u v : D, ~~ ((v \in f u) && (v \in g u)).

Definition x86_sel_indeg (D : diGraphType) (S : {set D})
    (f : D -> {set D}) (v : D) : nat :=
  #|[set u in S | v \in f u]|.

Definition x86_out_branching_on
    (D : diGraphType) (S : {set D}) (f : D -> {set D}) (r : D) : Prop :=
  r \in S /\
  x86_real_sel f /\
  x86_inside S f /\
  x86_sel_indeg S f r = 0 /\
  (forall v : D, v \in S -> v != r -> x86_sel_indeg S f v = 1) /\
  acyclicb (outsel f).

Definition x86_in_branching_on
    (D : diGraphType) (S : {set D}) (f : D -> {set D}) (r : D) : Prop :=
  r \in S /\
  x86_real_sel f /\
  x86_inside S f /\
  #|f r| = 0 /\
  (forall v : D, v \in S -> v != r -> #|f v| = 1) /\
  acyclicb (outsel f).

(** ** X86 statements ******************************************************)

(** Studies slice: Balliu-Brunelli-Crescenzi-Olivetti-Viennot conjecture that
    every strongly connected digraph has same-root arc-disjoint in/out
    branchings of linear size. *)
Definition strongly_connected_same_root_linear_branchings_statement : Prop :=
  exists cnum cden : nat,
    [/\ 0 < cnum, 0 < cden
      & forall D : diGraphType,
          0 < #|D| ->
          strongb D ->
          exists (r : D) (Sin Sout : {set D})
                 (Tin Tout : D -> {set D}),
            [/\ x86_in_branching_on Sin Tin r,
                x86_out_branching_on Sout Tout r,
                x86_arc_disjoint Tin Tout,
                cnum * #|D| <= cden * #|Sin|
              & cnum * #|D| <= cden * #|Sout|]].
