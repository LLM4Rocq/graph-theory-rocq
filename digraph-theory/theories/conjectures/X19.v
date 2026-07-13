(** * Digraph.conjectures.X19 -- v2 directed-cycle packing/girth rows *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph oriented dipath.
From Digraph.conjectures Require Import classic_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X19 vocabulary ************************************************)

Definition x19_loopless (D : diGraphType) : Prop :=
  forall v : D, ~~ (v --> v).

Definition x19_directed_girth_at_least (D : diGraphType) (g : nat) : Prop :=
  forall c : seq D, dicycle c -> g <= size c.

Definition x19_cycle_vertices (D : diGraphType) (c : seq D) : {set D} :=
  [set v | v \in c].

Definition x19_vertex_disjoint_dicycles
    (D : diGraphType) (cs : seq (seq D)) : Prop :=
  all (@dicycle D) cs /\
  forall c d : seq D, c \in cs -> d \in cs -> c != d ->
    [disjoint x19_cycle_vertices c & x19_cycle_vertices d].

Definition x19_distinct_cycle_lengths (D : diGraphType) (cs : seq (seq D)) : Prop :=
  uniq (map size cs).

(** ** X19 statements ******************************************************)

(** Studies slice: Behzad-Chartrand-Wall conjecture on regular digraph girth. *)
Definition behzad_chartrand_wall_girth_regular_digraph_statement : Prop :=
  forall (r g : nat) (D : diGraphType),
    0 < r -> 0 < g -> 0 < #|D| ->
    x19_loopless D ->
    diregular D r ->
    x19_directed_girth_at_least D g ->
    (r * (g - 1) + 1 <= #|D|)%N.

(** Studies slice: Lichiardopol's distinct-length directed-cycle packing conjecture. *)
Definition lichiardopol_distinct_length_dicycle_packing_statement : Prop :=
  forall k : nat, exists g : nat,
    forall D : diGraphType,
      0 < #|D| ->
      x19_loopless D ->
      (forall v : D, g <= outdeg v) ->
      exists cs : seq (seq D),
        size cs = k /\
        x19_vertex_disjoint_dicycles cs /\
        x19_distinct_cycle_lengths cs.
