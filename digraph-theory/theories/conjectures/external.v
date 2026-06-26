(** * Digraph.conjectures.external — cited external results as hypotheses

    Some implication edges (docs/CONJECTURES_FORMALIZATION_PLAN.md §7.3) rely on a
    published theorem not (yet) formalized in this library. Rather than [Admitted] or
    axiomatizing, we declare each such result here as a [Definition _statement : Prop]
    and carry it as an EXPLICIT hypothesis in the edge theorem that needs it — keeping
    every edge [Qed]-closed and the whole library axiom-free, with the external
    dependency greppable. Entries are added per phase; the P0/P1 layer needs none. *)

From HB Require Import structures.
From mathcomp Require Import all_boot.
From Digraph Require Import prelude digraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* (No external results are required by the P0/P1 edges.) *)
