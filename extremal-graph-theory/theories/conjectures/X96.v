(** * Extremal.conjectures.X96 -- v2 large C4-free subgraph row *)

From GTBase Require Export base.
From Extremal.conjectures Require Import X4 X59.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X96 vocabulary ************************************************)

Definition x96_c4_free (G : sgraph) : Prop :=
  ~ x59_has_cycle_length G 4.

Definition x96_m_three_fourths_lower
    (cnum cden m e : nat) : Prop :=
  (cnum ^ 4) * (m ^ 3) <= (cden ^ 4) * (e ^ 4).

(** ** X96 statements ******************************************************)

(** Studies slice: Bollobas-Erdos problem asking whether every m-edge graph
    has a C4-free subgraph with Omega(m^(3/4)) edges. *)
Definition bollobas_erdos_large_c4_free_subgraph_statement : Prop :=
  exists cnum cden : nat,
    [/\ 0 < cnum, 0 < cden
      & forall (m : nat) (G : sgraph),
          x4_edge_count G = m ->
          exists H : sgraph,
            [/\ x59_subgraph_of H G,
                x96_c4_free H
              & x96_m_three_fourths_lower cnum cden m (x4_edge_count H)]].
