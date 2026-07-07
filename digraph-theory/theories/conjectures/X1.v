(** * Digraph.conjectures.X1 — v2 milestone X1 (directed reconciliation)

    Re-export gate file. The v2-corpus rows reconciled in milestone X1
    (see meta/v2_reconciliation.json) are formalized by pre-existing constants
    in the sibling modules re-exported below; this file DEFINES NOTHING. It
    exists so `check_milestone.py X1 digraph-theory` finds a milestone .v in
    _CoqProject and can Print-Assumptions / exact-type-probe the reconciled
    constants through it. *)

From Digraph Require Export
  chi_bounded clique_cluster colouring_variants heroes_dichotomy sad twinwidth two_extremal unvd.
