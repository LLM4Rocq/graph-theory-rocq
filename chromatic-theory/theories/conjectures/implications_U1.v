(** * Chromatic.conjectures.implications_U1 — milestone U1 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the nine committed
    U1 conjecture statements (see [U1.v]).  As in the digraph-theory
    [implications.v] / [implications2.v] layer, every edge here is meant to be
    a *relative* theorem: a [Qed]-closed [Theorem A_statement -> B_statement]
    that is provable WITHOUT resolving (proving or refuting) either endpoint —
    it only transports one conjectural hypothesis to another, or applies one
    committed conjecture on a restricted subclass.  Any bridge fact that would
    need resolving a conjecture or heavy out-of-scope machinery is carried as an
    EXPLICIT hypothesis (never [Admitted], never [Axiom]), keeping the edge
    fully [Qed]-closed and the file axiom-free.

    ────────────────────────────────────────────────────────────────────────
    AUDIT RESULT: no [verified-literature] edge among the nine U1 nodes.
    ────────────────────────────────────────────────────────────────────────

    The nine U1 nodes are a deliberately diverse, mutually INDEPENDENT slice of
    the open/partial/solved graph-colouring corpus (the Jensen–Toft / "open
    problems in graph colouring" curation):

      Row 1  double_critical_graph_statement                 (characterization)
      Row 2  three_chromatic_0_2_graphs_statement            (∃-existence)
      Row 3  cycles_in_graphs_of_large_chromatic_number_…    (∀ lower count)
      Row 4  high_girth_low_degree_4_chromatic_graphs_…      (∃-existence)
      Row 5  erdos_faber_lovasz_statement                    (∀ χ = k)
      Row 6  the_borodin_kostochka_statement                 (∀ χ upper bound)
      Row 7  vertex_coloring_of_graph_fractional_powers_…    (∀ χ = ω)
      Row 8  melnikovs_valency_variety_statement             (∀ χ lower bound)
      Row 9  reeds_omega_delta_and_chi_statement             (∀ χ upper bound)

    No pair carries a clean relative implication that is provable without
    resolving an endpoint:

    • Row 6 (Borodin–Kostochka) vs Row 9 (Reed) — INDEPENDENT, both directions
      are FALSE, so NEITHER may be asserted (and a genuinely false edge must
      FAIL to compile — we do not force it):
        – Reed ⟹ B-K is FALSE / withdrawn: refuted at Δ = 9, ω = 8, where a
          graph with χ = 9 satisfies Reed (2·9 = 18 ≤ 9+1+8+1 = 19) yet
          violates B-K (max(Δ−1, ω) = max(8, 8) = 8 < 9).  This is the headline
          forbidden edge.
        – B-K ⟹ Reed is ALSO FALSE: B-K only constrains graphs with Δ ≥ 9 (so
          it cannot bound χ for the Δ < 9 graphs that Reed quantifies over),
          and even at Δ ≥ 9 its bound max(Δ−1, ω) is WEAKER than Reed's
          ⌈(Δ+1+ω)/2⌉+ when ω is small (e.g. Δ = 100, ω = 2: B-K gives χ ≤ 99,
          Reed demands 2χ ≤ 104 i.e. χ ≤ 52).  So B-K_statement cannot prove
          Reed_statement either.
      Both directions are reported as refuted-direction edges and intentionally
      kept OUT of this compiling file.

    • An upper-bound conjecture (Row 6 / Row 9) can never IMPLY a lower-bound
      conjecture (Row 8, Melnikov), nor the reverse — bounds run opposite ways.

    • The two ∃-existence rows do not transport: a high-girth 4-regular
      4-chromatic graph (Row 4) is not a (0,2)-graph (girth ≥ 5 forces ≤ 1
      common neighbour, breaking the "0 or 2" law), and a (0,2)-graph with
      χ = 3 (Row 2) is neither 4-regular nor 4-chromatic — so Row 2 ⇎ Row 4.

    • Rows 1, 5, 7 (characterization / equality statements) share no common
      hypothesis class with any other node, so none specializes to another.

    Consequently this file commits ZERO [Theorem]s: there is no honest
    [verified-literature] edge to schedule, and every plausible-looking edge is
    either FALSE (must not compile) or unsupported by the literature.  The file
    still loads (axiom-free) so the milestone's edge layer is present and green;
    the refuted-direction edges are recorded in the deliverable's edge table,
    not as Rocq theorems.

    This matches the U1 prior: for chromatic-bound conjectures expect FEW or NO
    verified edges — Reed and Borodin–Kostochka are independent; we do not
    fabricate. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring.
From Chromatic.conjectures Require Import U1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** No edge is scheduled: see the AUDIT RESULT above.  The nine U1 nodes carry
    no [verified-literature] relative implication, and the only expected
    relationship (Reed ⇄ Borodin–Kostochka) is false in BOTH directions and is
    therefore deliberately absent (a false edge must fail to compile). *)
