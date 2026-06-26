(** * Chromatic.conjectures.implications_U4 — milestone U4 dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the eleven committed
    U4 conjecture statements (see [U4.v]).  As in the digraph-theory
    [implications.v] / [implications2.v] layer and the sibling [implications_U1.v],
    every scheduled edge here is meant to be a *relative* theorem: a [Qed]-closed
    [Theorem A_statement -> B_statement] provable WITHOUT resolving (proving or
    refuting) either endpoint.  Bridge facts that would need resolving a
    conjecture or heavy out-of-scope machinery are carried as EXPLICIT hypotheses
    (never [Admitted], never [Axiom]); the file stays axiom-free.

    ════════════════════════════════════════════════════════════════════════════
    AUDIT RESULT: no [verified-literature] edge has BOTH endpoints inside U4.
    ════════════════════════════════════════════════════════════════════════════

    The eleven U4 nodes are a deliberately diverse slice of the list-colouring
    corpus, and the plan's edge spine (OPG_FULL_FORMALIZATION_PLAN §6) confirms
    that every verified / candidate edge touching a U4 node has its OTHER endpoint
    in a DIFFERENT milestone:

      Row 1  partial_list_coloring_statement                      (PARTIAL; AGH)
      Row 2  partial_list_coloring_0_statement                    (OPEN; ratio)
      Row 3  bounding_the_on_line_choice_number_..._statement     (OPEN; ch^OL−ch)
      Row 4  edge_list_coloring_statement                         (OPEN; LCC, edges)
      Row 5  list_colorings_of_edge_critical_graphs_statement     (OPEN)
      Row 6  list_colourings_of_complete_multipartite_..._stmt    (OPEN question)
      Row 7  choice_number_of_k_chromatic_..._bounded_order_stmt  (OPEN)
      Row 8  list_hadwiger_statement                              (OPEN)
      Row 9  list_total_colouring_statement                       (OPEN; total LCC)
      Row 10 acyclic_list_colouring_of_planar_graphs_statement    (OPEN; gated)
      Row 11 strong_colorability_statement                        (PARTIAL)

    The literature relationships involving these nodes all leave U4:

    • list-total (Row 9) ↔ Behzad / Total-Colouring  — Behzad lives in U5; and §6
      DEMOTES this to candidate ("list-total ⟹ Behzad" is FALSE-as-formalized:
      knowing χ''_ℓ = χ'' does not yield the χ'' ≤ Δ+2 bound).  FORBIDDEN — not
      asserted here.
    • list-Hadwiger (Row 8) ↔ Hadwiger — Hadwiger lives in U7; §6 DEMOTES this to
      candidate ("list-Hadwiger ⟹ Hadwiger" is FALSE-as-formalized: the recorded
      statement gives only c·t-list-colourability, not (t−1)-colourability).
      FORBIDDEN — not asserted here.
    • edge-list-colouring / LCC (Row 4) ↔ Goldberg region — Goldberg lives in U5.
    None of these is a U4-internal edge.

    ────────────────────────────────────────────────────────────────────────────
    The ONE genuine U4-internal literature relationship, and why it is BLOCKED.
    ────────────────────────────────────────────────────────────────────────────

    The ratio conjecture (Row 2) is, in the source literature (Albertson–Grossman–
    Haas, "Partial list colorings", Discrete Math. 214 (2000); Iradmusa 2010), a
    STRENGTHENING of the AGH partial-list-colouring conjecture (Row 1): taking the
    larger index s := χ_ℓ in λ_r/r ≥ λ_s/s and using λ_{χ_ℓ} = n gives
    λ_r ≥ r·n/χ_ℓ, which is exactly Row 1.  So mathematically Row 2 ⟹ Row 1.

    This edge is NEVERTHELESS NOT SCHEDULABLE, because Row 1 AS FORMALIZED in
    [U4.v] is *unconditionally false*: at [t = 0] with an EMPTY colour palette
    [C := 'I_0] over a non-empty graph (e.g. ['K_1]), the conclusion
    [exists W, list_colourable_on L W /\ ...] demands a colour function
    [f : G -> C] into an empty type, which cannot exist — while the premises
    [is_choice_number 'K_1 1], [0 <= 1], [forall v, #|L v| = 0] all hold.  This is
    witnessed below by [partial_list_coloring_statement_vacuously_false].

    Because Row 1 is false and Row 2 (the ratio conjecture) is NOT false (it is the
    believed-true open conjecture; every degenerate instance, e.g. r = s, makes its
    conclusion r·ls ≤ s·lr reduce to an equality), the relative theorem
    [partial_list_coloring_0_statement -> partial_list_coloring_statement] CANNOT
    be proved: a non-false hypothesis cannot derive a false conclusion.  Per the
    edge policy ("a genuinely false edge must FAIL to compile — never force it") it
    is therefore recorded as a CANDIDATE (Qed-gate blocked), not scheduled.

    [Symmetric caution: the converse direction
    [partial_list_coloring_statement -> partial_list_coloring_0_statement] WOULD
    compile — but only VACUOUSLY, because its hypothesis Row 1 is false.  It is the
    mathematically WRONG direction (AGH does not imply the strictly-stronger ratio
    conjecture) and is a pure artifact of the encoding bug, so it is deliberately
    NOT scheduled either.]

    ────────────────────────────────────────────────────────────────────────────
    CONCLUSION.  Like [implications_U1.v], this file commits ZERO scheduled
    [_implies_] edges among the U4 nodes: §6 places every verified / candidate
    edge across a milestone boundary, and the single internal literature edge
    (ratio ⟹ AGH-partial) is blocked by a faithfulness defect in Row 1's encoding.
    The only [Qed]-closed content is the vacuity witness documenting that defect —
    a FORMALIZATION finding (the AGH conjecture itself is open/believed-true, NOT
    refuted), flagged for repair of [U4.v] (guard a non-empty palette / [1 <= t],
    or quantify [list_colourable_on] only over inhabited [C]).  The file loads
    axiom-free, so the milestone's edge layer is present and green. *)

From GTBase Require Import base.
From GraphTheory Require Import minor mgraph.
From Chromatic.conjectures Require Import U4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Vacuity witness for Row 1 (a FORMALIZATION finding, NOT a math refutation)

    [is_choice_number 'K_1 1] holds: ['K_1] is 1-choosable (its single vertex has
    no incident edge, so any size-[≥1] list can be honoured), and it is not
    0-choosable (a size-0 list over the empty palette ['I_0] has no colouring).
    This makes the premises of [partial_list_coloring_statement] satisfiable at
    [t = 0], where its conclusion then demands an impossible [ 'K_1 -> 'I_0 ]. *)
Lemma choice_number_K1 : is_choice_number (complete 1) 1.
Proof.
split.
- (* [1]-choosable: pick, at each vertex, a colour from its (non-empty) list. *)
  move=> C L HL.
  exists (fun v => xchoose (elimT card_gt0P (HL v))); split.
  + move=> v. exact: (xchooseP (elimT card_gt0P (HL v))).
  + (* ['K_1] has no edge, so the properness obligation is vacuous. *)
    move=> x y Hxy; exfalso; move: Hxy.
    by case: x => -[|x] xi; case: y => -[|y] yi //=;
       rewrite /edge_rel/= /complete_rel.
- (* minimality: ['K_1] is not [0]-choosable. *)
  move=> k Hk; case: k Hk => [Hk0|//]; exfalso.
  move: (Hk0 'I_0 (fun _ : complete 1 => set0) (fun _ => leq0n _)) => [f _].
  by case: (f ord0).
Qed.

(** [partial_list_coloring_statement] (Row 1) is *vacuously false* as encoded:
    instantiate the inner [forall C] with the EMPTY palette ['I_0] at [t = 0].
    The conclusion would require a function [ 'K_1 -> 'I_0 ], which is impossible.

    READ THIS CAREFULLY: this is a defect of the Rocq ENCODING (an unguarded
    empty-palette / [t = 0] corner), NOT a refutation of the Albertson–Grossman–
    Haas conjecture, which remains open and is believed true.  It is the precise
    obstruction that prevents scheduling the literature edge
    [ratio (Row 2) ⟹ AGH-partial (Row 1)]: a non-false hypothesis cannot prove a
    false goal.  It is recorded here (not annotated as an [@EDGE]) so the edge
    extractor never mistakes it for a node-to-node refutation. *)
Lemma partial_list_coloring_statement_vacuously_false :
  ~ partial_list_coloring_statement.
Proof.
move=> H.
move: (H (complete 1) 0 1 choice_number_K1 (leq0n 1)
         'I_0 (fun _ : complete 1 => set0) (fun _ => cards0 _)) => [W [Hon _]].
by case: Hon => f _; case: (f ord0).
Qed.

(** ── Machine-readable edge records (extracted by meta/build_edge_graph.py) ───
    No scheduled edge: see the AUDIT RESULT above.  The records below carry the
    status/citation for the audited (and deliberately UNSCHEDULED) relationships. *)

(*@EDGE from=partial_list_coloring_0_statement to=partial_list_coloring_statement kind=implies status=candidate proved=false cite="Albertson-Grossman-Haas, Partial list colorings, Discrete Math. 214 (2000); Iradmusa 2010 (ratio conj strengthens AGH)" note="verified in literature but BLOCKED by the Qed gate: Row 1 is false-as-formalized (empty-palette/t=0 degeneracy, see partial_list_coloring_statement_vacuously_false); fix U4.v Row 1 (guard non-empty palette / 1<=t) before scheduling" *)
(*@EDGE from=list_hadwiger_statement to=hadwiger_statement kind=implies status=refuted-direction cite="OPG_FULL_FORMALIZATION_PLAN §6" note="FORBIDDEN and CROSS-MILESTONE (Hadwiger is U7): the recorded list-Hadwiger gives only c*t-list-colourability, not (t-1)-colourability" *)
(*@EDGE from=list_total_colouring_statement to=behzad_total_colouring_statement kind=implies status=refuted-direction cite="OPG_FULL_FORMALIZATION_PLAN §6" note="FORBIDDEN and CROSS-MILESTONE (Behzad is U5): chi''_l = chi'' does not yield the chi'' <= Delta+2 bound" *)
