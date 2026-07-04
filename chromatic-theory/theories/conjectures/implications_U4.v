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
    The ONE genuine U4-internal literature relationship (ratio ⟹ AGH-partial).
    ────────────────────────────────────────────────────────────────────────────

    The ratio conjecture (Row 2) is, in the source literature (Albertson–Grossman–
    Haas, "Partial list colorings", Discrete Math. 214 (2000); Iradmusa 2010), a
    STRENGTHENING of the AGH partial-list-colouring conjecture (Row 1): taking the
    larger index s := χ_ℓ in λ_r/r ≥ λ_s/s and using λ_{χ_ℓ} = n gives
    λ_r ≥ r·n/χ_ℓ, which is exactly Row 1.  So mathematically Row 2 ⟹ Row 1.

    ENCODING NOTE (post-release repair, audit finding #1).  A PRIOR encoding of
    Row 1 was unconditionally FALSE at [t = 0] over an empty palette [C := 'I_0]:
    [list_colourable_on] then demanded a total [f : G -> C] into an empty type.
    That is now FIXED — [list_colourable_on] is a PARTIAL ([option]-valued)
    colouring of [W] only (base.v), so [W = set0] / [t = 0] is vacuously TRUE and
    Row 1 is once again the faithful, open AGH proposition.  The [t = 0] corner is
    trivially true; the content lives at [1 <= t], which is open.

    This literature edge [partial_list_coloring_0_statement ⟹
    partial_list_coloring_statement] is therefore no longer blocked by a
    faithfulness defect; it is recorded as a CANDIDATE (its Rocq proof — via
    [λ_{χ_ℓ} = n] and the ratio at [s := χ_ℓ] — is future work, see the follow-up
    "verified-edge expansion" issue), not force-scheduled.

    ────────────────────────────────────────────────────────────────────────────
    CONCLUSION.  This file commits ZERO scheduled [_implies_] edges among the U4
    nodes: §6 places every verified / candidate edge across a milestone boundary,
    and the single internal literature edge (ratio ⟹ AGH-partial) is a proof
    obligation deferred to the edge-expansion track.  The only [Qed]-closed content
    is [choice_number_K1] (ch('K_1) = 1).  The file loads axiom-free. *)

From GTBase Require Import base.
From GraphTheory Require Import minor mgraph.
From Chromatic.conjectures Require Import U4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** ch('K_1) = 1 (a grounding identity for the choice number).

    ['K_1] is 1-choosable (its single vertex has no incident edge, so any
    size-[≥1] list can be honoured) and not 0-choosable (a size-0 list over the
    empty palette ['I_0] has no colouring — note [choosable]/[list_colourable]
    remain TOTAL colourings of the whole graph, which is the correct semantics
    for the full-graph choice number, unlike the partial [list_colourable_on]). *)
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


(** ── Machine-readable edge records (extracted by meta/build_edge_graph.py) ───
    No scheduled edge: see the AUDIT RESULT above.  The records below carry the
    status/citation for the audited (and deliberately UNSCHEDULED) relationships. *)

(*@EDGE from=partial_list_coloring_0_statement to=partial_list_coloring_statement kind=implies status=candidate proved=false cite="Albertson-Grossman-Haas, Partial list colorings, Discrete Math. 214 (2000); Iradmusa 2010 (ratio conj strengthens AGH)" note="ratio (Row 2) strengthens AGH-partial (Row 1) via lambda_{chi_l}=n at s:=chi_l; the earlier empty-palette/t=0 defect in Row 1 is FIXED (list_colourable_on is now partial/option-valued), so the edge is schedulable — its Rocq proof is future work (edge-expansion track)" *)
(*@EDGE from=list_hadwiger_statement to=hadwiger_statement kind=implies status=refuted-direction cite="OPG_FULL_FORMALIZATION_PLAN §6" note="FORBIDDEN and CROSS-MILESTONE (Hadwiger is U7): the recorded list-Hadwiger gives only c*t-list-colourability, not (t-1)-colourability" *)
(*@EDGE from=list_total_colouring_statement to=behzads_statement kind=implies status=refuted-direction cite="OPG_FULL_FORMALIZATION_PLAN §6" note="FORBIDDEN and CROSS-MILESTONE (Behzad node defined in U5): chi''_l = chi'' does not yield the chi'' <= Delta+2 bound" *)
