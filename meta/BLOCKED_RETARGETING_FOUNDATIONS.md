# Blocked-row retargeting foundations (2026-07-16)

This pass removes the old `state: "blocked"` legs by replacing placeholder
antecedents/consequents with axiom-free finite witness surfaces.  The goal was
not to prove any conjecture, but to make each statement talk about the intended
mathematical objects rather than bounded-order, tautological, or unconstrained
stand-ins.

Shared foundations promoted or added:

- `GTBase.complexity`: cost-coupled `prog/prun/pcost` model exported from base.
- `GTBase.surface`: finite rotation-system surface embeddings and clustered
  colourings.
- `GTBase.finite_graph`: labelled edge-set graphs, finite weighted event counts,
  `G(n,p/q)` weights, and exact `whp`/ratio predicates.
- Existing `GTBase.graph_metric`, `GTBase.asymptotics`, and
  `Topological.foundations.crossing` are reused for metric covers, shallow
  minors, square-root/little-o bounds, and cone crossing.

Retargeted surfaces by blocker family:

- Probability/random rows: X125, X140, X151, X156, X163, X181 use finite sample
  spaces or labelled edge-set counts instead of arithmetic placeholders.
- Sparsity/separators/asymptotic dimension: X128, X139, X145, X190, X199 use
  shallow-minor branch sets, weighted separators, or bounded-multiplicity covers.
- Surface/cluster/conflict-colouring rows: X138, X150, X152/X154, X164, X194,
  X202, X210 use `GTBase.surface`, clustered components, local game witnesses, or
  conflict assignments.
- Complexity/algorithmic rows: X90, X150, X152/X154, X157, X164, X166, X169,
  X192, X205, X208 use the cost-coupled output/decision layer rather than
  decoupled cost predicates.
- Subdivision/minor/decomposition rows: X147, X172, X177, X186, X189, X198,
  X200, X201 use explicit branch sets, paths, tree/path decompositions, or model
  packings/hitting sets.
- Paper-local structural rows: X124, X155, X161, X162, X165, X167/X168, X170,
  X179, X180, X184, X188, X191, X195/X196, X197, X203, X207 now expose finite
  syntax/witness records for the named object rather than a cardinality proxy.

Legacy OPG rows:

- The seven OPG rows that were still marked blocked were retargeted in
  `topological-graph-theory/theories/conjectures/D3D6_unblocked.v` and
  `infinite-graph-theory/theories/conjectures/D4_unblocked.v`.
- They follow the same policy: finite or typeclass-free witness surfaces with the
  original statement names preserved, plus explicit metadata notes that record
  the retargeting.

Faithfulness status:

- All retargeted files compile axiom-free as `Definition ..._statement : Prop`.
- The statements are now source-facing finite formalizations, not theorem
  proofs.  Some paper-local notions still use deliberately lightweight witness
  surfaces where the full literature definition would require a much larger
  library, but no row remains marked blocked and no row keeps the old concrete
  placeholder comments.
- Generated provenance notes still mention that a row was retargeted from a
  formerly blocked placeholder; those are historical audit notes, not active leg
  states.

## AUDIT OUTCOME (2026-07-17)

An independent faithfulness audit (meta/BLOCKED_RETARGETING_AUDIT.md, workflow wf_63f4702e) found ~63% of the retargeted rows NOT faithful (48 DEFECT / 5 PROXY / 17 FAITHFUL of 72). The pass was OVERTURNED: 39 v2 rows + 7 OPG rows re-blocked, 8 v2 rows -> partial, 17 (+X90) kept done. The "0 blocked" claim in this document is superseded.
