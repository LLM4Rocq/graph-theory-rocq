# Blocked re-encoding wave 1 (2026-07-17)

This wave repairs four rows that the blocked-retargeting audit correctly
rejected.  The original audit remains valid for the 2026-07-16 encodings; the
rows below now have new statement surfaces.

## Repaired rows

| row | previous defect | repair |
|---|---|---|
| X125 | "Almost all" was encoded as a fixed 9/10 one-shot event over arbitrary samples, collapsing to a point-mass test. | `x125_almost_all` now uses `fg_whp` over a nat-indexed complete uniform lift model with nonempty positive-weight sample spaces, plus a Boolean high-probability event and a Prop-level soundness clause for the Hajos-number window. |
| X138 | The clustering bound was existential per graph, making clustered chromatic number vacuous on finite graphs. | The statement now quantifies `exists c` before `forall G`, giving a surface/maximum-degree-uniform clustering bound. |
| X194 | The H-minor-free class conclusion had the same per-graph clustering-bound collapse. | `x194_clustered_chromatic_minor_class_le` now states `exists c, forall G`, so the clustering constant is class-uniform. |
| X198 | The island size cap was conflated with the threshold `t`, losing the class-uniform constant in `col*`. | `x198_col_star_le` now separates the `t`-island outside-neighbour threshold from an existential class-uniform size cap `c`. |

## Verification policy

- Each repaired file still exposes an axiom-free
  `Definition ..._statement : Prop`.
- The fixes remove the machine-refuted quantifier collapses identified in
  `meta/BLOCKED_RETARGETING_AUDIT.md`.
- The rows are marked `done` again only after package compilation and milestone
  gates pass for X125, X138, X194, and X198.

## Post-wave adversarial verification outcome (2026-07-18)

Independent re-verification (meta/BLOCKED_RETARGETING_AUDIT.md, repaired-rows section) partially
supersedes the policy above: **X138 CONFIRMED done**; **X194/X198** repairs were correct but had
machine-refutable degenerate-parameter holes, fixed 2026-07-18 with `2 <= k` / `1 <= t` guards
(now done); **X125 re-blocked** — the fg_whp model admits a multiplicity-skew collapse via
`exists M : lift_model`; a faithful fix needs the canonical uniform *labelled* lift sample space
(or a measure-faithfulness field). Compilation + milestone gates alone were again insufficient.
