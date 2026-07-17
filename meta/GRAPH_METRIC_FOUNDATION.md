# Graph Metric Foundation

Date: 2026-07-16

Scope: `GTBase.graph_metric`, promoted to support Chen-Chvatal metric-line rows
without per-row placeholders.

## Vocabulary

- `rel_ball r k x`: vertices reachable from `x` by at most `k` steps in a
  finite relation `r`.
- `graph_dist x y`: finite shortest-path distance with a total fallback at
  `#|G|`; on connected graphs this is the usual graph metric.
- `graph_between u v w`: metric betweenness, encoded as
  `dist u v + dist v w = dist u w`.
- `metric_line a b`: Chen-Chvatal line through two vertices, containing every
  vertex for which one of the three vertices lies between the other two.
- `metric_line_count G`: number of distinct lines determined by unordered
  non-equal vertex pairs, quotienting duplicate line sets by finite-set
  equality.
- `graph_edge_set G`: simple graph edges as two-element vertex sets.
- `graph_bridge e`: an edge whose endpoints are disconnected after deleting
  that edge.
- `bridge_count G`: number of bridges.

## Retargeted Rows

- X171 is now faithful: it states the pendant-edge or
  `#|G| <= metric_line_count G + bridge_count G` dichotomy outside a finite
  exceptional family.  The finite family is represented by an order bound,
  which is faithful for finite graph exceptions because only finitely many
  finite graphs have order at most a fixed natural number.
- X172 is partially improved but remains blocked: the counterexample predicate
  now uses the real inequality `metric_line_count G + bridge_count G < #|G|`,
  but the generated-family relation for repeated bridge-to-path replacement is
  still a placeholder.

## Boundary

This foundation deliberately does not define graph transformation closure under
bridge replacement.  That operation needs a construction relating a source
edge, a replacement path length, and the resulting finite graph, plus reflexive
transitive closure for repeated replacements.
