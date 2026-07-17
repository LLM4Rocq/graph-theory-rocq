# List-Flexibility And Poset Foundation Notes

Status: promoted on 2026-07-16.

## List Flexibility

`base/theories/list_flexibility.v` defines weighted list-flexibility over finite graphs.

It now owns:

- `weighted_request_total`
- `weighted_request_satisfied`
- `proper_list_colouring`
- `weighted_epsilon_flexible`
- `epsilon_flexible`

The weighted predicate quantifies over arbitrary finite colour palettes, list assignments, and natural request weights.  The epsilon parameter is a rational `p/q`, encoded by the finite inequality
`p * total <= q * satisfied`.

Retargeted rows:

- `X132`: planar list-flexibility for list sizes 5/4/3.
- `X183`: `d`-degenerate graphs with lists of size `d+1`, using base `k_degenerate`.

## Posets

`base/theories/posets.v` defines finite posets as finite carriers with a reflexive, antisymmetric, transitive boolean order.

It now owns:

- `finite_poset`
- `poset_chain`
- `poset_height_at_most`
- `poset_cover_graph`
- `poset_dimension_at_most`

Order dimension is represented by a finite realizer: a list of linear extensions whose intersection is exactly the poset order.

Retargeted rows:

- `X182`: posets with planar cover graphs have dimension bounded polynomially in height.

## Faithfulness Boundary

These foundations do not cover fixed-surface embeddings, probability, algorithmic running-time models, graph limits, or paper-local structural classes. Rows blocked on those independent notions remain blocked.
