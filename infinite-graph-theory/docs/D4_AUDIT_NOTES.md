# infinite-graph-theory — D4 preflight & audit notes (final phase)

New 13th area (namespace `Infinite`). **Strict preflight**: of the 14 D4 rows, **2 doable / 7 partial /
5 blocked**. `check_milestone D4doa` ACCEPTED, **2/2 axiom-free**. After D4, all 227 corpus rows are
attempted (done / partial / blocked, none left todo).

## Carrier — `iGraph` (NOT sgraph; sgraph is a finite finType)
`foundations/igraph.v`: `Record iGraph { iV : Type; iedge : iV -> iV -> Prop; iedge_sym; iedge_irr }`
with Prop-level `irel_sym`/`irel_irr`, the `iadj` accessor, and Prop-level predicates (`countable_graph`,
`ray`, `Komega` = the countable complete graph). mathcomp's bool `\in`/`path` need eqType/finType, so
infinite-graph combinatorics are Prop-level by necessity. Stays in foundations/, never base.

## The 2 doable rows → done
- **counting_3_colorings_of_the_hex_lattice** — a thermodynamic limit over *finite* hex tori. The
  agent first used Stdlib `Reals` (Rpower/INR), which the code-review caught as **NOT axiom-free** (it
  pulls `classic`, `functional_extensionality`, Dedekind-reals — 4 classical axioms). **Re-encoded
  axiom-free** over an abstract `rcfType`: `persite_cauchy` states that the per-site values `s_n` (the
  `|V_n|`-th roots of the 3-colouring counts, quantified by `s_n ^+ |V_n| = count_n` — no n-th-root
  function, no Stdlib reals) form a **Cauchy** sequence = the limit exists in the completion. Faithful;
  non-vacuity witness `persite_cauchy_const`. `hex_torus`/`is_proper3`/`n3colorings` (chromatic
  polynomial at 3) are the finite, axiom-free machinery.
- **exact_colorings_of_graphs** — over `K_ω` (countable complete graph): exact-colouring counting
  predicate (`exact_coloring`/`exactly_m_colored`). Axiom-free, faithful.

## 7 partial — statable with machinery we did not build
end_devouring_rays (ends), hamiltonian_cycles_in_line_graphs / _in_powers / infinite_uniquely_hamiltonian
(infinite Hamiltonicity = topological double-ray cycles), seymours_self_minor (infinite-graph minors),
unfriendly_partitions (cardinal neighbour comparison), strong_matchings_and_covers (infinite hypergraph
order theory). The `iGraph` carrier suffices; the missing piece is ends / infinite-Hamiltonicity /
infinite-minor / cardinal-comparison vocabulary — a future infinite-combinatorics layer.

## 5 blocked — out of scope (genuine cardinals / geometry / set theory)
characterizing_aleph_0_aleph_1_graphs (ℵ₁ cardinal arithmetic), coloring_the_odd_distance_graph (ℝ²
odd-distance geometry), highly_arc_transitive_two_ended_digraphs & universal_highly_arc_transitive_digraphs
(ends + automorphism actions + universality), unions_of_triangle_free_graphs (ZFC / independence-flavoured).
