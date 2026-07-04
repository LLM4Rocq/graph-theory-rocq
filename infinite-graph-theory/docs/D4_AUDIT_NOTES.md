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

## UPDATE (infinite-combinatorics track — M0–M5, 8 rows landed; audited 8/8, 0 blockers)

A per-row **preflight** (12 classifiers + synth) reclassified the 12 non-done D4 rows; **8 are buildable**
(6 done + 2 honest partials), **4 stay blocked**. Built over a minimal shared foundation in
`foundations/igraph.v` — **no choice / cardinal arithmetic / point-set topology / automorphism-group
placeholders**:

- **M0 primitives**: `card_le P Q := ∃ injection {x|P x}→{y|Q y}` (the *choice-free* definition of cardinal
  ≤); `finite_sub` (an `'I_n`-cover); `reachP`/`connected_set` (inductive walk-in-a-Prop-subset);
  `infinite_graph` (Dedekind ∃ nat-injection); `end_equiv` (Halin ends via finite separators + `reachP`).

Rows (each gated axiom-free; a consolidated 8-skeptic + synth audit found **no surviving trivialization,
refutation, vacuity, or smuggle** — 0 blockers):

| slug | milestone | encoding | status |
|---|---|---|---|
| unfriendly_partitions | D4inf1 | `∀ countable G, ∃ p, ∀x card_le (own_nbr)(cross_nbr)` | **done** |
| unions_of_triangle_free_graphs | D4inf1 | `∃G, K4_free ∧ ¬ctf_cover` (ℵ₀-cover = symmetric `nat` edge-colouring, no mono triangle) | **done** |
| seymours_self_minor_conjecture | D4inf2 | `∀ infinite G`, proper minor of itself; `minor_model` + 3-way `proper_witness` (vertex-del/contraction/edge-del) | **done** |
| strong_matchings_and_covers | D4inf4 | `iHypergraph`; edges≤k ⟹ strongly-maximal matching + strongly-minimal cover via `card_le` on symmetric differences | **done** |
| universal_highly_arc_transitive_digraphs | D4inf4 | `iDigraph`; HAT = UNFOLDED automorphism action on directed paths; `universal` via polarity-flipping `alt_walk`; guards has_arc+infinite+no_sink_source | **done** |
| end_devouring_rays | D4inf3 | combinatorial `end_equiv`; countable end + disjoint ω-rays ⟹ devouring reconfiguration + `same_start` | **done** |
| infinite_uniquely_hamiltonian_graphs | D4inf3 | loc-finite 1-ended r>2 regular; Hamilton circle **proxy** = spanning double ray (`int`-indexed) | **partial** |
| coloring_the_odd_distance_graph | D4inf5 | `iGraph` on `R*R` over `rcfType`, sqrt-free odd-distance; χ=∞ **proxy** = finite-subgraph unboundedness (reading-2) | **partial** |

**Vacuity guards that survived attack** (would trivialize/refute if dropped): seymours `proper_witness`
(the identity model provably fails it — `identity_not_proper`) + `infinite_graph` (finite G is refutable);
universal_HAT has_arc+infinite+no_sink_source (edgeless / finite directed cycle otherwise vacuous).
**Two proxies** (documented in file headers, kept partial): the double-ray surrogate for the Freudenthal
Hamilton circle (faithful only in the 1-ended locally-finite class), and reading-2 for χ=∞ (the
choice-free direction; converse is De Bruijn–Erdős) plus `∀R:rcfType` field-genericity.
**One recorded caveat** (not a defect): end_devouring_rays guards with whole-graph countability, stronger
than the source's *countable end* — it formalizes the countable-graph special case of Halin's theorem.

**4 rows stay BLOCKED**: hamiltonian_cycles_in_line_graphs / _in_powers (Freudenthal |G| + S¹ Hamilton
circle — genuine point-set topology), characterizing_aleph_0_aleph_1_graphs (uncountable cardinal *value*
ℵ₁ + no crisp consequent), highly_arc_transitive_two_ended_digraphs (Aut-group action + digraph-symmetry
collapse). After this track: **212 done / 8 partial / 7 blocked**.
