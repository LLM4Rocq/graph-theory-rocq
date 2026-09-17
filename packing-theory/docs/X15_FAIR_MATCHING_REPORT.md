# X15 — `bipartite_matching_underrepresentation`: proved

Target (in `packing-theory/theories/conjectures/X15.v`), arXiv:1611.03196
Conj. 1.15, with the explicit constant claimed by the LLM attack
(`attacks/1611.03196__03/output.md`):

```coq
forall m : nat, exists c : nat,
  c <= 32 * (m + 1)^3 /\
  forall (G : sgraph) (E : 'I_m -> {set {set G}}),
    bipartite G -> 0 < Delta G -> x15_edge_family E ->
    exists S, x15_matching S /\
      (#|x15_edge_set G| %/ Delta G <= #|S| + c)%N /\
      forall i, #|S :&: E i| <= ceil_div #|E i| (Delta G).
```

## 1. Verdict

**Proved**, with the constant `c(m) = (m+1)^2 (16m+29) <= 32(m+1)^3`.

All three live in `packing-theory/theories/foundations/fair_matching.v`:

| result | statement |
|---|---|
| `x15_llm_proof` | `bipartite_matching_underrepresentation_llm_statement` — with the attack's `c <= 32(m+1)^3` |
| `x15_llm2_proof` | `bipartite_matching_underrepresentation_llm2_statement` — with the constant actually obtained, `c <= (m+1)^2 (16m+29)` |
| `bipartite_matching_underrepresentation` | Conj. 1.15, no explicit constant |

Both are `Print Assumptions`-clean ("Closed under the global context"); no file
involved contains `Axiom`, `Parameter`, `Conjecture`, `admit` or `Admitted`
outside comments. `python3 meta/check_milestone.py X15 packing-theory` reports
`ACCEPTED: 11/11`, and the proof is registered in `meta/formal_resolutions.json`
under record key `1611.03196__03` (direction `prove`).

> The correspondence review recorded with that entry is **pending**: the
> registry entry names no independent reviewer. The formal statement it proves
> is the pre-existing, already-reviewed encoding in `X15.v`, unchanged.

## 2. The proof

Fix `G` bipartite with `D := Delta G > 0`, edge sets `E_1..E_m`, and write
`z(M) := (|M|, |M ∩ E_1|, …, |M ∩ E_m|)` for a matching `M`.

1. **König line colouring** — `E(G)` is the disjoint union of `D` matchings, so
   the target vector `(|E(G)|/D, |E_1|/D, …)` is the *average* of the `D`
   vectors `z(M_j)`.
   `ClassicalLemmas.konig.line_colouring.line_colouring_E`.
2. **Carathéodory over ℚ** — that average is a convex combination of at most
   `m+2` of the `z(M_j)`, with rational (here: cleared-denominator, natural)
   weights. `ClassicalLemmas.caratheodory.caratheodory.caratheodory_nat`.
3. **Halving two matchings with the Splitting Necklace Theorem** — for
   matchings `A`, `B` there is a matching `C ⊆ A ∪ B` with
   `|A| + |B| <= 2|C| + (16m+28)` and
   `2|C ∩ E_i| <= |A ∩ E_i| + |B ∩ E_i| + (8m+16)`.
   `matching_halving`, in `fair_matching.v`.
4. **Iterated interpolation** — a chain of halvings along the binary expansion
   of the weights realises the convex combination of step 2 with an error that
   does not grow with the number of bits.
   `mix_list`, in `fair_matching.v`.
5. **Trimming** — `trim_exists` (already in `fair_matching.v`) enforces the
   ceilings `⌈|E_i|/D⌉` by deletions, at a cost equal to the total excess; this
   is what turns the additive-error statement `x15_approx_fair` into X15 via
   the pre-existing `x15_approx_fair_instance`.

### The heart of step 3

Let `S := A △ B`. Every vertex meets at most one edge of `A` and one of `B`, so
the "share a vertex" relation on `S` has degree at most two; using the
bipartition it can be **oriented**, becoming a partial injection `nxt`
(`konig/paths2.v`). Closing `nxt` into a permutation and taking its orbits
linearises `S` into blocks along which consecutive edges meet.

The necklace is that sequence: one bead per (edge, statistic) pair, of type
`(which matching, which statistic)`, so `2(m+1)` types. `splitting_necklace_seq`
at `q = 2` gives each of two thieves *exactly* half of every type, with at most
`2(m+1)` cuts. Thief 0's `A`-edges and thief 1's `B`-edges are selected, and the
(few) conflicting edges are deleted: a conflict is a pair `{e, nxt e}` with
distinct thieves, hence lies at a cut or at the wrap of a non-monochromatic
block, so there are `O(m)` of them, and deletions only decrease every
coordinate.

Because the bead is the edge itself (refined per statistic), the shares are
exact and no dummy vertex, cell completion or perfect-matching padding is
needed — unlike the write-up's "cell = pair of edges with piecewise-constant
measures" presentation.

### The one deviation from the write-up

Step 3 of `attacks/1611.03196__03/output.md` uses a **prescribed-ratio**
continuous splitting theorem (its Lemma 1, Hobby–Rice style). That statement
does *not* follow from the equal-share Splitting Necklace Theorem with a cut
count independent of the ratio: reading `θ = a/q` off a `q`-splitting costs
`t(q-1)` cuts, so the error would grow with the denominator of `θ` and the final
constant would blow up.

Here **every interpolation is a halving** (`θ = 1/2`), and an arbitrary ratio is
realised by a **chain of halvings along the binary expansion** of a dyadic
approximation: `y_{L+1} = B`, `y_j = ½(P_j + y_{j+1})` with `P_j ∈ {A, B}` given
by bit `j`. Errors halve at each step, so `e <= e/2 + c` has fixed point `2c`:
the whole chain costs at most twice one halving, whatever the denominator. This
replaces the topological Lemma 1 by the necklace theorem we actually have, and
gives the same statement with a better constant.

## 3. Constant ledger

| quantity | value | where |
|---|---|---|
| one halving, scaled error `eh` | `16m + 28` | `mixing.eh`, from `matching_halving` |
| one dyadic chain | `eh + 1` per mixing step | `mix_dyadic` (fixed point of the halving recursion) |
| mixing `k <= m+2` matchings | `(size s).-1 * (eh + 1)` | `mix_list` |
| `Bmix m` | `(m+1)(16m + 29) <= 32(m+1)^2` | `fair_matching.Bmix`, `Bmix_le` |
| `c(m)` | `(m+1) * Bmix m = (m+1)^2(16m+29) <= 32(m+1)^3` | `x15_trim_instance`, `x15_approx_fair_instance`, `x15_llm2_proof` |

The last factor `m+1` is the trimming: the approximate fair matching is off by
`Bmix m` on every coordinate, and enforcing the `m` ceilings by deletion costs a
further `m * Bmix m` in size. `x15_trim_instance` states that step for an
arbitrary error `B`, which is what lets the exact constant be read off in
`x15_llm2_proof` instead of going through `32(m+1)^3`.

## 4. New code

All of it axiom-free. What is a classical lemma — reusable independently of
X15 — went to `classical-lemmas`, which depends only on mathcomp and
coq-graph-theory; the two developments that exist only for this proof (steps 3
and 4) live with the rest of the argument in `fair_matching.v`.

| file | lines | content |
|---|---|---|
| `classical-lemmas/theories/konig/paths2.v` | 783 | union of two matchings as chains of a partial injection; orbits, blocks, and the merge of two matchings |
| `classical-lemmas/theories/konig/line_colouring.v` | 427 | König's line-colouring theorem `χ' = Δ` for bipartite graphs, from Hall |
| `classical-lemmas/theories/caratheodory/caratheodory.v` | 320 | Carathéodory's theorem over ℚ, and its cleared-denominator form |
| `packing-theory/theories/foundations/fair_matching.v` | 2140 | steps 3 (`matching_halving`) and 4 (`realisesN`, `mix_dyadic`, `mix_list`), then the whole assembly: `x15_approx_fair_proof`, `x15_llm_proof`, `x15_llm2_proof`, `bipartite_matching_underrepresentation` |

`classical-lemmas/theories` was reorganised into `necklace/`, `konig/` and
`caratheodory/` (logical names `ClassicalLemmas.necklace.*` etc.);
`packing-theory` now depends on `classical-lemmas`
(`-Q ../classical-lemmas/theories ClassicalLemmas`, and the root `Makefile`
orders the two packages).

The topological input is
`ClassicalLemmas.necklace.necklace.splitting_necklace_seq` (Alon 1987, via
Meunier's simplotopal Tucker lemma), formalised earlier in this repository.

## 5. What `fair_matching.v` already contained

Unchanged and still used: `x15_edge_setE`, `matching_x15`, `x15_matching_sub`,
`edges_leq_cover`, `x15_big_matching` (König min-cover = max-matching),
`trim_exists`, `x15_approx_fair_instance`, `x15_approx_fair0`,
`x15_llm_instance0`. Section 4 of the previous version of this report listed
steps 1–4 as "not formalised"; that list is now the table of §4 above, with the
prescribed-ratio splitting of its item 3 replaced as described in §2.

## 6. Tooling note

Throughout this phase the `rocq-mcp-evolve` MCP server could not resolve any
`ClassicalLemmas.*` module: its cached project configuration predated the move
into subdirectories (a server restart is needed; `.vos` files were also
required, `make -f Makefile.coq vos`). Goals were read instead from a small
`rocq repl` harness and files recompiled with `rocq c`. Every recurring error
and its fix is appended to `tactics-playbook.md` (entries 84–98).
