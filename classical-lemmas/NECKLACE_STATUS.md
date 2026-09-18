# Necklace splitting (Meunier 2014) — formalisation status

Target: Alon's Splitting Necklace Theorem via Meunier, "Simplotopal maps and
necklace splitting", Discrete Math. 323 (2014), starting (per request) from the
ℤ_p-simplotopal Tucker lemma (Theorem 3.3) and its HSSZ/Meunier-2006 cochains.

**The development is COMPLETE.**  The headline result is

```coq
Theorem splitting_necklace_theorem (n t q : nat) (c : 'I_n -> 'I_t) :
  0 < q -> (forall k : 'I_t, q %| #|[set i | c i == k]|) ->
  exists a : 'I_n -> 'I_q,
    #|[set pr : 'I_n * 'I_n | (pr.2 == pr.1.+1 :> nat) && (a pr.1 != a pr.2)]|
      <= t * q.-1
    /\ forall (k : 'I_t) (j : 'I_q),
         #|[set i | (c i == k) && (a i == j)]| = #|[set i | c i == k]| %/ q.
```

in `theories/necklace/necklace.v`; `Print Assumptions` = "Closed under the global
context".

All files below compile with Rocq 9.1.1 + mathcomp and are `Print Assumptions`
clean ("Closed under the global context"); no `Axiom`/`Admitted`/`admit`.

## Provenance

Every `.v` file opens with a `Provenance, sources, and what corresponds to what`
comment giving, for that file: how it was produced, which models produced it and
at what measured token cost, the papers it formalises, and a
statement-by-statement correspondence between the paper and the Rocq names.

Produced with Claude Code (Anthropic), driving Rocq interactively through the
`rocq-mcp-evolve` MCP server — developed by the LLM4Rocq project,
<https://github.com/LLM4Rocq/rocq-mcp-evolve> (Apache-2.0; the opam package
still carries its former slug `LLM4Rocq/rocq-tools`), gratefully acknowledged.
Three models were used, in this order:

| model | when (UTC) | what |
|---|---|---|
| Claude Fable 5.1 | 14 Sep 20:52 – 22:46 | plan, `chains.v`, `necklace_complex.v`, the sequence layer of `necklace.v`, first half of `salt.v` |
| Claude Opus 4.8 | 14 Sep 22:48 – 15 Sep 06:39 | rest of `salt.v`, `cubical.v`, most of `hemispheres.v` |
| Claude Opus 5 | 15 Sep 06:39 – 18:31 | end of `hemispheres.v`, `simplotope.v`, `chainmap.v`, `bar.v`, `eta.v`, `tucker.v`, `necklace_prime.v`, end of `necklace.v` |

Token cost per file, estimated from the logs of the Claude Code session of
14–15 September 2026 (input + cache-creation + output tokens, i.e. tokens
processed anew; the cached context re-read at every turn, 772M over the
project, is excluded):

| file | lines | Fable 5.1 | Opus 4.8 | Opus 5 | total | output |
|---|---:|---:|---:|---:|---:|---:|
| `chains.v` | 260 | 62k | — | 139k | **201k** | 47k |
| `necklace_complex.v` | 101 | 1k | 25k | 8k | **35k** | 12k |
| `salt.v` | 532 | 355k | 73k | 186k | **615k** | 296k |
| `cubical.v` | 269 | — | 267k | 5k | **272k** | 108k |
| `hemispheres.v` | 729 | — | 384k | 73k | **457k** | 211k |
| `simplotope.v` | 967 | — | — | 627k | **627k** | 248k |
| `chainmap.v` | 362 | — | — | 123k | **123k** | 41k |
| `bar.v` | 579 | — | — | 263k | **263k** | 104k |
| `eta.v` | 697 | — | — | 271k | **271k** | 111k |
| `tucker.v` | 745 | — | — | 337k | **337k** | 105k |
| `necklace_prime.v` | 861 | — | — | 346k | **346k** | 135k |
| `necklace.v` | 442 | 275k | — | 277k | **551k** | 207k |
| **total** | **6544** | **693k** | **749k** | **2654k** | **4.10M** | **1624k** |

On top of that, three whole-session context rebuilds (compaction / resume) cost
1.61M tokens and are charged to no file, so the project total is **5.70M
tokens** processed anew (4.10M of it per-file work), plus 772M of cached
context re-reads.

Per stage:

| stage | files | tokens | output |
|---|---|---:|---:|
| infrastructure | `chains.v`, `necklace_complex.v` | 235k | 59k |
| Stage A - cochains | `salt.v` | 615k | 296k |
| Stage B - cubical complex + hemisphere chains | `cubical.v`, `hemispheres.v` | 728k | 319k |
| Stage C - simplotopal complex + induced chain map | `simplotope.v`, `chainmap.v` | 750k | 289k |
| Stage D - bar resolution + eta_# | `bar.v`, `eta.v` | 534k | 214k |
| Stage E - proof of Theorem 3.3 | `tucker.v` | 337k | 105k |
| Meunier 3.2-3.4 - prime case of Alon | `necklace_prime.v` | 346k | 135k |
| Meunier 3.1 - reduction to prime q + assembly | `necklace.v` | 551k | 207k |
| context rebuilds (x3) | — | 1605k | — |
| **total** | | **5.70M** | **1624k** |

Sources:

- **[M14]** F. Meunier, *Simplotopal maps and necklace splitting*, Discrete
  Mathematics **323** (2014) 14–26. (`Meunier2014-Simplotopal_Necklace_web.pdf`)
- **[A87]** N. Alon, *Splitting necklaces*, Advances in Mathematics **63**
  (1987) 247–253.
- **[HSSZ]** B. Hanke, R. Sanyal, C. Schultz, G. M. Ziegler, *Combinatorial
  Stokes formulas via minimal resolutions*, J. Combin. Theory Ser. A **116**
  (2009) 404–420. (`HankeSSZ-...-main.pdf`)
- **[M06]** F. Meunier, *A Z_q-Fan theorem*, technical report, "Topological
  combinatorics" workshop, Stockholm, 2006. (`Meunier2006-zqkyfan.pdf`)

## Done

- `theories/necklace/chains.v` — free chains `{ffun cell -> R^o}` over a ring: basis
  chains `cc`, linear extension `lin`, `lin_cc/linD/linZ/linB/lin_sum/lin_comp`,
  and `chain_ext` (two additive homogeneous maps agreeing on cells are equal).
- `theories/necklace/necklace_complex.v` — the complexes K = R^N|_X and L = (Δ_{p-1})^t
  of §3.2 as concrete finite objects (`vertex`, `covers`, `in_X`, `slide`,
  `vert`, `face`, `shiftp`, `shift_vertex`, `image_set`, `equivariant`,
  `simplotopal`) and the statement `zp_tucker` (Theorem 3.3 for these K, L).
- `theories/necklace/salt.v` — **Stage A: the co-hemisphere cochains and their two
  Stokes relations, fully proved.** Value-sequence model of HSSZ's
  `u ∘ f_d ∘ h`: `dmod` (mod-p difference), `diffs`, `salt` (strongly
  alternating, Def. 3.5), `mergeat`/`delete` (face maps of a simplex), the
  cyclic shift `sh`/`shiftv`, and the cochains `Phi d`. Key results:
    - `salt3`, `sigma_count`, `salt_merge_sum` — the arithmetic core;
    - `Phi_bd_even`: φ_{2l} ∘ ∂ = φ_{2l+1} ∘ (ν − id);
    - `Phi_bd_odd` : φ_{2l+1} ∘ ∂ = φ_{2l+2} ∘ (Σ_r ν^r);
    - `Phi0_shift` : Σ_r φ_0(ν^r v) = 1  (base case of the induction).
  These are exactly relations (3.8)/(4) of HSSZ/Meunier-2006 evaluated at the
  neutral element, i.e. the dual "(2)/(4)" hemispheres of the ℤ_p-Fan proof.

## Done (Stage B foundation)

- `theories/necklace/cubical.v` — **the cubical chain complex of R^N, fully proved and
  axiom-free.** Cells `cellN := {ffun 'I_N -> cell1}` (`cell1 = vertex + edge`),
  dimension = #edge-coordinates, cubical boundary `bd` oriented by coordinate
  order. Face calculus (`fvC`, `is_edge_fv`, `rk_fv`), and the keystone
  **`bd_bd : bd (bd x) = 0`** (∂∂=0), proved over any commutative ring via a
  diagonal-pairing argument valid in characteristic 2 (`sum_pair_anti`,
  `Tterm_anti`, `bd_bd1`). `Print Assumptions bd_bd` = Closed under the global
  context. This is the backbone for the hemisphere chains.

## Done (Stage B — hemisphere chains, COMPLETE)

- `theories/necklace/hemispheres.v` (729 lines) — **Stage B in full, axiom-free.** On top of
  `cubical.v` it adds the cyclic ℤ_p action `nu`, the operator `sigma = Σ_r ν^r`
  (with `nu` a chain map: `bd_nu`/`bd_sigma`; `nu^p = id`; `(ν−id)∘σ = σ∘(ν−id) = 0`),
  the path chain `P_1` (`consP`) with its boundary (`bd_P1` by telescoping) and the
  **front-factor boundary law `bd_placeP1`** (Lemma 2.3 for prepending `P_1`), and the
  hemisphere chains `htil`/`h` (formulas (5)–(7)). Deliverables, all `Print Assumptions`
  clean:
    - `h0_val` : `h_0 = (o,…,o,(n,1))` (the base vertex);
    - `hrel` / `hrel_odd` / `hrel_even` : `∂h_{2l+1} = Σ_r ν^r h_{2l}` and
      `∂h_{2l} = (ν−id) h_{2l−1}`;
    - `h_inK` : `h_d ∈ C(K)` (every cell of `h_d` has a full-path top-vertex coordinate,
      hence all its vertices lie in `X`).
  Char-`p` enters only through `sigma (cc o_cell) = 0` (hypothesis `p%:R = 0`; the intended
  ring is `'F_p`).

## Done (Stage C — the induced chain map, COMPLETE)

- `theories/necklace/simplotope.v` (~840 lines) — **the simplotopal complex `L = (Δ_{p-1})^t`,
  its chain complex, the facet-kernel lemmas and the ℤ_p action, all axiom-free.**
  Cells `Lcell := {ffun 'I_t -> {set 'I_p}}`, dimension `Ldim σ = Σ_i (|σ_i| - 1)`,
  boundary of §2.3 (`Lbd`, oriented by the increasing order in each factor and by the
  factor order). Results:
    - `Lbd_bd` : ∂∂ = 0 (same characteristic-2-safe pairing as `cubical.v`);
    - `Lfacet_inj`, `double_facet_uniq` : a facet, resp. a codimension-2 face, determines
      the removal(s) that produced it;
    - `Lsub_eq`, `Lsub_facet`, `Ldim_Lfacet`, `Ldim_valid` : sub-simplotopes of
      codimension 0 and 1;
    - **`Lfacet_ker2`** (Meunier's Lemma 2.1 + "corollary of Lemma 2.2"): if a combination
      of the facets of σ has zero boundary and `dim σ ≥ 2`, all its coefficients agree up
      to the induced orientations; **`Lfacet_ker1`** : same in dimension 1, from the
      augmentation instead of the boundary;
    - ℤ_p action: `Lsh` (cyclic shift of every factor), `esgn`, the induced chain map
      `Lnu` and **`Lbd_Lnu` : ∂ ∘ ν_# = ν_# ∘ ∂** (the shift is not orientation
      preserving; the sign is the parity identity `odd_sign_key`).

- `theories/necklace/chainmap.v` (~340 lines) — **Meunier's Theorem 2.4, axiom-free.** For an
  abstract graded source complex (`cellS`, `dimS`, `bdS1`, a subcomplex predicate `okS`)
  and a map `msp` sending a cell to the smallest simplotope of `L` containing its image,
  with the simplotopal hypothesis `Ldim (msp c) <= dimS c`, it builds
  `mu1 c = α_c ⋅ (msp c)` by recursion on the dimension and proves:
    - **`mu_bd`** : `∂ ∘ μ_# = μ_# ∘ ∂` on chains supported in the subcomplex;
    - **`mu_dim`** : `μ_#σ ≠ 0 ⟹ Ldim (msp σ) = dimS σ`, i.e. σ is mapped onto a
      simplotope of full dimension — the form used at the end of the proof of Theorem 3.3;
    - **`mu_nu1` / `mu_equiv`** : ℤ_p-equivariance, `μ_# ∘ ν = ν_# ∘ μ_#`, for any
      equivariant action on the source (`nuS_dim`, `nuS_msp`, `nuS_bd`).

  `theories/necklace/chains.v` gained `scale_ffunE`, `lin_eq_supp`, `chain_supp1`, `lin_sum_cond`.

## Done (Stage D — η_#, COMPLETE)

**Design change, deliberate.** Meunier sends `η_#` into the join `ℤ_p^{*N}`, which
forces the whole of his §2.6 (barycentric subdivision `sd_#`, Lemmas 2.5–2.7,
Prop. 2.8) plus a connectivity argument, because the join is only `(N-2)`-connected.
We send it instead into the **homogeneous bar resolution `EℤZ_p`**, which is the
complex Hanke–Sanyal–Schultz–Ziegler's cochains actually live on — and which
`salt.v` was already written for: `Phi d s` depends only on the residue sequence
`s` of length `d+1`, and its face maps are `delete i`.  `EℤZ_p` is CONTRACTIBLE,
with the one-line contraction "prepend the neutral element", so the equivariant
chain map is built by a plain induction on the dimension.  Nothing downstream
changes: the final argument of Theorem 3.3 never uses the join, only that `η_#`
is an equivariant chain map and that `Σ_r φ_0(ν^r η_#(v)) = 1` (our `Phi0_shift`).

- `theories/necklace/bar.v` (579 lines, axiom-free) — the bar complex of `ℤ_p`, truncated at
  length `M`, and the cochains.  A `d`-cell is a sequence of `d+1` residues, stored
  as an `M`-tuple padded with `None` (`padd` / `sqB` are the two directions; all
  combinatorics is done on plain sequences).  Contents:
    - `dels` (delete one entry) with the simplicial identity `dels_dels`;
    - the boundary `bdB` and **`bdB_bd` : ∂∂ = 0**, by a sign-reversing involution
      on pairs of deletion indices (`sum_invol`, new in `chains.v`, char-2 safe);
    - the ℤ_p action `nuB` with **`bdB_nuB` : ∂ ∘ ν = ν ∘ ∂** and `nuB_iter_p` :
      `ν^p = id` on normalised chains;
    - the contraction `DB` (prepend `0`), with **`bdB_DB_hom`**: a homogeneous cycle
      of dimension `k-1` (with vanishing augmentation when `k = 1`) satisfies
      `∂ (D z) = z`;
    - the HSSZ cochains `phi d` and the two Stokes relations as chain identities,
      **`phi_bd_even`** : `φ_{2l} ∘ ∂ = φ_{2l+1} ∘ (ν − id)`,
      **`phi_bd_odd`** : `φ_{2l+1} ∘ ∂ = φ_{2l+2} ∘ (Σ_r ν^r)`, and the base case
      **`phi0_orbit`** : `Σ_r φ_0(ν^r c) = 1` for a vertex — all lifted from
      `salt.v`'s `Phi_bd_even` / `Phi_bd_odd` / `Phi0_shift`.

- `theories/necklace/eta.v` (683 lines, axiom-free) — **the equivariant chain map
  `η_# : C(∂L) → C(EℤZ_p)`.**  Here `p` must be PRIME (Hypothesis `p_prime`), and
  `t > 0`.  Contents:
    - the cyclic shift as a permutation of `ℤ_p` (`iter_shp_inj`, `iter_shp_idx`,
      `iter_shp_surj`) and, for `p` prime, `iter_shp_mul_surj` /
      `shp_invariant_full`: a nonempty proper subset of `ℤ_p` cannot be invariant
      under a nontrivial power of the shift;
    - `∂L` as `okL` (all factors nonempty, not the top simplotope), closed under
      facets (`okL_facet`), with `Ldim s < t(p-1)` (`okL_Ldim`), and the FREE ℤ_p
      action `Lshk` on it (`Lshk_free`, `Lshk_idx`);
    - orbit representatives `repL` / `jofL` (smallest `enum_rank` in the orbit) with
      `repL_shk`, `Lshk_jofL`, `jofL_shL`;
    - the sign cocycle `Esg` along an orbit and **`Esg_p_even`** : `Σ_{i<p} esgn(ν^i r)`
      is even — this is what makes the SIGNED action `Lnu` on `C(L)` an action of
      ℤ_p, and what makes the construction consistent at the wrap-around;
    - the map itself, `eta1 s := ef (Ldim s) s` with
      `ef d.+1 s = ±ν^{jofL s} (D (Σ_facets ef d))` at the representative;
    - **`eta_bd` / `eta_chainmap`** : `∂ ∘ η_# = η_# ∘ ∂` on chains supported in `∂L`;
    - **`eta_equivariant`** : `η_# ∘ ν = ν ∘ η_#`;
    - **`eta_vertex`** : `η_#` of a vertex is a single bar 0-cell;
    - `ef_okB` : `η_#` of a `d`-cell is supported on bar cells of size `d+1`.

  `theories/necklace/chains.v` gained `sum_invol`, `lin_cc_id`, `supp_bigsum`, `sum_cc_aug`,
  `aug_bigsum`, `aug_lin`; `theories/necklace/simplotope.v` gained `Lbd1_aug` (the
  augmentation of the boundary of a 1-dimensional simplotope vanishes).

## Done (Stages C-glue + E — `zp_tucker` for prime `p`, COMPLETE)

- `theories/necklace/tucker.v` (~750 lines, axiom-free) — **the ℤ_p-simplotopal Tucker lemma
  (Meunier, Theorem 3.3) for prime `p`.**  Three layers:
    - *N-generic cubical facts* (`Section CubFacts`): support of `bd1`
      (`bd1_supp`), its augmentation (`bd1_aug`), `dimN_fv`, `inK_fv`,
      `dimN_shift`, and the vertex/edge computation of `vsel`.
    - *dimension homogeneity* (`Section Homog`): `homd k x` ("every cell of `x`
      has dimension `k`") with closure under `+`, `-`, `*:`, `Σ`, `lin`, `ν`,
      `σ`, `∂`, `consP`, and **`homd_h` : the hemisphere chain `h_d` is
      homogeneous of dimension `d`**.
    - *the glue* (`Section Glue`): the bridge between the cell representation
      `cellN` of `cubical.v` and the `(u, S)` representation of a face in
      `necklace_complex.v` — `uof`, `Sof`, `vert_vsel`, `face_inK`,
      `image_mspN`, `card_Sof` — and the smallest simplotope `mspN c` containing
      the image of a cell.  With `simplotopal lam` this gives the eight
      hypotheses of `chainmap.v`, hence the induced chain map `muK` with
      `muK_bd`, `muK_dim`, and (with `equivariant lam`) `muK_equiv`.
    - *the assembly* (`Section Induced`, with `0 < n`, `0 < t`, `prime p`,
      `p%:R = 0`): `EK x := η_#(μ_#(x))`, `Psi d x := φ_d(EK x)`, the support
      predicate `goodK`, the two transported Stokes relations `Psi_bd_even` /
      `Psi_bd_odd`, then Meunier's induction
      `baseA`/`stepA`/`stepB`/`indA`/`indB` up to
      **`keyD` : `Ψ_{D-1}(∂ h_D) = 1`** with `D = t(p-1)`.  Since `Ψ` factors
      through `μ_#`, this forces `μ_#(h_D) ≠ 0` (`muK_hD_neq0`), hence a cell
      `c` of `K` with `dim c = D` whose smallest simplotope has dimension `D`
      (`muK_dim`), i.e. is the top simplotope of `L` (`key_cell`).
    - **`zp_tucker_prime n t p p_gt0 : prime p -> 0 < t -> zp_tucker n t p p_gt0`**
      — `Print Assumptions` = "Closed under the global context".  The ring is
      instantiated to `'F_p` (`pchar_Fp` gives `p%:R = 0`).

## Done (Meunier §3.2–3.4 — the prime case of Alon's theorem)

- `theories/necklace/necklace_prime.v` (~860 lines, axiom-free) — **the "winner" map λ and
  Meunier's Lemmas 3.2 and 3.4.**  Contents, in the vocabulary of §3.2:
    - *the splitting encoded by a vertex*: `jw v b` is the FIRST coordinate of
      `v` whose cut lies strictly to the right of bead `b` (this is exactly
      `covers (v j) b`), and `own v b` is the thief it carries.  This is
      Meunier's rule "take `v_j = (k,r)` with the smallest `j` such that
      `k ≥ y`", read one bead at a time.  `jw` is nondecreasing in `b`
      (`jw_mono`), which is what bounds the number of cuts (`card_cutset`:
      at most `N - 1 = t(p-1)`).
    - *the `i`-winner* `lam v i`: the thief maximising
      `sc v i r = (#i-beads of r) * n.+1 + (rightmost i-bead of r)` — the count
      with Meunier's "rightmost bead" tie-break packed into a single number, so
      that the maximiser is unique (`sc_inj`) and `lam` is ℤ_p-equivariant
      (`lam_shift`, `lam_equivariant`).
    - *a face `(u, S)` of `K`*: the cuts of `S` sliding on bead `b`
      (`Sb b`) resp. on beads of type `i` (`Si i`, of cardinality `di i`).  The
      owner of `b` depends on the face vertex only through `T ∩ Sb b`
      (`own_dep`), hence `lam _ i` only through `T ∩ Si i` (`lam_depi`) — this
      is Meunier's "the positions of the sliding cuts can be chosen
      independently for each type".
    - *the special vertex* `vst`: for each type independently, the position
      `Topt i` of the `i`-cuts minimising the winner's score (`scw_min`).
    - CLAIM 3 (`card_Fb`): at most `#|Sb b| + 1` thieves can get bead `b` —
      proved by injecting the reachable first-covering coordinates into
      `Sb b` via the predecessor map `psi`;
      CLAIM 1 (`claim1`) and CLAIM 2 (`claim2`) as in the paper.
    - **`card_W` : `#|W i| ≤ d_i + 1`**, hence **`lam_simplotopal`**
      (Meunier's Lemma 3.2).
    - **`fair_vst`** (Meunier's Lemma 3.4): applying `zp_tucker_prime` to `lam`
      gives a face with `#|S| = t(p-1)` and every `W i` full, which forces
      `d_i = p-1` and `g i r = 1` for every non-winner, so every thief gets
      `M-1` or `M` beads of each type in `vst`; with `p | A_i` this pins every
      count to `A_i / p`.
    - **`necklace_prime`**: for prime `p`, every necklace has a `p`-splitting
      with at most `t(p-1)` cuts that is exactly fair on every type whose count
      is a multiple of `p`.  Types that do not occur are relabelled away first
      (λ cannot be both equivariant and simplotopal when some type is absent).

## Done (§3.1 — the reduction to prime `q`, and the theorem)

- `theories/necklace/necklace.v` (442 lines, axiom-free) — the "well-known trick" and the
  final assembly:
    - `cuts` / `fair` / `necklace_splitting_stmt` over ordinals, and
      `cuts_seq` / `count_pair` / `necklace_seq_stmt` over sequences;
    - `glue` (composing a `q1`-splitting with a `q2`-splitting on each thief's
      sub-necklace) with `glue_count` and `glue_cuts`, giving
      **`necklace_seq_mul`** and hence **`necklace_seq_of_prime`**;
    - the bridge between the two forms — `cuts_sum`, `cuts_seq_sum` and
      **`cuts_seq_mapE` : `cuts_seq [seq a i | i <- enum 'I_n] = cuts a`** —
      and the two translations `necklace_seq_of_stmt` / `necklace_stmt_of_seq`;
    - **`necklace_splitting`** : `0 < q -> necklace_splitting_stmt q`, and its
      spelled-out form **`splitting_necklace_theorem`** (plus the sequence
      version `splitting_necklace_seq`).

## The rest of the package: `konig/` and `caratheodory/` (16 Sep 2026)

`theories/` is split into three subdirectories, all under the logical root
`ClassicalLemmas`: `necklace/` (everything above), plus two more built for the
first client of the necklace theorem, Conjecture 1.15 of arXiv:1611.03196
(`packing-theory`, milestone X15 — see
`packing-theory/docs/X15_FAIR_MATCHING_REPORT.md`).

| file | headline |
|---|---|
| `theories/konig/paths2.v` | the union of two matchings, oriented by the bipartition into a partial injection: `nxt_inj`, `meetP`, `blocks`, `block_nth`, and `merge_matching` |
| `theories/konig/line_colouring.v` | König's line-colouring theorem: `line_colouring`, `line_colouring_E` (`χ'(G) = Δ(G)` for bipartite `G`), with `Hall_sat` |
| `theories/caratheodory/caratheodory.v` | Carathéodory's theorem over ℚ: `caratheodory`, `caratheodory_nat` |

Same conventions as above: axiom-free, `Print Assumptions`-clean, and every file
opens with its own `Provenance, sources, and what corresponds to what` comment.

The two developments that are *not* classical — the interpolation of two
matchings by a necklace splitting, and the chains of halvings that realise an
arbitrary convex combination of matchings — live with their only client, in
`packing-theory/theories/foundations/fair_matching.v`.
