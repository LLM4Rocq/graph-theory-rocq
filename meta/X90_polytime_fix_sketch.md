# X90 — what a faithful poly-time fix would take (design sketch)

> Companion to `meta/X10-X110_faithfulness_audit.md` (X90, the one deferred defect). X90 encodes the
> Bang-Jensen *F-Subdivision* complexity dichotomy: *for every fixed digraph F, deciding whether an
> input digraph contains a subdivision of F is polynomial-time solvable or NP-complete.* The current
> encoding is vacuous. This sketch says exactly why, what a faithful fix requires, three candidate
> designs (adversarially vacuity-checked), and the recommended path.
>
> **Status (2026-07-11): X90 is now tracked `blocked`** in the corpus (v2 statement legs: 277 done /
> 1 blocked). This sketch is the record of what a faithful fix would require; it has not been built.

## Why X90 is uniquely hard among the batch

Every other defect was a wrong hypothesis or definition — a one-region edit. X90 is different: the
statement quantifies over **"there exists a polynomial-time algorithm,"** and *the codebase has no
notion of an algorithm's running time.* A Coq function `diGraphType -> bool` has **no intrinsic
runtime**, so binding a polynomial to a *separate* `cost` function (what the current code does) is
meaningless — `cost := fun _ => 0` always satisfies it. Concretely the current definitions collapse:
`x90_in_np P` holds for **every** `P` (`cert_size := 0`), and `x90_polynomial_time_decidable` reduces to
bare classical decidability. The `cost`/`cert_size` fields are free parameters decoupled from any
computation.

**The fix is therefore not an edit but a new foundation:** a model of computation in which running time
is *defined by an operational semantics*, so "polynomial time" is a bound on an actual step count.

## What "faithful" requires (five ingredients)

1. **Programs are reified as first-order DATA** (not Coq functions), with a decidable syntax — so
   "a program" is a finite value with no smuggled-in oracle.
2. **An operational semantics with a step measure**: `run : prog -> input -> fuel -> result`, where the
   step count is a *deterministic function of (prog, input)*, not a choosable parameter.
3. **An input encoding** `enc : diGraphType -> bitstring` with `size (enc D)` polynomially related to
   `#|D|`, anchored to the corpus object (`enc` faithful to `contains_subdivision`).
4. **P / NP / reductions bound that step count**: `in_P` = a program that decides the language and
   *halts within a polynomial number of its own steps*; `in_NP` = a poly-size certificate + a
   *verifier program* that accepts within poly steps; `≤p` = a function computed by a poly-time program.
5. **A non-empty complete class**: `NP_hard` quantifying over *all* NP languages (Cook–Levin gives an
   inhabited complete problem), so the right disjunct is a real target, not an empty type.

## Three candidate designs (all adversarially vacuity-checked)

| | Approach A — import L-calculus complexity lib | **Approach B — minimal in-repo TM cost model** | Approach C — abstract class interface |
|---|---|---|---|
| **What** | Reuse `coq-library-complexity` (Forster/Kunze/Gäher: L's β-step cost, Cook–Levin, `inP`/`inNP`/`NPcomplete`, `⪯p`) | Reify a tiny single-tape TM as data; fuel-indexed `run`; time = actual steps | A `ComplexityModel` record axiomatizing the laws (P⊆NP, ≤p preorder, NP closed under ≤p, ∃ complete problem); state dichotomy `∀ M, …` |
| **Faithfulness** | **Gold standard** — literally the community's defs; L's step count is a *proved-reasonable* time measure (mechanized Time-Invariance Thesis) | High — cost = real step count of a reified program, anchored to the corpus predicate | Only if instantiated by a real model; **an abstract/degenerate model can make it vacuous** |
| **Feasible in this switch?** | **No.** The lib is Coq-8.16-only; the corpus needs ≥8.18/9.1 — disjoint opam constraints, no 9.x port. Forward-port = expert, *months*, metacoq-extraction risk | **Yes.** mathcomp-only; no new deps; axiom-free | Yes (builds now), but not a standalone remedy |
| **Effort / size** | Months + ~700–1500 LOC bridge — disproportionate | **~3–6 person-days, ~300–330 LOC, one module** | 1–2 days, ~150–200 LOC — but the real payload is still A/B |
| **Verdict** | North-Star yardstick; **do not pursue** here | **Recommended** feasible fix | Optional structuring layer *on top of* B |

## Recommended path — Approach B (self-contained TM cost model)

One new module (e.g. `digraph-theory/theories/foundations/tm_cost.v`), imported by `X90.v`, no new
opam dependency, axiom-free. Condensed skeleton:

```coq
(* A. Machine — every field is DATA (finfun transition = a finite TABLE, not a function) *)
Record TM := { tm_n : nat;
  tm_trans : {ffun 'I_tm_n.+1 * symbol -> option ('I_tm_n.+1 * symbol * dir)};  (* None = halt *)
  tm_acc : {set 'I_tm_n.+1} }.
Fixpoint run (M:TM) c fuel := (* FREEZES at the first halting config; step reads ONE (state,symbol) *) …
Definition result M x fuel : option bool := (* Some (accepted) once halted, else None *) …
Definition output M x fuel : option (seq bool) := (* decoded tape = the function value *) …

(* B. Encoding — adjacency matrix in Finite.enum order; size = #|D|^2, anchored to the corpus *)
Definition enc (D:diGraphType) : seq bool := flatten [seq [seq arc u v | v <- enum D] | u <- enum D].

(* C. Classes — the polynomial bounds the ACTUAL step budget (x90_poly_eval reused unchanged) *)
Definition in_P (L:Lang) := exists M p, forall x, exists b,
  result M x (x90_poly_eval p (size x)) = Some b /\ (b <-> L x).
Definition in_NP (L:Lang) := exists (V:TM) p q, forall x, L x <-> exists w,
  size w <= x90_poly_eval q (size x) /\ result V (pair_in x w) (x90_poly_eval p (size x)) = Some true.
Definition many_one_reduces L1 L2 := exists M f, poly_computes M f /\ forall x, L1 x <-> L2 (f x).
Definition NP_complete L := in_NP L /\ (forall L', in_NP L' -> many_one_reduces L' L).

(* D. Wrappers keep the x90_* names (manifest-stable); lang_of lifts a digraph predicate to a language *)
Definition f_subdivision_complexity_dichotomy_statement := forall F : diGraphType,
  x90_polynomial_time_decidable (contains_subdivision F) \/ x90_np_complete (contains_subdivision F).
```

**Why the vacuity is destroyed (the point of the whole exercise):** `cost`/`cert_size` no longer exist.
The old trivial witnesses stop type-checking — `in_NP` has no `cert_size` field, so an always-reject
verifier witnesses only the *empty* language and always-accept only the *full* one; a nontrivial `L`
forces a genuine verifier. `in_P` bounds `result M x (poly …)`, the machine's *actual* output after that
many steps, so `p := [::]` (budget 0) gives `result = None` and correctness fails for any non-constant
problem. Fuel is *forced* large enough for the machine to finish and be right.

**Three things that would silently reintroduce vacuity — forbid in review:** (a) making `tm_trans` a
`nat -> …` function instead of a `finfun` over a finite type (program becomes an arbitrary Coq function
again); (b) defining `result` to ignore fuel; (c) reintroducing any free `cost`/`cert_size` field.

**Known honest limitations (flag in-source, not bugs):** single-tape + adjacency-matrix ⇒ bounds are
class-invariant but *not degree-exact* (fine for a P-vs-NPc dichotomy, wrong for fine-grained
complexity); the top-level `\/` is a *constructive* disjunction (slightly stronger than the classical
reading — weaken to `~(~A /\ ~B)` if strict classical intent is wanted); `pair_in` must be a prefix-free
(length-prefixed) pairing or the verifier can't split instance from certificate.

## The actual decision for the campaign

Approach B is ~1 person-week of fiddly-but-standard mathcomp work for **one** conjecture row. Two
honest options:

1. **Invest** in `tm_cost.v` as a *reusable* poly-time foundation. Worth it only if other
   complexity-flavored conjectures are coming (then the cost amortizes and X90 becomes a thin wrapper).
2. **Reclassify X90 as `blocked` — "needs a complexity-theory layer, deliberately out of scope"** —
   exactly the existing `CORPUS_STATUS.md` category for the topological crossing-number rows awaiting a
   drawing/rotation layer. This is the honest status: the current statement is *not* faithful, and a
   faithful one requires a foundation the corpus deliberately doesn't have yet.

**Recommendation:** unless a wave of complexity-theory conjectures is planned, **mark X90 `blocked`**
(with a pointer to this sketch) rather than ship the vacuous statement as `done`. Approach A stays the
faithfulness yardstick; Approach C is only worth building as a thin layer *after* B exists.
