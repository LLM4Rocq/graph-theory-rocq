# Contributing

Thanks for your interest in `digraph-theory`.

## Ground rules

- **Read [`docs/DESIGN.md`](docs/DESIGN.md) first.** It fixes the layering, the
  representation decisions (digraph = relation over a finType; tournament as an HB
  structure; orders as `{perm V}`; `ω̄` via `omega` of the backedge graph at the
  `arg min` order), and the open decisions (§10).
- **Layering is strict.** A module may only import from the same or lower layers
  (`foundations < core < invariants < constructions < applications`). In
  particular, `coq-graph-theory` is imported in exactly one file,
  `foundations/interop_graph_theory.v` — do not import it elsewhere.
- **Reuse over reinvention.** Undirected `ω`/`α`/`χ`/cliques come from
  coq-graph-theory; finite groups, `'Z_n`, permutations, `arg min` from MathComp.
  Don't reimplement these.

## Style

- Lowercase file names (`tournament.v`), MathComp/SSReflect proof style.
- Each new public definition gets a one-line doc comment; each milestone updates
  `CHANGELOG.md`.
- Keep `make` green; add a smoke/regression check when a definition is meant to
  *compute* (cross-check against the Python oracle where one exists).

## Workflow

1. Branch from `main`.
2. `make` must pass locally before opening a PR.
3. Reference the milestone (M1…M6) and the relevant `docs/DESIGN.md` section.
