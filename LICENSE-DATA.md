# Data / embedded-statement licence notice

The **code** in this repository (Rocq sources, Python tooling, build files) is licensed
under Apache-2.0 (see `LICENSE`). The **third-party problem-statement texts embedded in
the metadata** are not ours to re-license and carry their upstream terms:

- **OpenProblemGarden content** — the `source_text` / `source_propositions` fields of
  `meta/opg_corpus_manifest.json` (and any doc quoting them) reproduce statements from
  [openproblemgarden.org](http://www.openproblemgarden.org/). They are licensed under the
  **GNU Free Documentation License v1.2** (or later), with attribution to the contributors
  at openproblemgarden.org; each row's `canonical_url` links back to its upstream page.
  (Terms inherited from the upstream corpus repo's `LICENSE-DATA.md`.)
- **erdosproblems.com content** — v2 manifest rows with `corpus: erdos` derive from
  [erdosproblems.com](https://www.erdosproblems.com/), maintained by Thomas Bloom; the
  same GFDL terms apply with attribution to that site.
- **arXiv-derived content** — v2 manifest rows with `corpus: arxiv` / `arxiv-studied`
  carry *our own normalized statements* plus a `source_locator` + `source_hash` pointing
  at the paper; verbatim quotes appear only in short `source_excerpt` fields and only
  where the paper's arXiv license permits reuse. Each row records the paper's license in
  its `license` field (captured at statement-recovery time). Attribution: the paper's
  authors, per the row's `arxiv_id`.

The GFDL v1.2 text: <https://www.gnu.org/licenses/old-licenses/fdl-1.2.txt>.

The formalized Rocq statements themselves (`Definition <name>_statement : Prop := ...`)
are original expressions of the underlying mathematical propositions and are covered by
the repository's Apache-2.0 license; mathematical facts are not copyrightable, and the
per-row provenance above credits every source.
