(** * ClassicalLemmas.necklace_complex — the complexes K, L of Meunier (2014), §3.2,
      and the statement of the ℤ_p-simplotopal Tucker lemma (Theorem 3.3).

    Reference: F. Meunier, "Simplotopal maps and necklace splitting", Discrete
    Math. 323 (2014) 14–26.

    The necklace has [n] beads (indexed by ['I_n], bead [b] sits at position
    [b+1] of the paper) and [t] types; [p] is the number of thieves.

    - [R] is the star with centre [o] and [p] paths of length [n]; its vertices
      are encoded as [cut := option ('I_n * 'I_p)], [None] being [o] and
      [Some (k, r)] the vertex [(k+1, r)] of the paper.  Its edges are the pairs
      [{slide x, x}] for [x <> None].
    - Vertices of [R^N], [N = t(p-1)+1], are [vertex := {ffun 'I_N -> cut}].
      [X] is the set of vertices having a coordinate of the form [(n, r)], i.e.
      a coordinate covering every bead ([in_X]).
    - A face of [R^N] is a product of vertices/edges of [R]; we represent it
      by its "top" vertex [u] together with the set [S] of coordinates carrying
      an edge (so [u j <> None] for [j \in S]), the vertices of the face being
      the [vert u T], [T \subset S].  [K] is the subcomplex of [R^N] induced by
      [X], so a face of [K] is a pair [(u, S)] all of whose vertices lie in [X]
      ([face u S]); its dimension is [#|S|].
    - [L = (Δ_{p-1})^t]; its vertices are ['I_t -> 'I_p] and its simplotopes
      the products of nonempty subsets of ['I_p].  The smallest simplotope of
      [L] containing the image of a face [(u, S)] under [mu] is
      [fun i => image_set mu u S i] and has dimension
      [\sum_i (#|image_set mu u S i| - 1)].  Hence [mu] is simplotopal iff that
      sum is at most [#|S|] on every face ([simplotopal]).
    - [ν] is the cyclic shift [r ↦ r+1 mod p] on thieves, acting freely on
      [K] and [L] ([shift_vertex], [shiftp]); [equivariant] is equivariance
      with respect to this generator.

    [zp_tucker] is Theorem 3.3 for these [K], [L]: every equivariant
    simplotopal map [K -> L] maps some [t(p-1)]-face of [K] onto the top
    simplotope of [L].  The hypothesis [0 < n] guarantees [K <> ∅]. *)

(** ** Provenance, sources, and what corresponds to what

    HOW THIS FILE WAS OBTAINED.  It was written with Claude Code (Anthropic),
    driving Rocq interactively through the rocq-mcp-evolve MCP server ("build"
    to list the open goals of a file, "open"/"step"/"try"/"check" to drive a
    single proof), so that a failing tactic was diagnosed on the spot instead
    of by recompiling.  rocq-mcp-evolve is developed by the LLM4Rocq project,
    https://github.com/LLM4Rocq/rocq-mcp-evolve (Apache-2.0; the opam package
    still carries its former slug LLM4Rocq/rocq-tools); it is gratefully
    acknowledged here.  Every error that recurred, together with the tactic
    that fixed it, is recorded in tactics-playbook.md at the root of the
    repository.  No result is admitted: "Print Assumptions" on the results of
    this file answers "Closed under the global context".

    MODELS AND ESTIMATED TOKEN COST FOR THIS FILE.

        Claude Fable 5.1      1k tokens   (09-14 21:49 UTC)
        Claude Opus 4.8      25k tokens   (09-15 05:52 -> 09-15 05:55 UTC)
        Claude Opus 5         8k tokens   (09-15 14:48 -> 09-15 15:06 UTC)
        TOTAL                35k tokens   of which 12k were output

      Method: the figures are estimated from the logs of the Claude Code
      session of 14-15 September 2026.  For every assistant message they count
      input + cache-creation + output tokens, i.e. the tokens processed anew,
      excluding the cached conversation that is re-read at each turn (772M
      over the project); a message is charged to the file its tool calls were
      acting on.  Three whole-session context rebuilds (compaction or resume),
      1.61M tokens in all, are charged to no file.  Project totals: 4.10M
      tokens of per-file work, 1.61M of context rebuilds, 5.70M overall.

    SOURCES.

      [M14]  F. Meunier, "Simplotopal maps and necklace splitting",
             Discrete Mathematics 323 (2014) 14-26.
             Local copy: classical-lemmas/Meunier2014-Simplotopal_Necklace_web.pdf

    WHAT CORRESPONDS TO WHAT.

      This file is the transcription of [M14, Sect. 3.2] (the encoding of the
      cuts) and of the statement of [M14, Theorem 3.3].

      - [M14, Sect. 3.2], "let R be the graph consisting of p paths of length n
        with a common endpoint o; the vertices along the r-th path are
        o, (1,r), ..., (n,r)"
                                    -> cut = option ('I_n * 'I_p), with None
                                       for o and Some (k,r) for (k+1,r);
                                       slide (the lower end of an edge of R),
                                       covers (the cut lies right of a bead)
      - [M14, Sect. 3.2], "X = {v : v_j = (n,r) for some j and some r}"
                                    -> in_X
      - [M14, Sect. 3.2], "define K as the subcomplex of R^(t(p-1)+1) induced
        by X"; a face of R^N is a product of vertices and edges of R, recorded
        here by its top vertex u and the set S of coordinates carrying an edge
                                    -> N t p = (t*p.-1).+1, vertex, vert, face
      - [M14, Sect. 3.2], "L := (Delta_{p-1})^t", and the smallest simplotope
        of L containing the image of a face
                                    -> image_set
      - [M14, Sect. 3.3], "let nu be the cyclic shift r |-> r+1 modulo p"
                                    -> shiftp, shift_cut, shift_vertex,
                                       equivariant
      - [M14, Lemma 3.2], the definition of a simplotopal map (the image of a
        d-face is contained in a simplotope of dimension at most d)
                                    -> simplotopal
      - [M14, Theorem 3.3]          -> zp_tucker *)

From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NecklaceComplex.
Variables (n t p : nat).
Hypothesis p_gt0 : 0 < p.

Definition N := (t * p.-1).+1.

Definition cut := option ('I_n * 'I_p).
Definition vertex := {ffun 'I_N -> cut}.

(** The cut [x] lies at or after bead [b]. *)
Definition covers (x : cut) (b : 'I_n) : bool :=
  if x is Some (k, _) then b <= k else false.

Definition in_X (v : vertex) : bool :=
  [forall b : 'I_n, [exists j : 'I_N, covers (v j) b]].

Definition ordp (k : 'I_n) : 'I_n :=
  Ordinal (leq_ltn_trans (leq_pred k) (ltn_ord k)).

(** The lower end of the edge of [R] whose upper end is [x]. *)
Definition slide (x : cut) : cut :=
  if x is Some (k, r) then (if k == 0 :> nat then None else Some (ordp k, r))
  else None.

Definition vert (u : vertex) (T : {set 'I_N}) : vertex :=
  [ffun j => if j \in T then slide (u j) else u j].

Definition face (u : vertex) (S : {set 'I_N}) : bool :=
  [forall j in S, u j != None] && [forall T in powerset S, in_X (vert u T)].

Definition shiftp (r : 'I_p) : 'I_p := Ordinal (ltn_pmod r.+1 p_gt0).

Definition shift_cut (x : cut) : cut := omap (fun kr => (kr.1, shiftp kr.2)) x.

Definition shift_vertex (v : vertex) : vertex := [ffun j => shift_cut (v j)].

Definition image_set (mu : vertex -> 'I_t -> 'I_p) (u : vertex) (S : {set 'I_N})
    (i : 'I_t) : {set 'I_p} :=
  [set mu (vert u T) i | T in powerset S].

Definition equivariant (mu : vertex -> 'I_t -> 'I_p) : Prop :=
  forall v, in_X v -> forall i, mu (shift_vertex v) i = shiftp (mu v i).

Definition simplotopal (mu : vertex -> 'I_t -> 'I_p) : Prop :=
  forall u S, face u S ->
    (\sum_(i : 'I_t) (#|image_set mu u S i| - 1) <= #|S|)%N.

(** Theorem 3.3 of Meunier (2014), for [K] and [L]. *)
Definition zp_tucker : Prop :=
  0 < n ->
  forall mu : vertex -> 'I_t -> 'I_p,
    equivariant mu -> simplotopal mu ->
    exists (u : vertex) (S : {set 'I_N}),
      [/\ face u S, #|S| = t * p.-1 & forall i, image_set mu u S i = setT].

End NecklaceComplex.

Arguments cut : clear implicits.
Arguments covers {n p} x b.
