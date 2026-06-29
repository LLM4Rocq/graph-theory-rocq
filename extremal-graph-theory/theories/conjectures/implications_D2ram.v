(** * Extremal.conjectures.implications_D2ram — relative implication/refutation
    edges among milestone D2ram's five open-problem nodes.

    Each *scheduled* edge is a Qed-closed RELATIVE theorem
    [Theorem <A>_implies_<B> : A_statement -> B_statement] provable WITHOUT
    resolving either endpoint, restricted to the plan §6 verified-literature set
    (the Qed gate is the safeguard; a false edge must fail to compile, and a
    candidate whose exact endpoints do not match is NOT forced — policy §6 / R4).

    ── RESULT FOR D2ram: ZERO verified-literature edges; ONE candidate edge. ──

    D2ram's five nodes (carriers in brackets):

      (1) multicolour_erdos_hajnal_statement
            [symmetric edge-colourings col : 'I_n -> 'I_n -> 'I_m of K_n, with a
             fixed m-colour pattern chi : 'I_k -> 'I_k -> 'I_m using all m colours]
            — every K_n-colouring has a chi-coloured K_k OR an n^eps set spanning
              <= m-1 colours.
      (2) complete_bipartite_subgraphs_of_perfect_graphs_statement
            [sgraph G and its complement compl G]
            — every perfect G on n vertices: G or G-bar has a complete bipartite
              subgraph with both parts >= n^{1-o(1)}.
      (3) chromatic_number_of_common_graphs_statement
            [sgraph H; 2-edge-colourings rel 'I_n of K_n]
            — common graphs have bounded chromatic number.
      (4) ramsey_properties_of_cayley_graphs_statement
            [finite abelian group gT; connection set S : {set gT}]
            — a fixed c: every abelian gT has a symmetric S whose Cayley graph
              has neither clique nor independent set of size > c*log|gT|.
      (5) the_erdos_hajnal_statement
            [sgraph H (forbidden) and sgraph G (host)]
            — every fixed H: every H-induced-free G has a clique or an independent
              set of size |V(G)|^{delta(H)}.

    §6 verified-literature edge table: contains NO edge with any D2ram node as an
    endpoint (its edges are chromatic/cycle/flow/directed: Petersen-colouring,
    Berge–Fulkerson, CDC, 4-flow<=>3-edge-colouring). No forbidden/withdrawn edge
    (Reed=>B-K, list-total=>Behzad, list-Hadwiger=>Hadwiger, CH=>Seymour-2nd-nbhd)
    touches D2ram either. So no edge is *scheduled* (no [_implies_]/[_equiv_]
    Theorem is closed here).

    ── The one genuine mathematical link: (1) generalises (5). ──

    The multicolour Erdős–Hajnal conjecture (1) is the natural Ramsey-coloured
    generalisation of the Erdős–Hajnal conjecture (5): with m = 2 colours, a
    graph G is the 2-edge-colouring of K_{|V(G)|} that paints {x,y} colour 1 when
    [x -- y] and colour 0 otherwise; a 2-colour pattern chi is then a graph H on k
    vertices.  Under that dictionary:
      • [contains_pattern chi col]  <->  G contains an INDUCED copy of H
        ([has_induced_copy H G]);  so the host being H-induced-free kills the
        first disjunct of (1);
      • the surviving disjunct gives a set A with [n^a <= #|A|^b] and
        [#|palette_on col A| <= m - 1 = 1]: a single colour inside A, i.e. A is a
        CLIQUE (colour 1) or an INDEPENDENT set (colour 0), hence
        [#|A| <= maxn ω(G) α(G)];
      • monotonicity of [_ ^ b] then yields [#|G|^a <= (maxn ω α)^b], and
        [b' := maxn a b] repairs the [a <= b] guard of (5) (using ω(G) >= 1 for a
        nonempty G).
    This is exactly the textbook "multicolour EH ⊇ EH" reduction.

    ── Why it is CANDIDATE, not verified — the Qed gate refuses it as stated. ──

    The reduction is blocked at (1)'s [uses_all_colours chi] hypothesis. With the
    forced m = 2, [uses_all_colours] demands chi use BOTH colours, i.e. the
    forbidden graph H has at least one edge AND at least one non-edge.  (5)
    quantifies over EVERY H, including:
      • H complete (all edges) — chi is monochromatically 1, [uses_all_colours]
        FAILS, so (1) cannot be instantiated; the needed bound for K_k-free hosts
        is a genuine Ramsey statement;
      • H edgeless on >= 2 vertices — chi is monochromatically 0, same failure;
        the bound for hosts with no large independent set is again Ramsey.
    (The H = K_0 and H = K_1 cases are vacuous: the empty graph induces into every
    G, and every nonempty G contains a single vertex, so [~ has_induced_copy] is
    false there.)  Hence (1) ALONE does not entail (5): the monochromatic-pattern
    base cases need an EXTERNAL Ramsey-type lemma (a [#|G|^a <= (maxn ω α)^b] bound
    for clique-/independence-bounded hosts), which is a cited-but-here-unformalised
    result, not a consequence of (1).  Per policy we therefore do NOT force a
    Theorem (it would not close from the hypothesis); we record the relationship as
    a CANDIDATE edge with its external dependency named, to be re-derived (and the
    Qed gate consulted) only once that Ramsey lemma is in scope.

    The REVERSE direction (5) => (1) is not scheduled either: (5) is the 2-state
    (edge/non-edge) graph instance, strictly weaker than the m-colour conjecture
    (1), so it cannot entail (1); recorded in prose only (no annotation), since it
    is "not derivable" rather than a withdrawn/false claim.

    All remaining pairs are independent in both directions over heterogeneous
    carriers: (2) perfect-graph bipartite structure, (3) bounded χ of common
    graphs, and (4) Cayley-graph Ramsey existence over abelian groups share no
    logical shape with one another or with (1)/(5); no map turns one into another.

    This file imports the five node statements to confirm they are in scope and
    that this module compiles axiom-free. *)

From mathcomp Require Import all_boot all_fingroup.
From GTBase Require Import base.
From Extremal Require Import conjectures.D2ram.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ── Candidate edge (machine-readable; NOT a Qed theorem) ──

    multicolour Erdős–Hajnal (1) generalises the Erdős–Hajnal conjecture (5).
    Real in the literature, but the exact formalisations do not close: (1)'s
    [uses_all_colours] guard excludes the monochromatic 2-colour patterns, i.e.
    the complete / edgeless forbidden graphs H, whose bounds are an external
    Ramsey statement (not a consequence of (1)). proved=false; re-derive only with
    that Ramsey lemma added as an explicit hypothesis. *)
(*@EDGE from=multicolour_erdos_hajnal_statement to=the_erdos_hajnal_statement kind=specializes status=candidate proved=false cite="Erdős–Hajnal 1989; multicolour generalisation, Conlon–Fox–Sudakov, Erdős–Hajnal surveys (OPG)" note="m=2 dictionary: G<->2-edge-colouring of K_n, H<->2-colour pattern; contains_pattern<->has_induced_copy, palette<=1<->clique/indep, n^a<=|A|^b & |A|<=maxn(omega,alpha) give the EH bound (b':=maxn a b fixes a<=b). BLOCKED: uses_all_colours forces non-monochromatic chi, so complete/edgeless H are uncovered and need an external Ramsey base-case lemma; not derivable from (1) alone, so no Theorem is scheduled." *)

(** Sanity: all five D2ram nodes are in scope as [Prop]s.  No [_implies_]/
    [_equiv_] Theorem is scheduled (see the module header and the candidate
    annotation above for the §6 / Qed-gate justification). *)
Remark D2ram_nodes_in_scope :
  (multicolour_erdos_hajnal_statement : Prop) = multicolour_erdos_hajnal_statement /\
  (complete_bipartite_subgraphs_of_perfect_graphs_statement : Prop) = complete_bipartite_subgraphs_of_perfect_graphs_statement /\
  (chromatic_number_of_common_graphs_statement : Prop) = chromatic_number_of_common_graphs_statement /\
  (ramsey_properties_of_cayley_graphs_statement : Prop) = ramsey_properties_of_cayley_graphs_statement /\
  (the_erdos_hajnal_statement : Prop) = the_erdos_hajnal_statement.
Proof. do 4 (split; [reflexivity|]); reflexivity. Qed.
