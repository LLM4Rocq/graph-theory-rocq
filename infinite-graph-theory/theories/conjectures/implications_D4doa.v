(** * Infinite.conjectures.implications_D4doa — milestone D4doa dependency-graph EDGES

    Machine-checked implication / refutation EDGES between the two committed
    D4doa conjecture statements (see [D4doa.v]).  As in the sibling
    [implications_D2chr.v] layer, every SCHEDULED edge would be a *relative*
    theorem: a [Qed]-closed [Theorem A_statement -> B_statement] provable WITHOUT
    resolving (proving or refuting) either endpoint.  This file is axiom-free: no
    [Conjecture]/[Axiom]/[Parameter]/[Admitted]; a genuinely false / unfounded
    edge is left to FAIL the [Qed] gate rather than forced, and any bridge fact
    that would need resolving a conjecture is never asserted.

    The two D4doa nodes are:
      • [counting_3_colorings_of_the_hex_lattice_statement]   (Row 1)
      • [exact_colorings_of_graphs_statement]                 (Row 2)

    ════════════════════════════════════════════════════════════════════════════
    RESULT:  no verified-literature edge is internal to D4doa.
    ════════════════════════════════════════════════════════════════════════════

    The §6 verified-literature edge table (OPG_FULL_FORMALIZATION_PLAN.md v4)
    lists ONLY cycle / edge-colouring edges (Petersen-colouring, Berge–Fulkerson,
    CDC, Tutte 4-flow); none of its endpoints is a D4doa node.  D4doa collects two
    PAIRWISE-INDEPENDENT open problems from the infinite / asymptotic bucket whose
    carriers, vocabulary and meta-questions are disjoint:

      • Row 1 is a THERMODYNAMIC-LIMIT existence statement: the per-site values
        [Rpower (INR (n3colorings (hex_torus k))) (1 / INR #|hex_torus k|)] — i.e.
        a real-analysis sequence built from chi(H_k, 3), the count of proper
        3-VERTEX-colourings of the FINITE honeycomb tori [hex_torus k] — converge
        to some real [L >= 1].  Object: a real number (an entropy-per-site
        constant); carrier: finite [sgraph]s; vocabulary: [n3colorings],
        [site_value], [converges] over [R].

      • Row 2 is a RAMSEY-type biconditional: for every symmetric exact
        [c]-EDGE-colouring of the INFINITE complete graph [Komega] there is an
        injective vertex sequence inducing an exactly-[m]-coloured countable
        clique, iff [m = 1 \/ m = 2 \/ c = m].  Object: a logical biconditional;
        carrier: the [iGraph] [Komega] (vertices [nat]); vocabulary:
        [Kedge_coloring], [sym_coloring], [exact_coloring], [exactly_m_colored].

    The two rows share NO carrier (finite [sgraph] vs. infinite [iGraph]
    [Komega]), NO colouring notion (proper 3-VERTEX-colourings counted as a
    chromatic-polynomial value vs. exact [c]-EDGE-colourings tested for a
    monochromatic-cardinality clique) and NO target object (a real limit vs. a
    biconditional).  Neither statement is a logical specialisation of the other,
    and there is no textbook reduction transporting one to the other.  The single
    surface temptation a reader might raise — "both are about colourings, so one
    should bound the other" — is a false friend (vertex/finite/counting vs.
    edge/infinite/Ramsey) and is recorded below for [meta/build_edge_graph.py] as
    a non-edge in BOTH directions; neither closes as a relative theorem.

    Hence ZERO D4doa-internal verified-literature edges; the two annotations below
    are recorded for the extractor and deliberately left unscheduled.

    Citations.  The row problems are independent OPG entries (problems manifest,
    plan v4 §6 edge policy); Row 1 is the hexagonal-lattice 3-colouring entropy
    (Baxter, J. Math. Phys. 11 (1970) 784–789, the per-site limit
    (3/2)^{3/2} ≈ 1.8392 for the honeycomb three-colouring constant); Row 2 is the
    "exact colourings of graphs" problem on [K_omega] (the P(c,m) iff m=1, m=2 or
    c=m record).  Neither paper relates the two problems. *)

From GTBase Require Export base.
From Infinite Require Import conjectures.D4doa.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ── Machine-readable edge records (extracted by meta/build_edge_graph.py) ───
    Each [from]/[to] is the exact [_statement] Definition name from [D4doa.v].
    Both are NON-edges under the faithful formulations: neither is scheduled as a
    [Theorem] and neither is asserted. *)

(*@EDGE from=counting_3_colorings_of_the_hex_lattice_statement to=exact_colorings_of_graphs_statement kind=implies status=refuted-direction proved=false cite="OPG_FULL_FORMALIZATION_PLAN.md v4 §6 edge policy; independent OPG infinite/asymptotic entries (Baxter, J. Math. Phys. 11 (1970) 784-789; exact-colourings-of-K_omega record)" note="Non-edge. Row 1 is a thermodynamic-limit existence claim: a real sequence of per-site values built from chi(H_k,3) (proper 3-VERTEX-colourings of FINITE honeycomb tori hex_torus k) converges to L>=1. Row 2 is a Ramsey biconditional on the INFINITE edge-coloured Komega. Disjoint carriers (finite sgraph vs iGraph Komega), disjoint colouring notions (vertex counting vs edge exact-colouring), disjoint targets (a real number vs a biconditional). No reduction transports the real limit to the Ramsey claim. Not stated." *)

(*@EDGE from=exact_colorings_of_graphs_statement to=counting_3_colorings_of_the_hex_lattice_statement kind=implies status=refuted-direction proved=false cite="OPG_FULL_FORMALIZATION_PLAN.md v4 §6 edge policy; independent OPG infinite/asymptotic entries (exact-colourings-of-K_omega record; Baxter, J. Math. Phys. 11 (1970) 784-789)" note="Non-edge. The exact-colourings biconditional on Komega (edge colourings, infinite carrier, Ramsey-type) gives no handle on the convergence of the hexagonal-tori per-site 3-colouring-count sequence (vertex colourings, finite carriers, real-analysis limit). Disjoint carriers, colouring notions and targets; no reduction. Not stated." *)
