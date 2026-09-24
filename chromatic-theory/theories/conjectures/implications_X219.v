(** * Chromatic.conjectures.implications_X219 -- dependency-graph EDGES for wave X219.

    Machine-checked implication edges into / out of the X219 statements.  Every
    SCHEDULED edge is a RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved
    WITHOUT resolving either endpoint.  Axiom-free: no [Axiom] / [Parameter] /
    [Admitted] / [Conjecture].  Candidate edges record the exact obstruction.

    The [cite="gc:eNNN"] fields point at [meta/corpus_relations.json]; rebuild it
    with [meta/build_corpus_relations.py] after this wave's manifest
    regeneration so the new formal names reach the relation endpoints. *)

From GTBase Require Import base.
From Chromatic.conjectures Require Import X32 X219 grounding_X219.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The 7/8 bound ==> the 5/6 bound ***********************************)

(*@EDGE from=triangle_free_planar_large_induced_two_degenerate_statement to=triangle_free_planar_five_sixths_two_degenerate_statement kind=implies status=verified proved=true proof=triangle_free_planar_large_induced_two_degenerate_implies_triangle_free_planar_five_sixths_two_degenerate cite="gc:e082" note="Corpus relation e082 (confirmed): identical hypothesis class (triangle-free planar) and identical conclusion type (an induced 2-degenerate subgraph on a prescribed fraction of the vertices), with a monotone parameter, 7/8 >= 5/6. The same vertex set S witnesses both bounds; the whole content is the cross-multiplied arithmetic 8|S| >= 7n implies 6|S| >= 5n." *)
Theorem triangle_free_planar_large_induced_two_degenerate_implies_triangle_free_planar_five_sixths_two_degenerate :
  triangle_free_planar_large_induced_two_degenerate_statement ->
  triangle_free_planar_five_sixths_two_degenerate_statement.
Proof.
move=> H G pl tf; have [S [Hcard Hdeg]] := H G pl tf.
by exists S; split => //; apply: x219_seven_eighths_implies_five_sixths.
Qed.

(** ** Candidate edges ****************************************************)

(*@EDGE from=toroidal_five_choosability_critical_iff_six_critical_statement to=toroidal_five_choosable_iff_five_colourable_statement kind=equiv status=candidate proved=false cite="gc:e027" note="Corpus relation e027 (confirmed, equivalence; the paper itself states Conjecture 2 and Conjecture 3 are equivalent). The bridge in both directions is the same missing ingredient: 'a toroidal graph fails a subgraph-monotone property if and only if it contains a subgraph that is CRITICAL for that property'. Extracting a critical subgraph needs a minimal-counterexample induction over subgraphs of a finite graph, together with the fact that the surface hypothesis is inherited by subgraphs -- and [surface_embeddable] is NOT known here to be subgraph-monotone (GTBase.surface has no restriction lemma for rotation systems). Both gaps are about the vocabulary, not about either conjecture, so the edge stays candidate." *)

(*@EDGE from=toroidal_five_choosable_iff_five_colourable_statement to=toroidal_edge_width_four_five_choosable_statement kind=implies status=candidate proved=false cite="gc:e123" note="Corpus relation e123 (confirmed; the paper introduces Conjecture 4 as a step towards Conjecture 3). BLOCKED TARGET: [toroidal_edge_width_four_five_choosable_statement] is this wave's blocked placeholder, in which edge-width at least four is replaced by GIRTH at least four because GTBase.surface has no contractibility predicate; proving the edge against the placeholder would certify a statement that is not the conjecture. Mathematically the step also needs that no 6-critical toroidal graph embeds with edge-width at least four, a case analysis over the four known 6-critical toroidal graphs, which is a theorem rather than a consequence of the source." *)

(*@EDGE from=asymmetric_bipartite_list_colouring_statement to=list_chromatic_number_and_maximum_degree_of_bipartit_statement kind=implies status=candidate proved=false cite="gc:e025" note="Corpus relation e025 (confirmed): apply case (ii) with Delta_A = Delta_B = Delta and k_A = k_B = ceil(C log Delta). CROSS-PACKAGE: the target lives in extremal-graph-theory/theories/conjectures/D2chr.v, which chromatic-theory does not depend on, so the theorem cannot be stated here. The rounding step (the source's real C log Delta versus this file's natural C * trunc_log 2 Delta) also has to be checked once both endpoints are in one package." *)

(*@EDGE from=edge_list_coloring_statement to=list_chromatic_index_even_clique_statement kind=implies status=candidate proved=false cite="gc:e039" note="Corpus relation e039 (confirmed): the List Colouring Conjecture restricted to cliques of even order is exactly the open half of this row. Missing bridge: U4's [edge_list_coloring_statement] is stated for loopless MULTIGRAPHS through [choosable (line_graph G)] and [chromatic_index G], whereas this row uses the simple-graph edge-choosability predicate [x219_edge_choosable] on 'K_n. Closing the edge needs (a) an equivalence between [x219_edge_choosable G k] and [choosable (line_graph G') k] for a multigraph G' whose underlying simple graph is G, and (b) the classical value chi'(K_n) = n-1 for even n -- neither is available, and (b) is a theorem, not a consequence of the source." *)

(*@EDGE from=planar_fractional_vertex_arboricity_two_statement to=large_induced_forest_in_a_planar_graph_statement kind=implies status=candidate proved=false cite="gc:e121" note="Corpus relation e121 (confirmed; the standard fractional-covering bound |V(G)|/a(G) <= va_f(G), stated in the source's own context). CROSS-PACKAGE: the target lives in topological-graph-theory/theories/conjectures/U13.v. The argument also needs the double-counting step 'if 2b induced forests cover every vertex b times then one of them has at least |V(G)|/2 vertices', i.e. a pigeonhole over the sum of the forest sizes, which is straightforward but must be written once both endpoints sit in one package." *)

Print Assumptions triangle_free_planar_large_induced_two_degenerate_implies_triangle_free_planar_five_sixths_two_degenerate.
