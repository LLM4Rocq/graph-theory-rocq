(** * Chromatic.conjectures.implications_X218 -- dependency-graph EDGES for wave X218.

    Machine-checked implication edges out of / into the X218 statements.  Every
    SCHEDULED edge is a RELATIVE theorem: a [Qed]-closed [Theorem A -> B] proved
    WITHOUT resolving either endpoint.  Axiom-free: no [Axiom] / [Parameter] /
    [Admitted] / [Conjecture].  Candidate edges record the exact obstruction.

    The [cite="gc:eNNN"] fields point at [meta/corpus_relations.json]; rebuild it
    with [meta/build_corpus_relations.py] after this wave's manifest
    regeneration so the new formal names reach the relation endpoints. *)

From GTBase Require Import base.
From Chromatic.foundations Require Import chi_bounding.
From Chromatic.conjectures Require Import U8 X218.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Arithmetic and embedding helpers **********************************)

Lemma x218_leq_expn_base (m n e : nat) : m <= n -> m ^ e <= n ^ e.
Proof. by move=> le; elim: e => [|e IH] //; rewrite !expnS leq_mul. Qed.

(** A clique on [d*t] vertices contains the complete [d]-partite graph with all
    parts of size [t] as a SUBGRAPH: any injection of its [d*t] vertices into
    the clique preserves edges, since every two distinct clique vertices are
    adjacent. *)
Lemma x218_clique_has_multipartite (G : sgraph) (d t : nat) :
  d * t <= ω([set: G]) -> has_subgraph G (x218_complete_multipartite d t).
Proof.
case: omegaP => K KM le.
have cl := maxclique_clique KM.
have cardle : #|{: 'I_d * 'I_t}| <= #|K| by rewrite card_prod !card_ord; exact: le.
pose f (x : 'I_d * 'I_t) : G := @enum_val G (mem K) (widen_ord cardle (enum_rank x)).
have finj : injective f.
  move=> x y /enum_val_inj /(f_equal (@nat_of_ord _)) /= exy.
  by apply: enum_rank_inj; apply: val_inj.
exists f => // x y.
rewrite /edge_rel /= /x218_multipartite_rel => ne.
have xy : x != y by apply: contraNneq ne => ->; rewrite eqxx.
by apply: cl; rewrite ?enum_valP //; apply: contraNneq xy => /finj.
Qed.

(** ** Polynomial Gyarfas-Sumner ==> Gyarfas-Sumner ***********************)

(*@EDGE from=polynomial_gyarfas_sumner_tree_statement to=graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement kind=implies status=verified proved=true proof=polynomial_gyarfas_sumner_tree_implies_graphs_with_a_forbidden_induced_tree_are_chi_bounded cite="gc:e175" note="Corpus relation e175 (confirmed): a polynomial chi-bounding function is in particular a chi-bounding function. Under the X218 encoding the bounding function of U8 is literally the polynomial t |-> c * t ^ d produced by poly_chi_bounded." *)
Theorem polynomial_gyarfas_sumner_tree_implies_graphs_with_a_forbidden_induced_tree_are_chi_bounded :
  polynomial_gyarfas_sumner_tree_statement ->
  graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement.
Proof. by move=> H T Tt; have [c [d Hcd]] := H T Tt; exists (fun s => c * s ^ d). Qed.

(** ** Every forest is good ==> every forest is multibounding *************)

(*@EDGE from=every_forest_is_good_statement to=every_forest_is_multibounding_statement kind=implies status=verified proved=true proof=every_forest_is_good_implies_every_forest_is_multibounding cite="gc:e171" note="Corpus relation e171 (confirmed, and stated in the target's own context): if G is H-free with no K_d(t) subgraph then omega(G) < d*t, because a clique on d*t vertices contains K_d(t) as a spanning subgraph; so chi(G) <= c * omega(G)^e <= c * d^e * t^e, a polynomial in t for each fixed d." *)
Theorem every_forest_is_good_implies_every_forest_is_multibounding :
  every_forest_is_good_statement -> every_forest_is_multibounding_statement.
Proof.
move=> H F Ff d dpos; have [c [e Hce]] := H F Ff.
exists (c * d ^ e), e => t G tpos nind nsub.
apply: leq_trans (Hce G nind) _.
have wle : ω([set: G]) <= d * t.
  rewrite leqNgt; apply/negP => lt.
  by apply: nsub; apply: x218_clique_has_multipartite; apply: ltnW.
rewrite -mulnA -expnMn leq_mul2l; apply/orP; right.
exact: x218_leq_expn_base.
Qed.

(** ** Candidate edges ****************************************************)

(*@EDGE from=polynomial_gyarfas_sumner_tree_statement to=path_induced_rooted_tree_polynomial_chi_bound_statement kind=implies status=candidate proved=false cite="gc:e041" note="Corpus relation e041 (confirmed): a graph containing T as an INDUCED subgraph contains a path-induced copy of (T,r), because every path of a tree is induced in it; hence the path-induced-copy-free class is contained in the T-free class and the polynomial bound transfers. The missing bridge under this encoding is the graph-theoretic fact that two non-consecutive vertices of a path of a FOREST are non-adjacent (needed to turn [T ~ induced S] into the [x218_induced_run] condition); that is a genuine forest lemma about [is_forest], not a consequence of either statement, and coq-graph-theory has no ready-made form of it." *)

(*@EDGE from=forest_free_polynomial_chi_bound_statement to=polynomial_gyarfas_sumner_tree_statement kind=implies status=candidate proved=false cite="gc:e033" note="Corpus relation e033 (confirmed): every tree is a forest, so the X65 forest statement specialises to trees. The two encodings of 'polynomially chi-bounded' differ: X65 uses [x3_polynomially_chi_bounded] (an arbitrary polynomial given by its natural coefficient list, evaluated by Horner) while X218 uses the normal form c * omega^d. The edge needs the domination lemma 'every Horner evaluation of a coefficient list p at t is at most (sum of p) * t^(size p - 1) for t >= 1', plus the t = 0 corner; that arithmetic lemma is not yet available and is the only gap." *)

(*@EDGE from=forest_free_polynomial_chi_bound_statement to=every_forest_is_multibounding_statement kind=implies status=candidate proved=false cite="gc:e034" note="Corpus relation e034 (confirmed, and stated in the target's context). Same obstruction as e033: the coefficient-list polynomial of X65 must first be dominated by a c * t^d normal form before the omega(G) < d*t step of every_forest_is_good_implies_every_forest_is_multibounding can be reused verbatim." *)

(*@EDGE from=every_forest_is_multibounding_statement to=graphs_with_a_forbidden_induced_tree_are_chi_bounded_statement kind=implies status=candidate proved=false cite="gc:e035" note="Corpus relation e035 (confirmed): take t = 1, so K_d(1) = K_d, and apply multiboundedness at d = omega(G)+1 to get chi(G) <= c. NOT DERIVABLE as encoded: the constant c depends on d, i.e. on the graph, and [x218_multibounding] provides it only as a Prop-level existential 'forall d, exists c e, ...'. Producing the single function f : nat -> nat that [chi_bounded] requires would need countable choice, which this development does not assume. This is a real encoding-level gap, not a mathematical one; a future re-encoding of multiboundedness with the constants given as functions of d would close the edge." *)

(*@EDGE from=every_forest_is_good_statement to=good_trees_disjoint_union_good_statement kind=implies status=candidate proved=false cite="gc:e036" note="Corpus relation e036 (confirmed): the disjoint union of two trees is a forest, so the source makes the target's conclusion hold unconditionally. Two bridges are missing here: (a) [is_forest [set: x66_disjoint_union H1 H2]] from [is_tree [set: H1]] and [is_tree [set: H2]] -- coq-graph-theory has no disjoint-union forest lemma; (b) the coefficient-list versus c * omega^d normal-form conversion of e033, since X66 states goodness through [x3_polynomially_chi_bounded]." *)

(*@EDGE from=every_forest_is_good_statement to=conj2_1605_statement kind=implies status=candidate proved=false cite="gc:e170" note="Corpus relation e170 (confirmed): polynomial chi-boundedness of every forest-free class implies plain chi-boundedness, which is the 'if' direction of the target. CROSS-PACKAGE: [conj2_1605_statement] is defined in digraph-theory/theories/conjectures/chi_bounded.v, which chromatic-theory does not depend on, so the theorem cannot be stated here; and the target is a biconditional whose 'only if' direction is a separate (easy) argument about classes with unbounded clique number." *)

(*@EDGE from=odd_minor_free_defective_clustered_treedepth_statement to=clustered_chromatic_minor_class_treedepth_bound_statement kind=implies status=candidate proved=false cite="gc:e168" note="Corpus relation e168 (confirmed, after the reviewers corrected both extracted statements). BLOCKED SOURCE ENDPOINT: [odd_minor_free_defective_clustered_treedepth_statement] is the wave's blocked placeholder (the odd-minor normalisation and the connected tree-depth convention td-bar are not verified against arXiv:2308.15721), and X194's target uses ordinary tree-depth with the bound 2k-2 rather than the connected tree-depth with k-1. Until the placeholder is re-authored against the paper the edge must not be scheduled: proving it would only validate the guess." *)

Print Assumptions polynomial_gyarfas_sumner_tree_implies_graphs_with_a_forbidden_induced_tree_are_chi_bounded.
Print Assumptions every_forest_is_good_implies_every_forest_is_multibounding.
