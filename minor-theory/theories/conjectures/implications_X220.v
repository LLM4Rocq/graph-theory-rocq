(** * Minor.conjectures.implications_X220 — corpus-relation edges of wave X220

    The six confirmed implies/equivalent_to edges of meta/corpus_relations.json whose
    endpoints are X220 rows, all recorded here as status=candidate: each of them
    rests on a substantive graph-theoretic argument (an even hole inside every
    C_4 / theta / prism / even wheel, an induced theta inside every subdivided
    wall, "classes of polynomial expansion are small", ...) that is far outside
    what can be re-derived here, or crosses two encodings of treewidth.  No false
    edge is forced: axiom-free, only [Qed]-closed results live in this file.

    What IS proved: two bridge lemmas that the e072 EQUIVALENCE needs — the
    polynomial envelope [x220_poly_eval] is monotone in its argument, and the
    induced biclique number really is an upper bound (a graph with induced
    biclique number [s] is [K_{s+1,s+1}]-free).  Together they are the two halves
    of the "K_{t,t}-free <-> biclique number < t" dictionary that the corpus
    argument for e072 uses; what is still missing for the edge to close is
    (i) the existence of the induced biclique number of an arbitrary graph, and
    (ii) the degenerate case [m = 0], which the source-side statement excludes by
    its positivity hypothesis while the target-side statement does not. *)

From GTBase Require Import base.
From Minor.foundations Require Import containment width_params.
From Minor.conjectures Require Import X27 X42 X220.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Proved bridge lemmas for e072 **************************************)

(** The Horner evaluation of a list of NATURAL coefficients is monotone. *)
Lemma x220_poly_eval_mono (p : seq nat) (a b : nat) :
  a <= b -> x220_poly_eval p a <= x220_poly_eval p b.
Proof.
move=> ab; elim: p => [|c q IH] //=.
by rewrite leq_add2l leq_mul.
Qed.

(** A graph whose induced biclique number is [s] has no induced ['K_s+1,s+1]. *)
Lemma x220_ibn_free (G : sgraph) (s : nat) :
  x220_ibn G s -> ~ has_induced_copy G (KB s.+1 s.+1).
Proof. by case=> _ /(_ s.+1) max /max; rewrite ltnn. Qed.

(** ** Candidate edges *****************************************************)

(*@EDGE from=bounded_degree_induced_wall_or_line_wall_statement to=bounded_degree_even_hole_free_bounded_treewidth_statement kind=implies status=candidate proved=false cite="gc:e053" note="Corpus argument: an even-hole-free graph has no induced k-wall (a brick is an induced 6-hole) and no induced line graph of a k-wall (the six edges of a brick induce a C_6 in the line graph), so the source applied at k = 3 bounds the treewidth of every even-hole-free graph of degree at most d. Not closed here: the brick/C_6 analysis of the wall and of its line graph is a genuine combinatorial argument, and the two rows moreover use different treewidth encodings (tw_le via the library sdecomp here, x27_treewidth_at_most in X27.v), so a bridge lemma between them is needed first." *)

(*@EDGE from=theta_prism_even_wheel_free_bounded_treewidth_statement to=even_hole_k4_diamond_free_bounded_treewidth_statement kind=implies status=candidate proved=false cite="gc:e051" note="Corpus argument: each of C_4, theta, prism and even wheel contains an even hole, so (even hole, K_4, diamond)-free graphs lie in the class C*_4 and the t = 4 instance of the source bounds their treewidth. Not closed here: 'every theta/prism/even wheel contains an even hole' is a parity argument on three internally disjoint paths, and the two rows use different treewidth encodings (tw_le vs x27_treewidth_at_most)." *)

(*@EDGE from=even_hole_diamond_free_bounded_tree_alpha_statement to=even_hole_k4_diamond_free_bounded_treewidth_statement kind=implies status=candidate proved=false cite="gc:e050" note="Corpus argument: (even hole, K_4, diamond)-free graphs are (even hole, diamond)-free, so the source gives bags of bounded independence number; K_4-freeness plus Ramsey then bounds the bag sizes, hence the treewidth. Not closed here: the Ramsey step (|B| < R(4, a+1)) is not available, and the target uses x27_treewidth_at_most while the source-side conclusion is tree_alpha_le." *)

(*@EDGE from=four_family_free_logarithmic_treewidth_statement to=even_hole_kt_free_logarithmic_treewidth_statement kind=implies status=candidate proved=false cite="gc:e052" note="Corpus argument: an (even hole, K_t)-free graph satisfies the four-family hypothesis at s = max(t,2), because K_{s,s} contains an induced C_4, every induced subdivision of the s-by-s wall contains an induced theta, the line graph of such a subdivision contains an induced prism, and every theta and every prism contains an even hole. Not closed here: each of those four containments is a separate structural argument about walls, line graphs and three-path configurations." *)

(*@EDGE from=bounded_tree_mu_polynomial_biclique_tree_alpha_statement to=tree_mu_ktt_free_polynomial_tree_alpha_statement kind=equiv status=candidate proved=false cite="gc:e072" note="The source paper states the two questions are equivalent, via 'G is K_{t,t}-free iff its induced biclique number is at most t-1'. Half the dictionary is proved in this file (x220_ibn_free, x220_poly_eval_mono). Still missing: the EXISTENCE of the induced biclique number of an arbitrary graph (the maximum of a bounded, nonempty set of t with an induced K_{t,t}), the monotonicity 'an induced K_{s,s} contains an induced K_{t,t} for t <= s', and the degenerate case m = 0, which the K_{t,t}-free form excludes by its positivity hypothesis while the biclique form does not." *)

(*@EDGE from=small_hereditary_class_bounded_twin_width_statement to=polynomial_expansion_bounded_twin_width_statement kind=implies status=candidate proved=false cite="gc:e078" note="Corpus argument: a class of polynomial expansion is small and may be taken hereditary (expansion is monotone under subgraphs), so the Small Conjecture bounds its twin-width. Not closed here: 'polynomial expansion implies small' is the counting theorem of Twin-width II and is not available; note also that the source row is recorded upstream as DISPROVED, so this edge documents a historical route, not a live one." *)

Print Assumptions x220_poly_eval_mono.
Print Assumptions x220_ibn_free.
