(** * Extremal.conjectures.implications_X223 -- corpus relation edges unlocked by wave X223.

    Five confirmed [implies] relations of meta/corpus_relations.json have both
    endpoints formalised once this wave lands:

      e076  arxiv:1810.00058#00 => #01   VERIFIED below (pure instantiation H = K_3)
      e160  arxiv:1708.07369#00 => #01   VERIFIED below (eventual => infinitely often)
      e077  arxiv:1810.00058#02 => #00   candidate (needs the paper's cleaning argument)
      e109  arxiv:2210.16971#01 => #00   candidate (the #01 endpoint is a BLOCKED placeholder)
      e116  opg:the_erdos_hajnal_conjecture => arxiv:1912.02342#00
                                         candidate (needs the shattering gadget H_d)

    NB the derived file meta/corpus_relations.json still records
    [from_formal_name]/[to_formal_name] = null for the endpoints this wave
    authors; it must be regenerated (meta/build_corpus_relations.py) before
    meta/build_edge_graph.py can re-check these [gc:] citations. *)

From GTBase Require Import base.
From Extremal.conjectures Require Import X58 X195 X196 X223.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** e076 -- Conjecture 1.4 for all H implies its open case H = K_3.

    Pure instantiation, plus one weakening step: X58's eps-boundedness uses the
    maximum degree (Delta(G) < eps|G|) whereas the recovered source condition, used
    by this wave, is the CLOSED neighbourhood one (|N[v]| < eps|G| for every v).
    Since Delta(G) = |N(x)| for some x and |N(x)| < |N[x]|, the closed form implies
    the Delta form, so the H-quantified statement applies to every graph this row
    quantifies over. *)
Theorem epsilon_bounded_h_free_anticomplete_pair_implies_triangle_free_eps_bounded_anticomplete_pair :
  epsilon_bounded_h_free_anticomplete_pair_statement ->
  triangle_free_eps_bounded_anticomplete_pair_statement.
Proof.
move=> EH.
have [p [d [p0 [pd Hcore]]]] := EH 'K_3.
exists p, d; split => // G G1 Hfree Heps.
have G0 : 0 < #|G| by apply: leq_trans G1.
have Hfree58 : x58_induced_free G 'K_3 by move=> S [iso]; exact: (Hfree S iso).
have Heps58 : x58_epsilon_bounded G p d.
  have [x0 Hx0] := eq_bigmax (fun x : G => #|N(x)|) G0.
  rewrite /x58_epsilon_bounded /Delta Hx0.
  apply: leq_ltn_trans (Heps x0).
  rewrite leq_mul2l; apply/orP; right; apply: ltnW.
  exact: proper_card (opn_proper_cln x0).
have [A [B [Hac [HA HB]]]] := Hcore G G1 Hfree58 Heps58.
by exists A, B; split.
Qed.

(*@EDGE from=epsilon_bounded_h_free_anticomplete_pair_statement to=triangle_free_eps_bounded_anticomplete_pair_statement kind=implies status=verified proof=epsilon_bounded_h_free_anticomplete_pair_implies_triangle_free_eps_bounded_anticomplete_pair cite="gc:e076" *)

(** ** e160 -- "k-nice for every large k" implies "k-nice for infinitely many k".

    Elementary: take the maximum of the two thresholds. *)
Theorem ramsey_nice_forest_family_eventual_implies_ramsey_nice_forest_family_infinite :
  ramsey_nice_forest_family_eventual_statement ->
  ramsey_nice_forest_family_infinite_statement.
Proof.
move=> H r Fam r0 Hf k0.
have [k1 Hk1] := H r Fam r0 Hf.
by exists (maxn k0 k1); split; [exact: leq_maxl | apply: Hk1; exact: leq_maxr].
Qed.

(*@EDGE from=ramsey_nice_forest_family_eventual_statement to=ramsey_nice_forest_family_infinite_statement kind=implies status=verified proof=ramsey_nice_forest_family_eventual_implies_ramsey_nice_forest_family_infinite cite="gc:e160" *)

(** ** e077 -- Conjecture 3.4 implies Conjecture 1.4 (CANDIDATE).

    The source itself records the implication 3.3 => 3.4 => 1.4.  It is NOT the
    trivial c = 0 instantiation: at c = 0 the guaranteed size eps*c^s*|G| of the
    A side degenerates to 0, so the sparse pair carries no information.  The real
    step is the paper's cleaning argument, which turns a c-sparse pair with c
    small into a genuinely ANTICOMPLETE pair by deleting the few vertices with
    many cross-neighbours; that argument is not formalised here, so the Qed gate
    refuses the edge and it is recorded as a candidate. *)
(*@EDGE from=h_free_eps_bounded_sparse_pair_statement to=epsilon_bounded_h_free_anticomplete_pair_statement kind=implies status=candidate proved=false cite="gc:e077" note="Literature-stated (the paper asserts 3.3 => 3.4 => 1.4). Not the c=0 instantiation: at c=0 the A-side bound eps*c^s*|G| collapses to 0. Needs the cleaning argument turning a sparse pair into an anticomplete one, which is not in scope here." *)

(** ** e109 -- directed forcing implies directed Sidorenko (CANDIDATE).

    The source endpoint arxiv:2210.16971#01 is recorded BLOCKED: its Rocq body
    ([directed_forcing_cyclic_statement]) is a PLACEHOLDER whose conclusion is
    the Sidorenko property rather than the forcing property, because forcing is a
    graph-limit notion with no finite form available here.  The corpus argument
    (forcing => Sidorenko by an interpolation / intermediate-value argument on
    oriented graphons, plus Theorem 1.5 for oriented forests) therefore has no
    faithful formal counterpart, and the placeholder does NOT entail the target
    either: it carries the extra hypothesis "the underlying graph has a cycle",
    which the bipartite target does not (oriented forests are a genuine case of
    Conjecture 1.4).  Recorded as a candidate. *)
(*@EDGE from=directed_forcing_cyclic_statement to=directed_sidorenko_bipartite_statement kind=implies status=candidate proved=false cite="gc:e109" note="Source endpoint is a BLOCKED placeholder (Sidorenko conclusion, not forcing). Even as stated it does not close: the placeholder assumes a cycle in the underlying graph, while the target also covers oriented forests." *)

(** ** e116 -- Erdos-Hajnal implies its VC-dimension specialisation (CANDIDATE).

    The literature reduction fixes, for each d, the bipartite gadget H_d on
    {v_1..v_{d+1}} u {w_S : S subset [d+1]} with w_S adjacent exactly to
    {v_i : i in S}; H_d has VC-dimension at least d+1, VC-dimension is monotone
    under induced subgraphs, so every graph of VC-dimension at most d is
    induced-H_d-free and Erdos-Hajnal applied to H = H_d gives the target with
    eps(d) = delta(H_d).  Formalising it needs the construction of H_d and the
    monotonicity lemma, neither of which is in scope for this wave, so no Theorem
    is scheduled. *)
(*@EDGE from=the_erdos_hajnal_statement to=vc_dimension_erdos_hajnal_statement kind=implies status=candidate proved=false cite="gc:e116" note="Needs the shattering gadget H_d (bipartite, parts of size d+1 and 2^(d+1)) and monotonicity of VC-dimension under induced subgraphs; neither is formalised here. the_erdos_hajnal_statement lives in D2ram.v, this wave's target in X223.v." *)

Print Assumptions epsilon_bounded_h_free_anticomplete_pair_implies_triangle_free_eps_bounded_anticomplete_pair.
Print Assumptions ramsey_nice_forest_family_eventual_implies_ramsey_nice_forest_family_infinite.
