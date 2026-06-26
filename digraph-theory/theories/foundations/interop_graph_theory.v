(** * Digraph.interop_graph_theory — the single bridge to coq-graph-theory

    DESIGN (docs/DESIGN.md §2, Decision D1): this is the ONLY file in the
    library permitted to import [coq-graph-theory]. It re-exports the
    undirected vocabulary the directed layer consumes — [sgraph], [clique],
    [cliques], the clique number [ω(_)] ([omega_mem]) together with [α(_)] and
    [χ(_)] — and adds the few generic ω-lemmas we need that graph-theory does
    not provide. If we ever swap or vendor that dependency, this is the one
    file to touch.

    Conventions from graph-theory (coloring.v): [ω(A)] is *subset-relative* —
    [A : {set G}] for a fixed [G : sgraph] — and monotone via [sub_omega].
    The backedge graph of a tournament under a vertex order is an [sgraph]
    built here-downstream (core/order.v), and ω̄ is the min over orders of its
    [ω] (docs/DESIGN.md §5). *)

From mathcomp Require Import all_boot.
From GraphTheory Require Export digraph sgraph coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Generic ω facts missing from graph-theory *)

Section OmegaFacts.
Variable G : sgraph.
Implicit Types (A K : {set G}) (x y : G).

Lemma clique_set1 x : clique [set x].
Proof. by move=> u v /set1P-> /set1P->; rewrite eqxx. Qed.

Lemma set1_cliques A x : x \in A -> [set x] \in cliques A.
Proof. by move=> xA; rewrite inE sub1set xA /=; apply/cliqueP/clique_set1. Qed.

Lemma omega_ge1 A : A != set0 -> 1 <= ω(A).
Proof.
by case/set0Pn=> x xA; rewrite -(cards1 x); apply/clique_bound/set1_cliques.
Qed.

Lemma omega_le_card A : ω(A) <= #|A|.
Proof.
by case: omegaP => K /maxcliquesW Kcl; apply/subset_leq_card/cliques_subset.
Qed.

(** An edgeless subset has clique number at most [1]. *)
Lemma omega_le1 A : {in A &, forall x y, ~~ x -- y} -> ω(A) <= 1.
Proof.
move=> A0; case: omegaP => K Kmax; rewrite leqNgt; apply/negP=> /card_gt1P.
case=> x [y] [xK yK xDy]; have /subsetP Ksub := cliques_subset (maxcliquesW Kmax).
have := maxclique_clique Kmax xK yK xDy.
by rewrite (negbTE (A0 _ _ (Ksub _ xK) (Ksub _ yK))).
Qed.

(** Conversely, a single edge pushes ω to at least 2. *)
Lemma omega_ge2 A x y : x \in A -> y \in A -> x -- y -> 2 <= ω(A).
Proof.
move=> xA yA xy; have xDy : x != y by apply: contraTneq xy => ->; rewrite sgP.
have -> : 2 = #|[set x; y]| by rewrite cards2 xDy.
apply: clique_bound; rewrite inE subUset !sub1set xA yA.
apply/cliqueP=> u v /set2P[]-> /set2P[]-> //; rewrite ?eqxx // => _.
by rewrite sgP.
Qed.

End OmegaFacts.

(** ω is monotone along injective edge-preserving maps (used to compare
    backedge graphs of a sub-tournament and its host). *)
Lemma omega_hom (G H : sgraph) (h : G -> H) (A : {set G}) :
  injective h -> {in A &, forall x y, x -- y -> h x -- h y} ->
  ω(A) <= ω(h @: A).
Proof.
move=> inj_h hom_h; case: omegaP => K Kmax.
have Kcl : clique K := maxclique_clique Kmax.
have KsubA : K \subset A := cliques_subset (maxcliquesW Kmax).
have /subsetP KA := KsubA.
rewrite -(card_imset K inj_h); apply: clique_bound.
rewrite inE imsetS //=; apply/cliqueP=> u v /imsetP[x xK ->] /imsetP[y yK ->].
rewrite (inj_eq inj_h) => xDy.
by apply: hom_h; rewrite ?KA //; apply: Kcl.
Qed.

(** ** Smoke check — ω of a tiny hand-built [sgraph]

    The original M0 exit criterion: graph-theory's clique number is usable on
    a concrete graph. [K2] is the complete graph on [bool]. *)

Definition K2_rel : rel bool := [rel x y | x != y].
Fact K2_sym : symmetric K2_rel.
Proof. by move=> x y; rewrite /K2_rel /= eq_sym. Qed.
Fact K2_irrefl : irreflexive K2_rel.
Proof. by move=> x; rewrite /K2_rel /= eqxx. Qed.
Definition K2 : sgraph := SGraph K2_sym K2_irrefl.

Lemma omega_K2 : ω([set: K2]) = 2.
Proof.
apply/anti_leq/andP; split.
- by rewrite (leq_trans (omega_le_card _)) // cardsT card_bool.
- by have e : (true : K2) -- false by []; apply: omega_ge2 e; rewrite inE.
Qed.
