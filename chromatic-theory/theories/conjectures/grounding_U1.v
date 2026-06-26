(** * Chromatic.conjectures.grounding_U1 — grounding lemmas for milestone U1.

    SIMPLE, Qed-closed sanity results validating the new primitives introduced
    in [U1.v]: for each new definition we record a satisfiable witness and at
    least one textbook identity (e.g. Δ('K_n.+1) = n, χ('K_n) = n,
    valency_variety('K_n.+1) = 1).  These are statement-validation lemmas, not
    the (open) conjectures themselves. *)

From mathcomp Require Import all_boot.
From GraphTheory Require Import digraph sgraph coloring.
From Chromatic.conjectures Require Import U1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Complete-graph helpers *)

(** In a complete graph the open neighbourhood of [x] is everything but [x]. *)
Lemma neigh_complete n (x : 'K_n) : N(x) = ~: [set x].
Proof. by apply/setP => y; rewrite !inE eq_sym. Qed.

(** Δ-ingredient: every vertex of 'K_n.+1 has degree exactly n. *)
Lemma deg_complete n (x : 'K_n.+1) : #|N(x)| = n.
Proof.
by rewrite neigh_complete (cardsCs (~: [set x])) setCK cards1 card_ord subn1.
Qed.

(** [set: 'K_n] is a clique. *)
Lemma clique_complete n : clique [set: 'K_n].
Proof. by move=> x y _ _ xy; rewrite /edge_rel /= xy. Qed.

(** ** [Delta] — textbook Δ('K_n.+1) = n. *)
Lemma Delta_complete n : Delta 'K_n.+1 = n.
Proof.
rewrite /Delta; apply/eqP; rewrite eqn_leq; apply/andP; split.
- by apply/bigmax_leqP => x _; rewrite deg_complete.
- by apply: (leq_trans _ (leq_bigmax ord0)); rewrite deg_complete.
Qed.

(** ** [regular] — witness + identity: 'K_n.+1 is n-regular. *)
Lemma regular_complete n : regular 'K_n.+1 n.
Proof. by move=> v; rewrite deg_complete. Qed.

(** ** [ceil_div] — textbook ⌈a/1⌉ = a. *)
Lemma ceil_div_1 a : ceil_div a 1 = a.
Proof. by rewrite /ceil_div addn1 subn1 /= divn1. Qed.

(** ** [common_nbr] — textbook symmetry common_nbr u v = common_nbr v u. *)
Lemma common_nbr_sym (G : sgraph) (u v : G) :
  common_nbr u v = common_nbr v u.
Proof. by rewrite /common_nbr setIC. Qed.

(** ** [chi] of a complete graph — textbook χ('K_n) = n. *)
Lemma chi_complete n : χ([set: 'K_n]) = n.
Proof.
rewrite chi_clique; first by rewrite cardsT card_ord.
exact: clique_complete.
Qed.

(** ** [girth_geq] — satisfiable witness.
    'K_2 carries an edge yet has NO genuine (length ≥ 3) cycle, so it has
    girth ≥ g for every g.  This is exactly the case the [2 < size c] guard
    fixes: the size-2 closed walk [[x; y]] is an edge, not a cycle. *)
Lemma girth_geq_K2 g : girth_geq 'K_2 g.
Proof.
move=> c /andP[_ /card_uniqP eqsz] hsz.
move: (max_card (mem c)); rewrite eqsz card_ord => h2.
by move: hsz; rewrite ltnNge h2.
Qed.

(** ** [double_critical] — witness: 'K_2 is double-critical. *)
Lemma double_critical_K2 : double_critical 'K_2.
Proof.
move=> x y xy.
have xney : x != y by move: xy; rewrite /edge_rel /=.
have e2 : [set x; y] = [set: 'K_2].
  by apply/eqP; rewrite eqEcard subsetT cardsU1 inE xney cards1 cardsT card_ord.
by rewrite e2 setDv chi0 chi_complete.
Qed.

(** ** [zero_two_graph] — witness: 'K_2 is a (0,2)-graph. *)
Lemma zero_two_K2 : zero_two_graph 'K_2.
Proof.
move=> u v uv; left.
rewrite /common_nbr !neigh_complete -setCU.
have -> : [set u] :|: [set v] = [set: 'K_2].
  by apply/eqP; rewrite eqEcard subsetT cardsU1 inE uv cards1 cardsT card_ord.
by rewrite setCT cards0.
Qed.

(** ** [n_cycles_len] — degenerate identity: 0-length count is 0. *)
Lemma n_cycles_len_0 (G : sgraph) : n_cycles_len G 0 = 0.
Proof. by rewrite /n_cycles_len muln0 divn0. Qed.

(** ** [count_cycles_mod] — identity: no cycle is 0 mod 0 (empty filter). *)
Lemma count_cycles_mod_0 (G : sgraph) : count_cycles_mod G 0 = 0.
Proof.
rewrite /count_cycles_mod big_pred0 // => L.
by rewrite dvd0n andbC; case: (val L) => [|l] //=.
Qed.

(** ** [edge_disjoint_clique_union] — witness: 'K_1 is a single K_1. *)
Lemma efl_K1 : edge_disjoint_clique_union 'K_1 1.
Proof.
exists (fun _ => [set: 'K_1]); split.
- by move=> i; rewrite cardsT card_ord.
- by move=> i; apply: clique_complete.
- by move=> i j; rewrite (ord1 i) (ord1 j) eqxx.
- by move=> x; exists ord0; rewrite inE.
- by move=> x y _; exists ord0; rewrite !inE.
Qed.

(** ** [graph_power] — identity: the 0-th power is edgeless. *)
Lemma graph_power0_edgeless (G : sgraph) (x y : graph_power G 0) :
  ~~ (x -- y).
Proof.
rewrite /edge_rel /= /pow_rel /reach_le /= !inE [y == x]eq_sym orbb andNb.
by [].
Qed.

(** ** [subdivision] — identity: original vertices are never adjacent
    (every edge is genuinely subdivided). *)
Lemma sub_inl_inl (G : sgraph) n (a b : G) :
  ~~ @edge_rel (subdivision G n) (inl a) (inl b).
Proof. by rewrite /edge_rel /= /sub_rel /=. Qed.

(** ** [frac_power] — identity: the 0-th fractional power is edgeless. *)
Lemma frac_power0_edgeless (G : sgraph) n (x y : frac_power G 0 n) :
  ~~ (x -- y).
Proof. exact: graph_power0_edgeless. Qed.

(** ** [valency_variety] — textbook identity: a regular graph has a single
    distinct degree, so valency_variety('K_n.+1) = 1. *)
Lemma undup_nseqS (a : nat) m : undup (nseq m.+1 a) = [:: a].
Proof. by elim: m => [//|m IH] /=; rewrite mem_head -IH. Qed.

Lemma undup_nseq (a : nat) m : 0 < m -> undup (nseq m a) = [:: a].
Proof. by case: m => // m _; apply: undup_nseqS. Qed.

Lemma valency_variety_complete n : valency_variety 'K_n.+1 = 1.
Proof.
rewrite /valency_variety.
have /all_pred1P -> :
    all (pred1 n) [seq #|N(x)| | x <- enum [set: 'K_n.+1]].
  by rewrite all_map; apply/allP => x _ /=; rewrite deg_complete.
rewrite undup_nseq; last by rewrite size_map -cardE cardsT card_ord.
by [].
Qed.
