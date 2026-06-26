(** * Digraph.order — vertex orders as permutations; the backedge graph

    DESIGN (docs/DESIGN.md §5, Decision D5): a total order on a finite vertex
    type [V] is represented by a permutation [p : {perm V}], read through the
    canonical enumeration as

      [u ≺_p v  :=  enum_rank (p u) < enum_rank (p v)]   ([ltp p u v]).

    The two pillars of this file:

    - **Realization** ([realize], [ltp_realizeE]): every irreflexive,
      transitive, total relation equals [ltp q] for some permutation [q] —
      constructed by sorting the enumeration. Its corollary [ltp_pullback]
      transports an order along any injective map, which is exactly what the
      monotonicity of ω̄ under sub-tournaments needs (an order on [V]
      restricts to an order on any subset).

    - **The backedge graph** ([backedge T p]): the *simple* graph on a
      tournament's vertices whose edges are the arcs pointing backwards
      w.r.t. [≺_p]. It is symmetric and irreflexive by construction and is
      packaged as a graph-theory [sgraph], so graph-theory's clique number
      [ω(_)] applies to it directly (that is the definition of ω̄,
      invariants/omegabar.v). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Orders as permutations *)

Section PermOrder.
Variable V : finType.
Implicit Types (p q : {perm V}) (u v w : V).

Definition ltp p u v := enum_rank (p u) < enum_rank (p v).

Lemma ltp_irrefl p : irreflexive (ltp p).
Proof. by move=> u; rewrite /ltp ltnn. Qed.

Lemma ltp_trans p : transitive (ltp p).
Proof. by move=> u v w; rewrite /ltp; apply: ltn_trans. Qed.

Lemma ltp_total p u v : u != v -> ltp p u v || ltp p v u.
Proof.
move=> uDv; rewrite /ltp -neq_ltn.
by rewrite val_eqE (inj_eq enum_rank_inj) (inj_eq perm_inj).
Qed.

Lemma ltp_asym p u v : ltp p u v -> ~~ ltp p v u.
Proof. by rewrite /ltp => h; rewrite -leqNgt ltnW. Qed.

(** ** Realization: every strict total order is [ltp] of some permutation *)

Section Realize.
Variable (r : rel V).
Hypothesis r_irr : irreflexive r.
Hypothesis r_trans : transitive r.
Hypothesis r_total : forall u v, u != v -> r u v || r v u.

Let le_r u v := (u == v) || r u v.

Fact le_r_total : total le_r.
Proof.
move=> u v; rewrite /le_r; case: (eqVneq u v) => [->|uDv] /=.
- by [].
- exact: r_total.
Qed.

Fact le_r_trans : transitive le_r.
Proof.
move=> v u w; rewrite /le_r => /orP[/eqP->|ruv] // /orP[/eqP<-|rvw].
- by rewrite ruv orbT.
- by rewrite (r_trans ruv rvw) orbT.
Qed.

Let s := sort le_r (enum V).

Fact mem_s u : u \in s. Proof. by rewrite mem_sort mem_enum. Qed.
Fact size_s : size s = #|V|. Proof. by rewrite size_sort -cardE. Qed.
Fact sorted_s : sorted le_r s. Proof. exact/sort_sorted/le_r_total. Qed.
Fact rank_lt u : index u s < #|V|. Proof. by rewrite -size_s index_mem mem_s. Qed.

Definition rfun u : V := enum_val (Ordinal (rank_lt u)).

Fact rfun_inj : injective rfun.
Proof.
move=> u v /enum_val_inj e.
have {}e : index u s = index v s by case: e.
by rewrite -(nth_index u (mem_s u)) -(nth_index u (mem_s v)) e.
Qed.

Definition realize : {perm V} := perm rfun_inj.

Lemma ltp_realizeE u v : ltp realize u v = r u v.
Proof.
rewrite /ltp !permE /rfun !enum_valK /=.
case: (eqVneq u v) => [->|uDv]; first by rewrite ltnn r_irr.
apply/idP/idP => [iuv|ruv].
- have /= := sorted_ltn_nth le_r_trans u sorted_s (index u s) (index v s).
  rewrite !inE !size_s !rank_lt => /(_ isT isT iuv).
  by rewrite !nth_index ?mem_s // /le_r (negbTE uDv).
- case: (ltngtP (index u s) (index v s)) => // [ivu|ieq]; last first.
    by move/(congr1 (nth u s)): ieq; rewrite !nth_index ?mem_s // => e; rewrite e eqxx in uDv.
  have /= := sorted_ltn_nth le_r_trans u sorted_s (index v s) (index u s).
  rewrite !inE !size_s !rank_lt => /(_ isT isT ivu).
  rewrite !nth_index ?mem_s // /le_r eq_sym (negbTE uDv) /= => rvu.
  by have := r_irr u; rewrite (r_trans ruv rvu).
Qed.

End Realize.
End PermOrder.

(** Transport an order along an injective map: the pulled-back order on [U]
    is again realized by a permutation. *)
Lemma ltp_pullback (U V : finType) (f : U -> V) (p : {perm V}) :
  injective f ->
  {q : {perm U} | forall u v, ltp q u v = ltp p (f u) (f v)}.
Proof.
move=> inj_f; pose r := [rel u v : U | ltp p (f u) (f v)].
have r_irr : irreflexive r by move=> u /=; rewrite ltp_irrefl.
have r_trans : transitive r by move=> a b c /=; apply: ltp_trans.
have r_total (u v : U) : u != v -> r u v || r v u.
  by move=> uDv; rewrite /r /=; apply: ltp_total; rewrite inj_eq.
by exists (realize r) => u v; rewrite (ltp_realizeE r_irr r_trans r_total).
Qed.

(** ** The backedge graph of a tournament under an order *)

Section Backedge.
Variables (T : tournament) (p : {perm T}).

Definition backedge_rel : rel T :=
  [rel u v | ltp p u v && (v --> u) || ltp p v u && (u --> v)].

Fact backedge_sym : symmetric backedge_rel.
Proof. by move=> u v; rewrite /backedge_rel /= orbC. Qed.

Fact backedge_irrefl : irreflexive backedge_rel.
Proof. by move=> u; rewrite /backedge_rel /= ltp_irrefl. Qed.

Definition backedge : sgraph := SGraph backedge_sym backedge_irrefl.

Lemma backedgeE (u v : backedge) :
  (u -- v) = ltp p u v && (v --> u) || ltp p v u && (u --> v).
Proof. by []. Qed.

(** An edge of the backedge graph is in particular an arc-disagreement, so
    its endpoints are distinct. *)
Lemma backedge_neq (u v : backedge) : u -- v -> u != v.
Proof.
rewrite backedgeE => /orP[]/andP[_ a]; first by rewrite eq_sym (arc_neq a).
exact: arc_neq a.
Qed.

End Backedge.

(** If the order linearizes the arcs (no backward arc at all), the backedge
    graph is edgeless. *)
Lemma backedge_arc_forward (T : tournament) (p : {perm T}) :
  (forall u v : T, u --> v -> ltp p u v) ->
  forall u v : backedge p, ~~ (u -- v).
Proof.
move=> fwd u v; rewrite backedgeE; apply/negP=> /orP[]/andP[lt a];
by have := ltp_asym (fwd _ _ a); rewrite lt.
Qed.
