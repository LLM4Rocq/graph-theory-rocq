(** * GTBase.base — graph-theory-base: the single owner of cross-area primitives

    The shared foundation of the graph-theory-rocq federation (plan §A ownership
    table).  It (1) RE-EXPORTS the core undirected vocabulary of coq-graph-theory
    so every area package imports it from ONE place, and (2) owns the cross-area
    primitives that more than one area needs.

    Surface discovered + validated by the U1 (chromatic-theory) milestone:
      re-exported:  [sgraph], [x -- y], [N(x)] (open_neigh), [χ(A)]=[chi_mem],
                    [ω(A)]=[omega_mem], [α], [clique]/[cliques], [connected],
                    ['K_n]=[complete n], [F ≃ G]=[diso], [ucycle]/[ucycleb];
      owned here:   [Delta] (Δ), [common_nbr], [regular], [girth_geq], [ceil_div].

    Planarity is NOT here yet: the [coq-graph-theory-planar] / [coq-fourcolor]
    layer (plan gate G2) is added only once that spike passes. *)

From mathcomp Require Export all_boot.
From GraphTheory Require Export digraph sgraph coloring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Maximum degree Δ(G).  Empty graph ↦ 0; users carry a non-triviality guard. *)
Definition Delta (G : sgraph) : nat := \max_(x : G) #|N(x)|.

(** ⌈a/b⌉, with the mathcomp convention ⌈a/0⌉ = 0.  Graph-free arithmetic helper. *)
Definition ceil_div (a b : nat) : nat := (a + b - 1) %/ b.

(** Common open neighbourhood of two vertices. *)
Definition common_nbr (G : sgraph) (u v : G) : {set G} := N(u) :&: N(v).

(** [d]-regularity: every vertex has degree exactly [d]. *)
Definition regular (G : sgraph) (d : nat) : Prop := forall v : G, #|N(v)| = d.

(** Girth ≥ [g]: every GENUINE cycle (size > 2; in a simple graph every cycle has
    size ≥ 3) has length ≥ [g].  The [2 < size c] guard is load-bearing — without
    it the empty/size-2 [ucycle] artefacts would make [girth_geq] unsatisfiable for
    [g ≥ 3].  Acyclic graphs satisfy it for all [g]. *)
Definition girth_geq (G : sgraph) (g : nat) : Prop :=
  forall c : seq G, ucycle (--) c -> 2 < size c -> g <= size c.

(** ** Homomorphisms, cores, and products (U3 surface)

    A [graph homomorphism] is an adjacency-preserving vertex map; [homs_to] is the
    existence of one; a [core] is a graph all of whose endomorphisms are bijective
    (for finite graphs, automorphisms).  The cartesian (box) product [□] is promoted
    here from hamiltonicity-theory/U2 (used by prisms); the tensor / direct /
    categorical product [×] is the product Hedetniemi's conjecture is about. *)

Definition is_hom (G H : sgraph) (f : G -> H) : Prop := forall x y : G, x -- y -> f x -- f y.
Definition homs_to (G H : sgraph) : Prop := exists f : G -> H, is_hom f.
Definition is_core (G : sgraph) : Prop := forall f : G -> G, is_hom f -> bijective f.

(** Cartesian (box) product G □ H. *)
Definition box_rel (G H : sgraph) : rel (G * H) :=
  fun p q => ((p.1 == q.1) && (p.2 -- q.2)) || ((p.2 == q.2) && (p.1 -- q.1)).
Lemma box_sym (G H : sgraph) : symmetric (@box_rel G H).
Proof.
by move=> p q; rewrite /box_rel ![p.1 == q.1]eq_sym ![p.2 == q.2]eq_sym
   ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'.
Qed.
Lemma box_irrefl (G H : sgraph) : irreflexive (@box_rel G H).
Proof. by move=> p; rewrite /box_rel !eqxx /= !sg_irrefl. Qed.
Definition cartesian_product (G H : sgraph) : sgraph := SGraph (@box_sym G H) (@box_irrefl G H).

(** Tensor / direct / categorical product G × H (the product in Hedetniemi's conjecture). *)
Definition tensor_rel (G H : sgraph) : rel (G * H) :=
  fun p q => (p.1 -- q.1) && (p.2 -- q.2).
Lemma tensor_sym (G H : sgraph) : symmetric (@tensor_rel G H).
Proof. by move=> p q; rewrite /tensor_rel ![p.1 -- q.1]sg_sym' ![p.2 -- q.2]sg_sym'. Qed.
Lemma tensor_irrefl (G H : sgraph) : irreflexive (@tensor_rel G H).
Proof. by move=> p; rewrite /tensor_rel !sg_irrefl. Qed.
Definition tensor_product (G H : sgraph) : sgraph := SGraph (@tensor_sym G H) (@tensor_irrefl G H).

(** ** Powers, subdivisions, fractional powers

    Pure, colouring-free [sgraph] constructions, promoted here because both
    chromatic-theory/U1 (fractional powers) and homomorphism-theory/U3 (frac-3/3-power)
    use them.  [graph_power G m] = the m-th power (distinct vertices at distance ≤ m
    adjacent); [subdivision G n] = the n-subdivision (n−1 internal vertices per edge);
    [frac_power G m n] = G^{m/n} = (G^{1/n})^m.  NB: [subdivision G n] degenerates for
    [n ≤ 1] (the meaningful regime is [n ≥ 2]); callers guard accordingly. *)
Section Power.
Variables (G : sgraph) (m : nat).
Fixpoint ball (k : nat) (x : G) : {set G} :=
  if k is k'.+1 then ball k' x :|: \bigcup_(z in ball k' x) N(z) else [set x].
Definition reach_le (x y : G) : bool := y \in ball m x.
Definition pow_rel : rel G := fun x y => (x != y) && (reach_le x y || reach_le y x).
Lemma pow_sym : symmetric pow_rel.
Proof. by move=> x y; rewrite /pow_rel eq_sym orbC. Qed.
Lemma pow_irrefl : irreflexive pow_rel.
Proof. by move=> x; rewrite /pow_rel eqxx. Qed.
Definition graph_power : sgraph := SGraph pow_sym pow_irrefl.
End Power.

Section Subdivision.
Variables (G : sgraph) (n : nat).
Definition oedge (p : G * G) : bool := (p.1 -- p.2) && (enum_rank p.1 < enum_rank p.2)%N.
Local Notation EdgeT := {p : G * G | oedge p}.
Definition lo (e : EdgeT) : G := (val e).1.
Definition hi (e : EdgeT) : G := (val e).2.
Definition SubVert : Type := (G + (EdgeT * 'I_n.-1))%type.
Definition sub_r0 (x y : SubVert) : bool :=
  match x, y with
  | inl _, inl _ => false
  | inl a, inr (e, i) => ((a == lo e) && (val i == 0)) || ((a == hi e) && (val i == n.-1.-1))
  | inr _, inl _ => false
  | inr (e, i), inr (e', j) => (e == e') && ((val i).+1 == val j)
  end.
Definition sub_rel (x y : SubVert) : bool := sub_r0 x y || sub_r0 y x.
Lemma sub_sym : symmetric sub_rel.
Proof. by move=> x y; rewrite /sub_rel orbC. Qed.
Lemma sub_irrefl : irreflexive sub_rel.
Proof. move=> x; rewrite /sub_rel orbb; case: x => [a|[e i]] //=. by rewrite eqxx /= (gtn_eqF (ltnSn _)). Qed.
Definition subdivision : sgraph := SGraph sub_sym sub_irrefl.
End Subdivision.

Definition frac_power (G : sgraph) (m n : nat) : sgraph := graph_power (subdivision G n) m.
