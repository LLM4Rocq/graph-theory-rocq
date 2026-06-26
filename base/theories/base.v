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
