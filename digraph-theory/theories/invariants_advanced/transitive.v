(** * Digraph.transitive — vertex-transitivity makes deletion uniform

    If Aut(T) acts transitively on the vertices, then ω̄(T − v) does not
    depend on [v]: an automorphism sending [u] to [v] restricts to an
    isomorphism [T − u ≅ T − v], and ω̄ is iso-invariant
    ([omegabar_dgiso]). Consequently [k]-ω̄-criticality of a
    vertex-transitive tournament reduces to a single deletion
    ([vt_kcritical]) — this is what lets the k=5 application check
    criticality of ACₙ[ACₙ] at the single vertex (0,0)
    (docs/DESIGN.md §6, §7). Demo: deletions in ACₙ ([AC_del_uniform]). *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup all_algebra.
From Digraph Require Import prelude interop_graph_theory digraph tournament order.
From Digraph Require Import omegabar critical.
From Digraph Require Import automorphism cayley circulant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section UniformDeletion.
Variable T : tournament.

(** An automorphism sending [u] to [g u] restricts to an isomorphism between
    the vertex-deleted sub-tournaments, so ω̄ agrees on them. *)
Lemma del_aut_iso (g : {perm T}) (u : T) :
  g \in dgaut (T : diGraphType) ->
  ω̄(del_tournament u) = ω̄(del_tournament (g u)).
Proof.
rewrite dgautE => /autbP gaut.
have mem_im (x : T) : x \in [set~ u] -> g x \in [set~ g u].
  by rewrite !inE (inj_eq perm_inj).
have mem_pre (y : T) : y \in [set~ g u] -> (g^-1 y)%g \in [set~ u].
  rewrite !inE => yneq; by rewrite -(inj_eq (@perm_inj _ g)) permKV.
pose f (x : del_tournament u) : del_tournament (g u) :=
  Sub (g (val x)) (mem_im _ (valP x)).
pose finv (y : del_tournament (g u)) : del_tournament u :=
  Sub ((g^-1 (val y))%g) (mem_pre _ (valP y)).
apply: (omegabar_dgiso (f:=f)).
- by exists finv => z; apply: val_inj; rewrite !SubK ?permK ?permKV.
- by move=> x y; rewrite !sub_arcE !SubK gaut.
Qed.

(** The marquee theorem: on a vertex-transitive tournament, ω̄ after deletion
    is the same whichever vertex is deleted. *)
Theorem omegabar_del_vt :
  vertex_transitiveb (T : diGraphType) ->
  forall u v : T, ω̄(del_tournament u) = ω̄(del_tournament v).
Proof.
move/vertex_transitivebP=> vt u v.
have [g gaut gE] := vt u v.
by rewrite (del_aut_iso u gaut) gE.
Qed.

(** Hence k-ω̄-criticality reduces to a single deletion. *)
Theorem vt_kcritical (k : nat) (v0 : T) :
  vertex_transitiveb (T : diGraphType) ->
  kcritical k T = (ω̄(T) == k) && (ω̄(del_tournament v0) == k.-1).
Proof.
move=> vt; rewrite /kcritical; congr (_ && _).
apply/forallP/eqP => [h | h v]; first exact/eqP/(h v0).
by apply/eqP; rewrite (omegabar_del_vt vt v v0) h.
Qed.

End UniformDeletion.

(** Demo: in the circulant tournament ACₙ all single-vertex deletions have
    the same ω̄ — its criticality will need only the deletion at 0 (M4). *)
Lemma AC_del_uniform (m' : nat) (u v : AC m') :
  ω̄(del_tournament u) = ω̄(del_tournament v).
Proof. exact: omegabar_del_vt (AC_vertex_transitive m') u v. Qed.
