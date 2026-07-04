(** * Grounding for Seymour's self-minor row (the encoding has content). *)

From GTBase Require Export base.
From Infinite Require Import foundations.igraph conjectures.D4inf2.
From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Graph isomorphism is reflexive. *)
Lemma iIso_refl (G : iGraph) : iIso G G.
Proof. by exists id; split=> //; exists id. Qed.

(** LOAD-BEARING: the IDENTITY minor model (singleton branch sets [b h := {h}])
    is NOT a proper witness — all three disjuncts fail.  So [proper_witness]
    genuinely excludes the trivial self-minor; the conjecture cannot be proven by
    the identity map. *)
Lemma identity_not_proper (G : iGraph) :
  ~ proper_witness (G := G) (H := G) (fun h x => x = h).
Proof.
rewrite /proper_witness /=.
move=> [[x H]|[[h [x [y [-> [-> H]]]]]|[h1 [h2 [x [y [Nadj [-> [-> Hadj]]]]]]]]].
- exact: (H x erefl).
- exact: (H erefl).
- exact: (Nadj Hadj).
Qed.

(** ** A concrete infinite graph that IS a proper minor of itself.

    The one-way infinite path (ray) on [nat]: deleting vertex [0] leaves a graph
    isomorphic (by the shift) to the whole ray — a proper minor via a genuine
    vertex deletion.  So [proper_self_minor] is inhabited (the conjecture's
    conclusion is achievable, not vacuously false). *)
Definition rayedge (x y : nat) : Prop := x.+1 = y \/ y.+1 = x.
Lemma rayedge_sym : irel_sym rayedge.
Proof. by move=> x y [E|E]; [right | left]. Qed.
Lemma rayedge_irr : irel_irr rayedge.
Proof. by move=> x [/eqP E | /eqP E]; move: E; rewrite (gtn_eqF (ltnSn x)). Qed.
Definition iRay : iGraph := Build_iGraph rayedge_sym rayedge_irr.

Lemma iRay_infinite : infinite_graph iRay.
Proof. by exists id. Qed.

Lemma iRay_proper_self_minor : proper_self_minor iRay.
Proof.
exists iRay, (fun h x => x = h.+1); split.
- exact: iIso_refl.
- split.
  + by move=> h; exists h.+1.
  + by move=> h x y -> ->; apply: reachP0.
  + by move=> h1 h2 x -> /succn_inj.
  + move=> h1 h2 Hadj; exists h1.+1, h2.+1; split; [by []|split; [by []|]].
    by case: Hadj => E; [left | right]; rewrite E.
- by left; exists 0 => h [].
Qed.
