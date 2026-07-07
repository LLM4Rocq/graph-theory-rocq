(** * Topological.foundations.crossing_genus — crossing number on the genus-i surface.

    Generalizes [crossing.crossing_planar_in] (whose base case is the genus-0
    planarity [wagner_planar]) to an arbitrary ORIENTABLE genus, by taking the
    base case to be [embedding.embeds_in_genus _ i] (a rotation system of Euler
    genus ≤ i).  With [xsplit] (one crossing resolution, from crossing.v):

      [crossing_genus_in i k G] : k split resolutions land G in a graph
                                  embeddable in genus i;
      [is_crossing_genus G i n] : n is the LEAST such k in this split model.

    So [is_crossing_number G n] (crossing.v) is the genus-0 analogue with a
    minor-based base; here the base is embedding-based, uniform across all i.

    CONNECTED-GRAPH GUARANTEE (fixes the Euler-genus side, not the whole crossing
    correspondence).  [euler_genus] is the
    CONNECTED-map Euler relation [2-2g = V-E+F] and is EXACT on connected maps
    with an edge (its only anomalies — understatement on disconnected maps, and
    genus 1 for the edgeless/one-vertex map — are documented in embedding.v).
    Crucially, [xsplit] PRESERVES connectivity: it deletes edges [a-b],[c-d] but
    the new vertex [None] is adjacent to [a,b,c,d], so a deleted edge reroutes
    ([a--None--b]) and no component is broken — this is proved here
    ([xsplit_connected]).  Hence for a CONNECTED [G] every planarization stays
    connected and [euler_genus] is exact on each.  This does NOT by itself prove
    equivalence to the usual drawing genus-crossing number, because the inherited
    [xsplit] model still lacks local rotation/alternation data at crossing
    vertices.  Consumers must therefore carry a connectivity guard (as
    [crossing_sequences] does), and the crossing-sequence row remains PARTIAL
    until a drawing/rotation equivalence layer is built. *)

From GTBase Require Export base.
From Topological.foundations Require Import embedding crossing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** [xsplit] preserves connectivity (the faithfulness anchor). *)

(** Generic transfer: a map sending every edge to a [connect] chain lifts
    [connect] itself. *)
Lemma homo_connect (T T' : finType) (f : T -> T') (e : rel T) (e' : rel T')
  (Hstep : forall x y, e x y -> connect e' (f x) (f y)) :
  forall x y, connect e x y -> connect e' (f x) (f y).
Proof.
move=> x y /connectP[p]; elim: p x => /= [|z p IH] x.
- by move=> _ ->; apply: connect0.
- by move=> /andP[e_xz Hp] Hl; apply: connect_trans (Hstep _ _ e_xz) (IH z Hp Hl).
Qed.

Section XsplitConnected.
Variables (G : sgraph) (a b c d : G).
Local Notation X := (xsplit a b c d).

Lemma xsplit_adjE (p q : X) : (p -- q) = xsplit_rel a b c d p q.
Proof. by []. Qed.

(** The crossing vertex [None] is adjacent to each of [a,b,c,d]. *)
Lemma xsplit_SN (w : G) : [|| w == a, w == b, w == c | w == d] -> (Some w : X) -- None.
Proof. by move=> Hw; rewrite xsplit_adjE /=; move: Hw; rewrite !orbA. Qed.
Lemma xsplit_NS (w : G) : [|| w == a, w == b, w == c | w == d] -> (None : X) -- Some w.
Proof. by move=> Hw; rewrite sgP; apply: xsplit_SN. Qed.

Lemma or4_ab (x : G) : (x == a) || (x == b) -> [|| x == a, x == b, x == c | x == d].
Proof. by move=> /orP[] H; apply/or4P; [exact: Or41 H | exact: Or42 H]. Qed.
Lemma or4_cd (x : G) : (x == c) || (x == d) -> [|| x == a, x == b, x == c | x == d].
Proof. by move=> /orP[] H; apply/or4P; [exact: Or43 H | exact: Or44 H]. Qed.

(** A [G]-edge that is neither deleted edge survives in [X]. *)
Lemma xsplit_SS (u v : G) : u -- v -> ~~ same_edge u v a b -> ~~ same_edge u v c d ->
  (Some u : X) -- Some v.
Proof. by move=> uv Nab Ncd; rewrite xsplit_adjE /= uv Nab Ncd. Qed.

(** Every [G]-edge lifts to a [connect] between the [Some]-images: kept directly,
    or (if deleted) rerouted through [None]. *)
Lemma xsplit_edge_lift (u v : G) : u -- v -> connect (@edge_rel X) (Some u) (Some v).
Proof.
move=> uv.
case: (boolP (same_edge u v a b)) => [Eab | Nab].
- have E : [set u; v] = [set a; b] by apply/eqP.
  have Hu : (u == a) || (u == b) by move: (set21 u v); rewrite E !inE.
  have Hv : (v == a) || (v == b) by move: (set22 u v); rewrite E !inE.
  by apply: connect_trans (connect1 (xsplit_SN (or4_ab Hu)))
                          (connect1 (xsplit_NS (or4_ab Hv))).
- case: (boolP (same_edge u v c d)) => [Ecd | Ncd].
  + have E : [set u; v] = [set c; d] by apply/eqP.
    have Hu : (u == c) || (u == d) by move: (set21 u v); rewrite E !inE.
    have Hv : (v == c) || (v == d) by move: (set22 u v); rewrite E !inE.
    by apply: connect_trans (connect1 (xsplit_SN (or4_cd Hu)))
                            (connect1 (xsplit_NS (or4_cd Hv))).
  + by apply: connect1; apply: xsplit_SS.
Qed.

(** MAIN: a crossing resolution of a connected graph stays connected. *)
Lemma xsplit_connected : connected [set: G] -> connected [set: X].
Proof.
move=> cG; apply: connectedTI => x y.
have liftc : forall u v : G, connect (@edge_rel X) (Some u) (Some v).
  move=> u v; apply: (homo_connect (f := fun w : G => (Some w : X))).
    exact: xsplit_edge_lift.
  by apply: (connectedTE cG).
have eSaN : (Some a : X) -- None by apply: xsplit_SN; rewrite eqxx.
have eNSa : (None : X) -- Some a by apply: xsplit_NS; rewrite eqxx.
have toN : forall p : X, connect (@edge_rel X) p None.
  by case=> [u|]; [apply: connect_trans (liftc u a) (connect1 eSaN) | exact: connect0].
have fromN : forall p : X, connect (@edge_rel X) None p.
  by case=> [u|]; [apply: connect_trans (connect1 eNSa) (liftc a u) | exact: connect0].
by apply: connect_trans (toN x) (fromN y).
Qed.
End XsplitConnected.

(** ** Genus crossing number. *)

(** Split-genus model: EXACTLY k crossing splits land G in orientable genus i. *)
Fixpoint crossing_genus_in (i k : nat) (G : sgraph) {struct k} : Prop :=
  match k with
  | 0 => embeds_in_genus G i
  | k'.+1 =>
      exists (a b c d : G),
        [/\ a -- b, c -- d & uniq [:: a; b; c; d]]
        /\ crossing_genus_in i k' (xsplit a b c d)
  end.

(** cr_i(G) = n : the least number of crossing splits landing G in genus i. *)
Definition is_crossing_genus (G : sgraph) (i n : nat) : Prop :=
  crossing_genus_in i n G /\ (forall k, crossing_genus_in i k G -> n <= k).

(** ** cr_i is FUNCTIONAL (at most one value). *)
Lemma is_crossing_genus_uniq (G : sgraph) (i m n : nat) :
  is_crossing_genus G i m -> is_crossing_genus G i n -> m = n.
Proof.
move=> [Pm Lm] [Pn Ln]; apply/eqP; rewrite eqn_leq.
by rewrite (Lm _ Pn) (Ln _ Pm).
Qed.

(** [embeds_in_genus] is monotone in the genus. *)
Lemma embeds_in_genus_leq (G : sgraph) (i j : nat) :
  i <= j -> embeds_in_genus G i -> embeds_in_genus G j.
Proof. by move=> le [E hE]; exists E; apply: leq_trans hE le. Qed.

(** Higher genus never needs MORE crossings: k splits landing in genus i also
    land in genus j ≥ i. *)
Lemma crossing_genus_in_leq (i j : nat) (Hij : i <= j) (k : nat) (G : sgraph) :
  crossing_genus_in i k G -> crossing_genus_in j k G.
Proof.
move: G; elim: k => [|k IH] G /=; first exact: embeds_in_genus_leq Hij.
move=> [a [b [c [d [Hcfg Hrec]]]]].
by exists a, b, c, d; split; [exact: Hcfg | apply: IH Hrec].
Qed.

(** The crossing SEQUENCE is NON-INCREASING in the genus: cr_{i+1}(G) ≤ cr_i(G) —
    exactly the monotonicity the "crossing sequences" conjecture ranges over. *)
Lemma is_crossing_genus_nonincreasing (G : sgraph) (i m n : nat) :
  is_crossing_genus G i m -> is_crossing_genus G i.+1 n -> n <= m.
Proof.
move=> [Pm _] [_ Ln]; apply: Ln.
by apply: (crossing_genus_in_leq (leqnSn i)); exact: Pm.
Qed.

(** cr_i(G) = 0  iff  G embeds in the genus-i surface. *)
Lemma crossing_genus0 (G : sgraph) (i : nat) :
  is_crossing_genus G i 0 <-> embeds_in_genus G i.
Proof.
split=> [[H0 _]|H]; first exact: H0.
by split=> // k _; apply: leq0n.
Qed.

(** Non-vacuity: every graph has cr_i = 0 for some genus i (its embedding's
    genus), so [is_crossing_genus] is inhabited — not a trivially-false predicate. *)
Lemma is_crossing_genus_inhab (G : sgraph) : exists i, is_crossing_genus G i 0.
Proof.
case: (embedding_exists G) => E.
by exists (euler_genus E); apply/crossing_genus0; exists E.
Qed.
