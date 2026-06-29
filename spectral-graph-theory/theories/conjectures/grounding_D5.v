(** * Spectral.conjectures.grounding_D5 — grounding lemmas for milestone D5.

    SIMPLE, Qed-closed sanity results validating the NEW area-specific primitives
    introduced in [D5.v].  D5's spectral matrix vocabulary ([adjmx], [Lapmx],
    [is_signing], [spectral_radius_le], [is_spectrum], [cospectral], the labelled-graph
    density [total_count]/[determined_count]) lives in the area-local foundation
    [Spectral.foundations.spectral]; the genuinely NEW combinatorial primitives DEFINED
    in [D5.v] are four:

      - [strongly_regular]  (Row 1, with the PRIMITIVITY guards: connected, 0<k<n-1),
      - [proper_colb]       (Row 4, proper boolean colouring),
      - [csf_coeff]         (Row 4, chromatic-symmetric-function monomial coefficient),
      - [same_csf]          (Row 4, equality of chromatic symmetric functions).

    For each we record a SATISFIABLE witness AND at least one textbook identity.  These
    are statement-validation lemmas, NOT the (open) conjectures themselves.

    Headline witness: [strongly_regular 'K_2,2].  The complete bipartite graph
    [K_{2,2}] = [C_4] is the smallest PRIMITIVE strongly-regular graph (parameters
    [(n,k,lam,mu) = (4,2,0,2)]); proving it satisfies the GUARDED [strongly_regular]
    shows the faithfulness fix (adding connectedness and [0 < k < n-1]) did NOT make the
    predicate vacuously unsatisfiable — a genuine SRG still qualifies, while the trivial
    edgeless / complete / matching graphs are now excluded.  Being triangle-free
    ([tf_K22]) it would even be a candidate witness for Row 1's existential. *)

From GTBase Require Import base.
From mathcomp Require Import all_algebra perm.
From Spectral Require Import foundations.spectral.
From Spectral.conjectures Require Import D5.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================================
    Row 1 — [strongly_regular] (guarded).
    ========================================================================== *)

(** SATISFIABLE WITNESS.  The complete bipartite graph [K_{2,2}] = [C_4] is strongly
    regular with parameters [k = 2], [lam = 0], [mu = 2]: connected, [2]-regular,
    [0 < 2 < 4-1 = 3], adjacent vertices (opposite sides) share no neighbour, and
    distinct non-adjacent vertices (same side) share both vertices of the other side.
    This certifies that the PRIMITIVITY-guarded definition is still inhabited. *)
Lemma sr_K22 : strongly_regular 'K_2,2.
Proof.
exists 2, 0, 2; split.
- exact: (@Knm_connected 1 1).
- by split=> //; rewrite card_sum !card_ord.
- by move=> [x|y]; rewrite ?deg_Knm_l ?deg_Knm_r.
- move=> [x|x] [y|y] uv //.
  + rewrite /common_nbr opn_Knm_l opn_Knm_r.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => z; rewrite !inE.
    by case: z => z; apply/andP => -[/imsetP[? _ ?] /imsetP[? _ ?]].
  + rewrite /common_nbr opn_Knm_l opn_Knm_r.
    apply/eqP; rewrite cards_eq0; apply/eqP/setP => z; rewrite !inE.
    by case: z => z; apply/andP => -[/imsetP[? _ ?] /imsetP[? _ ?]].
- move=> [x|x] [y|y] _ nadj //.
  + by rewrite /common_nbr !opn_Knm_l setIid card_imset ?cardsT ?card_ord //; exact: inr_inj.
  + by rewrite /common_nbr !opn_Knm_r setIid card_imset ?cardsT ?card_ord //; exact: inl_inj.
Qed.

(** TEXTBOOK IDENTITY.  [K_{2,2}] is triangle-free (bipartite), so [sr_K22] is in fact a
    candidate witness for the Row-1 existential, and confirms the [lam = 0] reading. *)
Lemma tf_K22 : triangle_free 'K_2,2.
Proof. by move=> [x|x] [y|y] [z|z]. Qed.

(** TEXTBOOK IDENTITY (projection).  Every strongly-regular graph is connected and
    regular for some degree — the guards are genuine consequences. *)
Lemma strongly_regular_connected (G : sgraph) :
  strongly_regular G -> connected [set: G].
Proof. by case=> k [lam] [mu] [] . Qed.

Lemma strongly_regular_regular (G : sgraph) :
  strongly_regular G -> exists k, regular G k.
Proof. by case=> k [lam] [mu] [_ _ rk _ _]; exists k. Qed.

(** ============================================================================
    Row 4 — [proper_colb].
    ========================================================================== *)

(** TEXTBOOK IDENTITY.  A "rainbow" (injective) colouring is always proper: distinct
    colours on every vertex trivially separate adjacent ones. *)
Lemma proper_colb_inj (G : sgraph) k (c : {ffun G -> 'I_k}) :
  injective c -> proper_colb c.
Proof.
move=> ci; apply/forallP=> x; apply/forallP=> y; apply/implyP=> xy.
by apply/negP=> /eqP /ci exy; move: xy; rewrite exy sg_irrefl.
Qed.

(** SATISFIABLE WITNESS.  The identity colouring of [K_2] (a [2]-colouring of an edge)
    is proper. *)
Lemma proper_colb_K2 : proper_colb [ffun x : 'K_2 => x].
Proof. by apply: proper_colb_inj => a b; rewrite !ffunE. Qed.

(** ============================================================================
    Row 4 — [csf_coeff].
    ========================================================================== *)

(** Helper / TEXTBOOK IDENTITY.  The colour classes of any [k]-colouring partition the
    vertex set, so their sizes sum to [#|G|]. *)
Lemma csf_fibre_sum (G : sgraph) k (c : {ffun G -> 'I_k}) :
  \sum_(b : 'I_k) #|[set x | c x == b]| = #|G|.
Proof.
rewrite -sum1_card (partition_big c predT) //=.
by apply: eq_bigr => b _; rewrite sum1dep_card.
Qed.

(** TEXTBOOK IDENTITY.  A monomial coefficient of the chromatic symmetric function
    vanishes unless the prescribed colour-class sizes [a] form a composition of [#|G|]:
    [csf_coeff] is supported on the compositions of [n]. *)
Lemma csf_coeff_eq0 (G : sgraph) k (a : 'I_k -> nat) :
  \sum_(b : 'I_k) a b != #|G| -> csf_coeff G a = 0.
Proof.
move=> Hne; apply/eqP; rewrite cards_eq0 -subset0; apply/subsetP => c.
rewrite !inE => /andP[_ /forallP Hsz]; exfalso.
move/negP: Hne; apply; apply/eqP.
rewrite -(csf_fibre_sum c); apply: eq_bigr => b _.
by rewrite (eqP (Hsz b)).
Qed.

(** SATISFIABLE WITNESS.  The one-vertex graph [K_1] has a non-zero monomial
    coefficient for the size-vector [a = (1)] (its single proper [1]-colouring), so
    [csf_coeff] is not identically zero. *)
Lemma csf_coeff_K1 : 0 < csf_coeff ('K_1) (fun _ : 'I_1 => 1).
Proof.
rewrite /csf_coeff card_gt0; apply/set0Pn; exists [ffun _ => ord0].
rewrite inE; apply/andP; split.
- by apply/forallP=> a; apply/forallP=> b; rewrite (ord1 a) (ord1 b) sg_irrefl.
apply/forallP=> b; rewrite (ord1 b) /=.
by rewrite (eq_card1 (x := ord0)) // => x; rewrite !inE ffunE eqxx (ord1 x).
Qed.

(** ============================================================================
    Row 4 — [same_csf].
    ========================================================================== *)

(** SATISFIABLE WITNESS + TEXTBOOK IDENTITY.  [same_csf] is an equivalence relation:
    reflexive (every graph has the same CSF as itself — the witness), symmetric, and
    transitive. *)
Lemma same_csf_refl (G : sgraph) : same_csf G G.
Proof. by move=> k a. Qed.

Lemma same_csf_sym (G H : sgraph) : same_csf G H -> same_csf H G.
Proof. by move=> h k a; rewrite h. Qed.

Lemma same_csf_trans (G H K : sgraph) :
  same_csf G H -> same_csf H K -> same_csf G K.
Proof. by move=> h1 h2 k a; rewrite h1 h2. Qed.
