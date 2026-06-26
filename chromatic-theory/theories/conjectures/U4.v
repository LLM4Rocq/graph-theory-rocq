(** * Chromatic.conjectures.U4 — milestone U4 (namespace Chromatic, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of eleven open/partial problems on LIST colouring (choosability),
    online list colouring (paintability), list edge/total colouring, the list
    Hadwiger conjecture, and strong colouring.

    CORE undirected vocabulary comes from graph-theory-base (GTBase.base, which
    re-exports coq-graph-theory's [sgraph], [x -- y], [N], [χ]=[chi_mem],
    [ω]=[omega_mem], [clique], ['K_n]=[complete n], [≃], [ucycle], plus base's
    cross-area [Delta]).  Two FURTHER coq-graph-theory modules are needed that
    base's undirected surface does not re-export and that base does NOT own:
      - [GraphTheory.minor]  : [minor G H] ("H is a minor of G") for Row 8;
      - [GraphTheory.mgraph] : the labelled multigraph record [graph Lv Le]
        (vertex/edge finTypes + [endpoint]/[incident]/[edges_at]) for the
        edge- and total-colouring rows (4, 5, 9).
    These are imported in addition to base; they are NOT part of base's owned
    surface, so no single-ownership rule is broken.

    KEY AREA PRIMITIVES introduced here (list-colouring vocabulary; candidates
    for a future [list-colouring] sub-layer once a 2nd area needs them):
      - [list_colourable] / [list_colourable_on] : (partial) L-colourability;
      - [choosable] / [is_choice_number] : k-choosability and the choice number
        χ_ℓ = ch (as a relation [is_choice_number G m], i.e. m is the least k
        such that G is k-choosable — avoids a non-constructive [ex_minn]
        obligation in a statement-only file);
      - [colourable_count] / [is_lambda] : λ_L and λ_t (Row 2);
      - [paintableb] / [paintable] / [is_online_choice_number] : the online
        list-colouring (Mr. Paint / Mrs. Correct) game and ch^OL (Row 3);
      - [line_graph] / [total_graph] / [mDelta] / [Delta_edge_critical]
        : multigraph edge/total constructions (Rows 4, 5, 9);
      - [complete_multipartite] : K_{m*k} = complete k-partite, parts of size m
        (Row 7);
      - [acyclic_colouring] / [acyclically_choosable] : Row 10 (PLANARITY-GATED);
      - [strongly_colorable] : Row 11. *)

(* mgraph imported BEFORE base: coq-graph-theory's mgraph defines a DIRECTED `line_graph`
   (DiGraph, target=source); importing it first lets base's undirected sgraph line_graph/
   total_graph shadow it. We use mgraph for the raw edge/incident/edges_at/source/target API. *)
From GraphTheory Require Import minor mgraph.
From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** List-colouring core vocabulary — PROMOTED to graph-theory-base.
    [list_colourable], [list_colourable_on], [choosable], [is_choice_number] now live in base/
    (reusable across U4 list / U5 edge-total / U8 χ-boundedness), reused here via the base export.
    No local definitions remain.  The list-colouring derivatives below ([colourable_count],
    paintability, line/total-graph, multipartite, acyclic, strong) stay area-local. *)

(** ** Partial list colouring : λ_L and λ_t (Row 2) *****************************)

(** [mu] is the maximum number of vertices of [G] colourable from [L]
    (= λ_L in the source). *)
Definition colourable_count (G : sgraph) (C : finType) (L : G -> {set C})
    (mu : nat) : Prop :=
  (exists W : {set G}, list_colourable_on L W /\ #|W| = mu) /\
  (forall W : {set G}, list_colourable_on L W -> #|W| <= mu).

(** [lam] is λ_t : the minimum, over all size-[t] list assignments [L], of the
    maximum number λ_L of [L]-colourable vertices. *)
Definition is_lambda (G : sgraph) (t lam : nat) : Prop :=
  (exists (C : finType) (L : G -> {set C}),
      (forall v : G, #|L v| = t) /\ colourable_count L lam) /\
  (forall (C : finType) (L : G -> {set C}) (mu : nat),
      (forall v : G, #|L v| = t) -> colourable_count L mu -> lam <= mu).

(** ** Online list colouring : the paintability game (Row 3) ********************)

(** The Mr. Paint / Mrs. Correct game on [G] with token budget [f : G -> nat].
    State: [A] = the still-uncoloured ("alive") vertices, [f v] = colours still
    available at [v].  Painter wins from [(A,f)] iff [A] is empty, or every
    alive vertex still has a token and, for every nonempty marked set [M] ⊆ [A]
    (Lister's move), Painter can pick a stable [I] ⊆ [M] to colour (remove),
    decrementing the tokens of the unchosen marked vertices, and win onward.
    [n] is recursion fuel; the wrapper [paintable] supplies enough (the strict
    decrease of [\sum (f v + 1)] each round). *)
Fixpoint paintableb (G : sgraph) (n : nat) (A : {set G}) (f : G -> nat)
    {struct n} : bool :=
  match n with
  | 0 => A == set0
  | n'.+1 =>
      (A == set0) ||
      ([forall v, (v \in A) ==> (0 < f v)] &&
       [forall M : {set G},
          (M \subset A) ==> (M != set0) ==>
          [exists I : {set G},
             [&& I \subset M, dom.stable I &
                 @paintableb G n' (A :\: I)
                   (fun v => if v \in M then (f v).-1 else f v)]]])
  end.

Definition paintable (G : sgraph) (f : G -> nat) : Prop :=
  @paintableb G (\sum_(v in [set: G]) (f v).+1) [set: G] f.

Definition k_paintable (G : sgraph) (k : nat) : Prop :=
  @paintable G (fun _ : G => k).

(** The online choice number ch^OL(G) as a relation: least [m] with [G]
    [m]-paintable. *)
Definition is_online_choice_number (G : sgraph) (m : nat) : Prop :=
  k_paintable G m /\ (forall k, k_paintable G k -> m <= k).

(** ** Multigraph line- and total-graph constructions (Rows 4, 5, 9) ***********)

(** [mgraph], [loopless], [line_graph], [total_graph] (and the helpers
    share_endpoint/line_rel/madj/total_rel) are PROMOTED to graph-theory-base — used here via the
    base export — since edge/total colouring is the U5 milestone too.  [chromatic_index] (χ') and
    [total_chromatic_number] (χ'') also live in base now.  Only the area-local derivatives below
    ([mDelta], [Delta_edge_critical]) remain here. *)

(** Maximum degree of a multigraph (parallel edges counted).  Genuinely new
    cross-area primitive — distinct from base's [Delta] (sgraph neighbourhood
    degree); tagged for migration if a 2nd multigraph area needs it.
    [@MOVE-to-base] *)
Definition mDelta (G : mgraph) : nat := \max_(v : G) #|edges_at v|.

(** [Δ]-edge-critical: deleting ANY edge strictly lowers the chromatic index
    χ'(G) = χ(L(G)).  Deleting edge [e] = deleting vertex [e] of the line
    graph, i.e. χ on [ [set: line_graph G] :\ e ]. *)
Definition Delta_edge_critical (G : mgraph) : Prop :=
  forall e : line_graph G,
    χ([set: line_graph G] :\ e) < χ([set: line_graph G]).

(** ** Complete multipartite graph K_{m*k} (Row 7) *****************************)

Definition cmp_rel (k m : nat) : rel ('I_k * 'I_m) :=
  fun x y => x.1 != y.1.

Lemma cmp_rel_sym (k m : nat) : symmetric (@cmp_rel k m).
Proof. by move=> x y; rewrite /cmp_rel eq_sym. Qed.

Lemma cmp_rel_irrefl (k m : nat) : irreflexive (@cmp_rel k m).
Proof. by move=> x; rewrite /cmp_rel eqxx. Qed.

(** K_{m*k}: complete [k]-partite graph with [k] parts each of size [m]
    (two vertices adjacent iff in different parts). *)
Definition complete_multipartite (k m : nat) : sgraph :=
  SGraph (@cmp_rel_sym k m) (@cmp_rel_irrefl k m).

(** ** Acyclic list colouring (Row 10, PLANARITY-GATED) ************************)

(** An acyclic proper L-colouring: proper, and every cycle of [G] uses MORE
    than two colours (no bichromatic cycle, i.e. every two colour classes
    induce a forest). *)
Definition acyclic_colouring (G : sgraph) (C : finType) (L : G -> {set C})
    (f : G -> C) : Prop :=
  [/\ (forall v : G, f v \in L v),
      (forall x y : G, x -- y -> f x != f y)
    & forall c : seq G, ucycleb (--) c -> 2 < size c ->
        2 < size (undup [seq f x | x <- c])].

Definition acyclically_choosable (G : sgraph) (k : nat) : Prop :=
  forall (C : finType) (L : G -> {set C}),
    (forall v : G, k <= #|L v|) ->
    exists f : G -> C, acyclic_colouring L f.

(** ** Strong colouring (Row 11) ***********************************************)

(** [G] is strongly [r]-colourable: for every partition of V(G) into blocks of
    size at most [r], there is a proper [r]-colouring assigning DISTINCT colours
    within every block. *)
Definition strongly_colorable (G : sgraph) (r : nat) : Prop :=
  forall P : {set {set G}},
    partition P [set: G] -> (forall B : {set G}, B \in P -> #|B| <= r) ->
    exists f : G -> 'I_r,
      (forall x y : G, x -- y -> f x != f y) /\
      (forall B : {set G}, B \in P -> {in B &, injective f}).

(** ============================================================================
    STATEMENTS
    ========================================================================== *)

(** ** Row 1 — Partial list colouring (PARTIAL).
    "G simple, n vertices, list chromatic number χ_ℓ; 0 ≤ t ≤ χ_ℓ, each vertex
    a list of t colours.  Then ≥ t·n/χ_ℓ vertices can be coloured from the
    lists."  Stated division-free: cl · #|W| ≥ t · n. *)
Definition partial_list_coloring_statement : Prop :=
  forall (G : sgraph) (t cl : nat),
    is_choice_number G cl -> t <= cl ->
    forall (C : finType) (L : G -> {set C}),
      (forall v : G, #|L v| = t) ->
      exists W : {set G},
        list_colourable_on L W /\ t * #|G| <= cl * #|W|.

(** ** Row 2 — Partial list colouring, ratio form (OPEN).
    "1 ≤ r ≤ s ≤ χ_ℓ ⇒ λ_r/r ≥ λ_s/s."  Division-free: s·λ_r ≥ r·λ_s. *)
Definition partial_list_coloring_0_statement : Prop :=
  forall (G : sgraph) (r s cl lr ls : nat),
    is_choice_number G cl ->
    1 <= r -> r <= s -> s <= cl ->
    is_lambda G r lr -> is_lambda G s ls ->
    r * ls <= s * lr.

(** ** Row 3 — Online vs offline choice number (OPEN).
    "Are there graphs for which ch^OL − ch is arbitrarily large?"  Stated as
    the affirmative open proposition: the gap is unbounded. *)
Definition bounding_the_on_line_choice_number_in_terms_of_the_c_statement : Prop :=
  forall M : nat, exists (G : sgraph) (ch chol : nat),
    [/\ is_choice_number G ch, is_online_choice_number G chol & M <= chol - ch].

(** ** Row 4 — Edge list colouring conjecture / List Colouring Conjecture (OPEN).
    "For a loopless multigraph G, the edge chromatic number equals the list
    edge chromatic number."  χ'(G) = χ(L(G)); χ'_ℓ(G) = ch(L(G)). *)
Definition edge_list_coloring_statement : Prop :=
  forall (G : mgraph) (m : nat),
    loopless G ->
    is_choice_number (line_graph G) m ->
    m = χ([set: line_graph G]).

(** ** Row 5 — List colourings of edge-critical graphs (OPEN).
    "G a Δ-edge-critical graph; each edge has a list of Δ colours.  Then G is
    L-edge-colourable unless all lists are equal."  L-edge-colourability =
    list-colourability of the line graph. *)
Definition list_colorings_of_edge_critical_graphs_statement : Prop :=
  forall (G : mgraph),
    loopless G -> Delta_edge_critical G ->
    forall (C : finType) (L : line_graph G -> {set C}),
      (forall e : line_graph G, #|L e| = mDelta G) ->
      (forall e e' : line_graph G, L e = L e') \/ list_colourable L.

(** ** Row 6 — List colourings of K_{a,b}+K_t (OPEN question).
    "Given a,b ≥ 2, what is the smallest t ≥ 0 with χ_ℓ(K_{a,b}+K_t)
    = χ(K_{a,b}+K_t)?"  Stated as: such a smallest [t] exists.  [K_{a,b}] is
    [KB a b] = ['K_a,b]; the join [+] is [sjoin]; [K_t] is [complete t]. *)
Definition list_colourings_of_complete_multipartite_graphs_with_statement : Prop :=
  forall a b : nat, 2 <= a -> 2 <= b ->
    exists t : nat,
      (forall m, is_choice_number (sjoin (KB a b) (complete t)) m ->
                 m = χ([set: sjoin (KB a b) (complete t)])) /\
      (forall t', t' < t ->
         ~ (forall m, is_choice_number (sjoin (KB a b) (complete t')) m ->
                      m = χ([set: sjoin (KB a b) (complete t')]))).

(** ** Row 7 — Choice number of k-chromatic graphs of bounded order (OPEN).
    "If G is k-chromatic on at most m·k vertices, then ch(G) ≤ ch(K_{m*k})." *)
Definition choice_number_of_k_chromatic_graphs_of_bounded_order_statement : Prop :=
  forall (G : sgraph) (k m chG chK : nat),
    χ([set: G]) = k -> #|G| <= m * k ->
    is_choice_number G chG ->
    is_choice_number (complete_multipartite k m) chK ->
    chG <= chK.

(** ** Row 8 — List Hadwiger conjecture (OPEN).
    "Every K_t-minor-free graph is c·t-list-colourable for some constant c ≥ 1."
    [minor G ('K_t)] = "'K_t is a minor of G"; K_t-minor-free = its negation. *)
Definition list_hadwiger_statement : Prop :=
  exists c : nat, 1 <= c /\
    forall (G : sgraph) (t chG : nat),
      ~ minor G ('K_t) -> is_choice_number G chG -> chG <= c * t.

(** ** Row 9 — List total colouring conjecture (OPEN).
    "If G is the total graph of a multigraph, then χ_ℓ(G) = χ(G)." *)
Definition list_total_colouring_statement : Prop :=
  forall (H : mgraph) (m : nat),
    is_choice_number (total_graph H) m ->
    m = χ([set: total_graph H]).

(** ** Row 10 — Acyclic list colouring of planar graphs (OPEN; PLANARITY-GATED).
    "Every planar graph is acyclically 5-choosable."  Planarity is the G2 gate
    (coq-graph-theory-planar / coq-fourcolor not installed): we discharge it as
    an ABSTRACT hypothesis [is_planar] INTO the statement — never a top-level
    Parameter/Axiom — so the file stays axiom-free; the row is marked
    compile_blocked because the real planar predicate is unavailable. *)
Definition acyclic_list_colouring_of_planar_graphs_statement : Prop :=
  forall (is_planar : sgraph -> Prop) (G : sgraph),
    is_planar G -> acyclically_choosable G 5.

(** ** Row 11 — Strong colourability (PARTIAL).
    "If Δ is the maximum degree of G, then G is strongly 2Δ-colourable." *)
Definition strong_colorability_statement : Prop :=
  forall G : sgraph, strongly_colorable G (2 * Delta G).
