(** * GTMisc.conjectures.implications_U13 — milestone U13 (misc) edges

    Implication / refutation EDGES among the twelve U13 "miscellaneous graph
    theory" nodes (Row 1 monochromatic-max-clique 2-colouring; Row 2
    book-thickness of subdivisions; Row 3 high-girth subgraph of large average
    degree; Row 4 union of degenerate graphs; Row 5 shuffle-exchange; Row 6
    pebbling of a Cartesian product; Row 7 the 57-regular Moore graph; Row 8
    Graceful Tree; Row 9 imbalance; Row 10 gold-grabbing game; Row 11 Beneš;
    Row 12 weighted colouring of hexagonal graphs), as Qed-closed RELATIVE
    theorems where one genuinely exists.

    OUTCOME (honest).  These twelve rows are MUTUALLY-INDEPENDENT open problems
    grouped only by the "miscellaneous" bucket; they share no textbook
    "A ⟹ B".  The verified-literature edge table of
    OPG_FULL_FORMALIZATION_PLAN.md §6 lists NONE of them.  Consequently this
    milestone schedules ZERO verified edges — there is no real
    [Theorem A_implies_B. Qed] to add, and per the edge policy a
    false/unclosing edge must NOT be forced (it must simply fail to compile).

    The single literature-MOTIVATED direction is the multistage-network pair
    (Rows 5 and 11), recorded below as a CANDIDATE annotation only
    (proved=false).  Beneš in the graph-theoretic form
    [bene_conjecture_graph_theoretic_form_0_statement] is the GENERAL claim:
    every square stage-regular relation [L] that is externally connected in [m]
    steps is rearrangeable in [2*m] stages.  The shuffle-exchange graph
    [se_adj k n] is one such network, externally connected in [n-1] steps, so
    Beneš would yield rearrangeability of [se_adj] at [2*(n-1) = 2*n-2] stages —
    EXACTLY the UPPER-BOUND conjunct of
    [shuffle_exchange_conjecture_statement].  But that statement is a CONJUNCTION
    whose second conjunct is the matching LOWER bound (optimality:
    [2*n-1 <= r] whenever [r-1] stages already rearrange), which Beneš does NOT
    deliver and which is itself open.  Hence the edge does NOT close as a
    relative theorem: deriving the full target from Beneš would require proving
    the open optimality conjunct, and additionally the external facts that
    [se_adj k n] is stage-regular and externally connected in [n-1] steps.  The
    direction therefore stays a candidate, never scheduled — the same
    "looks-like-an-edge but the target carries an extra open conjunct" pattern
    as the §6 withdrawn edges (list-total ⟹ Behzad, list-Hadwiger ⟹ Hadwiger).

    The file is self-contained (it re-states the two multistage-network nodes
    and their shared helpers verbatim from GTMisc.conjectures.U13 so the edge
    endpoints are in scope) and axiom-free: no Conjecture/Axiom/Parameter/
    Admitted, and no [Theorem … Qed] asserting an unproven edge. *)

From GTBase Require Import base.
From mathcomp Require Import fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Multistage-network helpers (verbatim from GTMisc.conjectures.U13) *)

Definition stage_regular {t : nat} (S : rel 'I_t) (d : nat) : Prop :=
  (forall i : 'I_t, #|[set j : 'I_t | S i j]| = d) /\
  (forall j : 'I_t, #|[set i : 'I_t | S i j]| = d).
Definition stage_reachable {t : nat} (S : rel 'I_t) (m : nat) (a b : 'I_t) : Prop :=
  exists w : seq 'I_t, [/\ size w = m, path S a w & last a w = b].
Definition externally_connected {t : nat} (S : rel 'I_t) (m : nat) : Prop :=
  forall a b : 'I_t, stage_reachable S m a b.
Definition multistage_route {t : nat} (S : rel 'I_t) (r : nat)
  (route : 'I_t -> nat -> 'I_t) (pi : {perm 'I_t}) : Prop :=
  [/\ (forall i : 'I_t, route i 0 = i),
      (forall i : 'I_t, route i r = pi i),
      (forall (i : 'I_t) (s : nat), s < r -> S (route i s) (route i s.+1)) &
      (forall s : nat, s <= r -> injective (route^~ s))].
Definition rearrangeable {t : nat} (S : rel 'I_t) (r : nat) : Prop :=
  forall pi : {perm 'I_t},
    exists route : 'I_t -> nat -> 'I_t, multistage_route S r route pi.

(** ** Row 5 node (shuffle-exchange), verbatim *)

Definition se_adj (k n : nat) : rel 'I_(k ^ (n - 1)) :=
  fun i j =>
    let t := k ^ (n - 1) in
    (val j + (t - (k * val i) %% t)) %% t < k.
Definition shuffle_exchange_conjecture_statement : Prop :=
  forall k n : nat,
    2 <= k -> 2 <= n ->
    rearrangeable (@se_adj k n) (2 * n - 2) /\
    (forall r : nat, 2 <= r -> rearrangeable (@se_adj k n) (r - 1) -> 2 * n - 1 <= r).

(** ** Row 11 node (Beneš, graph-theoretic form), verbatim *)

Definition bene_conjecture_graph_theoretic_form_0_statement : Prop :=
  forall (t : nat) (L : rel 'I_t) (d : nat),
    0 < t ->
    stage_regular L d ->
    forall m : nat,
      1 <= m ->
      externally_connected L m ->
      rearrangeable L (2 * m).

(** ** Edges.

    No verified-literature edge exists among the twelve U13 (misc) nodes, so no
    [Theorem … Qed] is asserted here.  The lone literature-motivated direction
    is recorded as a candidate only. *)

(*@EDGE from=bene_conjecture_graph_theoretic_form_0_statement to=shuffle_exchange_conjecture_statement kind=implies status=candidate proved=false cite="Beneš 1965; Stone 1971 (shuffle-exchange); Beauquier–Darrot 2002 (graph-theoretic Beneš)" note="General stage-regular rearrangeability (Beneš) would give the UPPER-bound conjunct (se_adj k n rearrangeable at 2*n-2) via external connectivity of the shuffle-exchange graph in n-1 steps, but shuffle_exchange_conjecture_statement also demands the matching LOWER bound (optimality 2*n-1<=r), which Beneš does not yield and is itself open; also needs external facts that se_adj is stage-regular and externally connected in n-1. Does NOT close as a single relative theorem." *)
