(** * Packing.conjectures.U13 — milestone U13 (namespace Packing, plan v4)

    Statement-only formalizations (axiom-free: no Conjecture/Axiom/Parameter/
    Admitted) of two open domination problems.

    CARRIERS ARE CHOSEN PER ROW (no blanket [sgraph] imposed by fiat, but both
    rows are genuinely about simple undirected graphs, so both carriers ARE
    [sgraph], as dictated by each row's [rocq_idiom]):

      - Row 1 [domination_in_cubic_graphs]: [sgraph]; cubic = [regular G 3]
        (base), 3-connected = [k_connected G 3] (base), the ceiling ⌈|G|/3⌉ =
        [ceil_div #|G| 3] (base), and the domination number is the cardinality
        of a minimum dominating set.
      - Row 2 [domination_in_plane_triangulations]: [sgraph]; PLANARITY-GATED /
        BLOCKED (G2 gate) — see below.

    REUSED FROM GraphTheory core ([dom]): [dom.dominating] (a vertex set whose
    closed neighbourhood is everything).  REUSED FROM base (NOT redefined):
    [regular] (cubic = 3-regular), [k_connected] (Whitney k-connectivity, which
    itself carries the guard [k < #|G|]), [ceil_div] (⌈a/b⌉ = (a+b-1) %/ b).

    AREA primitive introduced here (domination specific): [is_domination_number]
    — the relational "γ(G) = m" (m is the least cardinality of a dominating
    set), built on top of GraphTheory's [dom.dominating].  This mirrors the
    relational min/max idiom used elsewhere in this namespace ([is_min_fvs],
    [is_wsat], [is_max_cycle_packing] in U9): the statement quantifies over the
    witness [m] constrained by [is_domination_number G m], which is exactly the
    idiom's [domnum G <= …].

    PLANARITY G2-GATE (Row 2, [requires_planarity=true]): the planar / Four-
    Colour layer is NOT installed on this switch.  "Plane triangulation" is
    therefore modelled as an ABSTRACT predicate [plane_triangulation :
    sgraph -> Prop] quantified INSIDE the [Prop] — never a top-level
    Axiom/Parameter (that would contaminate Print Assumptions).  Because the
    real geometric notion of a plane triangulation is unavailable, this
    predicate is a placeholder: the row TYPE-CHECKS and is axiom-free, but is
    BLOCKED — it does not yet state the genuine geometric conjecture.  Row 1 is
    unaffected and models its statement fully. *)

From GTBase Require Export base.
From Topological.foundations Require Import embedding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ================================================================= *)
(** ** Shared domination primitive (area-specific) *)

(** [m] is the domination number γ(G): the least cardinality over all dominating
    sets (a dominating set [D] being one whose closed neighbourhood [NS[D]] is
    the whole vertex set, i.e. GraphTheory's [dom.dominating D]).  Stated
    relationally: some dominating set realises [m], and every dominating set has
    at least [m] vertices.  Well-defined on every graph since [[set: G]] is
    always dominating, but we do not need that fact to state the conjectures. *)
Definition is_domination_number (G : sgraph) (m : nat) : Prop :=
  (exists D : {set G}, dom.dominating D /\ #|D| = m) /\
  (forall D : {set G}, dom.dominating D -> m <= #|D|).

(** ================================================================= *)
(** ** Row 1 — Domination in cubic graphs  (OPEN)

    Source: "Problem: Does every 3-connected cubic graph G satisfy
    γ(G) ≤ ⌈|G|/3⌉ ?"

    Carrier: [sgraph].  cubic = [regular G 3] (base); 3-connected =
    [k_connected G 3] (base, which forces [3 < #|G|], the non-triviality guard);
    γ(G) = the [m] with [is_domination_number G m]; ⌈|G|/3⌉ = [ceil_div #|G| 3]
    (base).  This is the faithful reading of the idiom [domnum G <= ⌈|G|/3⌉]:
    γ(G) ≤ k ⟺ for the (unique) domination number [m], [m ≤ k]. *)
Definition domination_in_cubic_graphs_statement : Prop :=
  forall (G : sgraph) (m : nat),
    regular G 3 -> k_connected G 3 ->
    is_domination_number G m ->
    m <= ceil_div #|G| 3.

(** ** Row 2 — Domination in plane triangulations  (OPEN — done, Wave 1)

    Source: "Conjecture: Every sufficiently large plane triangulation G has a
    dominating set of size ≤ (1/4)|V(G)|."

    Wave 1 (Track-A embedding foundation): "plane triangulation" is the REAL
    combinatorial notion — a CONNECTED graph with a genus-0 rotation-system
    embedding all of whose faces are triangles ([planar_embedding E] +
    [triangulation E] from [Topological.foundations.embedding]).

    [connected [set: G]] is REQUIRED, not cosmetic: [euler_genus] is the
    connected-map Euler relation over truncating nat arithmetic, so without it
    disconnected pseudo-planar instances slip in (e.g. c ≥ 2 disjoint triangles
    have [2+E-V-F = 2-2c ≤ 0 → genus 0] yet need γ = n/3 > n/4, making the
    unguarded statement provably FALSE — caught by the Track-A review).  Plane
    triangulations are connected by definition, so the guard is faithful.

    "Sufficiently large" = an order threshold [n0] beyond which the bound holds;
    [n0 <= #|G|] also supplies the non-triviality guard.  "dominating set of size
    ≤ (1/4)|V(G)|" = γ(G) ≤ ⌊|G|/4⌋, i.e. the domination number [m]
    ([is_domination_number G m]) satisfies [m <= #|G| %/ 4]. *)
Definition domination_in_plane_triangulations_statement : Prop :=
  exists n0 : nat,
    forall (G : sgraph) (E : embedding G) (m : nat),
      connected [set: G] ->
      planar_embedding E -> triangulation E -> n0 <= #|G| ->
      is_domination_number G m ->
      m <= #|G| %/ 4.
