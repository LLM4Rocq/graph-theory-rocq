(** * Chromatic.conjectures.X129 -- v2 planar girth-5 square-colouring row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X129 vocabulary ************************************************)

(** Maximum degree Δ(G): the sgraph maximum degree [Delta] from base
    (Δ(G) = max over v of |N(v)|). *)
Definition x129_maxdeg (G : sgraph) : nat := Delta G.

(** ** X129 statements ******************************************************)

(** Dvořák–Kráľ–Nejedlý–Škrekovski: there is a degree threshold Δ₀ such that
    every planar graph G of girth at least 5 whose maximum degree is at least
    Δ₀ satisfies χ(G²) ≤ Δ(G) + 2, where G² = [graph_power G 2].

    Faithfulness. (i) "girth at least 5" is [girth_geq G 5] (every genuine cycle
    has length ≥ 5), NOT [has_girth G 5]: the latter is base's "girth EXACTLY 5"
    (girth_geq ∧ a genuine 5-cycle exists) and would wrongly exclude the girth-6+
    planar graphs the conjecture also covers — making the statement strictly
    weaker. (ii) The threshold is in the correct ∃Δ₀,∀G order (a single uniform
    Δ₀, not a per-graph one). (iii) The guard [Δ₀ ≤ Δ(G)] is satisfiable together
    with the hypotheses for every Δ₀ (e.g. a large star is a girth-≥5 planar graph
    of arbitrarily large maximum degree), so the ∀ is not vacuous. *)
Definition dvorak_kral_nejedly_skrekovski_planar_girth5_square_statement : Prop :=
  exists D0 : nat,
    forall G : sgraph,
      wagner_planar G ->
      girth_geq G 5 ->
      (D0 <= x129_maxdeg G)%N ->
      (χ([set: graph_power G 2]) <= x129_maxdeg G + 2)%N.
