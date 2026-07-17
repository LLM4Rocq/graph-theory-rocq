(** * GTMisc.conjectures.X172 -- v2 Chen-Chvatal bridge-replacement row *)

From GTBase Require Export base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X172 vocabulary ***********************************************)

Definition x172_path_edges (G : sgraph) (s : seq G) : {set {set G}} :=
  [set e in [seq [set p.1; p.2] | p <- zip s (behead s)]].

Definition x172_path_internal (G : sgraph) (s : seq G) : {set G} :=
  [set x : G | (x \in s) && (x != head x s) && (x != last x s)].

Definition x172_one_bridge_replacement (G H : sgraph) : Prop :=
  exists (a b : G) (f : G -> H) (p : seq H),
    a != b /\
    graph_bridge [set a; b] /\
    injective f /\
    path (--) (f a) p /\
    last (f a) p = f b /\
    uniq (f a :: p) /\
    [disjoint x172_path_internal (f a :: p)
     & [set y : H | [exists x : G, f x == y]]] /\
    (forall x y : G,
      [set x; y] != [set a; b] ->
      (x -- y <-> f x -- f y)) /\
    forall u v : H,
      u -- v ->
      ([set u; v] \in x172_path_edges (f a :: p)) \/
      (exists x y : G,
        [set x; y] != [set a; b] /\
        x -- y /\
        u = f x /\
        v = f y).

Inductive x172_generated_by_bridge_replacement : sgraph -> sgraph -> Prop :=
| x172_generated_refl G :
    x172_generated_by_bridge_replacement G G
| x172_generated_step G H K :
    x172_one_bridge_replacement G H ->
    x172_generated_by_bridge_replacement H K ->
    x172_generated_by_bridge_replacement G K.

Definition x172_counterexample_to_lines_bridges_bound (G : sgraph) : Prop :=
  connected [set: G] /\ metric_line_count G + bridge_count G < #|G|.

(** ** X172 statements *****************************************************)

(** Open question: whether all counterexamples to [ell(G)+br(G)>=|G|] arise
    from finitely many graphs by repeatedly replacing a bridge by a path. *)
Definition metric_lines_bridges_counterexamples_finitely_generated_statement : Prop :=
  exists finite_seed_bound : nat,
    forall G : sgraph,
      x172_counterexample_to_lines_bridges_bound G ->
      exists seed : sgraph,
        #|seed| <= finite_seed_bound /\
        x172_generated_by_bridge_replacement seed G.
