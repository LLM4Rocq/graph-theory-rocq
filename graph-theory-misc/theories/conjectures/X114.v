(** * GTMisc.conjectures.X114 -- v2 subcubic induced-subdivision NP-completeness row *)

From GTBase Require Export base.
From GTMisc.conjectures Require Import D7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Local X114 vocabulary ***********************************************)

(** Induced-subdivision model, replicated from Extremal.conjectures.X98
    (self-contained: graph-theory-misc does not import extremal-graph-theory).
    [x114_induced_subdivision H G] holds iff G contains a subdivision of H as an
    INDUCED subgraph: injective branch vertices, internally-disjoint induced
    edge-paths, and global inducedness (the only G-edges among model vertices join
    consecutive path vertices). *)

Definition x114_consecutive_in_path (G : sgraph) (p : seq G) (u v : G) : Prop :=
  (u, v) \in zip p (behead p) \/ (v, u) \in zip p (behead p).

Definition x114_induced_path_between (G : sgraph) (a b : G) (p : seq G) : Prop :=
  match p with
  | [::] => False
  | x :: q =>
      x = a /\
      last x q = b /\
      uniq p /\
      path (--) x q /\
      forall u v : G,
        u \in p -> v \in p -> u -- v -> u != v ->
        x114_consecutive_in_path p u v
  end.

Definition x114_internal (G : sgraph) (p : seq G) (a b x : G) : Prop :=
  x \in p /\ x != a /\ x != b.

Definition x114_model_vertex (H G : sgraph)
    (br : H -> G) (ep : H -> H -> seq G) (x : G) : Prop :=
  (exists h : H, br h = x) \/ (exists u v : H, u -- v /\ x \in ep u v).

Record x114_induced_subdivision_model (H G : sgraph) := X114Model {
  x114_branch : H -> G;
  x114_branch_injective : injective x114_branch;
  x114_edge_path : H -> H -> seq G;
  x114_edge_path_valid :
    forall u v : H,
      u -- v ->
      x114_induced_path_between
        (x114_branch u) (x114_branch v) (x114_edge_path u v);
  x114_internal_avoids_branch :
    forall (u v w : H) (x : G),
      u -- v ->
      x114_internal (x114_edge_path u v) (x114_branch u) (x114_branch v) x ->
      x != x114_branch w;
  x114_paths_internally_disjoint :
    forall (u v u' v' : H) (x : G),
      u -- v -> u' -- v' ->
      x114_internal (x114_edge_path u v) (x114_branch u) (x114_branch v) x ->
      x114_internal (x114_edge_path u' v') (x114_branch u') (x114_branch v') x ->
      (u = u' /\ v = v') \/ (u = v' /\ v = u');
  x114_global_induced :
    forall x y : G,
      x114_model_vertex x114_branch x114_edge_path x ->
      x114_model_vertex x114_branch x114_edge_path y ->
      x -- y ->
      exists u v : H, u -- v /\ x114_consecutive_in_path (x114_edge_path u v) x y
}.

Definition x114_induced_subdivision (H G : sgraph) : Prop :=
  inhabited (x114_induced_subdivision_model H G).

(** The H-INDUCED-SUBDIVISION-CONTAINMENT decision problem ([H]-ISC), packaged
    as a [D7.problem]: input a graph G (size = #|G|), YES iff G contains an
    induced subdivision of H. *)
Definition x114_hisc_problem (H : sgraph) : problem :=
  {| pinput := sgraph;
     psize  := fun G : sgraph => #|G|;
     pmem   := fun G : sgraph => x114_induced_subdivision H G |}.

(** NP-completeness on the D7 complexity layer: in NP AND NP-hard. *)
Definition x114_np_complete (P : problem) : Prop := in_NP P /\ NP_hard P.

(** Subcubic = maximum degree at most three. *)
Definition x114_subcubic (H : sgraph) : Prop := Delta H <= 3.

(** ** X114 statements *****************************************************)

(** Studies slice: Chudnovsky-Seymour-Trotignon question -- is there a subcubic
    graph H such that H-ISC (deciding whether an input graph contains H as an
    induced subdivision) is NP-complete?  Encoded as the existence of a subcubic
    H whose H-ISC problem is in NP and NP-hard on the D7 [problem]/[in_NP]/
    [NP_hard] complexity layer (the honest cost-bounded reading: NP-hardness is a
    universal claim over all NP problems, non-vacuous by construction; [in_NP]
    supplies a poly-size certificate + poly-cost correct verifier). *)
Definition subcubic_induced_subdivision_np_complete_statement : Prop :=
  exists H : sgraph,
    x114_subcubic H /\ x114_np_complete (x114_hisc_problem H).
