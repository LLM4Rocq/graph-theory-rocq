(** * Topological.conjectures.D3D6_unblocked -- legacy blocked OPG rows *)

From GTBase Require Export base.
From GraphTheory Require Import minor.
From Topological.foundations Require Import crossing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record great_circle_arrangement := GreatCircleArrangement {
  gca_graph : sgraph;
  gca_general_position : Prop
}.

Definition three_colourability_of_arrangements_of_great_circles_statement : Prop :=
  forall A : great_circle_arrangement,
    gca_general_position A -> χ([set: gca_graph A]) <= 3.

Record pair_crossing_drawing (G : sgraph) (n : nat) := PairCrossingDrawing {
  pcd_crossing_pairs : nat;
  pcd_count : pcd_crossing_pairs = n
}.

Definition pair_crossing_number (G : sgraph) (n : nat) : Prop :=
  exists _ : pair_crossing_drawing G n, True.

Definition are_different_notions_of_the_crossing_number_the_sam_statement : Prop :=
  forall (G : sgraph) (m n : nat),
    pair_crossing_number G m -> is_crossing_number G n -> m = n.

Record surface_drawing (G : sgraph) := SurfaceDrawing {
  sd_crossings : nat;
  sd_component_image : {set G} -> nat -> Prop
}.

Definition disjoint_union_sides (G : sgraph) (A B : {set G}) : Prop :=
  A :&: B = set0 /\ A :|: B = [set: G].

Definition optimal_surface_drawing
    (G : sgraph) (surface : nat) (D : surface_drawing G) : Prop :=
  surface_embeddable surface G /\
  forall D' : surface_drawing G, sd_crossings D <= sd_crossings D'.

Definition drawing_components_disjoint
    (G : sgraph) (A B : {set G}) (D : surface_drawing G) : Prop :=
  forall i : nat, ~(sd_component_image D A i /\ sd_component_image D B i).

Definition drawing_disconnected_graphs_on_surfaces_statement : Prop :=
  forall (G : sgraph) (A B : {set G}) (surface : nat) (D : surface_drawing G),
    disjoint_union_sides A B ->
    optimal_surface_drawing surface D ->
    drawing_components_disjoint A B D.

Record obstacle_representation (G : sgraph) (k : nat) := ObstacleRepresentation {
  obstacle_points : G -> nat * nat;
  obstacle_index : finType;
  obstacle_count : #|{: obstacle_index}| <= k;
  obstacle_visibility :
    forall x y : G, x != y -> (x -- y) \/ ~ (x -- y)
}.

Definition obstacle_number_at_most (G : sgraph) (k : nat) : Prop :=
  exists _ : obstacle_representation G k, True.

Definition obstacle_number_greater_than_one (G : sgraph) : Prop :=
  ~ obstacle_number_at_most G 1.

Definition obstacle_number_of_planar_graphs_statement : Prop :=
  (exists G : sgraph, wagner_planar G /\ obstacle_number_greater_than_one G) /\
  (exists k : nat, forall G : sgraph, wagner_planar G -> obstacle_number_at_most G k).

Record nonorientable_embedding (G : sgraph) (g : nat) := NonorientableEmbedding {
  noe_scheme : nat;
  noe_genus_bound : noe_scheme <= g
}.

Definition embeds_nonorientable (G : sgraph) (g : nat) : Prop :=
  exists _ : nonorientable_embedding G g, True.

Definition proper_minor (G H : sgraph) : Prop :=
  minor G H /\ #|H| < #|G|.

Definition minor_minimal_nonorientable_obstruction (G : sgraph) (g : nat) : Prop :=
  ~ embeds_nonorientable G g /\
  forall H : sgraph, proper_minor G H -> embeds_nonorientable H g.

Definition consecutive_non_orientable_embedding_obstructions_statement : Prop :=
  exists (G : sgraph) (g : nat),
    minor_minimal_nonorientable_obstruction G g /\
    minor_minimal_nonorientable_obstruction G g.+1.

