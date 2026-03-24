import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Finset.Card

/-!
# Paper Definitions

Definitions used to state the results of
`paper/arxiv-1702.07325.tex` as directly as Lean allows.

The paper mixes three kinds of objects:
- rent divisions in a standard simplex;
- roommate preferences and Hall-style room assignments;
- abstract simplex subdivisions and Sperner labelings.

This file provides a statement-facing API for all three.
-/

noncomputable section

open Set
open scoped BigOperators

namespace RentalHarmony

/-- Bedroom indices in an `n`-bedroom apartment. -/
abbrev Room (n : ℕ) := Fin n

/-- Real coordinate vectors on the simplex with `dimension + 1` coordinates. -/
abbrev RealPoint (dimension : ℕ) := Room (dimension + 1) → ℝ

/-- Integer lattice points with `dimension + 1` coordinates. -/
abbrev LatticePoint (dimension : ℕ) := Room (dimension + 1) → ℕ

/-- A rent division is a point of the standard simplex on the room index type. -/
abbrev RentDivision (n : ℕ) := stdSimplex ℝ (Room n)

/-- The equal-rent point `(1 / n, ..., 1 / n)` in the standard simplex. -/
abbrev barycentricRentDivision (n : ℕ) [Nonempty (Room n)] : RentDivision n :=
  stdSimplex.barycenter

/--
A roommate's acceptable-room relation on the rent simplex.

The "one-cent error margin" hypothesis from the paper is intentionally kept separate from this
structure; it will be attached to triangulations / sampled cells later.
-/
structure PreferenceProfile (n : ℕ) where
  Accepts : RentDivision n → Room n → Prop
  exists_acceptable : ∀ d, ∃ r, Accepts d r
  free_room_preferred :
    ∀ {d : RentDivision n} {free expensive : Room n},
      ((d : Room n → ℝ) free = 0) →
      0 < (d : Room n → ℝ) expensive →
      Accepts d free
  free_room_indifferent :
    ∀ {d : RentDivision n} {r s : Room n},
      ((d : Room n → ℝ) r = 0) →
      ((d : Room n → ℝ) s = 0) →
      (Accepts d r ↔ Accepts d s)

/--
The paper's third hypothesis: a roommate ignores sufficiently small pricing errors.

This packages the standing preference assumptions together with an explicit
positive tolerance radius on the normalized rent simplex.
-/
structure TolerantPreferenceProfile (n : ℕ) extends PreferenceProfile n where
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  tolerance_stable :
    ∀ {d d' : RentDivision n} {r : Room n},
      dist d d' < tolerance →
      Accepts d r →
      Accepts d' r

/-- The rooms acceptable to a roommate at a fixed rent division. -/
def acceptableRooms {n : ℕ} (P : PreferenceProfile n) (d : RentDivision n) : Set (Room n) :=
  {r | P.Accepts d r}

/-- The known roommates in the secretive-roommate problem. -/
abbrev KnownPreferences (n known : ℕ) := Fin known → PreferenceProfile n

/-- The known roommates together with the paper's explicit tolerance hypothesis. -/
abbrev KnownTolerantPreferences (n known : ℕ) := Fin known → TolerantPreferenceProfile n

/-- Forget the tolerance witness and retain only the underlying acceptable-room relation. -/
abbrev forgetTolerance {n known : ℕ}
    (prefs : KnownTolerantPreferences n known) : KnownPreferences n known :=
  fun i ↦ (prefs i).toPreferenceProfile

/-- A finite family of allowed rooms, indexed by agents. -/
abbrev RoomChoiceFamily (rooms agents : ℕ) := Fin agents → Finset (Room rooms)

/-- The union of room choices available to a finite set of agents. -/
def choiceNeighbors {rooms agents : ℕ} (choices : RoomChoiceFamily rooms agents)
    (A : Finset (Fin agents)) : Finset (Room rooms) :=
  {r | ∃ i ∈ A, r ∈ choices i}

/-- Hall's condition for a finite family of room choices. -/
def HallCondition {rooms agents : ℕ} (choices : RoomChoiceFamily rooms agents) : Prop :=
  ∀ A : Finset (Fin agents), A.card ≤ (choiceNeighbors choices A).card

/--
The stronger Hall condition used in the paper: every `k` agents collectively see at least
`k + 1` rooms, so one room may be removed in advance by the secretive roommate.
-/
def SecretiveHallCondition {rooms agents : ℕ} (choices : RoomChoiceFamily rooms agents) : Prop :=
  ∀ A : Finset (Fin agents), A.card + 1 ≤ (choiceNeighbors choices A).card

/-- Remove one room from every agent's choice set. -/
def choicesAvoiding {rooms agents : ℕ} (choices : RoomChoiceFamily rooms agents)
    (forbidden : Room rooms) : RoomChoiceFamily rooms agents :=
  fun i ↦ (choices i).erase forbidden

/-- An injective room assignment respecting a prescribed choice family. -/
def IsRoomAssignment {rooms agents : ℕ} (choices : RoomChoiceFamily rooms agents)
    (assignment : Fin agents → Room rooms) : Prop :=
  Function.Injective assignment ∧ ∀ i, assignment i ∈ choices i

/-- An injective room assignment respecting a choice family and avoiding one forbidden room. -/
def IsRoomAssignmentAvoiding {rooms agents : ℕ} (choices : RoomChoiceFamily rooms agents)
    (forbidden : Room rooms) (assignment : Fin agents → Room rooms) : Prop :=
  Function.Injective assignment ∧ ∀ i, assignment i ≠ forbidden ∧ assignment i ∈ choices i

/-- Convert acceptable-room predicates at one rent division into a finite choice family. -/
def acceptableChoiceFamily {rooms agents : ℕ} (prefs : KnownPreferences rooms agents)
    (d : RentDivision rooms) : RoomChoiceFamily rooms agents := by
  classical
  intro i
  exact Finset.univ.filter fun r => (prefs i).Accepts d r

/-- An injective assignment of acceptable rooms at a given rent division. -/
def IsAcceptableAssignment {rooms agents : ℕ} (prefs : KnownPreferences rooms agents)
    (d : RentDivision rooms) (assignment : Fin agents → Room rooms) : Prop :=
  Function.Injective assignment ∧ ∀ i, (prefs i).Accepts d (assignment i)

/-- An injective assignment of acceptable rooms avoiding one room chosen by the secretive agent. -/
def IsAcceptableAssignmentAvoiding {rooms agents : ℕ} (prefs : KnownPreferences rooms agents)
    (d : RentDivision rooms) (forbidden : Room rooms) (assignment : Fin agents → Room rooms) :
    Prop :=
  Function.Injective assignment ∧
    ∀ i, assignment i ≠ forbidden ∧ (prefs i).Accepts d (assignment i)

/--
There is a rent division that remains envy-free for the known roommates after any single room is
removed by the secretive roommate.
-/
def HasSecretiveEnvyFreeDivision {rooms : ℕ}
    (prefs : KnownPreferences rooms (rooms - 1)) : Prop :=
  ∃ d : RentDivision rooms, ∀ forbidden : Room rooms, ∃ assignment : Fin (rooms - 1) → Room rooms,
    IsAcceptableAssignmentAvoiding prefs d forbidden assignment

/--
An abstract subdivision of the standard `dimension`-simplex.

For theorem stating we record the full-dimensional facets and, for each vertex, the exact outer
face of the simplex that contains it.
-/
structure SimplicialSubdivision (dimension : ℕ) (Vertex : Type*) [Fintype Vertex]
    [DecidableEq Vertex] where
  vertexPos : Vertex → RentDivision (dimension + 1)
  vertexPos_injective : Function.Injective vertexPos
  boundaryFace : Vertex → Finset (Room (dimension + 1))
  boundaryFace_nonempty : ∀ v, (boundaryFace v).Nonempty
  vertex_boundary :
    ∀ v i, i ∉ boundaryFace v →
      ((vertexPos v : Room (dimension + 1) → ℝ) i = 0)
  boundaryFace_exact :
    ∀ v i, i ∈ boundaryFace v ↔
      ((vertexPos v : Room (dimension + 1) → ℝ) i ≠ 0)
  facets : Finset (Finset Vertex)
  facet_card : ∀ σ ∈ facets, σ.card = dimension + 1
  covers_simplex :
    ∀ x : RentDivision (dimension + 1), ∃ σ ∈ facets,
      ((x : RealPoint dimension) ∈
        convexHull ℝ
          (((fun v ↦ ((vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) '' ↑σ)))

/-- A Sperner labeling relative to a subdivision of the standard simplex. -/
structure SpernerLabeling {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) where
  label : Vertex → Room (dimension + 1)
  label_mem_boundaryFace : ∀ v, label v ∈ T.boundaryFace v

/-- The set of labels that occur on one facet. -/
def facetLabels {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (σ : Finset Vertex) (label : Vertex → Room (dimension + 1)) : Finset (Room (dimension + 1)) :=
  Finset.univ.filter fun i => ∃ v ∈ σ, label v = i

/-- A facet is fully labeled if every outer label occurs on one of its vertices. -/
def FullyLabeledFacet {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (σ : Finset Vertex) (label : Vertex → Room (dimension + 1)) : Prop :=
  ∀ i : Room (dimension + 1), ∃ v ∈ σ, label v = i

/-- The number of distinct labels occurring on one facet. -/
def DistinctLabelCount {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (σ : Finset Vertex) (label : Vertex → Room (dimension + 1)) : ℕ :=
  (facetLabels σ label).card

/--
The label compression used in the paper's first proof for three roommates.

The paper labels rooms by `1,2,3`; here the corresponding Lean labels are `0,1,2`.
-/
def compressedPreferenceLabel (a b : Room 3) : Room 3 :=
  if (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 2
  else if (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then 0
  else 1

/-- A self-map of the standard simplex preserves every boundary face setwise. -/
def PreservesBoundaryFaces {dimension : ℕ}
    (f : RentDivision (dimension + 1) → RentDivision (dimension + 1)) : Prop :=
  ∀ (d : RentDivision (dimension + 1)) (i : Room (dimension + 1)),
    ((d : Room (dimension + 1) → ℝ) i = 0) →
    ((f d : Room (dimension + 1) → ℝ) i = 0)

/--
Vertex data for the piecewise-linear maps used in the Sperner and rental-harmony arguments.

The affine-on-cells extension is not part of the statement API yet; at the theorem-stating stage we
record only the vertex images and the face constraints they satisfy.
-/
structure PiecewiseLinearVertexMap {dimension : ℕ} {Vertex : Type*} [Fintype Vertex]
    [DecidableEq Vertex] (T : SimplicialSubdivision dimension Vertex) where
  vertexMap : Vertex → RentDivision (dimension + 1)
  boundary_preserving :
    ∀ v i, i ∉ T.boundaryFace v →
      ((vertexMap v : Room (dimension + 1) → ℝ) i = 0)

/-- The point set given by the vertices of one facet in the domain subdivision. -/
def facetVertexPoints {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (σ : Finset Vertex) : Set (RealPoint dimension) :=
  (fun v ↦ ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) '' ↑σ

/-- A point lies in the geometric simplex spanned by one subdivision facet. -/
def FacetContainsPoint {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (σ : Finset Vertex)
    (x : RentDivision (dimension + 1)) : Prop :=
  ((x : RealPoint dimension) ∈ convexHull ℝ (facetVertexPoints T σ))

/-- The point set given by the image of one facet under a vertex map. -/
def facetImagePoints {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (σ : Finset Vertex) (φ : Vertex → RentDivision (dimension + 1)) : Set (RealPoint dimension) :=
  (fun v ↦ ((φ v : RentDivision (dimension + 1)) : RealPoint dimension)) '' ↑σ

/-- One facet image contains a given point of the ambient simplex. -/
def FacetImageContains {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (σ : Finset Vertex) (φ : Vertex → RentDivision (dimension + 1))
    (x : RentDivision (dimension + 1)) : Prop :=
  ((x : RealPoint dimension) ∈ convexHull ℝ (facetImagePoints σ φ))

/-- One facet image contains the simplex barycenter. -/
def FacetImageContainsBarycenter {dimension : ℕ} {Vertex : Type*} [Fintype Vertex]
    [DecidableEq Vertex] (σ : Finset Vertex) (φ : Vertex → RentDivision (dimension + 1)) : Prop :=
  FacetImageContains σ φ (barycentricRentDivision (dimension + 1))

/--
An actual piecewise-linear self-map of the simplex built from a subdivision and vertex images.

The `map_mem_facetImage` field records the cellwise affine realization needed to connect a
preimage point to a facet image in the codomain, and `map_vertex` records the intended
interpolation of the chosen vertex values.
-/
structure PiecewiseLinearSimplexMap {dimension : ℕ} {Vertex : Type*} [Fintype Vertex]
    [DecidableEq Vertex] (T : SimplicialSubdivision dimension Vertex) where
  vertexMap : Vertex → RentDivision (dimension + 1)
  toFun : RentDivision (dimension + 1) → RentDivision (dimension + 1)
  map_vertex : ∀ v, toFun (T.vertexPos v) = vertexMap v
  map_mem_facetImage :
    ∀ x, ∃ σ ∈ T.facets, FacetContainsPoint T σ x ∧ FacetImageContains σ vertexMap (toFun x)
  boundary_preserving : PreservesBoundaryFaces toFun

/-- A real point in the scaled simplex `total • Δ_dimension`. -/
def ScaledSimplexPoint (total dimension : ℕ) :=
  {y : RealPoint dimension // (∀ i, 0 ≤ y i) ∧ ∑ i, y i = (total : ℝ)}

/-- An integer lattice point in the scaled simplex `total • Δ_dimension`. -/
def IsScaledLatticePoint (total dimension : ℕ) (p : LatticePoint dimension) : Prop :=
  ∑ i, p i = total

/--
Genericity condition from Section 6: the point does not lie in the convex hull of any family of at
most `dimension` lattice points of `total • Δ_dimension`.
-/
def GenericScaledSimplexPoint {total dimension : ℕ}
    (y : ScaledSimplexPoint total dimension) : Prop :=
  ∀ s : Finset (LatticePoint dimension),
    (∀ p ∈ s, IsScaledLatticePoint total dimension p) →
    s.card ≤ dimension →
    ((y.1 : RealPoint dimension) ∉
      convexHull ℝ ((fun p : LatticePoint dimension ↦ fun i ↦ (p i : ℝ)) '' ↑s))

/-- The label-count vector attached to one vertex across several labelings. -/
def labelCountVector {dimension m : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (Ls : Fin m → Vertex → Room (dimension + 1)) (v : Vertex) : LatticePoint dimension :=
  fun i ↦ (Finset.univ.filter fun j : Fin m => Ls j v = i).card

/-- The real-valued point corresponding to a label-count vector. -/
def labelCountPoint {dimension m : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (Ls : Fin m → Vertex → Room (dimension + 1)) (v : Vertex) : RealPoint dimension :=
  fun i ↦ (labelCountVector Ls v i : ℝ)

/-- The label-count points contributed by the vertices of one facet. -/
def facetLabelCountPoints {dimension m : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (σ : Finset Vertex) (Ls : Fin m → Vertex → Room (dimension + 1)) : Set (RealPoint dimension) :=
  (fun v ↦ labelCountPoint Ls v) '' ↑σ

end RentalHarmony
