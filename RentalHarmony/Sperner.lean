import Mathlib.Analysis.Convex.Combination
import RentalHarmony.PaperDefinitions

/-!
# Sperner Support

Reusable geometric lemmas for the Sperner-style part of
`paper/arxiv-1702.07325.tex`.
-/

noncomputable section

open Set

namespace RentalHarmony

section Geometry

/-- The simplex vertex corresponding to a room label. -/
abbrev labeledRoomVertex {dimension : ℕ} (i : Room (dimension + 1)) :
    RentDivision (dimension + 1) :=
  stdSimplex.vertex (S := ℝ) i

/-- Distinct subdivision vertices define distinct points of the ambient simplex. -/
lemma vertexPos_point_injective
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) :
    Function.Injective (fun v : Vertex =>
      ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) := by
  intro a b h
  apply T.vertexPos_injective
  exact Subtype.ext h

/--
If a simplex point lies in one subdivision facet, then it admits explicit convex weights on the
vertices of that facet.
-/
lemma exists_facet_weights
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (σ : Finset Vertex)
    (x : RentDivision (dimension + 1))
    (hσx : FacetContainsPoint T σ x) :
    ∃ w : Vertex → ℝ,
      (∀ v ∈ σ, 0 ≤ w v) ∧
      (σ.sum w = 1) ∧
      σ.centerMass w
          (fun v => ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) =
        (x : RealPoint dimension) := by
  classical
  let p : Vertex → RealPoint dimension := fun v =>
    ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)
  have hp : Function.Injective p := vertexPos_point_injective T
  have hpσ : Set.InjOn p ↑σ := fun a _ b _ h => hp h
  have hmem : (x : RealPoint dimension) ∈ convexHull ℝ ↑(σ.image p) := by
    simpa [FacetContainsPoint, facetVertexPoints, p] using hσx
  rcases (Finset.mem_convexHull' (R := ℝ) (s := σ.image p)).1 hmem with
    ⟨wp, hwp0, hwp1, hwpx⟩
  refine ⟨fun v => wp (p v), ?_, ?_, ?_⟩
  · intro v hv
    exact hwp0 _ (Finset.mem_image_of_mem _ hv)
  · have h := hwp1
    rw [Finset.sum_image hpσ] at h
    simpa [p] using h
  · rw [Finset.centerMass_eq_of_sum_1 _ _ (by
      have h := hwp1
      rw [Finset.sum_image hpσ] at h
      simpa [p] using h)]
    have h := hwpx
    rw [Finset.sum_image hpσ] at h
    simpa [p] using h

/-- A subdivision vertex lies in the convex hull of any facet that contains it. -/
lemma facetContainsPoint_of_mem
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) {σ : Finset Vertex} {v : Vertex}
    (hv : v ∈ σ) :
    FacetContainsPoint T σ (T.vertexPos v) := by
  change (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) ∈
    convexHull ℝ (facetVertexPoints T σ))
  apply subset_convexHull
  exact ⟨v, hv, rfl⟩

/-- A facet image contains each of its labeled vertex images. -/
lemma facetImageContains_of_mem
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {σ : Finset Vertex} (φ : Vertex → RentDivision (dimension + 1)) {v : Vertex}
    (hv : v ∈ σ) :
    FacetImageContains σ φ (φ v) := by
  change (((φ v : RentDivision (dimension + 1)) : RealPoint dimension) ∈
    convexHull ℝ (facetImagePoints σ φ))
  apply subset_convexHull
  exact ⟨v, hv, rfl⟩

/--
The vertex map canonically induced by a Sperner labeling.

This is the piecewise-linear map whose vertices are sent to the corresponding standard-simplex
vertices.
-/
def spernerVertexMap {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {T : SimplicialSubdivision dimension Vertex} (L : SpernerLabeling T) :
    PiecewiseLinearVertexMap T where
  vertexMap v := labeledRoomVertex (L.label v)
  boundary_preserving := by
    intro v i hi
    have hneq : L.label v ≠ i := by
      intro hEq
      exact hi (hEq ▸ L.label_mem_boundaryFace v)
    simp [labeledRoomVertex, hneq]

/--
Every subdivision vertex now has an incident facet whose domain simplex and image simplex both
contain the corresponding vertex points.
-/
lemma exists_incident_facet_for_sperner_vertex
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (L : SpernerLabeling T) (v : Vertex) :
    ∃ σ ∈ T.facets,
      FacetContainsPoint T σ (T.vertexPos v) ∧
      FacetImageContains σ (spernerVertexMap L).vertexMap ((spernerVertexMap L).vertexMap v) := by
  rcases T.vertex_in_some_facet v with ⟨σ, hσ, hvσ⟩
  refine ⟨σ, hσ, facetContainsPoint_of_mem T hvσ, ?_⟩
  exact facetImageContains_of_mem (spernerVertexMap L).vertexMap hvσ

/-- Every barycentric coordinate of the simplex barycenter is positive. -/
lemma barycentricRentDivision_pos {dimension : ℕ} (i : Room (dimension + 1)) :
    0 < (((barycentricRentDivision (dimension + 1) : RentDivision (dimension + 1)) :
      RealPoint dimension) i) := by
  have hcard : 0 < Fintype.card (Room (dimension + 1)) := by
    simp [Room]
  have hcardR : 0 < (Fintype.card (Room (dimension + 1)) : ℝ) := by
    exact_mod_cast hcard
  change 0 < ((Fintype.card (Room (dimension + 1)) : ℝ)⁻¹)
  exact inv_pos.mpr hcardR

/-- The coordinate hyperplane `x i = 0` is convex. -/
lemma convex_coordZeroSet {dimension : ℕ} (i : Room (dimension + 1)) :
    Convex ℝ {x : RealPoint dimension | x i = 0} := by
  intro x hx y hy a b ha hb hab
  have hx0 : x i = 0 := by simpa using hx
  have hy0 : y i = 0 := by simpa using hy
  simp [hx0, hy0]

/--
If a label `i` is absent from a facet, then the corresponding coordinate vanishes on the whole
facet image of the Sperner vertex map.
-/
lemma facetImagePoints_subset_coordZeroSet_of_missing_label
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {T : SimplicialSubdivision dimension Vertex} (L : SpernerLabeling T) (σ : Finset Vertex)
    (i : Room (dimension + 1))
    (hmissing : ∀ v ∈ σ, L.label v ≠ i) :
    facetImagePoints σ (spernerVertexMap L).vertexMap ⊆ {x : RealPoint dimension | x i = 0} := by
  intro x hx
  rcases hx with ⟨v, hvσ, rfl⟩
  simp [spernerVertexMap, labeledRoomVertex, hmissing v hvσ]

/--
If the barycenter lies in the convex hull of the image of a facet under the Sperner vertex map,
then that facet is fully labeled.
-/
lemma fullyLabeledFacet_of_barycenter_mem_spernerImage
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {T : SimplicialSubdivision dimension Vertex} (L : SpernerLabeling T) (σ : Finset Vertex)
    (hσ : FacetImageContainsBarycenter σ (spernerVertexMap L).vertexMap) :
    FullyLabeledFacet σ L.label := by
  intro i
  by_contra hi
  have hmissing : ∀ v ∈ σ, L.label v ≠ i := by
    intro v hv hvi
    exact hi ⟨v, hv, hvi⟩
  have hsubset := facetImagePoints_subset_coordZeroSet_of_missing_label L σ i hmissing
  have hconv : convexHull ℝ (facetImagePoints σ (spernerVertexMap L).vertexMap) ⊆
      {x : RealPoint dimension | x i = 0} :=
    convexHull_min hsubset (convex_coordZeroSet i)
  have hzero :
      (((barycentricRentDivision (dimension + 1) : RentDivision (dimension + 1)) :
        RealPoint dimension) i) = 0 := by
    exact hconv hσ
  have hpos := barycentricRentDivision_pos (dimension := dimension) i
  linarith

end Geometry

end RentalHarmony
