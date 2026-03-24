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
