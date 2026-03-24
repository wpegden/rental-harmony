import Mathlib.Analysis.Convex.Combination
import RentalHarmony.PaperDefinitions

/-!
# Sperner Support

Reusable geometric lemmas for the Sperner-style part of
`paper/arxiv-1702.07325.tex`.
-/

noncomputable section

open Set
open scoped BigOperators

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

/-- A labeled subdivision vertex has positive coordinate in its own label. -/
lemma vertexPos_coord_pos_of_label_eq
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {T : SimplicialSubdivision dimension Vertex} (L : SpernerLabeling T)
    {v : Vertex} {i : Room (dimension + 1)} (hlabel : L.label v = i) :
    0 < (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) i) := by
  have hmem : i ∈ T.boundaryFace v := by
    simpa [hlabel] using L.label_mem_boundaryFace v
  have hne :
      (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) i) ≠ 0 :=
    (T.boundaryFace_exact v i).mp hmem
  have hnonneg :
      0 ≤ (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) i) :=
    (T.vertexPos v).2.1 i
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/--
The simplex point obtained by applying the Sperner vertex map to one facet and one system of
convex weights.
-/
def spernerFacetCenterMass
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {T : SimplicialSubdivision dimension Vertex} (L : SpernerLabeling T)
    (σ : Finset Vertex) (w : Vertex → ℝ)
    (hw₀ : ∀ v ∈ σ, 0 ≤ w v) (hw₁ : σ.sum w = 1) :
    RentDivision (dimension + 1) := by
  refine ⟨σ.centerMass w (fun v =>
    (((spernerVertexMap L).vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)),
    ?_⟩
  exact (convex_stdSimplex ℝ (Room (dimension + 1))).centerMass_mem
    hw₀ (by simp [hw₁]) (by intro v hv; exact ((spernerVertexMap L).vertexMap v).2)

@[simp] lemma coe_spernerFacetCenterMass
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {T : SimplicialSubdivision dimension Vertex} (L : SpernerLabeling T)
    (σ : Finset Vertex) (w : Vertex → ℝ)
    (hw₀ : ∀ v ∈ σ, 0 ≤ w v) (hw₁ : σ.sum w = 1) :
    ((spernerFacetCenterMass L σ w hw₀ hw₁ : RentDivision (dimension + 1)) :
      RealPoint dimension) =
      σ.centerMass w (fun v =>
        (((spernerVertexMap L).vertexMap v : RentDivision (dimension + 1)) :
          RealPoint dimension)) :=
  rfl

/--
If a facet center of mass has vanishing `i`-th coordinate, then any vertex of positive `i`-th
coordinate must receive zero weight.
-/
lemma facet_weight_eq_zero_of_coord_zero_of_label_eq
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {T : SimplicialSubdivision dimension Vertex} (L : SpernerLabeling T)
    {σ : Finset Vertex} {x : RentDivision (dimension + 1)} {w : Vertex → ℝ}
    (hw₀ : ∀ v ∈ σ, 0 ≤ w v) (hw₁ : σ.sum w = 1)
    (hwx :
      σ.centerMass w
          (fun v => ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) =
        (x : RealPoint dimension))
    {i : Room (dimension + 1)} (hx₀ : ((x : RealPoint dimension) i) = 0)
  {v : Vertex} (hvσ : v ∈ σ) (hlabel : L.label v = i) :
    w v = 0 := by
  have hcoord := congrArg (fun p : RealPoint dimension => p i) hwx
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁] at hcoord
  have hcoord' :
      ∑ u ∈ σ,
        w u * (((T.vertexPos u : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0 := by
    simpa [Pi.smul_apply, hx₀] using hcoord
  have hnonneg :
      ∀ u ∈ σ,
        0 ≤ w u * (((T.vertexPos u : RentDivision (dimension + 1)) : RealPoint dimension) i) := by
    intro u hu
    exact mul_nonneg (hw₀ u hu) ((T.vertexPos u).2.1 i)
  have htermzero :
      w v * (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hcoord' v hvσ
  have hpos := vertexPos_coord_pos_of_label_eq L hlabel
  nlinarith

/--
The weighted image of one domain facet under the Sperner vertex map preserves every vanished
coordinate of the original point.
-/
lemma spernerFacetCenterMass_coord_eq_zero_of_coord_eq_zero
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {T : SimplicialSubdivision dimension Vertex} (L : SpernerLabeling T)
    {σ : Finset Vertex} {x : RentDivision (dimension + 1)} {w : Vertex → ℝ}
    (hw₀ : ∀ v ∈ σ, 0 ≤ w v) (hw₁ : σ.sum w = 1)
    (hwx :
      σ.centerMass w
          (fun v => ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) =
        (x : RealPoint dimension))
    {i : Room (dimension + 1)} (hx₀ : ((x : RealPoint dimension) i) = 0) :
    (((spernerFacetCenterMass L σ w hw₀ hw₁ : RentDivision (dimension + 1)) :
      RealPoint dimension) i) = 0 := by
  rw [coe_spernerFacetCenterMass, Finset.centerMass_eq_of_sum_1 _ _ hw₁]
  rw [show
      (∑ v ∈ σ,
          w v •
            (((spernerVertexMap L).vertexMap v : RentDivision (dimension + 1)) :
              RealPoint dimension)) i =
        ∑ v ∈ σ,
          w v *
            ((((spernerVertexMap L).vertexMap v : RentDivision (dimension + 1)) :
              RealPoint dimension) i) by
      simp [Pi.smul_apply, smul_eq_mul]]
  refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 ?_
  · intro v hv
    exact mul_nonneg (hw₀ v hv) (((spernerVertexMap L).vertexMap v).2.1 i)
  · intro v hvσ
    by_cases hlabel : L.label v = i
    · have hwv0 := facet_weight_eq_zero_of_coord_zero_of_label_eq
        (L := L) hw₀ hw₁ hwx hx₀ hvσ hlabel
      simp [spernerVertexMap, labeledRoomVertex, hlabel, hwv0]
    · simp [spernerVertexMap, labeledRoomVertex, hlabel]

/--
Any point of one subdivision facet has an image point in the corresponding Sperner facet image
whose zero coordinates are preserved.
-/
lemma exists_spernerFacetImagePoint_of_facetContains
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {T : SimplicialSubdivision dimension Vertex} (L : SpernerLabeling T)
    {σ : Finset Vertex} {x : RentDivision (dimension + 1)}
    (hσx : FacetContainsPoint T σ x) :
    ∃ y : RentDivision (dimension + 1),
      (∀ i, ((x : RealPoint dimension) i) = 0 →
        ((y : RealPoint dimension) i) = 0) ∧
      FacetImageContains σ (spernerVertexMap L).vertexMap y := by
  rcases exists_facet_weights T σ x hσx with ⟨w, hw₀, hw₁, hwx⟩
  refine ⟨spernerFacetCenterMass L σ w hw₀ hw₁, ?_, ?_⟩
  · intro i hx₀
    simpa using spernerFacetCenterMass_coord_eq_zero_of_coord_eq_zero
      (L := L) hw₀ hw₁ hwx hx₀
  · change
      ((σ.centerMass w fun v =>
          (((spernerVertexMap L).vertexMap v : RentDivision (dimension + 1)) :
            RealPoint dimension)) ∈
        convexHull ℝ (facetImagePoints σ (spernerVertexMap L).vertexMap))
    exact σ.centerMass_mem_convexHull hw₀ (by simp [hw₁]) (by
      intro v hv
      exact ⟨v, hv, rfl⟩)

/--
Every simplex point has a Sperner-image point lying in the image of one containing subdivision
facet and preserving all vanished coordinates.
-/
lemma exists_spernerMapValue
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (L : SpernerLabeling T)
    (x : RentDivision (dimension + 1)) :
    ∃ y : RentDivision (dimension + 1),
      (∀ i, ((x : RealPoint dimension) i) = 0 →
        ((y : RealPoint dimension) i) = 0) ∧
      ∃ σ ∈ T.facets, FacetContainsPoint T σ x ∧
        FacetImageContains σ (spernerVertexMap L).vertexMap y := by
  by_cases hvertex : ∃ v, T.vertexPos v = x
  · let v := Classical.choose hvertex
    have hvx : T.vertexPos v = x := Classical.choose_spec hvertex
    refine ⟨(spernerVertexMap L).vertexMap v, ?_, ?_⟩
    · intro i hx₀
      have hi_not : i ∉ T.boundaryFace v := by
        intro hi
        have hne : ((x : RealPoint dimension) i) ≠ 0 := by
          simpa [hvx] using (T.boundaryFace_exact v i).mp hi
        exact hne hx₀
      simpa using (spernerVertexMap L).boundary_preserving v i hi_not
    · rcases exists_incident_facet_for_sperner_vertex T L v with ⟨σ, hσ, hσx, hσy⟩
      exact ⟨σ, hσ, by simpa [hvx] using hσx, hσy⟩
  · rcases T.covers_simplex x with ⟨σ, hσ, hσx⟩
    rcases exists_spernerFacetImagePoint_of_facetContains (L := L) hσx with
      ⟨y, hyzero, hyimage⟩
    exact ⟨y, hyzero, σ, hσ, hσx, hyimage⟩

/--
Paper Section 2: every Sperner labeling admits the piecewise-linear simplex map determined by its
vertex labels.
-/
theorem exists_piecewiseLinearSimplexMap_of_spernerLabeling
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (L : SpernerLabeling T) :
    ∃ φ : PiecewiseLinearSimplexMap T, φ.vertexMap = (spernerVertexMap L).vertexMap := by
  classical
  refine ⟨{
    vertexMap := (spernerVertexMap L).vertexMap
    toFun := fun x =>
      if hvertex : ∃ v, T.vertexPos v = x then
        (spernerVertexMap L).vertexMap (Classical.choose hvertex)
      else
        Classical.choose (exists_spernerMapValue T L x)
    map_vertex := ?_
    map_mem_facetImage := ?_
    boundary_preserving := ?_
    }, rfl⟩
  · intro v
    have hvertex : ∃ u, T.vertexPos u = T.vertexPos v := ⟨v, rfl⟩
    have hchoose : Classical.choose hvertex = v :=
      T.vertexPos_injective (Classical.choose_spec hvertex)
    simp [hvertex, hchoose]
  · intro x
    by_cases hvertex : ∃ v, T.vertexPos v = x
    · let v := Classical.choose hvertex
      have hvx : T.vertexPos v = x := Classical.choose_spec hvertex
      rcases exists_incident_facet_for_sperner_vertex T L v with ⟨σ, hσ, hσx, hσy⟩
      refine ⟨σ, hσ, by simpa [hvx] using hσx, ?_⟩
      simp [hvertex]
      simpa using hσy
    · rcases (Classical.choose_spec (exists_spernerMapValue T L x)).2 with ⟨σ, hσ, hσx, hσy⟩
      refine ⟨σ, hσ, hσx, ?_⟩
      simp [hvertex]
      simpa using hσy
  · intro x i hx₀
    by_cases hvertex : ∃ v, T.vertexPos v = x
    · let v := Classical.choose hvertex
      have hvx : T.vertexPos v = x := Classical.choose_spec hvertex
      have hi_not : i ∉ T.boundaryFace v := by
        intro hi
        have hne : ((x : RealPoint dimension) i) ≠ 0 := by
          simpa [hvx] using (T.boundaryFace_exact v i).mp hi
        exact hne hx₀
      simp [hvertex]
      simpa using (spernerVertexMap L).boundary_preserving v i hi_not
    · simpa [hvertex] using (Classical.choose_spec (exists_spernerMapValue T L x)).1 i hx₀

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
