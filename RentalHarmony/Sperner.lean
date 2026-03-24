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

/-- Any vertex outside the chosen supporting facet receives zero barycentric weight. -/
lemma baryCoord_eq_zero_of_not_mem_supportingFacet
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (x : RentDivision (dimension + 1)) (v : Vertex)
    (hv : v ∉ T.supportingFacet x) :
    T.baryCoord v x = 0 := by
  by_contra hne
  exact hv (T.baryCoord_supported x v hne)

/--
The subdivision's chosen supporting facet really contains the domain point, because the global
barycentric coordinates reconstruct the point from vertices of that facet.
-/
lemma supportingFacet_contains_point
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (x : RentDivision (dimension + 1)) :
    FacetContainsPoint T (T.supportingFacet x) x := by
  classical
  let τ : Finset Vertex := Finset.univ.filter fun v => T.baryCoord v x ≠ 0
  have hτsubset : τ ⊆ T.supportingFacet x := by
    intro v hv
    exact T.baryCoord_supported x v (by simpa [τ] using (Finset.mem_filter.mp hv).2)
  have hτpos : 0 < ∑ v ∈ τ, T.baryCoord v x := by
    have hτsum :
        ∑ v ∈ τ, T.baryCoord v x = ∑ v, T.baryCoord v x := by
      simpa [τ] using (Finset.sum_filter_ne_zero (s := Finset.univ) (f := fun v => T.baryCoord v x))
    rw [hτsum, T.baryCoord_sum x]
    positivity
  have hτmem :
      τ.centerMass (fun v => T.baryCoord v x)
          (fun v => ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) ∈
        convexHull ℝ (facetVertexPoints T (T.supportingFacet x)) := by
    apply τ.centerMass_mem_convexHull
    · intro v hv
      exact T.baryCoord_nonneg x v
    · exact hτpos
    · intro v hv
      exact ⟨v, hτsubset hv, rfl⟩
  have hτcenter :
      τ.centerMass (fun v => T.baryCoord v x)
          (fun v => ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) =
        (x : RealPoint dimension) := by
    calc
      τ.centerMass (fun v => T.baryCoord v x)
          (fun v => ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) =
          Finset.univ.centerMass (fun v => T.baryCoord v x)
            (fun v => ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) := by
              simpa [τ] using
                (Finset.centerMass_filter_ne_zero
                  (t := Finset.univ)
                  (w := fun v => T.baryCoord v x)
                  (z := fun v =>
                    ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)))
      _ = (x : RealPoint dimension) := T.baryCoord_reconstruct x
  simpa [FacetContainsPoint, hτcenter] using hτmem

/--
If the `i`-th coordinate of a simplex point vanishes, then every vertex carrying positive
barycentric weight at that point also has vanishing `i`-th coordinate.
-/
lemma vertexPos_coord_eq_zero_of_baryCoord_ne_zero_of_coord_eq_zero
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex)
    {x : RentDivision (dimension + 1)} {i : Room (dimension + 1)}
    (hx₀ : ((x : RealPoint dimension) i) = 0) {v : Vertex}
    (hv : T.baryCoord v x ≠ 0) :
    (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0 := by
  have hcoord := congrArg (fun p : RealPoint dimension => p i) (T.baryCoord_reconstruct x)
  rw [Finset.centerMass_eq_of_sum_1 _ _ (T.baryCoord_sum x)] at hcoord
  have hcoord' :
      ∑ u ∈ Finset.univ,
        T.baryCoord u x * (((T.vertexPos u : RentDivision (dimension + 1)) :
          RealPoint dimension) i) = 0 := by
    simpa [Pi.smul_apply, smul_eq_mul, hx₀] using hcoord
  have hnonneg :
      ∀ u ∈ Finset.univ,
        0 ≤ T.baryCoord u x * (((T.vertexPos u : RentDivision (dimension + 1)) :
          RealPoint dimension) i) := by
    intro u hu
    exact mul_nonneg (T.baryCoord_nonneg x u) ((T.vertexPos u).2.1 i)
  have htermzero :
      T.baryCoord v x * (((T.vertexPos v : RentDivision (dimension + 1)) :
        RealPoint dimension) i) = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hcoord' v (by simp)
  have hweightpos : 0 < T.baryCoord v x := lt_of_le_of_ne (T.baryCoord_nonneg x v) (Ne.symm hv)
  have hcoordnonneg :
      0 ≤ (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) i) :=
    (T.vertexPos v).2.1 i
  nlinarith

namespace PiecewiseLinearSimplexMap

variable {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
variable {T : SimplicialSubdivision dimension Vertex}

/-- Coordinate-wise expansion of the derived center-of-mass map. -/
theorem toRealPoint_apply (φ : PiecewiseLinearSimplexMap T)
    (x : RentDivision (dimension + 1)) (i : Room (dimension + 1)) :
    φ.toRealPoint x i =
      ∑ v, T.baryCoord v x *
        (((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension) i) := by
  rw [PiecewiseLinearSimplexMap.toRealPoint, Finset.centerMass_eq_of_sum_1 _ _ (T.baryCoord_sum x)]
  simp [Pi.smul_apply, smul_eq_mul]

/-- The derived ambient-vector-valued map is continuous. -/
theorem continuous_toRealPoint (φ : PiecewiseLinearSimplexMap T) :
    Continuous φ.toRealPoint := by
  refine continuous_pi ?_
  intro i
  simp_rw [toRealPoint_apply]
  exact continuous_finset_sum _ fun v hv => (T.continuous_baryCoord v).mul continuous_const

/-- The derived simplex-valued map is continuous. -/
theorem continuous_toFun (φ : PiecewiseLinearSimplexMap T) :
    Continuous φ.toFun := by
  simpa [PiecewiseLinearSimplexMap.toFun] using
    (Continuous.subtype_mk (continuous_toRealPoint (φ := φ)) fun x => (φ.toFun x).2)

/-- The derived simplex map interpolates its prescribed vertex values. -/
theorem map_vertex (φ : PiecewiseLinearSimplexMap T) (v : Vertex) :
    φ.toFun (T.vertexPos v) = φ.vertexMap v := by
  apply Subtype.ext
  simpa [PiecewiseLinearSimplexMap.toFun, PiecewiseLinearSimplexMap.toRealPoint,
    T.baryCoord_vertex] using
    (Finset.centerMass_ite_eq
      (t := Finset.univ)
      (i := v)
      (z := fun w =>
        ((φ.vertexMap w : RentDivision (dimension + 1)) : RealPoint dimension))
      (hi := by simp))

/--
The derived center-of-mass map sends every point to the convex hull of the image of its supporting
facet.
-/
theorem map_mem_facetImage (φ : PiecewiseLinearSimplexMap T)
    (x : RentDivision (dimension + 1)) :
    ∃ σ ∈ T.facets, FacetContainsPoint T σ x ∧ FacetImageContains σ φ.vertexMap (φ.toFun x) := by
  classical
  let τ : Finset Vertex := Finset.univ.filter fun v => T.baryCoord v x ≠ 0
  have hτsubset : τ ⊆ T.supportingFacet x := by
    intro v hv
    exact T.baryCoord_supported x v (by simpa [τ] using (Finset.mem_filter.mp hv).2)
  have hτpos : 0 < ∑ v ∈ τ, T.baryCoord v x := by
    have hτsum :
        ∑ v ∈ τ, T.baryCoord v x = ∑ v, T.baryCoord v x := by
      simpa [τ] using (Finset.sum_filter_ne_zero (s := Finset.univ) (f := fun v => T.baryCoord v x))
    rw [hτsum, T.baryCoord_sum x]
    positivity
  have hτimage :
      τ.centerMass (fun v => T.baryCoord v x)
          (fun v => ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ∈
        convexHull ℝ (facetImagePoints (T.supportingFacet x) φ.vertexMap) := by
    apply τ.centerMass_mem_convexHull
    · intro v hv
      exact T.baryCoord_nonneg x v
    · exact hτpos
    · intro v hv
      exact ⟨v, hτsubset hv, rfl⟩
  have hτcenter :
      τ.centerMass (fun v => T.baryCoord v x)
          (fun v => ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) =
        ((φ.toFun x : RentDivision (dimension + 1)) : RealPoint dimension) := by
    calc
      τ.centerMass (fun v => T.baryCoord v x)
          (fun v => ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) =
          Finset.univ.centerMass (fun v => T.baryCoord v x)
            (fun v => ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) := by
              simpa [τ] using
                (Finset.centerMass_filter_ne_zero
                  (t := Finset.univ)
                  (w := fun v => T.baryCoord v x)
                  (z := fun v =>
                    ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)))
      _ = φ.toRealPoint x := rfl
      _ = ((φ.toFun x : RentDivision (dimension + 1)) : RealPoint dimension) := by
            exact (PiecewiseLinearSimplexMap.coe_toFun (φ := φ) x).symm
  refine ⟨T.supportingFacet x, T.supportingFacet_mem x, supportingFacet_contains_point T x, ?_⟩
  simpa [FacetImageContains, hτcenter] using hτimage

/-- The derived center-of-mass map preserves every boundary face of the simplex. -/
theorem boundary_preserving_toFun (φ : PiecewiseLinearSimplexMap T) :
    PreservesBoundaryFaces φ.toFun := by
  intro x i hx₀
  rw [PiecewiseLinearSimplexMap.coe_toFun, PiecewiseLinearSimplexMap.toRealPoint]
  rw [Finset.centerMass_eq_of_sum_1 _ _ (T.baryCoord_sum x)]
  rw [show
      (∑ v ∈ Finset.univ,
          T.baryCoord v x •
            (((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension))) i =
        ∑ v ∈ Finset.univ,
          T.baryCoord v x *
            ((((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension) i)) by
      simp [Pi.smul_apply, smul_eq_mul]]
  refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 ?_
  · intro v hv
    exact mul_nonneg (T.baryCoord_nonneg x v) ((φ.vertexMap v).2.1 i)
  · intro v hv
    by_cases hv0 : T.baryCoord v x = 0
    · simp [hv0]
    · have hvertex0 :=
          vertexPos_coord_eq_zero_of_baryCoord_ne_zero_of_coord_eq_zero T hx₀ hv0
      have hi_not : i ∉ T.boundaryFace v := by
        intro hi
        exact ((T.boundaryFace_exact v i).mp hi) hvertex0
      simp [φ.boundary_preserving v i hi_not]

end PiecewiseLinearSimplexMap

/--
Paper Section 2: every Sperner labeling admits the piecewise-linear simplex map determined by its
vertex labels.
-/
theorem exists_piecewiseLinearSimplexMap_of_spernerLabeling
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (L : SpernerLabeling T) :
    ∃ φ : PiecewiseLinearSimplexMap T, φ.vertexMap = (spernerVertexMap L).vertexMap := by
  exact ⟨({ toPiecewiseLinearVertexMap := spernerVertexMap L } : PiecewiseLinearSimplexMap T), rfl⟩

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
