import Mathlib.Analysis.Convex.Combination
import RentalHarmony.PaperDefinitions
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Order.IntermediateValue

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

/-- The piecewise-linear simplex map as a bundled continuous map. -/
def toContinuousMap (φ : PiecewiseLinearSimplexMap T) :
    C(RentDivision (dimension + 1), RentDivision (dimension + 1)) :=
  ⟨φ.toFun, φ.continuous_toFun⟩

@[simp] theorem toContinuousMap_apply (φ : PiecewiseLinearSimplexMap T)
    (x : RentDivision (dimension + 1)) :
    φ.toContinuousMap x = φ.toFun x :=
  rfl

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

/-- A boundary-preserving simplex self-map preserves every coordinate face setwise. -/
theorem maps_face_to_itself {f : RentDivision (dimension + 1) → RentDivision (dimension + 1)}
    (hf : PreservesBoundaryFaces f) {σ : Finset (Room (dimension + 1))}
    {x : RentDivision (dimension + 1)}
    (hx : ∀ i, i ∉ σ → (((x : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0) :
    ∀ i, i ∉ σ → (((f x : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0 := by
  intro i hi
  exact hf x i (hx i hi)

/-- The topological boundary of the standard simplex, as a subtype. -/
abbrev SimplexBoundary (dimension : ℕ) :=
  {x : RentDivision (dimension + 1) // ∃ i : Room (dimension + 1),
    ((x : RealPoint dimension) i) = 0}

namespace SimplexBoundary

variable {dimension : ℕ}

/-- The inclusion of the simplex boundary into the simplex. -/
def inclusion : C(SimplexBoundary dimension, RentDivision (dimension + 1)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem inclusion_apply (x : SimplexBoundary dimension) :
    inclusion x = x :=
  rfl

end SimplexBoundary

/--
The straight-line homotopy from the identity map to a face-preserving piecewise-linear simplex map.

In the repaired barycentric-coordinate model this homotopy is available for free because both
endpoints lie in the convex simplex.
-/
def straightLineHomotopy (φ : PiecewiseLinearSimplexMap T) :
    ContinuousMap.Homotopy (ContinuousMap.id (RentDivision (dimension + 1))) φ.toContinuousMap where
  toFun tx := by
    refine
      ⟨(1 - (tx.1 : ℝ)) • (((tx.2 : RentDivision (dimension + 1)) : RealPoint dimension)) +
          (tx.1 : ℝ) •
            (((φ.toFun tx.2 : RentDivision (dimension + 1)) : RealPoint dimension)), ?_⟩
    exact (convex_stdSimplex ℝ (Room (dimension + 1))) tx.2.2 (φ.toFun tx.2).2
      (sub_nonneg.mpr tx.1.2.2) tx.1.2.1 (sub_add_cancel 1 (tx.1 : ℝ))
  continuous_toFun := by
    have ht : Continuous fun tx : unitInterval × RentDivision (dimension + 1) => ((tx.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx :
        Continuous fun tx : unitInterval × RentDivision (dimension + 1) =>
          (((tx.2 : RentDivision (dimension + 1)) : RealPoint dimension)) :=
      continuous_subtype_val.comp continuous_snd
    have hφ :
        Continuous fun tx : unitInterval × RentDivision (dimension + 1) =>
          (((φ.toFun tx.2 : RentDivision (dimension + 1)) : RealPoint dimension)) :=
      continuous_subtype_val.comp
        ((PiecewiseLinearSimplexMap.continuous_toFun (T := T) (φ := φ)).comp continuous_snd)
    exact (((continuous_const.sub ht).smul hx).add (ht.smul hφ)).subtype_mk fun tx =>
      (show
        (1 - (tx.1 : ℝ)) • (((tx.2 : RentDivision (dimension + 1)) : RealPoint dimension)) +
            (tx.1 : ℝ) •
              (((φ.toFun tx.2 : RentDivision (dimension + 1)) : RealPoint dimension)) ∈
          stdSimplex ℝ (Room (dimension + 1)) from by
            exact (convex_stdSimplex ℝ (Room (dimension + 1))) tx.2.2 (φ.toFun tx.2).2
              (sub_nonneg.mpr tx.1.2.2) tx.1.2.1 (sub_add_cancel 1 (tx.1 : ℝ)))
  map_zero_left := by
    intro x
    apply Subtype.ext
    funext i
    change
      (1 - (0 : ℝ)) *
          ((((x : RentDivision (dimension + 1)) : RealPoint dimension) i)) +
        (0 : ℝ) *
          ((((φ.toFun x : RentDivision (dimension + 1)) : RealPoint dimension) i)) =
      (((x : RentDivision (dimension + 1)) : RealPoint dimension) i)
    simp
  map_one_left := by
    intro x
    apply Subtype.ext
    funext i
    change
      (1 - (1 : ℝ)) *
          ((((x : RentDivision (dimension + 1)) : RealPoint dimension) i)) +
        (1 : ℝ) *
          ((((φ.toFun x : RentDivision (dimension + 1)) : RealPoint dimension) i)) =
      (((φ.toFun x : RentDivision (dimension + 1)) : RealPoint dimension) i)
    simp

/-- The intermediate map in the straight-line homotopy at time `t`. -/
def straightLineMap (φ : PiecewiseLinearSimplexMap T) (t : unitInterval) :
    C(RentDivision (dimension + 1), RentDivision (dimension + 1)) :=
  (φ.straightLineHomotopy).curry t

/--
Every intermediate map in the straight-line homotopy still preserves each boundary face setwise.
-/
theorem straightLineMap_preservesBoundaryFaces (φ : PiecewiseLinearSimplexMap T)
    (t : unitInterval) :
    PreservesBoundaryFaces (φ.straightLineMap t) := by
  intro x i hx₀
  have hφ₀ :
      (((φ.toFun x : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0 :=
    φ.boundary_preserving_toFun x i hx₀
  have hφReal : φ.toRealPoint x i = 0 := by
    simpa [PiecewiseLinearSimplexMap.coe_toFun] using hφ₀
  change
      (((1 - (t : ℝ)) • (((x : RentDivision (dimension + 1)) : RealPoint dimension)) +
          (t : ℝ) • (φ.toRealPoint x)) i) = 0
  simp [Pi.smul_apply, smul_eq_mul, hx₀, hφReal]

/--
The identity is homotopic to any face-preserving piecewise-linear simplex map through
face-preserving maps.
-/
theorem homotopicWith_id_boundaryPreserving (φ : PiecewiseLinearSimplexMap T) :
    ContinuousMap.HomotopicWith
      (ContinuousMap.id (RentDivision (dimension + 1))) φ.toContinuousMap
      (fun f => PreservesBoundaryFaces f) := by
  refine ⟨{ toHomotopy := φ.straightLineHomotopy, prop' := ?_ }⟩
  intro t
  exact φ.straightLineMap_preservesBoundaryFaces t

/-- The restriction of a face-preserving simplex map to the boundary subtype. -/
def toBoundaryMap (φ : PiecewiseLinearSimplexMap T) :
    C(SimplexBoundary dimension, SimplexBoundary dimension) := by
  refine ⟨fun x => ?_, ?_⟩
  · refine ⟨φ.toFun x.1, ?_⟩
    rcases x.2 with ⟨i, hi⟩
    exact ⟨i, φ.boundary_preserving_toFun x.1 i hi⟩
  · exact
      ((PiecewiseLinearSimplexMap.continuous_toFun (T := T) (φ := φ)).comp
        continuous_subtype_val).subtype_mk fun x => by
          rcases x.2 with ⟨i, hi⟩
          exact ⟨i, φ.boundary_preserving_toFun x.1 i hi⟩

@[simp] theorem toBoundaryMap_apply (φ : PiecewiseLinearSimplexMap T)
    (x : SimplexBoundary dimension) :
    (φ.toBoundaryMap x).1 = φ.toFun x.1 :=
  rfl

/--
Restricting the straight-line homotopy to the boundary gives a homotopy from the identity on the
boundary to the boundary restriction of the map.
-/
def boundaryStraightLineHomotopy (φ : PiecewiseLinearSimplexMap T) :
    ContinuousMap.Homotopy (ContinuousMap.id (SimplexBoundary dimension)) φ.toBoundaryMap where
  toFun tx := by
    refine ⟨(φ.straightLineHomotopy (tx.1, tx.2.1)), ?_⟩
    rcases tx.2.2 with ⟨i, hi⟩
    exact ⟨i, φ.straightLineMap_preservesBoundaryFaces tx.1 tx.2.1 i hi⟩
  continuous_toFun := by
    let g : unitInterval × SimplexBoundary dimension →
        unitInterval × RentDivision (dimension + 1) :=
      fun tx => (tx.1, tx.2.1)
    have hg : Continuous g := by
      exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact (φ.straightLineHomotopy.continuous.comp hg).subtype_mk fun tx => by
      rcases tx.2.2 with ⟨i, hi⟩
      exact ⟨i, φ.straightLineMap_preservesBoundaryFaces tx.1 tx.2.1 i hi⟩
  map_zero_left := by
    intro x
    apply Subtype.ext
    simp
  map_one_left := by
    intro x
    apply Subtype.ext
    simp [toBoundaryMap]

/--
Topological reduction of the surjectivity contradiction:
once a face-preserving simplex map extends to a nullhomotopic map into the boundary, the boundary
itself must be contractible.
-/
theorem boundary_contractible_of_nullhomotopic_boundaryExtension
    (φ : PiecewiseLinearSimplexMap T)
    (F : C(RentDivision (dimension + 1), SimplexBoundary dimension))
    (hF : F.comp (SimplexBoundary.inclusion (dimension := dimension)) = φ.toBoundaryMap)
    (hNull : F.Nullhomotopic) :
    ContractibleSpace (SimplexBoundary dimension) := by
  have hBoundaryNull :
      (F.comp (SimplexBoundary.inclusion (dimension := dimension))).Nullhomotopic :=
    hNull.comp_left (SimplexBoundary.inclusion (dimension := dimension))
  have hφNull : φ.toBoundaryMap.Nullhomotopic := by
    simpa [hF] using hBoundaryNull
  rcases hφNull with ⟨x, hx⟩
  have hidφ :
      ContinuousMap.Homotopic (ContinuousMap.id (SimplexBoundary dimension)) φ.toBoundaryMap :=
    ⟨φ.boundaryStraightLineHomotopy⟩
  exact (contractible_iff_id_nullhomotopic (SimplexBoundary dimension)).2 ⟨x, hidφ.trans hx⟩

/-- A point of the 1-simplex with vanishing second coordinate is the left endpoint. -/
lemma rentDivision_two_eq_vertex_zero_of_coord1_zero (x : RentDivision 2)
    (hx : (((x : RentDivision 2) : RealPoint 1) 1) = 0) :
    x = stdSimplex.vertex (S := ℝ) (0 : Fin 2) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · have hsum := stdSimplex.add_eq_one x
    have h0 : x 0 = 1 := by simpa [hx] using hsum
    simpa [stdSimplex.vertex] using h0
  · simpa [stdSimplex.vertex] using hx

/-- A point of the 1-simplex with vanishing first coordinate is the right endpoint. -/
lemma rentDivision_two_eq_vertex_one_of_coord0_zero (x : RentDivision 2)
    (hx : (((x : RentDivision 2) : RealPoint 1) 0) = 0) :
    x = stdSimplex.vertex (S := ℝ) (1 : Fin 2) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · simpa [stdSimplex.vertex] using hx
  · have hsum := stdSimplex.add_eq_one x
    have h1 : x 1 = 1 := by simpa [hx, add_comm] using hsum
    simpa [stdSimplex.vertex] using h1

end PiecewiseLinearSimplexMap

/--
Paper Section 5 in dimension `1`: a continuous face-preserving piecewise-linear self-map of the
interval is surjective.
-/
theorem facePreservingMap_surjective_dimensionOne
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision 1 Vertex) (φ : PiecewiseLinearSimplexMap T) :
    Function.Surjective φ.toFun := by
  let h : RentDivision 2 ≃ₜ unitInterval := stdSimplexHomeomorphUnitInterval
  let g : unitInterval → unitInterval := fun t => h (φ.toFun (h.symm t))
  have hg : Continuous g :=
    h.continuous_toFun.comp ((PiecewiseLinearSimplexMap.continuous_toFun (T := T) (φ := φ)).comp
      h.symm.continuous_toFun)
  have hsymm0 : h.symm 0 = stdSimplex.vertex (S := ℝ) (0 : Fin 2) := by
    apply h.injective
    simp [h]
  have hsymm1 : h.symm 1 = stdSimplex.vertex (S := ℝ) (1 : Fin 2) := by
    apply h.injective
    simp [h]
  have hg0 : g 0 = 0 := by
    rw [show g 0 = h (φ.toFun (stdSimplex.vertex (S := ℝ) (0 : Fin 2))) by
      simp [g, hsymm0]]
    have hcoord :
        (((φ.toFun (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) : RentDivision 2) :
          RealPoint 1) 1) = 0 :=
      PiecewiseLinearSimplexMap.boundary_preserving_toFun (T := T) (φ := φ)
        (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) 1 rfl
    rw [PiecewiseLinearSimplexMap.rentDivision_two_eq_vertex_zero_of_coord1_zero _ hcoord]
    simp [h]
  have hg1 : g 1 = 1 := by
    rw [show g 1 = h (φ.toFun (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) by
      simp [g, hsymm1]]
    have hcoord :
        (((φ.toFun (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) : RentDivision 2) :
          RealPoint 1) 0) = 0 :=
      PiecewiseLinearSimplexMap.boundary_preserving_toFun (T := T) (φ := φ)
        (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) 0 rfl
    rw [PiecewiseLinearSimplexMap.rentDivision_two_eq_vertex_one_of_coord0_zero _ hcoord]
    simp [h]
  intro y
  let hy : unitInterval := h y
  have hy_mem : hy ∈ Set.Icc (g 0) (g 1) := by
    rw [hg0, hg1]
    exact ⟨hy.2.1, hy.2.2⟩
  rcases (intermediate_value_univ 0 1 hg hy_mem) with ⟨t, ht⟩
  refine ⟨h.symm t, ?_⟩
  apply h.injective
  simpa [g, hy] using ht

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
