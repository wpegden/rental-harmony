import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import RentalHarmony.PaperDefinitions

/-!
# Section 5 Graph Support

Lower-dimensional face and incidence infrastructure for the combinatorial Section 5 proof from
`paper/arxiv-1702.07325.tex`.
-/

noncomputable section

open Set

namespace RentalHarmony

universe u

section Faces

variable {dimension : ℕ} {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
variable (T : SimplicialSubdivision dimension Vertex)

/-- A nonempty face of the subdivision, represented as a nonempty subset of one facet. -/
structure SubdivisionFace where
  carrier : Finset Vertex
  nonempty : carrier.Nonempty
  subset_facet : ∃ σ ∈ T.facets, carrier ⊆ σ

namespace SubdivisionFace

variable {T : SimplicialSubdivision dimension Vertex}

/-- The simplicial dimension of a nonempty subdivision face. -/
def dim (τ : SubdivisionFace T) : ℕ :=
  τ.carrier.card - 1

@[simp] lemma card_pos (τ : SubdivisionFace T) : 0 < τ.carrier.card :=
  Finset.card_pos.mpr τ.nonempty

lemma card_le (τ : SubdivisionFace T) : τ.carrier.card ≤ dimension + 1 := by
  rcases τ.subset_facet with ⟨σ, hσ, hτσ⟩
  calc
    τ.carrier.card ≤ σ.card := Finset.card_le_card hτσ
    _ = dimension + 1 := T.facet_card σ hσ

lemma card_eq_dim_succ (τ : SubdivisionFace T) : τ.carrier.card = τ.dim + 1 := by
  unfold dim
  symm
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt τ.card_pos)

lemma dim_le (τ : SubdivisionFace T) : τ.dim ≤ dimension := by
  have hcard : τ.dim + 1 ≤ dimension + 1 := by
    simpa [τ.card_eq_dim_succ] using τ.card_le
  exact Nat.succ_le_succ_iff.mp hcard

lemma exists_facet_superset (τ : SubdivisionFace T) :
    ∃ σ ∈ T.facets, τ.carrier ⊆ σ :=
  τ.subset_facet

/-- Every nonempty subset of a subdivision face is again a subdivision face. -/
def ofSubset (τ : SubdivisionFace T) (s : Finset Vertex) (hs : s ⊆ τ.carrier)
    (hsne : s.Nonempty) : SubdivisionFace T where
  carrier := s
  nonempty := hsne
  subset_facet := by
    rcases τ.subset_facet with ⟨σ, hσ, hτσ⟩
    exact ⟨σ, hσ, hs.trans hτσ⟩

/-- Any subdivision vertex determines a singleton face. -/
def singleton (v : Vertex) : SubdivisionFace T where
  carrier := ({v} : Finset Vertex)
  nonempty := Finset.singleton_nonempty v
  subset_facet := by
    rcases T.vertex_in_some_facet v with ⟨σ, hσ, hvσ⟩
    exact ⟨σ, hσ, Finset.singleton_subset_iff.mpr hvσ⟩

@[simp] lemma singleton_carrier (v : Vertex) :
    (singleton (T := T) v).carrier = ({v} : Finset Vertex) :=
  rfl

/-- Any actual facet can be viewed as a subdivision face. -/
def ofFacet (σ : Finset Vertex) (hσ : σ ∈ T.facets) : SubdivisionFace T where
  carrier := σ
  nonempty := by
    apply Finset.card_pos.mp
    rw [T.facet_card σ hσ]
    positivity
  subset_facet := ⟨σ, hσ, Finset.Subset.rfl⟩

@[simp] lemma ofFacet_carrier (σ : Finset Vertex) (hσ : σ ∈ T.facets) :
    (ofFacet (T := T) σ hσ).carrier = σ :=
  rfl

@[ext] theorem ext {τ σ : SubdivisionFace T} (h : τ.carrier = σ.carrier) : τ = σ := by
  cases τ
  cases σ
  cases h
  simp

/-- The geometric point set spanned by one subdivision face. -/
def vertexPoints (τ : SubdivisionFace T) : Set (RealPoint dimension) :=
  (fun v ↦ ((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)) '' ↑τ.carrier

/-- A simplex point lies in the geometric simplex spanned by a subdivision face. -/
def ContainsPoint (τ : SubdivisionFace T) (x : RentDivision (dimension + 1)) : Prop :=
  ((x : RealPoint dimension) ∈ convexHull ℝ (τ.vertexPoints (T := T)))

/-- The image point set of one subdivision face under a vertex map. -/
def imagePoints (τ : SubdivisionFace T) (φ : Vertex → RentDivision (dimension + 1)) :
    Set (RealPoint dimension) :=
  (fun v ↦ ((φ v : RentDivision (dimension + 1)) : RealPoint dimension)) '' ↑τ.carrier

/-- A subdivision-face image contains a given simplex point. -/
def ImageContains (τ : SubdivisionFace T) (φ : Vertex → RentDivision (dimension + 1))
    (x : RentDivision (dimension + 1)) : Prop :=
  ((x : RealPoint dimension) ∈ convexHull ℝ (τ.imagePoints (T := T) φ))

lemma imageContains_mono {τ σ : SubdivisionFace T} (h : τ.carrier ⊆ σ.carrier)
    {φ : Vertex → RentDivision (dimension + 1)} {x : RentDivision (dimension + 1)}
    (hx : τ.ImageContains (T := T) φ x) :
    σ.ImageContains (T := T) φ x := by
  change ((x : RealPoint dimension) ∈ convexHull ℝ (σ.imagePoints (T := T) φ))
  exact Set.mem_of_subset_of_mem
    (convexHull_mono <| by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, h hv, rfl⟩) hx

lemma containsPoint_of_mem {τ : SubdivisionFace T} {v : Vertex} (hv : v ∈ τ.carrier) :
    τ.ContainsPoint (T := T) (T.vertexPos v) := by
  change (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) ∈
    convexHull ℝ (τ.vertexPoints (T := T)))
  apply subset_convexHull
  exact ⟨v, hv, rfl⟩

lemma imageContains_of_mem {τ : SubdivisionFace T} (φ : Vertex → RentDivision (dimension + 1))
    {v : Vertex} (hv : v ∈ τ.carrier) :
    τ.ImageContains (T := T) φ (φ v) := by
  change (((φ v : RentDivision (dimension + 1)) : RealPoint dimension) ∈
    convexHull ℝ (τ.imagePoints (T := T) φ))
  apply subset_convexHull
  exact ⟨v, hv, rfl⟩

/-- Face inclusion relation inside the subdivision face poset. -/
def IsSubface (τ σ : SubdivisionFace T) : Prop :=
  τ.carrier ⊆ σ.carrier

/-- Codimension-`1` incidence relation used in the Section 5 graph. -/
def IsCodimOneSubface (τ σ : SubdivisionFace T) : Prop :=
  τ.IsSubface σ ∧ τ.carrier.card + 1 = σ.carrier.card

lemma isSubface_refl (τ : SubdivisionFace T) : τ.IsSubface τ :=
  Finset.Subset.rfl

lemma ofSubset_isSubface (τ : SubdivisionFace T) (s : Finset Vertex) (hs : s ⊆ τ.carrier)
    (hsne : s.Nonempty) :
    (τ.ofSubset s hs hsne).IsSubface τ :=
  hs

lemma singleton_isSubface_of_mem (τ : SubdivisionFace T) {v : Vertex} (hv : v ∈ τ.carrier) :
    (singleton (T := T) v).IsSubface τ := by
  simpa [IsSubface, singleton_carrier (T := T)] using Finset.singleton_subset_iff.mpr hv

lemma erase_isCodimOneSubface (τ : SubdivisionFace T) {v : Vertex} (hv : v ∈ τ.carrier)
    (hτ : 1 < τ.carrier.card) :
    (τ.ofSubset (τ.carrier.erase v) (Finset.erase_subset _ _) (by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hv]
      exact Nat.sub_pos_of_lt hτ)).IsCodimOneSubface τ := by
  constructor
  · exact Finset.erase_subset _ _
  · change (τ.carrier.erase v).card + 1 = τ.carrier.card
    rw [Finset.card_erase_of_mem hv]
    exact Nat.sub_add_cancel (Nat.le_of_lt hτ)

/--
Carrier-normalized codimension-`1` subfaces of a fixed subdivision face.

This removes dependence on which ambient facet proof was used to manufacture a raw
`SubdivisionFace` and keeps only the carrier-level data relevant to local continuation arguments.
-/
structure CarrierCodimOneSubface (τ : SubdivisionFace T) where
  carrier : Finset Vertex
  nonempty : carrier.Nonempty
  subset : carrier ⊆ τ.carrier
  card : carrier.card + 1 = τ.carrier.card

namespace CarrierCodimOneSubface

def toSubdivisionFace {τ : SubdivisionFace T} (ρ : CarrierCodimOneSubface τ) : SubdivisionFace T :=
  τ.ofSubset ρ.carrier ρ.subset ρ.nonempty

@[simp] lemma toSubdivisionFace_carrier {τ : SubdivisionFace T} (ρ : CarrierCodimOneSubface τ) :
    ρ.toSubdivisionFace.carrier = ρ.carrier :=
  rfl

lemma isCodimOneSubface {τ : SubdivisionFace T} (ρ : CarrierCodimOneSubface τ) :
    ρ.toSubdivisionFace.IsCodimOneSubface τ := by
  constructor
  · exact ρ.subset
  · simpa [toSubdivisionFace] using ρ.card

def ofIsCodimOneSubface {τ ρ : SubdivisionFace T} (h : ρ.IsCodimOneSubface τ) :
    CarrierCodimOneSubface τ where
  carrier := ρ.carrier
  nonempty := ρ.nonempty
  subset := h.1
  card := h.2

@[simp] lemma ofIsCodimOneSubface_carrier {τ ρ : SubdivisionFace T} (h : ρ.IsCodimOneSubface τ) :
    (ofIsCodimOneSubface h).carrier = ρ.carrier :=
  rfl

end CarrierCodimOneSubface

end SubdivisionFace

end Faces

section PrefixGeometry

variable {dimension : ℕ}

/--
The outer prefix face spanned by the first `k + 1` simplex vertices, bundled as a subtype.

This is the support object needed to compare Section 5 milestone points with smaller standard
simplices.
-/
def PrefixFace (k : Fin (dimension + 1)) :=
  {x : RentDivision (dimension + 1) //
    ∀ i : Room (dimension + 1), k.1 < i.1 → ((x : RealPoint dimension) i) = 0}

namespace PrefixFace

variable {k : Fin (dimension + 1)}

/-- Reindex the first `k + 1` ambient coordinates by a smaller `Fin (k + 1)`. -/
def indexEquiv : Fin (k.1 + 1) ≃ {i : Fin (dimension + 1) // i.1 < k.1 + 1} where
  toFun j := ⟨j.castLE (Nat.succ_le_of_lt k.2), by simpa using j.2⟩
  invFun i := ⟨i.1.1, i.2⟩
  left_inv j := by
    ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- Restrict a point of the prefix face to the corresponding smaller simplex. -/
def restrict (x : PrefixFace (dimension := dimension) k) : RentDivision (k.1 + 1) := by
  refine ⟨fun j => ((x.1 : RealPoint dimension) (j.castLE (Nat.succ_le_of_lt k.2))), ?_⟩
  refine ⟨?_, ?_⟩
  · intro j
    exact (x.1.2).1 _
  · let p : Fin (dimension + 1) → Prop := fun i => i.1 < k.1 + 1
    have hsplit :
        (∑ i : {j // p j}, ((x.1 : RealPoint dimension) i.1)) +
          ∑ i : {j // ¬ p j}, ((x.1 : RealPoint dimension) i.1) =
            ∑ i : Fin (dimension + 1), ((x.1 : RealPoint dimension) i) :=
      Fintype.sum_subtype_add_sum_subtype (p := p)
        (f := fun i : Fin (dimension + 1) => ((x.1 : RealPoint dimension) i))
    have hsmall :
        (∑ i : {j // p j}, ((x.1 : RealPoint dimension) i.1)) =
          ∑ j : Fin (k.1 + 1),
            ((x.1 : RealPoint dimension) (j.castLE (Nat.succ_le_of_lt k.2))) := by
      symm
      simpa using
        (Fintype.sum_equiv (indexEquiv (k := k))
          (fun j : Fin (k.1 + 1) =>
            ((x.1 : RealPoint dimension) (j.castLE (Nat.succ_le_of_lt k.2))))
          (fun i : {j // p j} => ((x.1 : RealPoint dimension) i.1))
          (fun j => rfl))
    have htail : (∑ i : {j // ¬ p j}, ((x.1 : RealPoint dimension) i.1)) = 0 := by
      apply Fintype.sum_eq_zero
      intro i
      have hi : k.1 < i.1 := by
        have : ¬ i.1 < k.1 + 1 := i.2
        omega
      exact x.2 i.1 hi
    have hxsum : (∑ i : Fin (dimension + 1), ((x.1 : RealPoint dimension) i)) = 1 := (x.1.2).2
    rw [← hsmall]
    linarith [hsplit, htail, hxsum]

/-- Pad a smaller simplex point with trailing zeros to land in the ambient prefix face. -/
def pad (y : RentDivision (k.1 + 1)) : PrefixFace (dimension := dimension) k := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun i => if hi : i.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1, hi⟩) else 0, ?_⟩
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i.1 < k.1 + 1
      · simp [hi]
      · simp [hi]
    · let p : Fin (dimension + 1) → Prop := fun i => i.1 < k.1 + 1
      have hsplit :
          (∑ i : {j // p j},
              (if hi : i.1.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1.1, hi⟩) else 0)) +
            ∑ i : {j // ¬ p j},
              (if hi : i.1.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1.1, hi⟩) else 0) =
              ∑ i : Fin (dimension + 1),
                (if hi : i.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1, hi⟩) else 0) :=
        Fintype.sum_subtype_add_sum_subtype (p := p)
          (f := fun i : Fin (dimension + 1) =>
            if hi : i.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1, hi⟩) else 0)
      have hsmall :
          (∑ i : {j // p j},
              (if hi : i.1.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1.1, hi⟩) else 0)) =
            ∑ j : Fin (k.1 + 1), ((y : RealPoint k.1) j) := by
        simpa using
          (Fintype.sum_equiv (indexEquiv (k := k)).symm
            (fun i : {j // p j} =>
              if hi : i.1.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1.1, hi⟩) else 0)
            (fun j : Fin (k.1 + 1) => ((y : RealPoint k.1) j))
            (fun i => by
              have hle : i.1.1 ≤ k.1 := by omega
              simp [indexEquiv, hle]))
      have htail :
          (∑ i : {j // ¬ p j},
              (if hi : i.1.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1.1, hi⟩) else 0)) = 0 := by
        apply Fintype.sum_eq_zero
        intro i
        simp [p, i.2]
      have hysum : (∑ j : Fin (k.1 + 1), ((y : RealPoint k.1) j)) = 1 := y.2.2
      linarith [hsplit, hsmall, htail, hysum]
  · intro i hi
    have hnot : ¬ i.1 < k.1 + 1 := by omega
    change (if hi' : i.1 < k.1 + 1 then ((↑y : RealPoint k.1) ⟨i.1, hi'⟩) else 0) = 0
    simp [hnot]

@[simp] lemma restrict_apply (x : PrefixFace (dimension := dimension) k) (j : Fin (k.1 + 1)) :
    ((restrict (k := k) x : RealPoint k.1) j) =
      ((x.1 : RealPoint dimension) (j.castLE (Nat.succ_le_of_lt k.2))) :=
  rfl

@[simp] lemma pad_apply_lt (y : RentDivision (k.1 + 1)) {i : Room (dimension + 1)}
    (hi : i.1 < k.1 + 1) :
    (((pad (k := k) y).1 : RealPoint dimension) i) = ((y : RealPoint k.1) ⟨i.1, hi⟩) := by
  have hle : i ≤ k := Nat.le_of_lt_succ hi
  have hEq : (⟨i.1, Nat.lt_succ_of_le hle⟩ : Fin (k.1 + 1)) = ⟨i.1, hi⟩ := by
    apply Fin.ext
    rfl
  unfold pad
  change (if hi' : i.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1, hi'⟩) else 0) =
    ((y : RealPoint k.1) ⟨i.1, hi⟩)
  simp [hi, hEq]

@[simp] lemma pad_apply_ge (y : RentDivision (k.1 + 1)) {i : Room (dimension + 1)}
    (hi : ¬ i.1 < k.1 + 1) :
    (((pad (k := k) y).1 : RealPoint dimension) i) = 0 := by
  unfold pad
  change (if hi' : i.1 < k.1 + 1 then ((y : RealPoint k.1) ⟨i.1, hi'⟩) else 0) = 0
  simp [hi]

/-- The outer prefix face is explicitly equivalent to the smaller standard simplex. -/
def equivRentDivision : PrefixFace (dimension := dimension) k ≃ RentDivision (k.1 + 1) where
  toFun := restrict (k := k)
  invFun := pad (k := k)
  left_inv x := by
    apply Subtype.ext
    ext i
    by_cases hi : i.1 < k.1 + 1
    · have hEq : ((⟨i.1, hi⟩ : Fin (k.1 + 1)).castLE (Nat.succ_le_of_lt k.2) :
          Fin (dimension + 1)) = i := by
        apply Fin.ext
        rfl
      rw [pad_apply_lt (k := k) (y := restrict (k := k) x) hi]
      simp [hEq]
    · have hgt : k.1 < i.1 := by omega
      rw [pad_apply_ge (k := k) (y := restrict (k := k) x) hi]
      symm
      exact x.2 i hgt
  right_inv y := by
    ext j
    have hEq :
        (⟨(j.castLE (Nat.succ_le_of_lt k.2)).1, by simpa using j.2⟩ : Fin (k.1 + 1)) = j := by
      apply Fin.ext
      rfl
    rw [restrict_apply]
    rw [pad_apply_lt (k := k) (y := y) (i := j.castLE (Nat.succ_le_of_lt k.2))]
    · rw [hEq]
    · simpa using j.2

/--
The corresponding point of the smaller simplex, viewed in its affine span.

This packages `restrict` with the ambient affine-span coercion used by the smaller-simplex
avoidance theorem.
-/
def smallPoint (x : PrefixFace (dimension := dimension) k) :
    affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1)) :=
  ⟨restrict (k := k) x,
    subset_affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))
      (restrict (k := k) x).property⟩

@[simp] lemma coe_smallPoint (x : PrefixFace (dimension := dimension) k) :
    ((smallPoint (dimension := dimension) (k := k) x :
      affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))) :
        RealPoint k.1) =
      ((restrict (k := k) x : RentDivision (k.1 + 1)) : RealPoint k.1) :=
  rfl

@[simp] lemma smallPoint_pad (y : RentDivision (k.1 + 1)) :
    smallPoint (dimension := dimension) (k := k) (pad (k := k) y) =
      ⟨(y : RealPoint k.1),
        subset_affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))
          y.property⟩ := by
  apply Subtype.ext
  ext j
  change (((restrict (k := k) (pad (k := k) y) : RentDivision (k.1 + 1)) :
      RealPoint k.1) j) = ((y : RealPoint k.1) j)
  rw [restrict_apply]
  rw [pad_apply_lt (dimension := dimension) (k := k) (y := y)
      (i := j.castLE (Nat.succ_le_of_lt k.2)) (by simpa using j.2)]
  simp

/-- Restrict ambient coordinates to the first `k + 1` rooms. -/
def restrictLinear : RealPoint dimension →ₗ[ℝ] RealPoint k.1 where
  toFun f j := f (j.castLE (Nat.succ_le_of_lt k.2))
  map_add' f g := by
    ext j
    rfl
  map_smul' a f := by
    ext j
    rfl

@[simp] lemma restrictLinear_apply (f : RealPoint dimension) (j : Fin (k.1 + 1)) :
    restrictLinear (k := k) f j = f (j.castLE (Nat.succ_le_of_lt k.2)) :=
  rfl

@[simp] lemma restrictLinear_pad (y : RentDivision (k.1 + 1)) :
    restrictLinear (k := k)
      (((pad (dimension := dimension) (k := k) y).1 : RentDivision (dimension + 1)) :
        RealPoint dimension) =
      ((y : RealPoint k.1)) := by
  ext j
  rw [restrictLinear_apply]
  simpa using
    (pad_apply_lt (dimension := dimension) (k := k) (y := y)
      (i := j.castLE (Nat.succ_le_of_lt k.2)) (by simpa using j.2))

/-- Pad an ambient point of the smaller simplex by trailing zero coordinates. -/
def padLinear : RealPoint k.1 →ₗ[ℝ] RealPoint dimension where
  toFun y i := if hi : i ≤ k then y ⟨i.1, Nat.lt_succ_of_le hi⟩ else 0
  map_add' y z := by
    ext i
    by_cases hi : i ≤ k
    · simp [hi]
    · simp [hi]
  map_smul' a y := by
    ext i
    by_cases hi : i ≤ k
    · simp [hi]
    · simp [hi]

@[simp] lemma padLinear_apply_lt (y : RealPoint k.1) {i : Room (dimension + 1)}
    (hi : i.1 < k.1 + 1) :
    padLinear (dimension := dimension) (k := k) y i = y ⟨i.1, hi⟩ := by
  have hle : i ≤ k := Nat.le_of_lt_succ hi
  have hEq : (⟨i.1, Nat.lt_succ_of_le hle⟩ : Fin (k.1 + 1)) = ⟨i.1, hi⟩ := by
    apply Fin.ext
    rfl
  simp [padLinear, hle, hEq]

@[simp] lemma padLinear_apply_ge (y : RealPoint k.1) {i : Room (dimension + 1)}
    (hi : ¬ i.1 < k.1 + 1) :
    padLinear (dimension := dimension) (k := k) y i = 0 := by
  have hle : ¬ i ≤ k := by
    intro hle
    exact hi (Nat.lt_succ_of_le hle)
  simp [padLinear, hle]

@[simp] lemma padLinear_restrict (x : PrefixFace (dimension := dimension) k) :
    padLinear (dimension := dimension) (k := k)
        (((restrict (dimension := dimension) (k := k) x : RentDivision (k.1 + 1)) :
          RealPoint k.1)) =
      (((x.1 : RentDivision (dimension + 1)) : RealPoint dimension)) := by
  ext i
  by_cases hi : i.1 < k.1 + 1
  · have hEq :
        (⟨i.1, hi⟩ : Fin (k.1 + 1)).castLE (Nat.succ_le_of_lt k.2) = i := by
      apply Fin.ext
      rfl
    rw [padLinear_apply_lt (dimension := dimension) (k := k) (y := _) hi, restrict_apply]
    simpa [hEq]
  · rw [padLinear_apply_ge (dimension := dimension) (k := k) (y := _) hi]
    have hgt : k.1 < i.1 := by
      omega
    symm
    exact x.2 i hgt

end PrefixFace

/-- The `j`-th original vertex inside the prefix face spanned by the first `k + 1` rooms. -/
def prefixVertex (k : Fin (dimension + 1)) (j : Fin (k.1 + 1)) :
    RentDivision (dimension + 1) :=
  stdSimplex.vertex (S := ℝ) (Fin.castLE (Nat.succ_le_of_lt k.2) j)

/--
The barycenter of the outer face spanned by the first `k + 1` simplex vertices.

This is the paper's `b_k` after translating from the paper's `1`-based indexing to Lean's
`0`-based `Fin` indexing.
-/
def prefixBarycenter (k : Fin (dimension + 1)) : RentDivision (dimension + 1) := by
  refine
    ⟨Finset.univ.centerMass (fun _ : Fin (k.1 + 1) => (1 : ℝ))
      (fun j =>
        ((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
          RealPoint dimension)), ?_⟩
  refine (convex_stdSimplex ℝ (Room (dimension + 1))).centerMass_mem ?_ ?_ ?_
  · intro j hj
    positivity
  · have hsum : 0 < ∑ j : Fin (k.1 + 1), (1 : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one, mul_one]
      exact_mod_cast Nat.succ_pos k.1
    simpa using hsum
  · intro j hj
    exact (prefixVertex (dimension := dimension) k j).2

/-- The segment joining two successive prefix-face barycenters. -/
def prefixBarycenterSegment (k : Fin dimension) : Set (RealPoint dimension) :=
  segment ℝ
    (((prefixBarycenter (dimension := dimension) k.castSucc : RentDivision (dimension + 1)) :
      RealPoint dimension))
    (((prefixBarycenter (dimension := dimension) k.succ : RentDivision (dimension + 1)) :
      RealPoint dimension))

@[simp] lemma restrictLinear_prefixVertex (k : Fin (dimension + 1)) (j : Fin (k.1 + 1)) :
    PrefixFace.restrictLinear (dimension := dimension) (k := k)
        (((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
          RealPoint dimension)) =
      (((stdSimplex.vertex (S := ℝ) j : stdSimplex ℝ (Room (k.1 + 1))) :
        RealPoint k.1)) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [PrefixFace.restrictLinear_apply, prefixVertex, stdSimplex.vertex]
  · simp [PrefixFace.restrictLinear_apply, prefixVertex, stdSimplex.vertex, h]

lemma prefixVertex_injective (k : Fin (dimension + 1)) :
    Function.Injective
      (fun j : Fin (k.1 + 1) =>
        ((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
          RealPoint dimension)) := by
  intro i j hij
  have hrestrict :=
    congrArg (PrefixFace.restrictLinear (dimension := dimension) (k := k)) hij
  exact stdSimplex.vertex_injective <| by
    simpa [restrictLinear_prefixVertex (dimension := dimension) (k := k)] using hrestrict

def prefixVertexFinset (k : Fin (dimension + 1)) : Finset (RealPoint dimension) :=
  Finset.univ.image fun j : Fin (k.1 + 1) =>
    ((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
      RealPoint dimension)

lemma prefixVertexFinset_coe (k : Fin (dimension + 1)) :
    ((prefixVertexFinset (dimension := dimension) k : Finset (RealPoint dimension)) :
        Set (RealPoint dimension)) =
      Set.range (fun j : Fin (k.1 + 1) =>
        ((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
          RealPoint dimension)) := by
  ext x
  simp [prefixVertexFinset]

lemma prefixVertexFinset_card (k : Fin (dimension + 1)) :
    (prefixVertexFinset (dimension := dimension) k).card = k.1 + 1 := by
  classical
  simpa [prefixVertexFinset] using
    (Finset.card_image_of_injective (s := Finset.univ)
      (f := fun j : Fin (k.1 + 1) =>
        ((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
          RealPoint dimension))
      (prefixVertex_injective (dimension := dimension) k))

@[simp] lemma PrefixFace.padLinear_single_one
    (k : Fin (dimension + 1)) (j : Fin (k.1 + 1)) :
    PrefixFace.padLinear (dimension := dimension) (k := k)
        (Pi.single j (1 : ℝ)) =
      (((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
        RealPoint dimension)) := by
  ext i
  by_cases hi : i ≤ k
  · have hi' : i.1 < k.1 + 1 := Nat.lt_succ_of_le hi
    by_cases hij : (⟨i.1, hi'⟩ : Fin (k.1 + 1)) = j
    · have hEq : i = j.castLE (Nat.succ_le_of_lt k.2) := by
        apply Fin.ext
        simpa using congrArg Fin.val hij
      subst hEq
      simp [PrefixFace.padLinear, hi, prefixVertex, stdSimplex.vertex]
    · have hEq : i ≠ j.castLE (Nat.succ_le_of_lt k.2) := by
        intro hEq
        apply hij
        apply Fin.ext
        simpa using congrArg Fin.val hEq
      simp [PrefixFace.padLinear, hi, prefixVertex, stdSimplex.vertex, hij, hEq]
  · have hEq : j.castLE (Nat.succ_le_of_lt k.2) ≠ i := by
      intro hEq
      apply hi
      cases hEq
      exact Nat.le_of_lt_succ j.2
    simp [PrefixFace.padLinear, hi, prefixVertex, stdSimplex.vertex, hEq]

lemma PrefixFace.image_padLinear_range_single_eq_prefixVertex
    (k : Fin (dimension + 1)) :
    PrefixFace.padLinear (dimension := dimension) (k := k) ''
        Set.range (fun j : Fin (k.1 + 1) => Pi.single j (1 : ℝ)) =
      Set.range (fun j : Fin (k.1 + 1) =>
        ((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
          RealPoint dimension)) := by
  ext x
  constructor
  · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, (PrefixFace.padLinear_single_one (dimension := dimension) k j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Pi.single j (1 : ℝ), ⟨j, rfl⟩,
      PrefixFace.padLinear_single_one (dimension := dimension) k j⟩

lemma PrefixFace.mem_affineSpan_prefixVertexFinset
    (k : Fin (dimension + 1)) (x : PrefixFace (dimension := dimension) k) :
    (((x.1 : RentDivision (dimension + 1)) : RealPoint dimension) ∈
      affineSpan ℝ
        (((prefixVertexFinset (dimension := dimension) k : Finset (RealPoint dimension)) :
          Set (RealPoint dimension)))) := by
  let y : RealPoint k.1 :=
    ((PrefixFace.restrict (dimension := dimension) (k := k) x : RentDivision (k.1 + 1)) :
      RealPoint k.1)
  have hyconv :
      y ∈ convexHull ℝ (Set.range fun j : Fin (k.1 + 1) => Pi.single j (1 : ℝ)) := by
    rw [convexHull_rangle_single_eq_stdSimplex]
    exact (PrefixFace.restrict (dimension := dimension) (k := k) x).property
  have hpad :
      PrefixFace.padLinear (dimension := dimension) (k := k) y ∈
        convexHull ℝ
          (PrefixFace.padLinear (dimension := dimension) (k := k) ''
            Set.range (fun j : Fin (k.1 + 1) => Pi.single j (1 : ℝ))) := by
    have himage :
        PrefixFace.padLinear (dimension := dimension) (k := k) y ∈
          PrefixFace.padLinear (dimension := dimension) (k := k) ''
            convexHull ℝ (Set.range fun j : Fin (k.1 + 1) => Pi.single j (1 : ℝ)) :=
      ⟨y, hyconv, rfl⟩
    rw [LinearMap.image_convexHull] at himage
    exact himage
  have hconv :
      (((x.1 : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          (((prefixVertexFinset (dimension := dimension) k : Finset (RealPoint dimension)) :
            Set (RealPoint dimension)))) := by
    simpa [y, PrefixFace.padLinear_restrict, PrefixFace.image_padLinear_range_single_eq_prefixVertex,
      prefixVertexFinset_coe] using hpad
  exact convexHull_subset_affineSpan _ hconv

lemma PrefixFace.mem_affineSpan_prefixVertexFinset_of_coord_eq_zero
    (k : Fin (dimension + 1)) {x : RentDivision (dimension + 1)}
    (hx :
      ∀ i : Room (dimension + 1), k.1 < i.1 →
        (((x : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0) :
    (((x : RentDivision (dimension + 1)) : RealPoint dimension) ∈
      affineSpan ℝ
        (((prefixVertexFinset (dimension := dimension) k : Finset (RealPoint dimension)) :
          Set (RealPoint dimension)))) := by
  exact PrefixFace.mem_affineSpan_prefixVertexFinset (dimension := dimension) k ⟨x, hx⟩

/--
Section 5 allows the barycenters to be perturbed slightly in order to enforce genericity.

This structure records such a milestone chain: the initial point is still `e₁`, the final point is
still the true barycenter of the full simplex, and every intermediate point remains in the
corresponding prefix outer face.
-/
structure Section5MilestoneChain where
  point : Fin (dimension + 1) → RentDivision (dimension + 1)
  start_eq : point 0 = prefixBarycenter (dimension := dimension) 0
  terminal_eq :
    point (Fin.last dimension) =
      prefixBarycenter (dimension := dimension) (Fin.last dimension)
  point_subdividesPrefixFace :
    ∀ k : Fin (dimension + 1), ∀ i : Room (dimension + 1), k.1 < i.1 →
      (((point k : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0

namespace Section5MilestoneChain

/-- Every milestone point lies in its prescribed prefix face. -/
def prefixPoint (c : Section5MilestoneChain (dimension := dimension)) (k : Fin (dimension + 1)) :
    PrefixFace (dimension := dimension) k :=
  ⟨c.point k, c.point_subdividesPrefixFace k⟩

/-- The segment joining two successive milestones. -/
def segment (c : Section5MilestoneChain (dimension := dimension)) (k : Fin dimension) :
    Set (RealPoint dimension) :=
  _root_.segment ℝ
    (((c.point k.castSucc : RentDivision (dimension + 1)) : RealPoint dimension))
    (((c.point k.succ : RentDivision (dimension + 1)) : RealPoint dimension))

end Section5MilestoneChain

end PrefixGeometry

section Avoidance

variable {V P : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V] [Nonempty P]

/--
A proper affine subspace of a finite-dimensional normed affine space has empty interior.

This is the basic finite-union avoidance input needed for the Section 5 milestone perturbation.
-/
lemma affineSubspace_interior_eq_empty_of_ne_top
    (Q : AffineSubspace ℝ P) (hQ : Q ≠ ⊤) :
    interior (Q : Set P) = ∅ := by
  classical
  let p : P := Classical.arbitrary P
  let e : P ≃ᵃⁱ[ℝ] V := AffineIsometryEquiv.constVSub ℝ p
  let f : P →ᵃ[ℝ] V := e.toAffineEquiv.toAffineMap
  have hf : Function.Injective f := e.injective
  by_contra h
  have hne : (interior (Q : Set P)).Nonempty := Set.nonempty_iff_ne_empty.mpr h
  have himage :
      (interior ((Q.map f : AffineSubspace ℝ V) : Set V)).Nonempty := by
    have : (e.toHomeomorph '' interior (Q : Set P)).Nonempty := hne.image e.toHomeomorph
    rw [e.toHomeomorph.image_interior] at this
    simpa [f, AffineSubspace.coe_map] using this
  have htop :
      affineSpan ℝ (((Q.map f : AffineSubspace ℝ V) : Set V)) = ⊤ :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top
      (s := ((Q.map f : AffineSubspace ℝ V) : Set V))
      (Q.map f).convex).mp himage
  have hmaptop : Q.map f = ⊤ := by
    have htop' : affineSpan ℝ (f '' (Q : Set P)) = ⊤ := by
      simpa [AffineSubspace.coe_map, f] using htop
    calc
      Q.map f = (affineSpan ℝ (Q : Set P)).map f := by rw [AffineSubspace.affineSpan_coe]
      _ = affineSpan ℝ (f '' (Q : Set P)) := AffineSubspace.map_span (f := f) (s := (Q : Set P))
    exact htop'
  have hQtop : Q = ⊤ := by
    have hcomap := congrArg (fun S : AffineSubspace ℝ V => S.comap f) hmaptop
    simpa [f, AffineSubspace.comap_map_eq_of_injective hf, AffineSubspace.comap_top]
      using hcomap
  exact hQ hQtop

lemma interior_biUnion_finset_affineSubspace_eq_empty
    (S : Finset (AffineSubspace ℝ P))
    (hproper : ∀ Q ∈ S, Q ≠ (⊤ : AffineSubspace ℝ P)) :
    interior (⋃ Q ∈ S, (Q : Set P)) = ∅ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert Q S hQnot ih =>
      have hQempty : interior (Q : Set P) = ∅ :=
        affineSubspace_interior_eq_empty_of_ne_top Q (hproper Q (by simp))
      have hSempty : interior (⋃ Q' ∈ S, (Q' : Set P)) = ∅ := by
        refine ih ?_
        intro Q' hQ'
        exact hproper Q' (by simp [hQ'])
      have hQclosed : IsClosed (Q : Set P) := Q.closed_of_finiteDimensional
      rw [show (⋃ R ∈ insert Q S, (R : Set P)) = (Q : Set P) ∪ ⋃ R ∈ S, (R : Set P) by
        simp]
      rw [interior_union_isClosed_of_interior_empty hQclosed hSempty, hQempty]

lemma exists_mem_open_not_mem_biUnion_affineSubspace
    {u : Set P} (hu : IsOpen u) (hune : u.Nonempty)
    (S : Finset (AffineSubspace ℝ P))
    (hproper : ∀ Q ∈ S, Q ≠ (⊤ : AffineSubspace ℝ P)) :
    ∃ x, x ∈ u ∧ ∀ Q ∈ S, x ∉ (Q : Set P) := by
  have hEmpty : interior (⋃ Q ∈ S, (Q : Set P)) = ∅ :=
    interior_biUnion_finset_affineSubspace_eq_empty S hproper
  have hnot : ¬ u ⊆ ⋃ Q ∈ S, (Q : Set P) := by
    intro hsub
    have hinterior : u ⊆ interior (⋃ Q ∈ S, (Q : Set P)) :=
      interior_maximal hsub hu
    rw [hEmpty] at hinterior
    exact hune.not_subset_empty hinterior
  simpa [Set.subset_def] using Set.not_subset.mp hnot

section StdSimplexAvoid

variable {dimension : ℕ}

/-- The standard simplex vertices are affinely independent in the ambient coordinate space. -/
lemma affineIndependent_stdSimplexVertices (n : ℕ) :
    AffineIndependent ℝ
      (fun i : Room n =>
        ((stdSimplex.vertex (S := ℝ) i : stdSimplex ℝ (Room n)) : Room n → ℝ)) := by
  classical
  rw [affineIndependent_iff]
  intro s w hw0 hw1 i hi
  have hw1i := congr_fun hw1 i
  rw [Finset.sum_apply, Pi.zero_apply] at hw1i
  simp_rw [Pi.smul_apply, smul_eq_mul] at hw1i
  have hsimp :
      (∑ e ∈ s, w e * (((stdSimplex.vertex (S := ℝ) e : stdSimplex ℝ (Room n)) :
        Room n → ℝ) i)) = w i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [stdSimplex.vertex, hji]
    · intro hi'
      exact False.elim (hi' hi)
  rw [hsimp] at hw1i
  simpa using hw1i

lemma affineIndependent_prefixVertices (k : Fin (dimension + 1)) :
    AffineIndependent ℝ
      (fun j : Fin (k.1 + 1) =>
        ((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
          RealPoint dimension)) := by
  have hstd :
      AffineIndependent ℝ
        (fun j : Fin (k.1 + 1) =>
          (((stdSimplex.vertex (S := ℝ) j : stdSimplex ℝ (Room (k.1 + 1))) :
            RealPoint k.1))) := by
    simpa [stdSimplex.vertex] using affineIndependent_stdSimplexVertices (k.1 + 1)
  have hcomp :
      AffineIndependent ℝ
        ((PrefixFace.restrictLinear (dimension := dimension) (k := k)) ∘
          fun j : Fin (k.1 + 1) =>
            ((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
              RealPoint dimension)) := by
    convert hstd using 1
    funext j
    simpa [Function.comp] using
      (restrictLinear_prefixVertex (dimension := dimension) (k := k) j)
  apply AffineIndependent.of_comp
    (PrefixFace.restrictLinear (dimension := dimension) (k := k)).toAffineMap
  exact hcomp

lemma affineIndependent_prefixVertexFinset (k : Fin (dimension + 1)) :
    AffineIndependent ℝ
      (fun x :
        (((prefixVertexFinset (dimension := dimension) k : Finset (RealPoint dimension)) :
          Set (RealPoint dimension))) => (x : RealPoint dimension)) := by
  rw [prefixVertexFinset_coe]
  exact (affineIndependent_prefixVertices (dimension := dimension) k).range

/--
At most `dimension` points of the smaller simplex cannot span its full affine hull.

This is the cardinality step turning lower-dimensional convex hulls into proper affine subspaces.
-/
theorem smallSimplex_affineSpan_ne_top_of_card_le
    (t :
      Finset
        (affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension))))
    (ht : t.card ≤ dimension) :
    affineSpan ℝ
      (t :
        Set
          (affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) :
            Set (RealPoint dimension)))) ≠ ⊤ := by
  classical
  let A : Set (RealPoint dimension) := stdSimplex ℝ (Room (dimension + 1))
  let E : AffineSubspace ℝ (RealPoint dimension) := affineSpan ℝ A
  let p : Room (dimension + 1) → RealPoint dimension :=
    fun i => ((stdSimplex.vertex (S := ℝ) i : stdSimplex ℝ (Room (dimension + 1))) :
      RealPoint dimension)
  let s : Finset (RealPoint dimension) := Finset.univ.image p
  have hp_indep : AffineIndependent ℝ p :=
    affineIndependent_stdSimplexVertices (dimension + 1)
  have hp_injective : Function.Injective p := by
    intro i j hij
    by_contra hne
    have hcoord := congr_fun hij i
    simp [p, stdSimplex.vertex, hne] at hcoord
  have hs_range : (s : Set (RealPoint dimension)) = Set.range p := by
    ext x
    simp [s]
  have hs_indep :
      AffineIndependent ℝ
        (fun x : (s : Set (RealPoint dimension)) => (x : RealPoint dimension)) := by
    rw [hs_range]
    exact hp_indep.range
  have hs_card : s.card = dimension + 1 := by
    simpa [Room] using
      (Finset.card_image_of_injective (Finset.univ : Finset (Room (dimension + 1))) hp_injective)
  intro htop
  let u : Finset (RealPoint dimension) := t.image (fun x : E => (x : RealPoint dimension))
  have hsubset :
      (s : Set (RealPoint dimension)) ⊆ affineSpan ℝ (u : Set (RealPoint dimension)) := by
    intro x hx
    rw [hs_range] at hx
    rcases hx with ⟨i, rfl⟩
    have hpi : p i ∈ A := by
      exact (stdSimplex.vertex (S := ℝ) i).property
    let piE : E := ⟨p i, subset_affineSpan ℝ A hpi⟩
    have hpiE : piE ∈ affineSpan ℝ (t : Set E) := by
      rw [htop]
      simp
    have hmap : p i ∈ (affineSpan ℝ (t : Set E)).map (E.subtype : E →ᵃ[ℝ] RealPoint dimension) := by
      exact AffineSubspace.mem_map.mpr ⟨piE, hpiE, rfl⟩
    simpa [u, E, A, AffineSubspace.map_span] using hmap
  have hcard_le :
      s.card ≤ u.card := by
    simpa using
      (AffineIndependent.card_le_card_of_subset_affineSpan
        (s := s) (t := u) hs_indep hsubset)
  have himage_card : u.card = t.card := by
    exact Finset.card_image_of_injective _ Subtype.val_injective
  omega

/--
Inside a smaller standard simplex, any finite union of proper affine subspaces misses some point of
the relative interior.

This is the smaller-simplex form of the finite-avoidance theorem needed for the Section 5
milestone-chain construction.
-/
theorem exists_mem_smallSimplexInterior_not_mem_biUnion_affineSubspace
    (S :
      Finset
        (AffineSubspace ℝ
          (affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension)))))
    (hproper : ∀ Q ∈ S, Q ≠ ⊤) :
    ∃ x :
      affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension)),
      x ∈ interior
          (((↑) :
              affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension)) →
                RealPoint dimension) ⁻¹'
            (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension))) ∧
        ∀ Q ∈ S, x ∉ (Q : Set _) := by
  let A : Set (RealPoint dimension) := stdSimplex ℝ (Room (dimension + 1))
  have hAconv : Convex ℝ A := convex_stdSimplex ℝ (Room (dimension + 1))
  have hAne : A.Nonempty := by
    refine ⟨stdSimplex.barycenter, ?_⟩
    exact (stdSimplex.barycenter : stdSimplex ℝ (Room (dimension + 1))).property
  have hPreNonempty :
      (interior (((↑) : affineSpan ℝ A → RealPoint dimension) ⁻¹' A :
          Set (affineSpan ℝ A))).Nonempty := by
    rcases hAne.intrinsicInterior hAconv with ⟨x, hx⟩
    rcases mem_intrinsicInterior.mp hx with ⟨y, hy, rfl⟩
    exact ⟨y, hy⟩
  simpa [A] using
    exists_mem_open_not_mem_biUnion_affineSubspace
      (u := interior (((↑) : affineSpan ℝ A → RealPoint dimension) ⁻¹' A :
        Set (affineSpan ℝ A)))
      isOpen_interior hPreNonempty S hproper

/--
Inside a smaller standard simplex, one can avoid any finite family of convex hulls generated by at
most `dimension` points.

This is the convex-hull version of the avoidance theorem needed to choose generic milestone points.
-/
theorem exists_mem_smallSimplexInterior_not_mem_biUnion_convexHull_of_card_le
    (T :
      Finset
        (Finset
          (affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension)))))
    (hcard : ∀ t ∈ T, t.card ≤ dimension) :
    ∃ x :
      affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension)),
      x ∈ interior
          (((↑) :
              affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension)) →
                RealPoint dimension) ⁻¹'
            (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension))) ∧
        ∀ t ∈ T, (x : RealPoint dimension) ∉ convexHull ℝ (((↑) :
          affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) :
            Set (RealPoint dimension)) → RealPoint dimension) '' (t : Set _)) := by
  classical
  let E : AffineSubspace ℝ (RealPoint dimension) :=
    affineSpan ℝ (stdSimplex ℝ (Room (dimension + 1)) : Set (RealPoint dimension))
  let S :
      Finset
        (AffineSubspace ℝ E) :=
    T.image (fun t : Finset E => affineSpan ℝ (t : Set E))
  have hproper : ∀ Q ∈ S, Q ≠ ⊤ := by
    intro Q hQ
    rcases Finset.mem_image.mp hQ with ⟨t, htT, rfl⟩
    exact smallSimplex_affineSpan_ne_top_of_card_le t (hcard t htT)
  rcases exists_mem_smallSimplexInterior_not_mem_biUnion_affineSubspace S hproper with
    ⟨x, hxint, hxavoid⟩
  refine ⟨x, hxint, ?_⟩
  intro t htT hxt
  have hxspan_ambient :
      (x : RealPoint dimension) ∈
        affineSpan ℝ (((↑) : E → RealPoint dimension) '' (t : Set E)) := by
    exact
      (convexHull_min (subset_affineSpan ℝ (s := (((↑) : E → RealPoint dimension) '' (t : Set E))))
        (AffineSubspace.convex _)) hxt
  have hxspan : x ∈ affineSpan ℝ (t : Set E) := by
    have hmap :
        (x : RealPoint dimension) ∈ (affineSpan ℝ (t : Set E)).map
          (E.subtype : E →ᵃ[ℝ] RealPoint dimension) := by
      simpa [E, AffineSubspace.map_span] using hxspan_ambient
    exact
      (AffineSubspace.mem_map_iff_mem_of_injective
        (f := (E.subtype : E →ᵃ[ℝ] RealPoint dimension)) Subtype.val_injective).mp hmap
  exact hxavoid _ (Finset.mem_image.mpr ⟨t, htT, rfl⟩) hxspan

end StdSimplexAvoid

end Avoidance

section PrefixFaceAvoidance

variable {dimension : ℕ} {k : Fin (dimension + 1)}

namespace PrefixFace

lemma image_restrictLinear_prefixPoints
    (t : Finset (PrefixFace (dimension := dimension) k)) :
    restrictLinear (k := k) ''
        ((fun z : PrefixFace (dimension := dimension) k =>
          ((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)) '' (t : Set _)) =
      ((↑) :
          affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1)) →
            RealPoint k.1) ''
        ((t.image (fun z => smallPoint (dimension := dimension) (k := k) z)) : Set _) := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨smallPoint (dimension := dimension) (k := k) z, ?_, ?_⟩
    · exact Finset.mem_image_of_mem _ hz
    · ext j
      change restrictLinear (k := k)
          (((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)) j =
        ((smallPoint (dimension := dimension) (k := k) z :
          affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))) :
            RealPoint k.1) j
      rfl
  · rintro ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
    refine ⟨((z.1 : RentDivision (dimension + 1)) : RealPoint dimension), ?_, ?_⟩
    · exact ⟨z, hz, rfl⟩
    · ext j
      change
        (((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)
            (j.castLE (Nat.succ_le_of_lt k.2))) =
          ((smallPoint (dimension := dimension) (k := k) z :
            affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))) :
              RealPoint k.1) j
      rfl

/--
Transport the smaller-simplex convex-hull avoidance theorem back to an ambient prefix face.

This is the precise support step needed for the Section 5 milestone construction: once the
forbidden sets in a prefix face are bounded by `k` vertices, one can choose a prefix-face point
whose restricted smaller-simplex coordinates lie in the relative interior and whose ambient point
avoids all of those forbidden convex hulls.
-/
theorem exists_smallPointInterior_not_mem_biUnion_convexHull_of_card_le
    (T : Finset (Finset (PrefixFace (dimension := dimension) k)))
    (hcard : ∀ t ∈ T, t.card ≤ k.1) :
    ∃ x : PrefixFace (dimension := dimension) k,
      smallPoint (dimension := dimension) (k := k) x ∈
          interior
            (((↑) :
                affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1)) →
                  RealPoint k.1) ⁻¹'
              (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))) ∧
        ∀ t ∈ T,
          ((x.1 : RentDivision (dimension + 1)) : RealPoint dimension) ∉
            convexHull ℝ
              ((fun z : PrefixFace (dimension := dimension) k =>
                  ((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)) ''
                (t : Set _)) := by
  classical
  let E : AffineSubspace ℝ (RealPoint k.1) :=
    affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))
  let smallT : Finset (Finset E) :=
    T.image (fun t => t.image (fun z => smallPoint (dimension := dimension) (k := k) z))
  have hcardSmall : ∀ t ∈ smallT, t.card ≤ k.1 := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨u, hu, rfl⟩
    exact (Finset.card_image_le).trans (hcard u hu)
  rcases exists_mem_smallSimplexInterior_not_mem_biUnion_convexHull_of_card_le
      (dimension := k.1) smallT hcardSmall with ⟨xE, hxint, hxavoid⟩
  have hxmem_pre :
      xE ∈
        (((↑) :
            affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1)) →
              RealPoint k.1) ⁻¹'
          (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))) :=
    interior_subset hxint
  have hxmem :
      (xE : RealPoint k.1) ∈ stdSimplex ℝ (Room (k.1 + 1)) :=
    hxmem_pre
  let y : RentDivision (k.1 + 1) := ⟨xE, hxmem⟩
  refine ⟨pad (dimension := dimension) (k := k) y, ?_, ?_⟩
  · have hpad :
        smallPoint (dimension := dimension) (k := k)
          (pad (dimension := dimension) (k := k) y) = xE := by
      calc
        smallPoint (dimension := dimension) (k := k)
            (pad (dimension := dimension) (k := k) y) =
          ⟨(y : RealPoint k.1),
            subset_affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))
              y.property⟩ := smallPoint_pad (dimension := dimension) (k := k) y
        _ = xE := by
          apply Subtype.ext
          rfl
    simpa [hpad] using hxint
  · intro t ht hxt
    have hsmall :
        restrictLinear (k := k)
            ((((pad (dimension := dimension) (k := k) y).1 :
                RentDivision (dimension + 1)) : RealPoint dimension)) ∈
          convexHull ℝ
            (restrictLinear (k := k) ''
              ((fun z : PrefixFace (dimension := dimension) k =>
                  ((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)) ''
                (t : Set _))) := by
      have :
          restrictLinear (k := k)
              ((((pad (dimension := dimension) (k := k) y).1 :
                  RentDivision (dimension + 1)) : RealPoint dimension)) ∈
            restrictLinear (k := k) ''
              convexHull ℝ
                ((fun z : PrefixFace (dimension := dimension) k =>
                    ((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)) '' (t : Set _)) :=
        ⟨_, hxt, rfl⟩
      rw [LinearMap.image_convexHull] at this
      exact this
    have hsmall' :
        (xE : RealPoint k.1) ∈
          convexHull ℝ
            (((↑) :
                affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1)) →
                  RealPoint k.1) ''
              ((t.image (fun z => smallPoint (dimension := dimension) (k := k) z)) : Set E)) := by
      simpa [y, image_restrictLinear_prefixPoints, restrictLinear_pad]
        using hsmall
    exact hxavoid _ (Finset.mem_image.mpr ⟨t, ht, rfl⟩) hsmall'

end PrefixFace

end PrefixFaceAvoidance

section GraphData

variable {dimension : ℕ} {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
variable {T : SimplicialSubdivision dimension Vertex}

namespace SubdivisionFace

/--
A subdivision face lies in the prefix outer face spanned by the first `k + 1` simplex vertices.

This is the domain-side condition appearing in the paper's Section 5 graph construction.
-/
def SubdividesPrefixFace (τ : SubdivisionFace T) (k : Fin (dimension + 1)) : Prop :=
  ∀ v ∈ τ.carrier, ∀ i : Room (dimension + 1), k.1 < i.1 →
    (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0

lemma subdividesPrefixFace_of_subface {τ σ : SubdivisionFace T} (hτσ : τ.IsSubface σ)
    {k : Fin (dimension + 1)} (hσ : σ.SubdividesPrefixFace (T := T) k) :
    τ.SubdividesPrefixFace (T := T) k := by
  intro v hv i hi
  exact hσ v (hτσ hv) i hi

lemma subdividesPrefixFace_succ_of_castSucc {τ : SubdivisionFace T} {k : Fin dimension}
    (hτ : τ.SubdividesPrefixFace (T := T) k.castSucc) :
    τ.SubdividesPrefixFace (T := T) k.succ := by
  intro v hv i hi
  exact hτ v hv i (lt_trans (Nat.lt_succ_self k.1) hi)

lemma mem_of_mem_codimOneSubface_or_other
    {τ ρ₁ ρ₂ : SubdivisionFace T}
    (hρ₁ : ρ₁.IsCodimOneSubface τ)
    (hρ₂ : ρ₂.IsCodimOneSubface τ)
    (hρne : ρ₁ ≠ ρ₂)
    {v : Vertex} (hv : v ∈ τ.carrier) :
    v ∈ ρ₁.carrier ∨ v ∈ ρ₂.carrier := by
  by_cases hv₁ : v ∈ ρ₁.carrier
  · exact Or.inl hv₁
  · by_cases hv₂ : v ∈ ρ₂.carrier
    · exact Or.inr hv₂
    · have hρ₁erase : ρ₁.carrier ⊆ τ.carrier.erase v := by
        intro w hw
        refine Finset.mem_erase.mpr ⟨?_, hρ₁.1 hw⟩
        intro hEq
        exact hv₁ (hEq ▸ hw)
      have hρ₂erase : ρ₂.carrier ⊆ τ.carrier.erase v := by
        intro w hw
        refine Finset.mem_erase.mpr ⟨?_, hρ₂.1 hw⟩
        intro hEq
        exact hv₂ (hEq ▸ hw)
      have hcardρ₁ : ρ₁.carrier.card = (τ.carrier.erase v).card := by
        rw [Finset.card_erase_of_mem hv]
        exact Nat.eq_sub_of_add_eq hρ₁.2
      have hcardρ₂ : ρ₂.carrier.card = (τ.carrier.erase v).card := by
        rw [Finset.card_erase_of_mem hv]
        exact Nat.eq_sub_of_add_eq hρ₂.2
      have hEq₁ : ρ₁.carrier = τ.carrier.erase v :=
        Finset.eq_of_subset_of_card_le hρ₁erase (by simpa [hcardρ₁])
      have hEq₂ : ρ₂.carrier = τ.carrier.erase v :=
        Finset.eq_of_subset_of_card_le hρ₂erase (by simpa [hcardρ₂])
      exact False.elim <| hρne (SubdivisionFace.ext (hEq₁.trans hEq₂.symm))

theorem subdividesPrefixFace_of_two_distinct_codimOneSubfaces
    {τ ρ₁ ρ₂ : SubdivisionFace T}
    (hρ₁ : ρ₁.IsCodimOneSubface τ)
    (hρ₂ : ρ₂.IsCodimOneSubface τ)
    (hρne : ρ₁ ≠ ρ₂)
    {k : Fin (dimension + 1)}
    (hsub₁ : ρ₁.SubdividesPrefixFace (T := T) k)
    (hsub₂ : ρ₂.SubdividesPrefixFace (T := T) k) :
    τ.SubdividesPrefixFace (T := T) k := by
  intro v hv i hi
  rcases mem_of_mem_codimOneSubface_or_other (T := T) hρ₁ hρ₂ hρne hv with hv₁ | hv₂
  · exact hsub₁ v hv₁ i hi
  · exact hsub₂ v hv₂ i hi

/-- The image of a subdivision face meets one of the chosen Section 5 milestone segments. -/
def ImageMeetsMilestoneSegment (c : Section5MilestoneChain (dimension := dimension))
    (τ : SubdivisionFace T) (φ : Vertex → RentDivision (dimension + 1)) (k : Fin dimension) :
    Prop :=
  ∃ x : RentDivision (dimension + 1),
    ((x : RealPoint dimension) ∈ c.segment k) ∧
      τ.ImageContains (T := T) φ x

/--
The image of a subdivision face meets the interior of one milestone segment.

This packages the paper's genericity requirement that intersections with `[b_k, b_{k+1}]` occur
away from the segment endpoints unless one is in an endpoint case handled separately.
-/
def ImageMeetsOpenMilestoneSegment (c : Section5MilestoneChain (dimension := dimension))
    (τ : SubdivisionFace T) (φ : Vertex → RentDivision (dimension + 1)) (k : Fin dimension) :
    Prop :=
  ∃ x : RentDivision (dimension + 1),
    ((x : RealPoint dimension) ∈ c.segment k) ∧
      x ≠ c.point k.castSucc ∧
      x ≠ c.point k.succ ∧
      τ.ImageContains (T := T) φ x

/-- The image of a subdivision face contains one of the chosen Section 5 milestones. -/
def ImageContainsMilestone (c : Section5MilestoneChain (dimension := dimension))
    (τ : SubdivisionFace T) (φ : Vertex → RentDivision (dimension + 1))
    (k : Fin (dimension + 1)) : Prop :=
  τ.ImageContains (T := T) φ (c.point k)

lemma imageContainsMilestone_mono
    {c : Section5MilestoneChain (dimension := dimension)} {τ σ : SubdivisionFace T}
    (h : τ.carrier ⊆ σ.carrier) {φ : Vertex → RentDivision (dimension + 1)}
    {k : Fin (dimension + 1)}
    (hk : τ.ImageContainsMilestone (T := T) c φ k) :
    σ.ImageContainsMilestone (T := T) c φ k :=
  imageContains_mono (T := T) h hk

/--
The chosen milestone lies in the image of a face, but not already in the image of any of its
codimension-`1` subfaces.

This is an image-side surrogate for the paper's relative-interior milestone condition.
-/
def ImageContainsPointAwayFromBoundary (τ : SubdivisionFace T)
    (φ : Vertex → RentDivision (dimension + 1)) (x : RentDivision (dimension + 1)) : Prop :=
  τ.ImageContains (T := T) φ x ∧
    ∀ ρ : SubdivisionFace T, ρ.IsCodimOneSubface τ → ¬ ρ.ImageContains (T := T) φ x

/--
Specialization of `ImageContainsPointAwayFromBoundary` to milestone points.
-/
def ImageContainsMilestoneAwayFromBoundary (c : Section5MilestoneChain (dimension := dimension))
    (τ : SubdivisionFace T) (φ : Vertex → RentDivision (dimension + 1))
    (k : Fin (dimension + 1)) : Prop :=
  τ.ImageContainsPointAwayFromBoundary (T := T) φ (c.point k)

lemma imageMeetsMilestoneSegment_of_imageMeetsOpenMilestoneSegment
    {c : Section5MilestoneChain (dimension := dimension)} {τ : SubdivisionFace T}
    {φ : Vertex → RentDivision (dimension + 1)} {k : Fin dimension}
    (hτ : τ.ImageMeetsOpenMilestoneSegment (T := T) c φ k) :
    τ.ImageMeetsMilestoneSegment (T := T) c φ k := by
  rcases hτ with ⟨x, hxseg, -, -, himg⟩
  exact ⟨x, hxseg, himg⟩

lemma imageMeetsMilestoneSegment_mono
    {c : Section5MilestoneChain (dimension := dimension)} {τ σ : SubdivisionFace T}
    (h : τ.carrier ⊆ σ.carrier) {φ : Vertex → RentDivision (dimension + 1)}
    {k : Fin dimension}
    (hτ : τ.ImageMeetsMilestoneSegment (T := T) c φ k) :
    σ.ImageMeetsMilestoneSegment (T := T) c φ k := by
  rcases hτ with ⟨x, hxseg, hximg⟩
  exact ⟨x, hxseg, imageContains_mono (T := T) h hximg⟩

lemma imageMeetsOpenMilestoneSegment_mono
    {c : Section5MilestoneChain (dimension := dimension)} {τ σ : SubdivisionFace T}
    (h : τ.carrier ⊆ σ.carrier) {φ : Vertex → RentDivision (dimension + 1)}
    {k : Fin dimension}
    (hτ : τ.ImageMeetsOpenMilestoneSegment (T := T) c φ k) :
    σ.ImageMeetsOpenMilestoneSegment (T := T) c φ k := by
  rcases hτ with ⟨x, hxseg, hxlower, hxupper, hximg⟩
  exact ⟨x, hxseg, hxlower, hxupper, imageContains_mono (T := T) h hximg⟩

lemma imageMeetsOpenMilestoneSegment_of_meets_of_not_containsMilestones
    {c : Section5MilestoneChain (dimension := dimension)} {τ : SubdivisionFace T}
    {φ : Vertex → RentDivision (dimension + 1)} {k : Fin dimension}
    (hτ : τ.ImageMeetsMilestoneSegment (T := T) c φ k)
    (hlower : ¬ τ.ImageContainsMilestone (T := T) c φ k.castSucc)
    (hupper : ¬ τ.ImageContainsMilestone (T := T) c φ k.succ) :
    τ.ImageMeetsOpenMilestoneSegment (T := T) c φ k := by
  rcases hτ with ⟨x, hxseg, himg⟩
  refine ⟨x, hxseg, ?_, ?_, himg⟩
  · intro hx
    apply hlower
    simpa [SubdivisionFace.ImageContainsMilestone, hx, SubdivisionFace.ImageContains] using himg
  · intro hx
    apply hupper
    simpa [SubdivisionFace.ImageContainsMilestone, hx, SubdivisionFace.ImageContains] using himg

lemma imageContainsMilestone_of_imageContainsMilestoneAwayFromBoundary
    {c : Section5MilestoneChain (dimension := dimension)} {τ : SubdivisionFace T}
    {φ : Vertex → RentDivision (dimension + 1)} {k : Fin (dimension + 1)}
    (hτ : τ.ImageContainsMilestoneAwayFromBoundary (T := T) c φ k) :
    τ.ImageContainsMilestone (T := T) c φ k :=
  hτ.1

end SubdivisionFace

end GraphData

section MilestoneFamilies

variable {dimension : ℕ} {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
variable {T : SimplicialSubdivision dimension Vertex}
variable (φ : PiecewiseLinearSimplexMap T)

namespace SubdivisionFace

/--
One image vertex of a subdivision face, re-bundled as a point of the corresponding prefix face.

This is the target-side version of `SubdividesPrefixFace`: because the piecewise-linear map
preserves boundary faces, any vertex of a face subdividing the `k`-th prefix face is sent back
into that same prefix face.
-/
def prefixImageVertex (φ : PiecewiseLinearSimplexMap T) {k : Fin (dimension + 1)}
    (τ : SubdivisionFace T)
    (hτ : τ.SubdividesPrefixFace (T := T) k) (v : Vertex) (hv : v ∈ τ.carrier) :
    PrefixFace (dimension := dimension) k :=
  ⟨φ.vertexMap v, by
    intro i hi
    have hvi : (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0 :=
      hτ v hv i hi
    have hnot : i ∉ T.boundaryFace v := by
      intro hi'
      exact ((T.boundaryFace_exact v i).mp hi') hvi
    exact φ.boundary_preserving v i hnot⟩

@[simp] lemma prefixImageVertex_val (φ : PiecewiseLinearSimplexMap T) {k : Fin (dimension + 1)}
    (τ : SubdivisionFace T)
    (hτ : τ.SubdividesPrefixFace (T := T) k) (v : Vertex) (hv : v ∈ τ.carrier) :
    (prefixImageVertex (T := T) φ τ hτ v hv).1 = φ.vertexMap v :=
  rfl

/--
The finite set of target-side prefix-face vertices coming from a subdivision face.

These are the actual points whose convex hull is excluded when choosing a generic Section 5
milestone in the `k`-th prefix face.
-/
def prefixImageVertices (φ : PiecewiseLinearSimplexMap T) {k : Fin (dimension + 1)}
    (τ : SubdivisionFace T)
    (hτ : τ.SubdividesPrefixFace (T := T) k) : Finset (PrefixFace (dimension := dimension) k) :=
  by
    classical
    exact τ.carrier.attach.image (fun v => prefixImageVertex (T := T) φ τ hτ v.1 v.2)

lemma card_prefixImageVertices_le (φ : PiecewiseLinearSimplexMap T) {k : Fin (dimension + 1)}
    (τ : SubdivisionFace T)
    (hτ : τ.SubdividesPrefixFace (T := T) k) :
    (prefixImageVertices (T := T) φ τ hτ).card ≤ τ.carrier.card := by
  classical
  unfold prefixImageVertices
  calc
    (τ.carrier.attach.image
        (fun v => prefixImageVertex (T := T) φ τ hτ v.1 v.2)).card ≤
      τ.carrier.attach.card := Finset.card_image_le
    _ = τ.carrier.card := by rw [Finset.card_attach]

end SubdivisionFace

/--
The actual finite family of lower-dimensional face images to avoid in the `k`-th prefix face.

This packages the Section 5 milestone constraint at one level: when choosing the `k`-th milestone,
avoid the images of all subdivision faces inside the `k`-th prefix face that have at most `k`
vertices, i.e. dimension at most `k - 1`.
-/
lemma carrier_injective : Function.Injective (fun τ : SubdivisionFace T => τ.carrier) := by
  intro τ σ h
  cases τ
  cases σ
  cases h
  rfl

/-- The lower-dimensional prefix faces whose images are forbidden milestone locations. -/
def milestoneForbiddenFaces (k : Fin (dimension + 1)) : Finset (SubdivisionFace T) := by
  classical
  letI : Fintype (SubdivisionFace T) :=
    Fintype.ofInjective (fun τ : SubdivisionFace T => τ.carrier) (carrier_injective (T := T))
  exact Finset.univ.filter fun τ : SubdivisionFace T =>
    τ.SubdividesPrefixFace (T := T) k ∧ τ.carrier.card ≤ k.1

def milestoneForbiddenFamily (k : Fin (dimension + 1)) :
    Finset (Finset (PrefixFace (dimension := dimension) k)) := by
  classical
  exact (milestoneForbiddenFaces (T := T) k).attach.image
    (fun τ => τ.1.prefixImageVertices φ (Finset.mem_filter.mp τ.2).2.1)

lemma card_milestoneForbiddenFamily_member_le {k : Fin (dimension + 1)}
    {t : Finset (PrefixFace (dimension := dimension) k)}
    (ht : t ∈ milestoneForbiddenFamily (T := T) (φ := φ) k) :
    t.card ≤ k.1 := by
  classical
  rcases Finset.mem_image.mp ht with ⟨τ, hτmem, rfl⟩
  have hτprops := Finset.mem_filter.mp τ.2
  exact (τ.1.card_prefixImageVertices_le φ hτprops.2.1).trans hτprops.2.2

lemma prefixImageVertices_mem_milestoneForbiddenFamily {k : Fin (dimension + 1)}
    (τ : SubdivisionFace T) (hτ : τ.SubdividesPrefixFace (T := T) k)
    (hcard : τ.carrier.card ≤ k.1) :
    τ.prefixImageVertices φ hτ ∈ milestoneForbiddenFamily (T := T) (φ := φ) k := by
  classical
  unfold milestoneForbiddenFamily
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨τ, by simp [milestoneForbiddenFaces, hτ, hcard]⟩, by simp, ?_⟩
  simp

/--
At every prefix level, one can choose a milestone point avoiding the actual lower-dimensional
Section 5 forbidden family at that level.
-/
theorem exists_prefixMilestonePoint_avoiding_forbiddenFamily (k : Fin (dimension + 1)) :
    ∃ x : PrefixFace (dimension := dimension) k,
      PrefixFace.smallPoint (dimension := dimension) (k := k) x ∈
          interior
            (((↑) :
                affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1)) →
                  RealPoint k.1) ⁻¹'
              (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))) ∧
        ∀ t ∈ milestoneForbiddenFamily (T := T) (φ := φ) k,
          ((x.1 : RentDivision (dimension + 1)) : RealPoint dimension) ∉
            convexHull ℝ
              ((fun z : PrefixFace (dimension := dimension) k =>
                  ((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)) ''
                (t : Set _)) := by
  exact
    PrefixFace.exists_smallPointInterior_not_mem_biUnion_convexHull_of_card_le
      (T := milestoneForbiddenFamily (T := T) (φ := φ) k)
      (fun t ht => card_milestoneForbiddenFamily_member_le (T := T) (φ := φ) ht)

lemma prefixVertex_coord_eq_zero_of_lt (k : Fin (dimension + 1)) (j : Fin (k.1 + 1))
    {i : Room (dimension + 1)} (hi : k.1 < i.1) :
    (((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
      RealPoint dimension) i) = 0 := by
  have hne : j.castLE (Nat.succ_le_of_lt k.2) ≠ i := by
    intro hEq
    have hle : i.1 ≤ k.1 := by
      have hle' : (j.castLE (Nat.succ_le_of_lt k.2)).1 ≤ k.1 := by
        simpa using Nat.le_of_lt_succ j.2
      simpa [hEq] using hle'
    omega
  simp [prefixVertex, stdSimplex.vertex, hne]

lemma prefixBarycenter_coord_eq_zero_of_lt (k : Fin (dimension + 1))
    {i : Room (dimension + 1)} (hi : k.1 < i.1) :
    (((prefixBarycenter (dimension := dimension) k : RentDivision (dimension + 1)) :
      RealPoint dimension) i) = 0 := by
  unfold prefixBarycenter
  change
    (((Finset.univ.centerMass (fun _ : Fin (k.1 + 1) => (1 : ℝ))
      (fun j =>
        ((prefixVertex (dimension := dimension) k j : RentDivision (dimension + 1)) :
          RealPoint dimension))) i) = 0)
  simp [Finset.centerMass, Pi.smul_apply, smul_eq_mul,
    prefixVertex_coord_eq_zero_of_lt (dimension := dimension) k, hi]

/-- The true barycenter of a prefix face, re-bundled as a point of that prefix face. -/
def prefixBarycenterPoint (k : Fin (dimension + 1)) : PrefixFace (dimension := dimension) k :=
  ⟨prefixBarycenter (dimension := dimension) k,
    fun _ hi => prefixBarycenter_coord_eq_zero_of_lt (dimension := dimension) k hi⟩

/--
The concrete milestone points used for the Section 5 graph proof:
start at `e₁`, end at the true simplex barycenter, and use levelwise avoiding choices in between.
-/
noncomputable def chosenPrefixMilestonePoint (k : Fin (dimension + 1)) :
    PrefixFace (dimension := dimension) k :=
  if hk0 : k = 0 then
    hk0 ▸ prefixBarycenterPoint (dimension := dimension) 0
  else if hklast : k = Fin.last dimension then
    hklast ▸ prefixBarycenterPoint (dimension := dimension) (Fin.last dimension)
  else
    Classical.choose (exists_prefixMilestonePoint_avoiding_forbiddenFamily
      (T := T) (φ := φ) k)

lemma chosenPrefixMilestonePoint_spec {k : Fin (dimension + 1)}
    (hk0 : k ≠ 0) (hklast : k ≠ Fin.last dimension) :
    PrefixFace.smallPoint (dimension := dimension) (k := k)
        (chosenPrefixMilestonePoint (φ := φ) k) ∈
          interior
            (((↑) :
                affineSpan ℝ (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1)) →
                  RealPoint k.1) ⁻¹'
              (stdSimplex ℝ (Room (k.1 + 1)) : Set (RealPoint k.1))) ∧
      ∀ t ∈ milestoneForbiddenFamily (T := T) (φ := φ) k,
        (((chosenPrefixMilestonePoint (φ := φ) k).1 :
            RentDivision (dimension + 1)) : RealPoint dimension) ∉
          convexHull ℝ
            ((fun z : PrefixFace (dimension := dimension) k =>
                ((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)) ''
              (t : Set _)) := by
  simpa [chosenPrefixMilestonePoint, hk0, hklast] using
    (Classical.choose_spec
      (exists_prefixMilestonePoint_avoiding_forbiddenFamily (T := T) (φ := φ) k))

/-- The Section 5 milestone chain with fixed endpoints and chosen intermediate avoiding points. -/
noncomputable def chosenMilestoneChain : Section5MilestoneChain (dimension := dimension) where
  point k := (chosenPrefixMilestonePoint (T := T) (φ := φ) k).1
  start_eq := by
    simp [chosenPrefixMilestonePoint, prefixBarycenterPoint]
  terminal_eq := by
    unfold chosenPrefixMilestonePoint
    by_cases hk0 : (Fin.last dimension : Fin (dimension + 1)) = 0
    · have hdim : dimension = 0 := by
        have hval := congrArg Fin.val hk0
        simpa using hval
      subst hdim
      simp [prefixBarycenterPoint]
    · simp [hk0, prefixBarycenterPoint]
  point_subdividesPrefixFace := by
    intro k i hi
    exact (chosenPrefixMilestonePoint (T := T) (φ := φ) k).2 i hi

@[simp] lemma chosenMilestoneChain_point (k : Fin (dimension + 1)) :
    (chosenMilestoneChain (φ := φ)).point k =
      (chosenPrefixMilestonePoint (φ := φ) k).1 :=
  rfl

@[simp] lemma prefixVertex_last (j : Fin (dimension + 1)) :
    prefixVertex (dimension := dimension) (Fin.last dimension) j =
      stdSimplex.vertex (S := ℝ) j := by
  ext i
  by_cases h : i = j
  · subst h
    simp [prefixVertex, stdSimplex.vertex]
  · simp [prefixVertex, stdSimplex.vertex, h]

lemma prefixBarycenter_last_eq_barycentricRentDivision :
    prefixBarycenter (dimension := dimension) (Fin.last dimension) =
      barycentricRentDivision (dimension + 1) := by
  ext i
  change
    (Finset.univ.centerMass (fun _ : Fin (dimension + 1) => (1 : ℝ))
      (fun j =>
        ((prefixVertex (dimension := dimension) (Fin.last dimension) j :
          RentDivision (dimension + 1)) : RealPoint dimension)) i) =
      (((barycentricRentDivision (dimension + 1) : RentDivision (dimension + 1)) :
        RealPoint dimension) i)
  rw [show ((barycentricRentDivision (dimension + 1) : RentDivision (dimension + 1)) :
      RealPoint dimension) =
      Finset.centerMass Finset.univ (fun _ : Room (dimension + 1) => (1 : ℝ))
        (fun j => ((stdSimplex.vertex (S := ℝ) j : RentDivision (dimension + 1)) :
          RealPoint dimension)) by
        simpa [barycentricRentDivision] using
          (stdSimplex.barycenter_eq_centerMass (𝕜 := ℝ) (X := Room (dimension + 1)))]
  simp [prefixVertex_last]

lemma chosenMilestoneChain_terminal_eq_barycenter :
    (chosenMilestoneChain (T := T) (φ := φ)).point (Fin.last dimension) =
      barycentricRentDivision (dimension + 1) := by
  rw [(chosenMilestoneChain (T := T) (φ := φ)).terminal_eq]
  exact prefixBarycenter_last_eq_barycentricRentDivision (dimension := dimension)

lemma chosenPrefixMilestonePoint_terminal_eq_barycenter :
    (chosenPrefixMilestonePoint (T := T) (φ := φ) (Fin.last dimension)).1 =
      barycentricRentDivision (dimension + 1) := by
  rw [← chosenMilestoneChain_point (T := T) (φ := φ) (Fin.last dimension)]
  exact chosenMilestoneChain_terminal_eq_barycenter (T := T) (φ := φ)

lemma imagePoints_eq_prefixImageVertices {k : Fin (dimension + 1)}
    (τ : SubdivisionFace T) (hτ : τ.SubdividesPrefixFace (T := T) k) :
    τ.imagePoints φ.vertexMap =
      (fun z : PrefixFace (dimension := dimension) k =>
        ((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)) ''
          ((τ.prefixImageVertices φ hτ : Finset (PrefixFace (dimension := dimension) k)) : Set
            (PrefixFace (dimension := dimension) k)) := by
  classical
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨SubdivisionFace.prefixImageVertex (T := T) φ τ hτ v hv, ?_, by simp⟩
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, by simp, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨v, hvmem, hvz⟩
    rcases v with ⟨v, hv⟩
    refine ⟨v, hv, ?_⟩
    simpa using congrArg Subtype.val hvz

end MilestoneFamilies

section GraphStructure

variable {dimension : ℕ} {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
variable {T : SimplicialSubdivision dimension Vertex}
variable (c : Section5MilestoneChain (dimension := dimension))
variable (φ : PiecewiseLinearSimplexMap T)

/--
A positive-dimensional vertex of the paper's Section 5 graph.

Such a node is a subdivision face of dimension `k + 1` that subdivides the prefix outer face
spanned by the first `k + 2` simplex vertices and whose image meets the segment joining the
successive Section 5 milestones.
-/
structure Section5PositiveNode where
  level : Fin dimension
  face : SubdivisionFace T
  face_dim : face.dim = level.1 + 1
  subdivides : face.SubdividesPrefixFace (T := T) level.succ
  meets_segment : face.ImageMeetsMilestoneSegment (T := T) c φ.vertexMap level

/-- The vertices of the Section 5 graph: a special start node and the positive-dimensional faces. -/
inductive Section5GraphNode
  | start
  | positive (_ : Section5PositiveNode c φ)

namespace Section5PositiveNode

@[ext] theorem ext {ν μ : Section5PositiveNode c φ}
    (hlevel : ν.level = μ.level) (hface : ν.face = μ.face) : ν = μ := by
  cases ν
  cases μ
  cases hlevel
  cases hface
  simp

/--
The start node is connected to those one-dimensional graph faces that geometrically contain the
first simplex vertex `e₁`.
-/
def IsStartIncident (ν : Section5PositiveNode c φ) : Prop :=
  ν.level.1 = 0 ∧
    ν.face.ContainsPoint (T := T) (c.point 0)

/--
Horizontal adjacency in the Section 5 graph: two same-level faces are connected when they share a
codimension-`1` subface whose image meets the corresponding milestone segment.
-/
def HorizontalAdj (ν μ : Section5PositiveNode c φ) : Prop :=
  ν.level = μ.level ∧
    ν.face ≠ μ.face ∧
    ∃ τ : SubdivisionFace T,
      τ.IsCodimOneSubface ν.face ∧
      τ.IsCodimOneSubface μ.face ∧
      τ.ImageMeetsMilestoneSegment (T := T) c φ.vertexMap ν.level

/--
Vertical adjacency in the Section 5 graph: a `(k + 1)`-dimensional face is connected to an
incident `k`-dimensional face whose image contains the intermediate milestone.
-/
def VerticalAdj (lower upper : Section5PositiveNode c φ) : Prop :=
  lower.level.1 + 1 = upper.level.1 ∧
    lower.face.IsCodimOneSubface upper.face ∧
    lower.face.ImageContainsMilestone (T := T) c φ.vertexMap lower.level.succ

lemma horizontalAdj_symm {ν μ : Section5PositiveNode c φ} :
    ν.HorizontalAdj (T := T) c φ μ → μ.HorizontalAdj (T := T) c φ ν := by
  rintro ⟨hlevel, hne, τ, hτν, hτμ, hseg⟩
  refine ⟨hlevel.symm, hne.symm, τ, hτμ, hτν, ?_⟩
  simpa [hlevel] using hseg

lemma not_horizontalAdj_self (ν : Section5PositiveNode c φ) :
    ¬ ν.HorizontalAdj (T := T) c φ ν := by
  rintro ⟨_, hne, _⟩
  exact hne rfl

lemma not_verticalAdj_self (ν : Section5PositiveNode c φ) :
    ¬ ν.VerticalAdj (T := T) c φ ν := by
  rintro ⟨hlevel, _, _⟩
  exact Nat.succ_ne_self _ hlevel

lemma isStartIncident_face_dim (ν : Section5PositiveNode c φ)
    (hν : ν.IsStartIncident (T := T) c φ) : ν.face.dim = 1 := by
  rcases hν with ⟨hlevel, _⟩
  rw [ν.face_dim, hlevel]

end Section5PositiveNode

section Parity

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]

/--
Finite-graph parity principle used by the Section 5 walk argument.

If one distinguished start vertex has odd degree and every nonterminal vertex away from the start
has even degree, then some terminal vertex distinct from the start must exist.
-/
theorem exists_terminal_of_odd_start_and_nonterminal_even
    (start : V) (terminal : V → Prop)
    (hstart : Odd (G.degree start))
    (heven : ∀ v, v ≠ start → ¬ terminal v → Even (G.degree v)) :
    ∃ v, v ≠ start ∧ terminal v := by
  rcases G.exists_ne_odd_degree_of_exists_odd_degree start hstart with ⟨v, hv, hoddv⟩
  refine ⟨v, hv, ?_⟩
  by_contra hterminal
  exact (Nat.not_even_iff_odd.mpr hoddv) (heven v hv hterminal)

end Parity

namespace Section5GraphNode

/-- The adjacency relation on the paper's Section 5 graph. -/
def Adj : Section5GraphNode c φ → Section5GraphNode c φ → Prop
  | .start, .start => False
  | .start, .positive ν => ν.IsStartIncident (T := T) c φ
  | .positive ν, .start => ν.IsStartIncident (T := T) c φ
  | .positive ν, .positive μ =>
      ν.HorizontalAdj (T := T) c φ μ ∨
        ν.VerticalAdj (T := T) c φ μ ∨
        μ.VerticalAdj (T := T) c φ ν

lemma adj_symm : Symmetric (Adj (T := T) c φ) := by
  intro a b hab
  cases a with
  | start =>
      cases b with
      | start =>
          cases hab
      | positive ν =>
          exact hab
  | positive ν =>
      cases b with
      | start =>
          exact hab
      | positive μ =>
          rcases hab with h | h | h
          · exact Or.inl (Section5PositiveNode.horizontalAdj_symm (T := T) (c := c) (φ := φ) h)
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)

lemma not_adj_self (v : Section5GraphNode c φ) : ¬ Adj (T := T) c φ v v := by
  cases v with
  | start =>
      simp [Adj]
  | positive ν =>
      intro h
      rcases h with h | h | h
      · exact Section5PositiveNode.not_horizontalAdj_self (T := T) (c := c) (φ := φ) ν h
      · exact Section5PositiveNode.not_verticalAdj_self (T := T) (c := c) (φ := φ) ν h
      · exact Section5PositiveNode.not_verticalAdj_self (T := T) (c := c) (φ := φ) ν h

/-- The graph used in the paper's Section 5 trap-door / path-following argument. -/
def graph : SimpleGraph (Section5GraphNode c φ) where
  Adj := Adj (T := T) c φ
  symm := adj_symm (T := T) (c := c) (φ := φ)
  loopless := ⟨fun v => not_adj_self (T := T) (c := c) (φ := φ) v⟩

@[simp] lemma adj_start_start :
    ¬ Adj (T := T) c φ (.start) (.start) := by
  simp [Adj]

@[simp] lemma adj_start_positive {ν : Section5PositiveNode c φ} :
    Adj (T := T) c φ (.start) (.positive ν) ↔ ν.IsStartIncident (T := T) c φ := by
  rfl

@[simp] lemma adj_positive_start {ν : Section5PositiveNode c φ} :
    Adj (T := T) c φ (.positive ν) (.start) ↔ ν.IsStartIncident (T := T) c φ := by
  rfl

lemma adj_positive_positive_iff {ν μ : Section5PositiveNode c φ} :
    Adj (T := T) c φ (.positive ν) (.positive μ) ↔
      ν.HorizontalAdj (T := T) c φ μ ∨
        ν.VerticalAdj (T := T) c φ μ ∨
        μ.VerticalAdj (T := T) c φ ν := by
  rfl

/--
The terminal vertices sought in Section 5: top-dimensional subdivision faces whose image contains
the barycenter of the ambient simplex.
-/
def IsTerminal : Section5GraphNode c φ → Prop
  | .start => False
  | .positive ν =>
      ν.face.dim = dimension ∧
        ν.face.ImageContainsMilestone (T := T) c φ.vertexMap (Fin.last dimension)

theorem exists_subset_contains_lowerMilestone_of_exists_upperCoord_ne_zero
    {ν : Section5PositiveNode c φ}
    (hcontains :
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc)
    (hupperVertex :
      ∃ v ∈ ν.face.carrier,
        (((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) ≠ 0) :
    ∃ s : Finset Vertex,
      s ⊆ ν.face.carrier ∧
      s.card ≤ ν.level.succ.1 ∧
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (s : Set Vertex))) := by
  classical
  let pfun : Vertex → RealPoint dimension := fun v =>
    ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)
  let img : Finset (RealPoint dimension) := ν.face.carrier.image pfun
  let imgZero : Finset (RealPoint dimension) := img.filter fun y => y ν.level.succ = 0
  have hcontains_img :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ ((img : Finset (RealPoint dimension)) : Set (RealPoint dimension))) := by
    simpa [SubdivisionFace.ImageContains, SubdivisionFace.imagePoints, img, pfun] using hcontains
  rcases (Finset.mem_convexHull' (R := ℝ) (s := img)).1 hcontains_img with
    ⟨w, hw_nonneg, hw_sum, hw_repr⟩
  have hmilestone_zero :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension)
        ν.level.succ) = 0 := by
    exact c.point_subdividesPrefixFace ν.level.castSucc ν.level.succ (by simp)
  have hcoord_sum :
      ∑ y ∈ img, w y * y ν.level.succ = 0 := by
    have hcoord := congrArg (fun z : RealPoint dimension => z ν.level.succ) hw_repr
    simp [Pi.smul_apply, smul_eq_mul, hmilestone_zero] at hcoord
    exact hcoord
  have hterm_nonneg :
      ∀ y ∈ img, 0 ≤ w y * y ν.level.succ := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
    exact mul_nonneg (hw_nonneg _ (Finset.mem_image_of_mem _ hv)) ((φ.vertexMap v).2.1 _)
  have hterm_zero :
      ∀ y ∈ img, w y * y ν.level.succ = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hcoord_sum
  have hw_zero_of_coord_ne_zero :
      ∀ y ∈ img, y ν.level.succ ≠ 0 → w y = 0 := by
    intro y hy hy0
    have hzero := hterm_zero y hy
    exact mul_right_cancel₀ hy0 (by simpa [hzero] using hzero)
  have hsum_imgZero : ∑ y ∈ imgZero, w y = 1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not img (fun y => y ν.level.succ = 0) w
    have hnotZero :
        ∑ y ∈ img.filter fun y => ¬ y ν.level.succ = 0, w y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      exact hw_zero_of_coord_ne_zero y
        ((Finset.mem_filter.mp hy).1)
        (by simpa using (Finset.mem_filter.mp hy).2)
    have hsum' :
        (∑ y ∈ imgZero, w y) +
            ∑ y ∈ img.filter (fun y => ¬ y ν.level.succ = 0), w y = 1 := by
      simpa [imgZero] using hsplit.trans hw_sum
    simpa [hnotZero] using hsum'
  have hw_repr_imgZero :
      ∑ y ∈ imgZero, w y • y =
        (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension)) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not img
      (fun y => y ν.level.succ = 0) (fun y => w y • y)
    have hnotZero :
        ∑ y ∈ img.filter fun y => ¬ y ν.level.succ = 0, w y • y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hw0 : w y = 0 :=
        hw_zero_of_coord_ne_zero y (Finset.mem_filter.mp hy).1 (by simpa using (Finset.mem_filter.mp hy).2)
      simp [hw0]
    have hrepr' :
        (∑ y ∈ imgZero, w y • y) +
            ∑ y ∈ img.filter (fun y => ¬ y ν.level.succ = 0), w y • y =
          (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension)) := by
      simpa [imgZero] using hsplit.trans hw_repr
    simpa [hnotZero] using hrepr'
  have hcontains_imgZero :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ ((imgZero : Finset (RealPoint dimension)) : Set (RealPoint dimension))) := by
    exact (Finset.mem_convexHull' (R := ℝ) (s := imgZero)).2
      ⟨w, fun y hy => hw_nonneg _ (by exact (Finset.mem_filter.mp hy).1), hsum_imgZero, hw_repr_imgZero⟩
  rcases hupperVertex with ⟨v0, hv0, hv0neq⟩
  have hv0img : pfun v0 ∈ img := Finset.mem_image_of_mem _ hv0
  have hv0not : pfun v0 ∉ imgZero := by
    intro hv
    exact hv0neq ((Finset.mem_filter.mp hv).2)
  have hcard_imgZero_lt_img : imgZero.card < img.card := by
    exact Finset.card_lt_card <|
      (Finset.ssubset_iff_of_subset (by
        intro y hy
        exact (Finset.mem_filter.mp hy).1)).2 ⟨pfun v0, hv0img, hv0not⟩
  have hcard_img_le_face : img.card ≤ ν.face.carrier.card := by
    exact Finset.card_image_le
  have hcard_imgZero_le :
      imgZero.card ≤ ν.level.succ.1 := by
    have hfacecard : ν.face.carrier.card = ν.level.succ.1 + 1 := by
      rw [ν.face.card_eq_dim_succ, ν.face_dim]
      simp
    have hlt_face : imgZero.card < ν.face.carrier.card :=
      lt_of_lt_of_le hcard_imgZero_lt_img hcard_img_le_face
    exact Nat.lt_succ_iff.mp (by simpa [hfacecard] using hlt_face)
  let chooseVertex : {y // y ∈ imgZero} → Vertex := fun y =>
    Classical.choose (Finset.mem_image.mp ((Finset.mem_filter.mp y.2).1))
  have hchoose_mem :
      ∀ y : {y // y ∈ imgZero}, chooseVertex y ∈ ν.face.carrier := by
    intro y
    exact (Classical.choose_spec (Finset.mem_image.mp ((Finset.mem_filter.mp y.2).1))).1
  have hchoose_image :
      ∀ y : {y // y ∈ imgZero}, pfun (chooseVertex y) = y.1 := by
    intro y
    exact (Classical.choose_spec (Finset.mem_image.mp ((Finset.mem_filter.mp y.2).1))).2
  have hchoose_injective : Function.Injective chooseVertex := by
    intro y z hEq
    apply Subtype.ext
    simpa [hchoose_image y, hchoose_image z] using congrArg pfun hEq
  let s : Finset Vertex := imgZero.attach.image chooseVertex
  have hs_subset : s ⊆ ν.face.carrier := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨y, hy, rfl⟩
    exact hchoose_mem y
  have hs_card : s.card = imgZero.card := by
    simpa [s] using
      Finset.card_image_of_injective (s := imgZero.attach) (f := chooseVertex) hchoose_injective
  have hs_image :
      s.image pfun = imgZero := by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hu with ⟨z, hz, hEq⟩
      have huEq : pfun u = z.1 := by simpa [hEq] using hchoose_image z
      simpa [huEq] using z.2
    · intro hy
      refine Finset.mem_image.mpr ?_
      refine ⟨chooseVertex ⟨y, hy⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨y, hy⟩, by simp, rfl⟩
      · simpa [hchoose_image ⟨y, hy⟩]
  have hs_image_set :
      ((fun v : Vertex => pfun v) '' (s : Set Vertex)) =
        ((imgZero : Finset (RealPoint dimension)) : Set (RealPoint dimension)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : pfun x ∈ s.image pfun := Finset.mem_image_of_mem _ hx
      simpa [hs_image] using hx'
    · intro hy
      have hy' : y ∈ s.image pfun := by simpa [hs_image] using hy
      simpa using hy'
  refine ⟨s, hs_subset, by simpa [hs_card] using hcard_imgZero_le, ?_⟩
  simpa [SubdivisionFace.ImageContains, pfun, hs_image_set] using hcontains_imgZero

theorem exists_subset_contains_lowerMilestone_of_all_imageVertices_lowerPrefix
    {ν : Section5PositiveNode c φ}
    (hcontains :
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc)
    (hallLower :
      ∀ v ∈ ν.face.carrier,
        (((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0) :
    ∃ s : Finset Vertex,
      s ⊆ ν.face.carrier ∧
      s.card ≤ ν.level.succ.1 ∧
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (s : Set Vertex))) := by
  classical
  let pfun : Vertex → RealPoint dimension := fun v =>
    ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)
  have hcontains_img :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ (pfun '' (ν.face.carrier : Set Vertex))) := by
    simpa [SubdivisionFace.ImageContains, SubdivisionFace.imagePoints, pfun] using hcontains
  let t : Finset (RealPoint dimension) :=
    Caratheodory.minCardFinsetOfMemConvexHull hcontains_img
  have ht_subset :
      (t : Set (RealPoint dimension)) ⊆ pfun '' (ν.face.carrier : Set Vertex) :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hcontains_img
  have ht_mem :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ (t : Set (RealPoint dimension))) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hcontains_img
  have ht_indep :
      AffineIndependent ℝ (fun x : (t : Set (RealPoint dimension)) => (x : RealPoint dimension)) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hcontains_img
  have ht_aff :
      (t : Set (RealPoint dimension)) ⊆
        affineSpan ℝ
          (((prefixVertexFinset (dimension := dimension) ν.level.castSucc :
              Finset (RealPoint dimension)) : Set (RealPoint dimension))) := by
    intro y hy
    rcases ht_subset hy with ⟨v, hv, rfl⟩
    apply PrefixFace.mem_affineSpan_prefixVertexFinset_of_coord_eq_zero
      (dimension := dimension) (k := ν.level.castSucc)
    intro i hi
    by_cases hisucc : i = ν.level.succ
    · subst hisucc
      exact hallLower v hv
    · have hgt : ν.level.succ.1 < i.1 := by
        have hge : ν.level.succ.1 ≤ i.1 := by
          simpa using Nat.succ_le_of_lt hi
        have hne : ν.level.succ.1 ≠ i.1 := by
          intro hEq
          apply hisucc
          apply Fin.ext
          exact hEq.symm
        exact lt_of_le_of_ne hge hne
      have hdomain :
          (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) i) = 0 :=
        ν.subdivides v hv i hgt
      have hnot : i ∉ T.boundaryFace v := by
        intro hi_mem
        exact ((T.boundaryFace_exact v i).mp hi_mem) hdomain
      exact φ.boundary_preserving v i hnot
  have ht_card_le :
      t.card ≤ ν.level.succ.1 := by
    have hcard_prefix :
        t.card ≤ (prefixVertexFinset (dimension := dimension) ν.level.castSucc).card := by
      simpa using
        (AffineIndependent.card_le_card_of_subset_affineSpan
          (s := t)
          (t := prefixVertexFinset (dimension := dimension) ν.level.castSucc)
          ht_indep ht_aff)
    simpa [prefixVertexFinset_card] using hcard_prefix
  let chooseVertex : {y // y ∈ t} → Vertex := fun y =>
    Classical.choose (ht_subset y.2)
  have hchoose_mem :
      ∀ y : {y // y ∈ t}, chooseVertex y ∈ ν.face.carrier := by
    intro y
    exact (Classical.choose_spec (ht_subset y.2)).1
  have hchoose_image :
      ∀ y : {y // y ∈ t}, pfun (chooseVertex y) = y.1 := by
    intro y
    exact (Classical.choose_spec (ht_subset y.2)).2
  have hchoose_injective : Function.Injective chooseVertex := by
    intro y z hEq
    apply Subtype.ext
    simpa [hchoose_image y, hchoose_image z] using congrArg pfun hEq
  let s : Finset Vertex := t.attach.image chooseVertex
  have hs_subset : s ⊆ ν.face.carrier := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨y, hy, rfl⟩
    exact hchoose_mem y
  have hs_card : s.card = t.card := by
    simpa [s] using
      Finset.card_image_of_injective (s := t.attach) (f := chooseVertex) hchoose_injective
  have hs_image :
      s.image pfun = t := by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hu with ⟨z, hz, hEq⟩
      have huEq : pfun u = z.1 := by
        simpa [hEq] using hchoose_image z
      simpa [huEq] using z.2
    · intro hy
      refine Finset.mem_image.mpr ?_
      refine ⟨chooseVertex ⟨y, hy⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨y, hy⟩, by simp, rfl⟩
      · simpa [hchoose_image ⟨y, hy⟩]
  have hs_image_set :
      ((fun v : Vertex => pfun v) '' (s : Set Vertex)) = (t : Set (RealPoint dimension)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : pfun x ∈ s.image pfun := Finset.mem_image_of_mem _ hx
      simpa [hs_image] using hx'
    · intro hy
      have hy' : y ∈ s.image pfun := by
        simpa [hs_image] using hy
      simpa using hy'
  refine ⟨s, hs_subset, by simpa [hs_card] using ht_card_le, ?_⟩
  simpa [SubdivisionFace.ImageContains, pfun, hs_image_set] using ht_mem

theorem exists_codimOneSubface_contains_lowerMilestone_of_subset
    {ν : Section5PositiveNode c φ} {s : Finset Vertex}
    (hs : s ⊆ ν.face.carrier)
    (hcard : s.card ≤ ν.level.succ.1)
    (himg :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (s : Set Vertex)))) :
    ∃ ρ : SubdivisionFace T,
      ρ.IsCodimOneSubface ν.face ∧
        ρ.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc := by
  have hfacecard : ν.face.carrier.card = ν.level.succ.1 + 1 := by
    rw [ν.face.card_eq_dim_succ, ν.face_dim]
    simp
  have hslt : s.card < ν.face.carrier.card := by
    calc
      s.card ≤ ν.level.succ.1 := hcard
      _ < ν.level.succ.1 + 1 := Nat.lt_succ_self _
      _ = ν.face.carrier.card := hfacecard.symm
  rcases Finset.exists_mem_notMem_of_card_lt_card hslt with ⟨v, hvface, hvs⟩
  have hsErase : s ⊆ ν.face.carrier.erase v := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨by
      intro hEq
      exact hvs (hEq ▸ hw), hs (by simpa using hw)⟩
  let ρ : SubdivisionFace T :=
    ν.face.ofSubset (ν.face.carrier.erase v) (Finset.erase_subset _ _) (by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hvface]
      have hfacecard_pos : 1 < ν.face.carrier.card := by
        rw [hfacecard]
        simp
      exact Nat.sub_pos_of_lt hfacecard_pos)
  have himg' :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun w : Vertex =>
              ((φ.vertexMap w : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            ((ν.face.carrier.erase v : Finset Vertex) : Set Vertex))) :=
    convexHull_mono (by
      intro x hx
      rcases hx with ⟨w, hw, rfl⟩
      exact ⟨w, hsErase hw, rfl⟩) himg
  refine ⟨ρ, ?_, ?_⟩
  · exact ν.face.erase_isCodimOneSubface hvface (by
      rw [hfacecard]
      simp)
  · change
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun w : Vertex =>
              ((φ.vertexMap w : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            ((ν.face.carrier.erase v : Finset Vertex) : Set Vertex)))
    exact himg'

theorem exists_codimOneSubface_contains_lowerMilestone_of_exists_upperCoord_ne_zero
    {ν : Section5PositiveNode c φ}
    (hcontains :
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc)
    (hupperVertex :
      ∃ v ∈ ν.face.carrier,
        (((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) ≠ 0) :
    ∃ ρ : SubdivisionFace T,
      ρ.IsCodimOneSubface ν.face ∧
        ρ.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc := by
  rcases exists_subset_contains_lowerMilestone_of_exists_upperCoord_ne_zero
      (T := T) (c := c) (φ := φ) hcontains hupperVertex with ⟨s, hs, hcard, himg⟩
  exact exists_codimOneSubface_contains_lowerMilestone_of_subset
    (T := T) (c := c) (φ := φ) hs hcard himg

def verticalNeighborOfCodimOneSubfaceContainsLowerMilestone
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    {ρ : SubdivisionFace T}
    (hρ : ρ.IsCodimOneSubface ν.face)
    (hρsub : ρ.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρmil : ρ.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc) :
    Section5PositiveNode c φ := by
  let lowerLevel : Fin dimension :=
    ⟨ν.level.1 - 1, by
      simpa [Nat.pred_eq_sub_one] using
        lt_trans (Nat.pred_lt (Nat.ne_of_gt hk)) ν.level.2⟩
  have hk_le : 1 ≤ ν.level.1 := Nat.succ_le_of_lt hk
  have hsucc : lowerLevel.succ = ν.level.castSucc := by
    apply Fin.ext
    simp [lowerLevel, Nat.sub_add_cancel hk_le]
  have hρcard : ρ.carrier.card = ν.level.1 + 1 := by
    have hρeq : ρ.carrier.card + 1 = (ν.level.1 + 1) + 1 := by
      calc
        ρ.carrier.card + 1 = ν.face.carrier.card := hρ.2
        _ = (ν.level.1 + 1) + 1 := by rw [ν.face.card_eq_dim_succ, ν.face_dim]
    exact Nat.add_right_cancel hρeq
  have hρdim : ρ.dim = lowerLevel.1 + 1 := by
    calc
      ρ.dim = ρ.carrier.card - 1 := rfl
      _ = ν.level.1 := by simp [hρcard]
      _ = lowerLevel.1 + 1 := by
        simp [lowerLevel, Nat.sub_add_cancel hk_le]
  have hρmeets : ρ.ImageMeetsMilestoneSegment (T := T) c φ.vertexMap lowerLevel := by
    refine ⟨c.point lowerLevel.succ, ?_, ?_⟩
    · simpa [Section5MilestoneChain.segment, hsucc] using
        (right_mem_segment ℝ
          (((c.point lowerLevel.castSucc : RentDivision (dimension + 1)) : RealPoint dimension))
          (((c.point lowerLevel.succ : RentDivision (dimension + 1)) : RealPoint dimension)))
    · simpa [SubdivisionFace.ImageContainsMilestone, hsucc] using hρmil
  exact
    { level := lowerLevel
      face := ρ
      face_dim := hρdim
      subdivides := by simpa [hsucc] using hρsub
      meets_segment := hρmeets }

theorem verticalNeighborOfCodimOneSubfaceContainsLowerMilestone_verticalAdj
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    {ρ : SubdivisionFace T}
    (hρ : ρ.IsCodimOneSubface ν.face)
    (hρsub : ρ.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρmil : ρ.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc) :
    (verticalNeighborOfCodimOneSubfaceContainsLowerMilestone
      (T := T) (c := c) (φ := φ) hk hρ hρsub hρmil).VerticalAdj (T := T) c φ ν := by
  let lowerLevel : Fin dimension :=
    ⟨ν.level.1 - 1, by
      simpa [Nat.pred_eq_sub_one] using
        lt_trans (Nat.pred_lt (Nat.ne_of_gt hk)) ν.level.2⟩
  have hk_le : 1 ≤ ν.level.1 := Nat.succ_le_of_lt hk
  have hsucc : lowerLevel.succ = ν.level.castSucc := by
    apply Fin.ext
    simp [lowerLevel, Nat.sub_add_cancel hk_le]
  refine ⟨?_, hρ, ?_⟩
  · simp [verticalNeighborOfCodimOneSubfaceContainsLowerMilestone, Nat.sub_add_cancel hk_le]
  · simpa [verticalNeighborOfCodimOneSubfaceContainsLowerMilestone, lowerLevel, hsucc]
      using hρmil

theorem exists_verticalAdj_of_codimOneSubface_contains_lowerMilestone
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    {ρ : SubdivisionFace T}
    (hρ : ρ.IsCodimOneSubface ν.face)
    (hρsub : ρ.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρmil : ρ.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc) :
    ∃ μ : Section5PositiveNode c φ, μ.VerticalAdj (T := T) c φ ν := by
  refine ⟨
    verticalNeighborOfCodimOneSubfaceContainsLowerMilestone
      (T := T) (c := c) (φ := φ) hk hρ hρsub hρmil, ?_⟩
  exact verticalNeighborOfCodimOneSubfaceContainsLowerMilestone_verticalAdj
    (T := T) (c := c) (φ := φ) hk hρ hρsub hρmil

theorem exists_graphNeighbor_of_codimOneSubface_contains_lowerMilestone
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    {ρ : SubdivisionFace T}
    (hρ : ρ.IsCodimOneSubface ν.face)
    (hρsub : ρ.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρmil : ρ.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc) :
    ∃ w : Section5GraphNode c φ,
      w ≠ .positive ν ∧ Adj (T := T) c φ (.positive ν) w := by
  rcases exists_verticalAdj_of_codimOneSubface_contains_lowerMilestone
      (T := T) (c := c) (φ := φ) hk hρ hρsub hρmil with ⟨μ, hμ⟩
  refine ⟨.positive μ, ?_, ?_⟩
  · intro hEq
    cases hEq
    exact Section5PositiveNode.not_verticalAdj_self (T := T) (c := c) (φ := φ) ν hμ
  · exact Or.inr (Or.inr hμ)

theorem exists_verticalAdj_of_lowerPrefixSubset_contains_lowerMilestone
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    {s : Finset Vertex}
    (hs : s ⊆ ν.face.carrier)
    (hcard : s.card = ν.level.succ.1)
    (hslower :
      ∀ v ∈ s,
        (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0)
    (himg :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (s : Set Vertex)))) :
    ∃ μ : Section5PositiveNode c φ, μ.VerticalAdj (T := T) c φ ν := by
  have hsne : s.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    exact Nat.succ_pos _
  let ρ : SubdivisionFace T := ν.face.ofSubset s hs hsne
  have hρ : ρ.IsCodimOneSubface ν.face := by
    constructor
    · exact hs
    · have hfacecard : ν.face.carrier.card = ν.level.succ.1 + 1 := by
        rw [ν.face.card_eq_dim_succ, ν.face_dim]
        simp
      dsimp [ρ]
      calc
        s.card + 1 = ν.level.succ.1 + 1 := by rw [hcard]
        _ = ν.face.carrier.card := hfacecard.symm
  have hρsub : ρ.SubdividesPrefixFace (T := T) ν.level.castSucc := by
    intro v hv i hi
    by_cases hisucc : i = ν.level.succ
    · subst hisucc
      exact hslower v hv
    · have hgt : ν.level.succ.1 < i.1 := by
        have hge : ν.level.succ.1 ≤ i.1 := by
          simpa using Nat.succ_le_of_lt hi
        have hne : ν.level.succ.1 ≠ i.1 := by
          intro hEq
          apply hisucc
          exact Fin.ext hEq.symm
        exact lt_of_le_of_ne hge hne
      exact ν.subdivides v (hs hv) i hgt
  have hρmil :
      ρ.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc := by
    dsimp [ρ]
    simpa [SubdivisionFace.ImageContainsMilestone, SubdivisionFace.ImageContains,
      SubdivisionFace.imagePoints] using himg
  exact exists_verticalAdj_of_codimOneSubface_contains_lowerMilestone
    (T := T) (c := c) (φ := φ) hk hρ hρsub hρmil

theorem exists_graphNeighbor_of_lowerPrefixSubset_contains_lowerMilestone
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    {s : Finset Vertex}
    (hs : s ⊆ ν.face.carrier)
    (hcard : s.card = ν.level.succ.1)
    (hslower :
      ∀ v ∈ s,
        (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0)
    (himg :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (s : Set Vertex)))) :
    ∃ w : Section5GraphNode c φ,
      w ≠ .positive ν ∧ Adj (T := T) c φ (.positive ν) w := by
  rcases exists_verticalAdj_of_lowerPrefixSubset_contains_lowerMilestone
      (T := T) (c := c) (φ := φ) hk hs hcard hslower himg with ⟨μ, hμ⟩
  refine ⟨.positive μ, ?_, ?_⟩
  · intro hEq
    cases hEq
    exact Section5PositiveNode.not_verticalAdj_self (T := T) (c := c) (φ := φ) ν hμ
  · exact Or.inr (Or.inr hμ)

theorem exists_verticalAdj_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    {s u : Finset Vertex}
    (hsu : s ⊆ u)
    (hu : u ⊆ ν.face.carrier)
    (hscard : s.card ≤ ν.level.succ.1)
    (hucard : ν.level.succ.1 ≤ u.card)
    (hulower :
      ∀ v ∈ u,
        (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0)
    (himg :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (s : Set Vertex)))) :
    ∃ μ : Section5PositiveNode c φ, μ.VerticalAdj (T := T) c φ ν := by
  obtain ⟨t, hst, htu, htcard⟩ := Finset.exists_subsuperset_card_eq hsu hscard hucard
  have ht_lower :
      ∀ v ∈ t,
        (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0 :=
    fun v hv => hulower v (htu hv)
  have ht_img :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (t : Set Vertex))) := by
    exact convexHull_mono (by
      intro x hx
      rcases hx with ⟨v, hv, rfl⟩
      exact ⟨v, hst hv, rfl⟩) himg
  exact exists_verticalAdj_of_lowerPrefixSubset_contains_lowerMilestone
    (T := T) (c := c) (φ := φ) hk (htu.trans hu) htcard ht_lower ht_img

theorem exists_graphNeighbor_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    {s u : Finset Vertex}
    (hsu : s ⊆ u)
    (hu : u ⊆ ν.face.carrier)
    (hscard : s.card ≤ ν.level.succ.1)
    (hucard : ν.level.succ.1 ≤ u.card)
    (hulower :
      ∀ v ∈ u,
        (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0)
    (himg :
      (((c.point ν.level.castSucc : RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (s : Set Vertex)))) :
    ∃ w : Section5GraphNode c φ,
      w ≠ .positive ν ∧ Adj (T := T) c φ (.positive ν) w := by
  rcases exists_verticalAdj_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone
      (T := T) (c := c) (φ := φ) hk hsu hu hscard hucard hulower himg with ⟨μ, hμ⟩
  refine ⟨.positive μ, ?_, ?_⟩
  · intro hEq
    cases hEq
    exact Section5PositiveNode.not_verticalAdj_self (T := T) (c := c) (φ := φ) ν hμ
  · exact Or.inr (Or.inr hμ)

/--
Internal support-layer contract isolating the remaining lower-door geometry in the all-image-lower
case.

The current abstract subdivision API does not supply this large lower-prefix carrier set, but once
it is available the lower-milestone branch can be fed into the existing enlargement lemma above.
-/
structure PositiveFaceLowerPrefixReflection : Prop where
  exists_lowerPrefixCarrier_and_support_of_contains_lowerMilestone :
    ∀ {ν : Section5PositiveNode c φ},
      0 < ν.level.1 →
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc →
      ∃ s u : Finset Vertex,
        s ⊆ u ∧
        u ⊆ ν.face.carrier ∧
        s.card ≤ ν.level.succ.1 ∧
        ν.level.succ.1 ≤ u.card ∧
        (∀ v ∈ u,
          (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)
            ν.level.succ) = 0) ∧
        ((((c.point ν.level.castSucc : RentDivision (dimension + 1)) :
            RealPoint dimension) ∈
          convexHull ℝ
            ((fun v : Vertex =>
                ((φ.vertexMap v : RentDivision (dimension + 1)) :
                  RealPoint dimension)) '' (s : Set Vertex))))

/--
This semantic positive-face reflection hypothesis immediately yields the more combinatorial
carrier-set bundle used by the existing enlargement lemma.
-/
structure FaceLocalLargeLowerPrefixCarrierSpec : Prop where
  exists_support_in_largeLowerPrefixCarrier_of_contains_lowerMilestone :
    ∀ {ν : Section5PositiveNode c φ},
      0 < ν.level.1 →
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc →
      ∃ s u : Finset Vertex,
        s ⊆ u ∧
        u ⊆ ν.face.carrier ∧
        s.card ≤ ν.level.succ.1 ∧
        ν.level.succ.1 ≤ u.card ∧
        (∀ v ∈ u,
          (((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension)
            ν.level.succ) = 0) ∧
        ((((c.point ν.level.castSucc : RentDivision (dimension + 1)) :
            RealPoint dimension) ∈
          convexHull ℝ
            ((fun v : Vertex =>
                ((φ.vertexMap v : RentDivision (dimension + 1)) :
                  RealPoint dimension)) '' (s : Set Vertex))))

theorem faceLocalLargeLowerPrefixCarrierSpec_of_positiveFaceLowerPrefixReflection
    (hreflect : PositiveFaceLowerPrefixReflection (T := T) (c := c) (φ := φ)) :
    FaceLocalLargeLowerPrefixCarrierSpec (T := T) (c := c) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hcontains
  exact hreflect.exists_lowerPrefixCarrier_and_support_of_contains_lowerMilestone hk hcontains

/--
This derives the older graph-neighbor contract from the sharper large-lower-prefix carrier-set
formulation above.
-/
structure FaceLocalLowerPrefixCarrierSpec : Prop where
  exists_graphNeighbor_of_contains_lowerMilestone :
    ∀ {ν : Section5PositiveNode c φ},
      0 < ν.level.1 →
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc →
      ∃ w : Section5GraphNode c φ,
        w ≠ .positive ν ∧ Adj (T := T) c φ (.positive ν) w

theorem faceLocalLowerPrefixCarrierSpec_of_largeLowerPrefixCarrierSpec
    (hspec : FaceLocalLargeLowerPrefixCarrierSpec (T := T) (c := c) (φ := φ)) :
    FaceLocalLowerPrefixCarrierSpec (T := T) (c := c) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hcontains
  rcases hspec.exists_support_in_largeLowerPrefixCarrier_of_contains_lowerMilestone hk hcontains
      with ⟨s, u, hsu, hu, hscard, hucard, hulower, himg⟩
  exact exists_graphNeighbor_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone
    (T := T) (c := c) (φ := φ) hk hsu hu hscard hucard hulower himg

theorem exists_verticalAdj_of_contains_lowerMilestone_of_largeLowerPrefixCarrierSpec
    (hspec : FaceLocalLargeLowerPrefixCarrierSpec (T := T) (c := c) (φ := φ))
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    (hcontains :
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc) :
    ∃ μ : Section5PositiveNode c φ, μ.VerticalAdj (T := T) c φ ν := by
  rcases hspec.exists_support_in_largeLowerPrefixCarrier_of_contains_lowerMilestone hk hcontains
      with ⟨s, u, hsu, hu, hscard, hucard, hulower, himg⟩
  exact exists_verticalAdj_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone
    (T := T) (c := c) (φ := φ) hk hsu hu hscard hucard hulower himg

theorem exists_verticalAdj_of_contains_lowerMilestone_of_reflection
    (hreflect : PositiveFaceLowerPrefixReflection (T := T) (c := c) (φ := φ))
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    (hcontains :
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc) :
    ∃ μ : Section5PositiveNode c φ, μ.VerticalAdj (T := T) c φ ν := by
  exact exists_verticalAdj_of_contains_lowerMilestone_of_largeLowerPrefixCarrierSpec
    (T := T) (c := c) (φ := φ)
    (faceLocalLargeLowerPrefixCarrierSpec_of_positiveFaceLowerPrefixReflection
      (T := T) (c := c) (φ := φ) hreflect)
    hk hcontains

theorem exists_graphNeighbor_of_contains_lowerMilestone_of_faceLocalSpec
    (hspec : FaceLocalLowerPrefixCarrierSpec (T := T) (c := c) (φ := φ))
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    (hcontains :
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc) :
    ∃ w : Section5GraphNode c φ,
      w ≠ .positive ν ∧ Adj (T := T) c φ (.positive ν) w := by
  exact hspec.exists_graphNeighbor_of_contains_lowerMilestone hk hcontains

theorem exists_lowerMilestoneCarrier_of_reflection
    (hreflect : PositiveFaceLowerPrefixReflection (T := T) (c := c) (φ := φ))
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    (hcontains :
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc) :
    ∃ ρ : SubdivisionFace.CarrierCodimOneSubface ν.face,
      ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc ∧
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc := by
  rcases exists_verticalAdj_of_contains_lowerMilestone_of_reflection
      (T := T) (c := c) (φ := φ) hreflect hk hcontains with ⟨μ, hμ⟩
  rcases hμ with ⟨hlevel, hμν, hμmil⟩
  let ρ : SubdivisionFace.CarrierCodimOneSubface ν.face :=
    SubdivisionFace.CarrierCodimOneSubface.ofIsCodimOneSubface hμν
  have hsucc : μ.level.succ = ν.level.castSucc := by
    apply Fin.ext
    exact hlevel
  refine ⟨ρ, ?_, ?_⟩
  · intro v hv i hi
    exact μ.subdivides v
      (by
        simpa [ρ, SubdivisionFace.CarrierCodimOneSubface.ofIsCodimOneSubface_carrier] using hv)
      i (by simpa [hsucc] using hi)
  · simpa [SubdivisionFace.ImageContainsMilestone, hsucc, ρ,
      SubdivisionFace.CarrierCodimOneSubface.ofIsCodimOneSubface_carrier] using hμmil

theorem chosenMilestoneChain_nextMilestoneAwayFromBoundary_of_nonterminal
    {ν : Section5PositiveNode (c := chosenMilestoneChain (φ := φ)) φ}
    (hcontains :
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hν : ¬ IsTerminal (c := chosenMilestoneChain (φ := φ)) φ (.positive ν)) :
    ν.face.ImageContainsMilestoneAwayFromBoundary (T := T)
      (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ := by
  refine ⟨hcontains, ?_⟩
  intro ρ hρ hρcontains
  have hk0 : ν.level.succ ≠ 0 := by
    intro hk
    exact Fin.succ_ne_zero ν.level hk
  have hklast : ν.level.succ ≠ Fin.last dimension := by
    intro hk
    apply hν
    refine ⟨?_, by simpa [hk] using hcontains⟩
    have hval : ν.level.1 + 1 = dimension := by
      exact congrArg Fin.val hk
    rw [ν.face_dim]
    simpa using hval
  have hρsub :
      ρ.SubdividesPrefixFace (T := T) ν.level.succ :=
    SubdivisionFace.subdividesPrefixFace_of_subface (T := T) hρ.1 ν.subdivides
  have hρcard : ρ.carrier.card ≤ ν.level.succ.1 := by
    have hfacecard : ν.face.carrier.card = ν.level.succ.1 + 1 := by
      rw [ν.face.card_eq_dim_succ, ν.face_dim]
      simp
    have hρeq : ρ.carrier.card + 1 = ν.level.succ.1 + 1 := by
      calc
        ρ.carrier.card + 1 = ν.face.carrier.card := hρ.2
        _ = ν.level.succ.1 + 1 := hfacecard
    exact le_of_eq (Nat.add_right_cancel hρeq)
  have hρmem :
      ρ.prefixImageVertices φ hρsub ∈
        milestoneForbiddenFamily (T := T) (φ := φ) ν.level.succ :=
    prefixImageVertices_mem_milestoneForbiddenFamily (T := T) (φ := φ) ρ hρsub hρcard
  have hspec :=
    chosenPrefixMilestonePoint_spec (T := T) (φ := φ) hk0 hklast
  have havoid := hspec.2 _ hρmem
  have hmil :
      ((((chosenMilestoneChain (φ := φ)).point ν.level.succ :
          RentDivision (dimension + 1)) : RealPoint dimension) ∈
        convexHull ℝ
          ((fun z : PrefixFace (dimension := dimension) ν.level.succ =>
              ((z.1 : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            ((ρ.prefixImageVertices φ hρsub : Finset
                (PrefixFace (dimension := dimension) ν.level.succ)) : Set
                (PrefixFace (dimension := dimension) ν.level.succ)))) := by
    simpa [SubdivisionFace.ImageContainsMilestone, SubdivisionFace.ImageContains,
      chosenMilestoneChain_point,
      imagePoints_eq_prefixImageVertices (T := T) (φ := φ) ρ hρsub] using hρcontains
  exact havoid hmil

theorem chosenMilestoneChain_openSegment_of_missingNextMilestone_of_not_lowerMilestone
    {ν : Section5PositiveNode (c := chosenMilestoneChain (φ := φ)) φ}
    (hlower :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ) :
    ν.face.ImageMeetsOpenMilestoneSegment (T := T)
      (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level := by
  exact
    SubdivisionFace.imageMeetsOpenMilestoneSegment_of_meets_of_not_containsMilestones
      (T := T) ν.meets_segment hlower hupper

theorem chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone
    {ν : Section5PositiveNode (c := chosenMilestoneChain (φ := φ)) φ}
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ) :
    ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level ∨
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc := by
  by_cases hlower : ν.face.ImageContainsMilestone (T := T)
      (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc
  · exact Or.inr hlower
  · exact Or.inl
      (chosenMilestoneChain_openSegment_of_missingNextMilestone_of_not_lowerMilestone
        (T := T) (φ := φ) hlower hupper)

theorem chosenMilestoneChain_contains_lowerMilestone_of_missingNextMilestone_of_not_openCrossing
    {ν : Section5PositiveNode (c := chosenMilestoneChain (φ := φ)) φ}
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hclosed :
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level) :
    ν.face.ImageContainsMilestone (T := T)
      (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc := by
  rcases chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone
      (T := T) (φ := φ) (ν := ν) hupper with hopen | hlower
  · exact False.elim (hclosed hopen)
  · exact hlower

/--
Local degree data expected from the geometric genericity analysis in Section 5.

The paper's "rooms and doors" argument is local: one starting room has exactly one door, and every
nonterminal room has exactly two doors. This structure packages those consequences abstractly, so
the graph-theoretic parity step can be proved independently of the remaining convex-geometry work.
-/
structure LocalDegreeHypotheses where
  start_neighbor : Section5PositiveNode c φ
  start_adj :
    Adj (T := T) c φ .start (.positive start_neighbor)
  start_unique :
    ∀ w : Section5GraphNode c φ,
      Adj (T := T) c φ .start w → w = .positive start_neighbor
  nonterminal_two_neighbors :
    ∀ ν : Section5PositiveNode c φ,
      ¬ IsTerminal (T := T) c φ (.positive ν) →
      ∃ a b : Section5GraphNode c φ,
        a ≠ b ∧
        Adj (T := T) c φ (.positive ν) a ∧
        Adj (T := T) c φ (.positive ν) b ∧
        ∀ w : Section5GraphNode c φ,
          Adj (T := T) c φ (.positive ν) w → w = a ∨ w = b

/--
Casewise local-genericity hypotheses matching the paper's Section 5 discussion.

The paper distinguishes two local situations for a positive graph node `ν`.
If the next milestone `c_{k+1}` is not in the image of `ν.face`, then the segment
`[c_k, c_{k+1}]` should cross the image through exactly two doors.
If `c_{k+1}` is in the image of `ν.face`, then either `ν` is already terminal or there are again
exactly two continuation doors, now with one door arising from the milestone endpoint.
This structure records those two geometric cases abstractly, before converting them into the
graph-theoretic degree package `LocalDegreeHypotheses`.
-/
structure GeometricGenericity where
  start_neighbor : Section5PositiveNode c φ
  start_adj :
    Adj (T := T) c φ .start (.positive start_neighbor)
  start_unique :
    ∀ w : Section5GraphNode c φ,
      Adj (T := T) c φ .start w → w = .positive start_neighbor
  two_doors_of_missing_nextMilestone :
    ∀ ν : Section5PositiveNode c φ,
      ¬ ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.succ →
      ∃ a b : Section5GraphNode c φ,
        a ≠ b ∧
        Adj (T := T) c φ (.positive ν) a ∧
        Adj (T := T) c φ (.positive ν) b ∧
        ∀ w : Section5GraphNode c φ,
          Adj (T := T) c φ (.positive ν) w → w = a ∨ w = b
  two_doors_of_nextMilestone :
    ∀ ν : Section5PositiveNode c φ,
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.succ →
      ¬ IsTerminal (T := T) c φ (.positive ν) →
      ∃ a b : Section5GraphNode c φ,
        a ≠ b ∧
        Adj (T := T) c φ (.positive ν) a ∧
        Adj (T := T) c φ (.positive ν) b ∧
        ∀ w : Section5GraphNode c φ,
          Adj (T := T) c φ (.positive ν) w → w = a ∨ w = b

/--
Concrete milestone-segment genericity package for Section 5.

This strengthens `GeometricGenericity` with explicit milestone-segment predicates, but now keeps
the paper's lower-endpoint vertical-door case in the missing-next-milestone branch instead of
forcing every such intersection to be an open crossing.
-/
structure MilestoneSegmentTransversality
    extends GeometricGenericity (T := T) (c := c) (φ := φ) where
  missing_nextMilestone_openCrossing_or_contains_lowerMilestone :
    ∀ ν : Section5PositiveNode c φ,
      ¬ ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.succ →
      ν.face.ImageMeetsOpenMilestoneSegment (T := T) c φ.vertexMap ν.level ∨
        ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc
  nextMilestone_awayFromBoundary_of_nonterminal :
    ∀ ν : Section5PositiveNode c φ,
      ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.succ →
      ¬ IsTerminal (T := T) c φ (.positive ν) →
      ν.face.ImageContainsMilestoneAwayFromBoundary (T := T) c φ.vertexMap ν.level.succ

/--
Remaining graph-local contract for the concrete chosen chain.

The explicit milestone geometry already proved in this file reduces the higher-dimensional Section 5
argument to these start and door-count statements.
-/
structure ChosenMilestoneChainLevelZeroBoundarySpec where
  start_neighbor : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ
  start_adj :
    Adj (T := T) (chosenMilestoneChain (φ := φ)) φ .start (.positive start_neighbor)
  start_unique :
    ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ .start w →
        w = .positive start_neighbor
  two_doors_of_missing_nextMilestone_level_zero :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ν.level.1 = 0 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

structure ChosenMilestoneChainGraphLocalRestSpec where
  two_doors_of_missing_nextMilestone_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b
  two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      (∃ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        w ≠ .positive ν ∧
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w) →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b
  two_doors_of_nextMilestone_awayFromBoundary :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ν.face.ImageContainsMilestoneAwayFromBoundary (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ IsTerminal (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

/--
Minimal higher-dimensional transversality input for the open-crossing branch.

The current abstract face-image API does not rule out a positive face collapsing onto the
milestone segment, so the paper's "two continuation doors" claim for open crossings has to be
supplied separately at this stage.
-/
structure ChosenMilestoneChainOpenCrossingSpec where
  two_doors_of_missing_nextMilestone_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

/--
Remaining positive-level continuation input once the level-`0` boundary model and open-crossing
transversality are separated out.
-/
structure ChosenMilestoneChainPositiveLevelSpec where
  two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      (∃ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        w ≠ .positive ν ∧
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w) →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b
  two_doors_of_nextMilestone_awayFromBoundary :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ν.face.ImageContainsMilestoneAwayFromBoundary (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ IsTerminal (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

/--
Positive-level missing-next continuation needed after the open-crossing case has already been
discharged. This isolates the remaining lower-endpoint branch in the paper's missing-next case.
-/
structure ChosenMilestoneChainPositiveLevelLowerMilestoneSpec where
  two_doors_of_missing_nextMilestone_positiveLevel_contains_lowerMilestone :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      (∃ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        w ≠ .positive ν ∧
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w) →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

/--
The exact remaining lower-endpoint continuation theorem at positive levels.

This is the same branch as `ChosenMilestoneChainPositiveLevelLowerMilestoneSpec`, but with the
auxiliary "some extra neighbor exists" premise removed from the interface. If this theorem is
available, the older spec follows immediately by ignoring that redundant witness.
-/
structure ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec where
  two_doors_of_missing_nextMilestone_positiveLevel_contains_lowerMilestone :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

/--
Top-dimensional lower-milestone door theorem for the positive-level missing-next branch.

This isolates the replacement route needed after the ambient-facet same-level continuation theorem
was shown impossible at top dimension.
-/
structure ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneDoorSpec where
  two_doors_of_missing_nextMilestone_positiveLevel_topDim_contains_lowerMilestone :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ν.face.dim = dimension →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

/--
First missing geometric input for the top-dimensional lower-milestone branch.

This isolates exactly the multiplicity statement suggested by the paper's endpoint picture:
the lower milestone should lie on two distinct codimension-`1` lower-prefix carriers of the
top-dimensional face.
-/
structure ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec where
  exists_two_distinct_codimOneSubfaces_of_missing_nextMilestone_positiveLevel_topDim_contains_lowerMilestone :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ν.face.dim = dimension →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ ρ₁ ρ₂ : SubdivisionFace T,
        ρ₁ ≠ ρ₂ ∧
        ρ₁.IsCodimOneSubface ν.face ∧
        ρ₂.IsCodimOneSubface ν.face ∧
        ρ₁.SubdividesPrefixFace (T := T) ν.level.castSucc ∧
        ρ₂.SubdividesPrefixFace (T := T) ν.level.castSucc ∧
        ρ₁.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc ∧
        ρ₂.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc

/--
Sharper top-dimensional local gap: once one normalized lower-prefix codimension-`1` carrier is
known, produce a second distinct one.
-/
structure ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierSpec where
  exists_second_codimOneSubface_of_missing_nextMilestone_positiveLevel_topDim_contains_lowerMilestone :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ),
      0 < ν.level.1 →
      ν.face.dim = dimension →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      {ρ₁ : SubdivisionFace.CarrierCodimOneSubface ν.face} →
      ρ₁.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc →
      ρ₁.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ ρ₂ : SubdivisionFace T,
        ρ₂ ≠ ρ₁.toSubdivisionFace ∧
        ρ₂.IsCodimOneSubface ν.face ∧
        ρ₂.SubdividesPrefixFace (T := T) ν.level.castSucc ∧
        ρ₂.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc

/--
Exact remaining image-side top-dimensional gap.

Once the whole top-dimensional face is already known to lie in the lower prefix face, the
remaining task is only to show that the lower milestone is carried by a second codimension-`1`
subface besides the reflected one.
-/
theorem exists_second_codimOneSubface_imageContains_of_subset_in_codimOneSubface
    {τ : SubdivisionFace T} {φ : Vertex → RentDivision (dimension + 1)}
    {x : RentDivision (dimension + 1)}
    {ρ₁ : SubdivisionFace.CarrierCodimOneSubface τ}
    {s : Finset Vertex}
    (hs : s ⊆ ρ₁.carrier)
    (hcard : s.card + 1 ≤ ρ₁.carrier.card)
    (himg :
      ((x : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ v : RentDivision (dimension + 1)) : RealPoint dimension)) '' (s : Set Vertex)))) :
    ∃ ρ₂ : SubdivisionFace T,
      ρ₂ ≠ ρ₁.toSubdivisionFace ∧
      ρ₂.IsCodimOneSubface τ ∧
      ρ₂.ImageContains (T := T) φ x := by
  have hslt : s.card < ρ₁.carrier.card := by
    exact lt_of_lt_of_le (Nat.lt_succ_self s.card) hcard
  rcases Finset.exists_mem_notMem_of_card_lt_card hslt with ⟨v, hvρ₁, hvs⟩
  have hvτ : v ∈ τ.carrier := ρ₁.subset hvρ₁
  have hρ₁pos : 1 ≤ ρ₁.carrier.card := by
    calc
      1 ≤ s.card + 1 := Nat.succ_le_succ (Nat.zero_le _)
      _ ≤ ρ₁.carrier.card := hcard
  have hτcard : 1 < τ.carrier.card := by
    calc
      1 < ρ₁.carrier.card + 1 := Nat.lt_succ_of_le hρ₁pos
      _ = τ.carrier.card := ρ₁.card
  let ρ₂ : SubdivisionFace T :=
    τ.ofSubset (τ.carrier.erase v) (Finset.erase_subset _ _) (by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hvτ]
      exact Nat.sub_pos_of_lt hτcard)
  have hs₂ : s ⊆ ρ₂.carrier := by
    intro w hw
    refine Finset.mem_erase.mpr ⟨?_, ρ₁.subset (hs hw)⟩
    intro hwv
    exact hvs (hwv ▸ hw)
  have himg₂ :
      ρ₂.ImageContains (T := T) φ x := by
    change
      ((x : RealPoint dimension) ∈
        convexHull ℝ
          ((fun w : Vertex =>
              ((φ w : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            ((τ.carrier.erase v : Finset Vertex) : Set Vertex)))
    exact convexHull_mono (by
      intro y hy
      rcases hy with ⟨w, hw, rfl⟩
      exact ⟨w, hs₂ hw, rfl⟩) himg
  refine ⟨ρ₂, ?_, ?_, himg₂⟩
  · intro hEq
    have hvρ₂ : v ∈ ρ₂.carrier := by simpa [hEq] using hvρ₁
    exact (Finset.mem_erase.mp hvρ₂).1 rfl
  · exact τ.erase_isCodimOneSubface hvτ hτcard

omit [Fintype Vertex] [DecidableEq Vertex] in
theorem exists_smaller_support_of_mem_convexHull_of_not_affineIndependent_image
    (pfun : Vertex → RealPoint dimension)
    {x : RealPoint dimension} {s : Finset Vertex}
    (hx : x ∈ convexHull ℝ (pfun '' (s : Set Vertex)))
    (hdep :
      ¬ AffineIndependent ℝ
        (fun y : ((s.image pfun : Finset (RealPoint dimension)) : Set (RealPoint dimension)) =>
          (y : RealPoint dimension))) :
    ∃ s' : Finset Vertex,
      s' ⊆ s ∧
      s'.card + 1 ≤ s.card ∧
      x ∈ convexHull ℝ (pfun '' (s' : Set Vertex)) := by
  classical
  have hx_img :
      x ∈ convexHull ℝ (((s.image pfun : Finset (RealPoint dimension)) : Set (RealPoint dimension))) := by
    simpa using hx
  let t : Finset (RealPoint dimension) := Caratheodory.minCardFinsetOfMemConvexHull hx_img
  have ht_subset_set :
      (t : Set (RealPoint dimension)) ⊆ ((s.image pfun : Finset (RealPoint dimension)) : Set (RealPoint dimension)) :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx_img
  have ht_mem :
      x ∈ convexHull ℝ ((t : Finset (RealPoint dimension)) : Set (RealPoint dimension)) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx_img
  have ht_indep :
      AffineIndependent ℝ (fun y : ((t : Finset (RealPoint dimension)) : Set (RealPoint dimension)) =>
        (y : RealPoint dimension)) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx_img
  have ht_subset : t ⊆ s.image pfun := by
    intro y hy
    exact ht_subset_set hy
  have ht_card_lt_img : t.card < (s.image pfun).card := by
    by_contra hnot
    have himg_le : (s.image pfun).card ≤ t.card := Nat.le_of_not_gt hnot
    have hEq : t = s.image pfun := Finset.eq_of_subset_of_card_le ht_subset himg_le
    rw [← hEq] at hdep
    exact hdep ht_indep
  have ht_card_lt_s : t.card < s.card := lt_of_lt_of_le ht_card_lt_img Finset.card_image_le
  let chooseVertex : {y // y ∈ t} → Vertex := fun y =>
    Classical.choose (Finset.mem_image.mp (ht_subset_set y.2))
  have hchoose_mem : ∀ y : {y // y ∈ t}, chooseVertex y ∈ s := by
    intro y
    exact (Classical.choose_spec (Finset.mem_image.mp (ht_subset_set y.2))).1
  have hchoose_image : ∀ y : {y // y ∈ t}, pfun (chooseVertex y) = y.1 := by
    intro y
    exact (Classical.choose_spec (Finset.mem_image.mp (ht_subset_set y.2))).2
  have hchoose_injective : Function.Injective chooseVertex := by
    intro y z hEq
    apply Subtype.ext
    simpa [hchoose_image y, hchoose_image z] using congrArg pfun hEq
  let s' : Finset Vertex := t.attach.image chooseVertex
  have hs'_subset : s' ⊆ s := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨y, hy, rfl⟩
    exact hchoose_mem y
  have hs'_card : s'.card = t.card := by
    simpa [s'] using
      Finset.card_image_of_injective (s := t.attach) (f := chooseVertex) hchoose_injective
  have hs'_image : s'.image pfun = t := by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hu with ⟨z, hz, hEq⟩
      have huEq : pfun u = z.1 := by simpa [hEq] using hchoose_image z
      simpa [huEq] using z.2
    · intro hy
      refine Finset.mem_image.mpr ?_
      refine ⟨chooseVertex ⟨y, hy⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨y, hy⟩, by simp, rfl⟩
      · simpa [hchoose_image ⟨y, hy⟩]
  have hs'_image_set : pfun '' (s' : Set Vertex) = ((t : Finset (RealPoint dimension)) : Set (RealPoint dimension)) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : pfun u ∈ s'.image pfun := Finset.mem_image_of_mem _ hu
      simpa [hs'_image] using hu'
    · intro hy
      have hy' : y ∈ s'.image pfun := by simpa [hs'_image] using hy
      simpa using hy'
  refine ⟨s', hs'_subset, Nat.succ_le_of_lt (by simpa [hs'_card] using ht_card_lt_s), ?_⟩
  simpa [hs'_image_set] using ht_mem

theorem not_exists_smaller_support_of_pair_of_mem_openSegment
    (pfun : Vertex → RealPoint dimension)
    {u v : Vertex} (huv : pfun u ≠ pfun v)
    {x : RealPoint dimension}
    (hx : x ∈ openSegment ℝ (pfun u) (pfun v)) :
    ¬ ∃ s' : Finset Vertex,
      s' ⊆ ({u, v} : Finset Vertex) ∧
      s'.card + 1 ≤ ({u, v} : Finset Vertex).card ∧
      x ∈ convexHull ℝ (pfun '' (s' : Set Vertex)) := by
  classical
  have huv' : u ≠ v := by
    intro hEq
    exact huv (by simpa [hEq])
  have hpaircard : ({u, v} : Finset Vertex).card = 2 := by
    simp [Finset.card_pair, huv']
  have hxu : x ≠ pfun u := by
    intro hEq
    have hleft : pfun u ∈ openSegment ℝ (pfun u) (pfun v) := by
      simpa [hEq] using hx
    exact huv ((left_mem_openSegment_iff.mp hleft))
  have hxv : x ≠ pfun v := by
    intro hEq
    have hright : pfun v ∈ openSegment ℝ (pfun u) (pfun v) := by
      simpa [hEq] using hx
    exact huv (right_mem_openSegment_iff.mp hright)
  rintro ⟨s', hs', hcard, hxconv⟩
  have hs'le : s'.card ≤ 1 := by
    have : s'.card + 1 ≤ 2 := by simpa [hpaircard] using hcard
    omega
  by_cases hs'zero : s'.card = 0
  · have hs'empty : s' = ∅ := Finset.card_eq_zero.mp hs'zero
    have : x ∈ convexHull ℝ (pfun '' ((∅ : Finset Vertex) : Set Vertex)) := by
      simpa [hs'empty] using hxconv
    simpa using this
  · have hs'one : s'.card = 1 := by omega
    rcases Finset.card_eq_one.mp hs'one with ⟨w, hw⟩
    have hwpair : w = u ∨ w = v := by
      have hwmem : w ∈ ({u, v} : Finset Vertex) := by
        apply hs'
        simpa [hw]
      simpa using hwmem
    have hxw : x = pfun w := by
      have : x ∈ convexHull ℝ (pfun '' ({w} : Set Vertex)) := by
        simpa [hw] using hxconv
      simpa [convexHull_singleton] using this
    rcases hwpair with rfl | rfl
    · exact hxu hxw
    · exact hxv hxw

structure ChosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec where
  exists_subset_in_codimOneSubface_of_point_of_positiveLevel_topDim_of_faceSubdividesLowerPrefix :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
      (x : RentDivision (dimension + 1)),
      0 < ν.level.1 →
      ν.face.dim = dimension →
      ν.face.SubdividesPrefixFace (T := T) ν.level.castSucc →
      {ρ₁ : SubdivisionFace.CarrierCodimOneSubface ν.face} →
      ρ₁.toSubdivisionFace.ImageContains (T := T) φ.vertexMap x →
      ∃ s : Finset Vertex,
        s ⊆ ρ₁.carrier ∧
        s.card ≤ ν.level.castSucc.1 ∧
        ((x : RealPoint dimension) ∈
          convexHull ℝ
            ((fun v : Vertex =>
                ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
              (s : Set Vertex)))

structure ChosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec where
  exists_smaller_support_in_codimOneSubface_of_point_of_positiveLevel_topDim_of_faceSubdividesLowerPrefix :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
      (x : RentDivision (dimension + 1)),
      0 < ν.level.1 →
      ν.face.dim = dimension →
      ν.face.SubdividesPrefixFace (T := T) ν.level.castSucc →
      {ρ₁ : SubdivisionFace.CarrierCodimOneSubface ν.face} →
      {s : Finset Vertex} →
      s ⊆ ρ₁.carrier →
      ((x : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (s : Set Vertex))) →
      ∃ s' : Finset Vertex,
        s' ⊆ s ∧
        s'.card + 1 ≤ s.card ∧
        ((x : RealPoint dimension) ∈
          convexHull ℝ
          ((fun v : Vertex =>
                ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
              (s' : Set Vertex)))

def chosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec_of_affineDependentImage
    (hdep :
      ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
        (x : RentDivision (dimension + 1)),
        0 < ν.level.1 →
        ν.face.dim = dimension →
        ν.face.SubdividesPrefixFace (T := T) ν.level.castSucc →
        {ρ₁ : SubdivisionFace.CarrierCodimOneSubface ν.face} →
        {s : Finset Vertex} →
        s ⊆ ρ₁.carrier →
        ((x : RealPoint dimension) ∈
          convexHull ℝ
            ((fun v : Vertex =>
                ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
              (s : Set Vertex))) →
        ¬ AffineIndependent ℝ
          (fun y : (((s.image fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) :
                Finset (RealPoint dimension)) : Set (RealPoint dimension)) =>
            (y : RealPoint dimension))) :
    ChosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν x hk hνdim hνsub ρ₁ s hs hx
  exact exists_smaller_support_of_mem_convexHull_of_not_affineIndependent_image
    (pfun := fun v : Vertex =>
      ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension))
    hx
    (hdep ν x hk hνdim hνsub hs hx)

def chosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec_of_oneVertexDrop
    (hdrop :
      ChosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν x hk hνdim hνsub ρ₁ hρ₁x
  have hρ₁carrier :
      ((x : RealPoint dimension) ∈
        convexHull ℝ
          ((fun v : Vertex =>
              ((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension)) ''
            (ρ₁.carrier : Set Vertex))) := by
    simpa [SubdivisionFace.ImageContains, SubdivisionFace.imagePoints,
      SubdivisionFace.CarrierCodimOneSubface.toSubdivisionFace_carrier] using hρ₁x
  rcases hdrop with ⟨hdrop⟩
  rcases hdrop ν x hk hνdim hνsub (by intro v hv; exact hv) hρ₁carrier with
    ⟨s, hs, hcard, himg⟩
  have hρ₁card : ρ₁.carrier.card = ν.level.succ.1 := by
    have hcard' : ρ₁.carrier.card + 1 = ν.level.succ.1 + 1 := by
      calc
        ρ₁.carrier.card + 1 = ν.face.carrier.card := ρ₁.card
        _ = ν.face.dim + 1 := ν.face.card_eq_dim_succ
        _ = (ν.level.1 + 1) + 1 := by rw [ν.face_dim]
        _ = ν.level.succ.1 + 1 := by simp
    exact Nat.add_right_cancel hcard'
  refine ⟨s, hs, ?_, himg⟩
  have hsle : s.card + 1 ≤ ν.level.castSucc.1 + 1 := by
    calc
      s.card + 1 ≤ ρ₁.carrier.card := hcard
      _ = ν.level.succ.1 := hρ₁card
      _ = ν.level.castSucc.1 + 1 := by simp
  exact Nat.succ_le_succ_iff.mp hsle

structure ChosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec where
  exists_second_codimOneSubface_of_point_of_positiveLevel_topDim_of_faceSubdividesLowerPrefix :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
      (x : RentDivision (dimension + 1)),
      0 < ν.level.1 →
      ν.face.dim = dimension →
      ν.face.SubdividesPrefixFace (T := T) ν.level.castSucc →
      {ρ₁ : SubdivisionFace.CarrierCodimOneSubface ν.face} →
      ρ₁.toSubdivisionFace.ImageContains (T := T) φ.vertexMap x →
      ∃ ρ₂ : SubdivisionFace T,
        ρ₂ ≠ ρ₁.toSubdivisionFace ∧
        ρ₂.IsCodimOneSubface ν.face ∧
        ρ₂.ImageContains (T := T) φ.vertexMap x

def chosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec_of_supportShrink
    (hshrink :
      ChosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν x hk hνdim hνsub ρ₁ hρ₁x
  rcases hshrink with ⟨hshrink⟩
  rcases hshrink ν x hk hνdim hνsub hρ₁x with
    ⟨s, hs, hcard, himg⟩
  have hρ₁card : ρ₁.carrier.card = ν.level.succ.1 := by
    have hcard' : ρ₁.carrier.card + 1 = ν.level.succ.1 + 1 := by
      calc
        ρ₁.carrier.card + 1 = ν.face.carrier.card := ρ₁.card
        _ = ν.face.dim + 1 := ν.face.card_eq_dim_succ
        _ = (ν.level.1 + 1) + 1 := by rw [ν.face_dim]
        _ = ν.level.succ.1 + 1 := by simp
    exact Nat.add_right_cancel hcard'
  have hsCard' : s.card + 1 ≤ ρ₁.carrier.card := by
    calc
      s.card + 1 ≤ ν.level.castSucc.1 + 1 := Nat.succ_le_succ hcard
      _ = ν.level.succ.1 := by simp
      _ = ρ₁.carrier.card := hρ₁card.symm
  exact exists_second_codimOneSubface_imageContains_of_subset_in_codimOneSubface
    (T := T) (hs := hs) hsCard' himg

structure ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec where
  exists_second_codimOneSubface_of_missing_nextMilestone_positiveLevel_topDim_contains_lowerMilestone_of_faceSubdividesLowerPrefix :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ),
      0 < ν.level.1 →
      ν.face.dim = dimension →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.SubdividesPrefixFace (T := T) ν.level.castSucc →
      {ρ₁ : SubdivisionFace.CarrierCodimOneSubface ν.face} →
      ρ₁.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ ρ₂ : SubdivisionFace T,
        ρ₂ ≠ ρ₁.toSubdivisionFace ∧
        ρ₂.IsCodimOneSubface ν.face ∧
        ρ₂.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc

def chosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec_of_boundaryPointMultiplicity
    (hboundary :
      ChosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hνdim _hupper hνsub ρ₁ hρ₁mil
  simpa [SubdivisionFace.ImageContainsMilestone] using
    hboundary.exists_second_codimOneSubface_of_point_of_positiveLevel_topDim_of_faceSubdividesLowerPrefix
      ν ((chosenMilestoneChain (φ := φ)).point ν.level.castSucc) hk hνdim hνsub
      (ρ₁ := ρ₁) hρ₁mil

theorem exists_second_codimOneSubface_of_faceSubdividesLowerPrefix
    (himage :
      ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec
        (T := T) (φ := φ))
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    (hνdim : ν.face.dim = dimension)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hνsub : ν.face.SubdividesPrefixFace (T := T) ν.level.castSucc)
    {ρ₁ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (hρ₁mil :
      ρ₁.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc) :
    ∃ ρ₂ : SubdivisionFace T,
      ρ₂ ≠ ρ₁.toSubdivisionFace ∧
      ρ₂.IsCodimOneSubface ν.face ∧
      ρ₂.SubdividesPrefixFace (T := T) ν.level.castSucc ∧
      ρ₂.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc := by
  rcases himage with ⟨himage⟩
  rcases himage ν hk hνdim hupper hνsub hρ₁mil with
    ⟨ρ₂, hρ₂ne, hρ₂, hρ₂mil⟩
  refine ⟨ρ₂, hρ₂ne, hρ₂, ?_, hρ₂mil⟩
  exact SubdivisionFace.subdividesPrefixFace_of_subface (T := T) hρ₂.1 hνsub

def chosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec_of_reflection_and_secondCarrier
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hsecond :
      ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hνdim hupper hlower
  rcases exists_lowerMilestoneCarrier_of_reflection
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hreflect hk hlower with
    ⟨ρ₁, hρ₁sub, hρ₁mil⟩
  rcases hsecond.exists_second_codimOneSubface_of_missing_nextMilestone_positiveLevel_topDim_contains_lowerMilestone
      ν hk hνdim hupper (ρ₁ := ρ₁) hρ₁sub hρ₁mil with
    ⟨ρ₂, hρ₂ne, hρ₂, hρ₂sub, hρ₂mil⟩
  exact ⟨ρ₁.toSubdivisionFace, ρ₂, by simpa using hρ₂ne.symm, ρ₁.isCodimOneSubface,
    hρ₂, hρ₁sub, hρ₂sub, hρ₁mil, hρ₂mil⟩

theorem faceSubdividesLowerPrefix_of_reflection_and_topDimLowerMilestoneSecondCarrier
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hsecond :
      ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierSpec
        (T := T) (φ := φ))
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    (hνdim : ν.face.dim = dimension)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hlower :
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc) :
    ν.face.SubdividesPrefixFace (T := T) ν.level.castSucc := by
  rcases exists_lowerMilestoneCarrier_of_reflection
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hreflect hk hlower with
    ⟨ρ₁, hρ₁sub, hρ₁mil⟩
  rcases hsecond.exists_second_codimOneSubface_of_missing_nextMilestone_positiveLevel_topDim_contains_lowerMilestone
      ν hk hνdim hupper (ρ₁ := ρ₁) hρ₁sub hρ₁mil with
    ⟨ρ₂, hρ₂ne, hρ₂, hρ₂sub, _hρ₂mil⟩
  exact SubdivisionFace.subdividesPrefixFace_of_two_distinct_codimOneSubfaces
    (T := T) ρ₁.isCodimOneSubface hρ₂ (by simpa using hρ₂ne.symm) hρ₁sub hρ₂sub

/--
Below-top-dimensional lower-milestone door theorem for the positive-level missing-next branch.

This is the branch where the fresh-prefix-vertex continuation route still makes sense.
-/
structure ChosenMilestoneChainPositiveLevelBelowTopDimLowerMilestoneDoorSpec where
  two_doors_of_missing_nextMilestone_positiveLevel_belowTopDim_contains_lowerMilestone :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ν.face.dim < dimension →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

def chosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec_of_topDim_and_belowTopDim
    (htop : ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneDoorSpec
      (T := T) (φ := φ))
    (hbelow : ChosenMilestoneChainPositiveLevelBelowTopDimLowerMilestoneDoorSpec
      (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hupper hlower
  by_cases htopdim : ν.face.dim = dimension
  · exact htop.two_doors_of_missing_nextMilestone_positiveLevel_topDim_contains_lowerMilestone
      ν hk htopdim hupper hlower
  · have hbelowdim : ν.face.dim < dimension :=
      lt_of_le_of_ne ν.face.dim_le (fun h => htopdim h)
    exact hbelow.two_doors_of_missing_nextMilestone_positiveLevel_belowTopDim_contains_lowerMilestone
      ν hk hbelowdim hupper hlower

theorem exists_two_distinct_verticalNeighbors_of_two_distinct_codimOneSubfaces_contains_lowerMilestone
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    {ρ₁ ρ₂ : SubdivisionFace T}
    (hρ₁ : ρ₁.IsCodimOneSubface ν.face)
    (hρ₂ : ρ₂.IsCodimOneSubface ν.face)
    (hρ₁sub : ρ₁.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρ₂sub : ρ₂.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρ₁mil :
      ρ₁.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc)
    (hρ₂mil :
      ρ₂.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc)
    (hρne : ρ₁ ≠ ρ₂) :
    ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      a ≠ b ∧
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b := by
  let μ₁ :=
    verticalNeighborOfCodimOneSubfaceContainsLowerMilestone
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hk hρ₁ hρ₁sub hρ₁mil
  let μ₂ :=
    verticalNeighborOfCodimOneSubfaceContainsLowerMilestone
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hk hρ₂ hρ₂sub hρ₂mil
  have hμ₁ :
      μ₁.VerticalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ ν :=
    verticalNeighborOfCodimOneSubfaceContainsLowerMilestone_verticalAdj
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hk hρ₁ hρ₁sub hρ₁mil
  have hμ₂ :
      μ₂.VerticalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ ν :=
    verticalNeighborOfCodimOneSubfaceContainsLowerMilestone_verticalAdj
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hk hρ₂ hρ₂sub hρ₂mil
  have hμne : μ₁ ≠ μ₂ := by
    intro hEq
    apply hρne
    simpa [μ₁, μ₂, verticalNeighborOfCodimOneSubfaceContainsLowerMilestone] using
      congrArg Section5PositiveNode.face hEq
  refine ⟨.positive μ₁, .positive μ₂, ?_, ?_, ?_⟩
  · intro hEq
    injection hEq with hEq'
    exact hμne hEq'
  · exact Or.inr (Or.inr hμ₁)
  · exact Or.inr (Or.inr hμ₂)

theorem exists_two_distinct_verticalNeighbors_of_topDimLowerMilestoneCarrierMultiplicity
    (hmult : ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec
      (T := T) (φ := φ))
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    (hνdim : ν.face.dim = dimension)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hlower :
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc) :
    ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      a ≠ b ∧
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b := by
  rcases hmult.exists_two_distinct_codimOneSubfaces_of_missing_nextMilestone_positiveLevel_topDim_contains_lowerMilestone
      ν hk hνdim hupper hlower with
    ⟨ρ₁, ρ₂, hρne, hρ₁, hρ₂, hρ₁sub, hρ₂sub, hρ₁mil, hρ₂mil⟩
  exact exists_two_distinct_verticalNeighbors_of_two_distinct_codimOneSubfaces_contains_lowerMilestone
    (T := T) (φ := φ) hk hρ₁ hρ₂ hρ₁sub hρ₂sub hρ₁mil hρ₂mil hρne

theorem exists_two_distinct_verticalNeighbors_of_reflection_and_topDimLowerMilestoneSecondCarrier
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hsecond :
      ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierSpec
        (T := T) (φ := φ))
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    (hνdim : ν.face.dim = dimension)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hlower :
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc) :
    ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      a ≠ b ∧
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b := by
  exact exists_two_distinct_verticalNeighbors_of_topDimLowerMilestoneCarrierMultiplicity
    (T := T) (φ := φ)
    (chosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec_of_reflection_and_secondCarrier
      (T := T) (φ := φ) hreflect hsecond)
    hk hνdim hupper hlower

/--
The positive-level missing-next branch after removing the already-isolated open-crossing case.

This packages the exact complement of `ChosenMilestoneChainOpenCrossingSpec` at positive levels:
once the next milestone is absent and there is no open crossing of the milestone segment, the
remaining two-door conclusion is the only missing local theorem.
-/
structure ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec where
  two_doors_of_missing_nextMilestone_positiveLevel_of_not_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

def chosenMilestoneChainPositiveLevelNoOpenCrossingSpec_of_lowerMilestoneDoorSpec
    (hdoor : ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec
      (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hupper hclosed
  exact hdoor.two_doors_of_missing_nextMilestone_positiveLevel_contains_lowerMilestone
    ν hk hupper
    (chosenMilestoneChain_contains_lowerMilestone_of_missingNextMilestone_of_not_openCrossing
      (T := T) (φ := φ) (ν := ν) hupper hclosed)

/--
Top-dimensional no-open-crossing door theorem at positive levels.

This is the exact branch of the paper's local door count that remains after separating the open
crossing case. It is strictly weaker than the older lower-milestone door theorem: the lower
milestone conclusion is recovered automatically from `hupper` and `hclosed`.
-/
structure ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec where
  two_doors_of_missing_nextMilestone_positiveLevel_topDim_of_not_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ν.face.dim = dimension →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

/--
Below-top-dimensional no-open-crossing door theorem at positive levels.

This is the genuinely lower-dimensional continuation branch, separated from the top-dimensional
endpoint case described in paper lines 395--396.
-/
structure ChosenMilestoneChainPositiveLevelBelowTopDimNoOpenCrossingDoorSpec where
  two_doors_of_missing_nextMilestone_positiveLevel_belowTopDim_of_not_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ν.face.dim < dimension →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

def chosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec_of_lowerMilestoneDoorSpec
    (hdoor :
      ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneDoorSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hνdim hupper hclosed
  exact hdoor.two_doors_of_missing_nextMilestone_positiveLevel_topDim_contains_lowerMilestone
    ν hk hνdim hupper
    (chosenMilestoneChain_contains_lowerMilestone_of_missingNextMilestone_of_not_openCrossing
      (T := T) (φ := φ) (ν := ν) hupper hclosed)

def chosenMilestoneChainPositiveLevelBelowTopDimNoOpenCrossingDoorSpec_of_lowerMilestoneDoorSpec
    (hdoor :
      ChosenMilestoneChainPositiveLevelBelowTopDimLowerMilestoneDoorSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelBelowTopDimNoOpenCrossingDoorSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hνdim hupper hclosed
  exact
    hdoor.two_doors_of_missing_nextMilestone_positiveLevel_belowTopDim_contains_lowerMilestone
      ν hk hνdim hupper
      (chosenMilestoneChain_contains_lowerMilestone_of_missingNextMilestone_of_not_openCrossing
        (T := T) (φ := φ) (ν := ν) hupper hclosed)

def chosenMilestoneChainPositiveLevelNoOpenCrossingSpec_of_topDim_and_belowTopDim
    (htop :
      ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec
        (T := T) (φ := φ))
    (hbelow :
      ChosenMilestoneChainPositiveLevelBelowTopDimNoOpenCrossingDoorSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hupper hclosed
  by_cases htopdim : ν.face.dim = dimension
  · exact
      htop.two_doors_of_missing_nextMilestone_positiveLevel_topDim_of_not_openCrossing
        ν hk htopdim hupper hclosed
  · have hbelowdim : ν.face.dim < dimension :=
      lt_of_le_of_ne ν.face.dim_le (fun h => htopdim h)
    exact
      hbelow.two_doors_of_missing_nextMilestone_positiveLevel_belowTopDim_of_not_openCrossing
        ν hk hbelowdim hupper hclosed

/--
Carrier-level continuation contract for the no-open-crossing positive-level branch.

This records the codimension-`1` carrier face carrying the lower milestone and asks for a unique
same-level continuation across that normalized carrier object.
-/
structure ChosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec where
  unique_sameLevelContinuation_of_not_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ ρ : SubdivisionFace.CarrierCodimOneSubface ν.face,
        ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc ∧
        ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc ∧
        ∃! μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
          μ ≠ ν ∧ μ.level = ν.level ∧ ρ.carrier ⊆ μ.face.carrier

/--
Graph-relevant same-level continuations of a normalized codimension-`1` carrier face.

These are the only cofaces that could contribute a second door in the no-open-crossing
positive-level branch: same level as `ν`, distinct from `ν`, and containing the normalized
carrier face.
-/
def IsSameLevelCarrierContinuationCandidate
    (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
    (ρ : SubdivisionFace.CarrierCodimOneSubface ν.face)
    (μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ) : Prop :=
  μ ≠ ν ∧ μ.level = ν.level ∧ ρ.carrier ⊆ μ.face.carrier

/--
Sharper carrier-level continuation contract isolating exactly the graph-relevant same-level
cofaces in the no-open-crossing branch.
-/
structure ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec where
  exists_unique_candidate_of_not_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ ρ : SubdivisionFace.CarrierCodimOneSubface ν.face,
        ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc ∧
        ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc ∧
        ∃! μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
          IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ

/--
Existence half of the filtered same-level continuation theorem.

This isolates the first genuinely missing step in the no-open-crossing branch: producing any
graph-relevant same-level continuation candidate once the normalized lower-milestone carrier has
been identified.
-/
structure ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec where
  exists_candidate_of_not_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ ρ : SubdivisionFace.CarrierCodimOneSubface ν.face,
        ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc ∧
        ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc ∧
        ∃ μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
          IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ

/--
Minimal same-level continuation existence once the normalized codimension-`1` carrier face is
already fixed.

After `PositiveFaceLowerPrefixReflection` has supplied the lower-milestone carrier, the genuinely
remaining existence theorem no longer depends on the no-open-crossing hypotheses themselves. This
is precisely the missing upward extension step dual to
`SubdivisionFace.subdividesPrefixFace_of_subface`: extend a codimension-`1` prefix-face carrier to
a distinct same-level prefix-face coface.
-/
structure ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec where
  exists_sameLevelPrefixFace_in_ambientFacet_of_carrier :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
      {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face} {σ : Finset Vertex},
      σ ∈ T.facets →
      ν.face.carrier ⊆ σ →
      ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc →
      ∃ μface : SubdivisionFace T,
        μface ≠ ν.face ∧
        μface.dim = ν.level.1 + 1 ∧
        μface.SubdividesPrefixFace (T := T) ν.level.succ ∧
        ρ.toSubdivisionFace.IsCodimOneSubface μface ∧
        μface.carrier ⊆ σ

theorem exists_sameLevelPrefixFace_in_ambientFacet_of_freshPrefixVertex
    (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face} {σ : Finset Vertex}
    (hσ : σ ∈ T.facets)
    (hνσ : ν.face.carrier ⊆ σ)
    (hρsub : ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc)
    {v : Vertex}
    (hvσ : v ∈ σ)
    (hvν : v ∉ ν.face.carrier)
    (hvprefix :
      (SubdivisionFace.singleton (T := T) v).SubdividesPrefixFace (T := T) ν.level.succ) :
    ∃ μface : SubdivisionFace T,
      μface ≠ ν.face ∧
      μface.dim = ν.level.1 + 1 ∧
      μface.SubdividesPrefixFace (T := T) ν.level.succ ∧
      ρ.toSubdivisionFace.IsCodimOneSubface μface ∧
      μface.carrier ⊆ σ := by
  have hvρ : v ∉ ρ.carrier := by
    intro hvρ
    exact hvν (ρ.subset hvρ)
  let σface : SubdivisionFace T := SubdivisionFace.ofFacet (T := T) σ hσ
  let μface : SubdivisionFace T :=
    σface.ofSubset (insert v ρ.carrier)
      (by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwρ
        · exact hvσ
        · exact hνσ (ρ.subset hwρ))
      (Finset.insert_nonempty v ρ.carrier)
  have hμne : μface ≠ ν.face := by
    intro hEq
    have hvμ : v ∈ μface.carrier := by
      change v ∈ insert v ρ.carrier
      exact Finset.mem_insert_self v ρ.carrier
    exact hvν (by simpa [hEq] using hvμ)
  have hμcard : μface.carrier.card = ν.level.1 + 2 := by
    change (insert v ρ.carrier).card = ν.level.1 + 2
    rw [Finset.card_insert_of_notMem hvρ]
    calc
      ρ.carrier.card + 1 = ν.face.carrier.card := ρ.card
      _ = ν.level.1 + 2 := by
        rw [ν.face.card_eq_dim_succ, ν.face_dim]
  have hμdim : μface.dim = ν.level.1 + 1 := by
    have hμdim' : μface.dim + 1 = ν.level.1 + 2 := by
      calc
        μface.dim + 1 = μface.carrier.card := by symm; exact μface.card_eq_dim_succ
        _ = ν.level.1 + 2 := hμcard
    omega
  have hρsub' :
      ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.succ :=
    SubdivisionFace.subdividesPrefixFace_succ_of_castSucc (T := T) hρsub
  have hμsub : μface.SubdividesPrefixFace (T := T) ν.level.succ := by
    intro w hw i hi
    rcases Finset.mem_insert.mp hw with hwv | hwρ
    · have hwsingle : w ∈ (SubdivisionFace.singleton (T := T) v).carrier := by
        simpa [SubdivisionFace.singleton_carrier, hwv]
      exact hvprefix w hwsingle i hi
    · exact hρsub' w hwρ i hi
  have hρμ : ρ.toSubdivisionFace.IsCodimOneSubface μface := by
    constructor
    · intro w hw
      have hwρ : w ∈ ρ.carrier := by
        simpa [SubdivisionFace.CarrierCodimOneSubface.toSubdivisionFace_carrier] using hw
      change w ∈ insert v ρ.carrier
      exact Finset.mem_insert_of_mem hwρ
    · change ρ.carrier.card + 1 = (insert v ρ.carrier).card
      rw [Finset.card_insert_of_notMem hvρ]
  have hμσ : μface.carrier ⊆ σ := by
    intro w hw
    rcases Finset.mem_insert.mp hw with hwv | hwρ
    · exact hwv ▸ hvσ
    · exact hνσ (ρ.subset hwρ)
  exact ⟨μface, hμne, hμdim, hμsub, hρμ, hμσ⟩

theorem chosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec_of_freshPrefixVertex
    (hvertex :
      ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
        {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face} {σ : Finset Vertex},
        σ ∈ T.facets →
        ν.face.carrier ⊆ σ →
        ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc →
        ∃ v ∈ σ, v ∉ ν.face.carrier ∧
          (SubdivisionFace.singleton (T := T) v).SubdividesPrefixFace (T := T) ν.level.succ) :
    ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν ρ σ hσ hνσ hρsub
  rcases hvertex ν hσ hνσ hρsub with ⟨v, hvσ, hvν, hvprefix⟩
  exact exists_sameLevelPrefixFace_in_ambientFacet_of_freshPrefixVertex
    (T := T) (φ := φ) ν hσ hνσ hρsub hvσ hvν hvprefix

lemma ambientFacet_eq_of_topDim
    (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
    {σ : Finset Vertex}
    (hσ : σ ∈ T.facets)
    (hνσ : ν.face.carrier ⊆ σ)
    (hνdim : ν.face.dim = dimension) :
    ν.face.carrier = σ := by
  apply Finset.eq_of_subset_of_card_le hνσ
  have hνcard : ν.face.carrier.card = dimension + 1 := by
    rw [ν.face.card_eq_dim_succ, hνdim]
  rw [T.facet_card σ hσ, hνcard]

lemma no_freshAmbientFacetVertex_of_topDim
    (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
    {σ : Finset Vertex}
    (hσ : σ ∈ T.facets)
    (hνσ : ν.face.carrier ⊆ σ)
    (hνdim : ν.face.dim = dimension) :
    ¬ ∃ v ∈ σ, v ∉ ν.face.carrier := by
  intro hfresh
  rcases hfresh with ⟨v, hvσ, hvν⟩
  have hEq := ambientFacet_eq_of_topDim (T := T) (φ := φ) ν hσ hνσ hνdim
  exact hvν (by simpa [hEq] using hvσ)

lemma exists_freshAmbientFacetVertex_of_lt_topDim
    (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
    {σ : Finset Vertex}
    (hσ : σ ∈ T.facets)
    (_hνσ : ν.face.carrier ⊆ σ)
    (hνdim : ν.face.dim < dimension) :
    ∃ v ∈ σ, v ∉ ν.face.carrier := by
  have hcard_lt : ν.face.carrier.card < σ.card := by
    calc
      ν.face.carrier.card = ν.face.dim + 1 := ν.face.card_eq_dim_succ
      _ < dimension + 1 := by omega
      _ = σ.card := by rw [T.facet_card σ hσ]
  by_contra hfresh
  push_neg at hfresh
  have hσν : σ ⊆ ν.face.carrier := hfresh
  have hcard_ge : σ.card ≤ ν.face.carrier.card := Finset.card_le_card hσν
  exact Nat.not_lt_of_ge hcard_ge hcard_lt

lemma not_exists_sameLevelPrefixFace_in_ambientFacet_of_topDim
    (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face} {σ : Finset Vertex}
    (hσ : σ ∈ T.facets)
    (hνσ : ν.face.carrier ⊆ σ)
    (hνdim : ν.face.dim = dimension) :
    ¬ ∃ μface : SubdivisionFace T,
      μface ≠ ν.face ∧
      μface.dim = ν.level.1 + 1 ∧
      μface.SubdividesPrefixFace (T := T) ν.level.succ ∧
      ρ.toSubdivisionFace.IsCodimOneSubface μface ∧
      μface.carrier ⊆ σ := by
  intro hμ
  rcases hμ with ⟨μface, hμne, hμdim, -, -, hμσ⟩
  have hμtop : μface.dim = dimension := by
    calc
      μface.dim = ν.level.1 + 1 := hμdim
      _ = ν.face.dim := by rw [ν.face_dim]
      _ = dimension := hνdim
  have hμeqσ : μface.carrier = σ := by
    apply Finset.eq_of_subset_of_card_le hμσ
    have hμcard : μface.carrier.card = dimension + 1 := by
      rw [μface.card_eq_dim_succ, hμtop]
    rw [T.facet_card σ hσ, hμcard]
  have hνeqσ := ambientFacet_eq_of_topDim (T := T) (φ := φ) ν hσ hνσ hνdim
  exact hμne (SubdivisionFace.ext (hμeqσ.trans hνeqσ.symm))

structure ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec where
  exists_sameLevelCoface_in_ambientFacet_of_carrier :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
      {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face} {σ : Finset Vertex},
      σ ∈ T.facets →
      ν.face.carrier ⊆ σ →
      ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc →
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
        μ ≠ ν ∧
        μ.level = ν.level ∧
        ρ.toSubdivisionFace.IsCodimOneSubface μ.face ∧
        μ.face.carrier ⊆ σ

def chosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec_of_prefixExtension
    (hext :
      ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν ρ σ hσ hνσ hρsub hρmil
  rcases hext.exists_sameLevelPrefixFace_in_ambientFacet_of_carrier ν hσ hνσ hρsub with
    ⟨μface, hμne, hμdim, hμsub, hρμ, hμσ⟩
  have hμmil :
      μface.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc := by
    exact SubdivisionFace.imageContainsMilestone_mono (T := T) hρμ.1 hρmil
  have hμseg :
      μface.ImageMeetsMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level := by
    refine ⟨chosenMilestoneChain (φ := φ).point ν.level.castSucc, ?_, ?_⟩
    · exact left_mem_segment ℝ
        (((chosenMilestoneChain (φ := φ)).point ν.level.castSucc :
            RentDivision (dimension + 1)) : RealPoint dimension)
        (((chosenMilestoneChain (φ := φ)).point ν.level.succ :
            RentDivision (dimension + 1)) : RealPoint dimension)
    · simpa [SubdivisionFace.ImageContainsMilestone] using hμmil
  let μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ := {
    level := ν.level
    face := μface
    face_dim := hμdim
    subdivides := hμsub
    meets_segment := hμseg
  }
  refine ⟨μ, ?_, rfl, ?_, ?_⟩
  · intro hμeq
    exact hμne (congrArg Section5PositiveNode.face hμeq)
  · simpa [μ] using hρμ
  · simpa [μ] using hμσ

/--
This packages the paper's facet-local segment-exit picture inside one ambient simplex.
-/
structure ChosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec where
  exists_sameLevelCoface_of_carrier :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
      {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face},
      ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc →
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
        μ ≠ ν ∧
        μ.level = ν.level ∧
        ρ.toSubdivisionFace.IsCodimOneSubface μ.face

/--
Ambient-facet exit implies the older fixed-carrier same-level coface-extension theorem.
-/
def chosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec_of_ambientFacetExit
    (hexit :
      ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν ρ hρsub hρmil
  rcases ν.face.subset_facet with ⟨σ, hσ, hνσ⟩
  rcases hexit.exists_sameLevelCoface_in_ambientFacet_of_carrier ν hσ hνσ hρsub hρmil with
    ⟨μ, hne, hlevel, hρμ, -⟩
  exact ⟨μ, hne, hlevel, hρμ⟩

def chosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec_of_prefixExtension
    (hext :
      ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec_of_ambientFacetExit
    (T := T) (φ := φ)
    (chosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec_of_prefixExtension
      (T := T) (φ := φ) hext)

/--
Candidate-level version of the fixed-carrier coface-extension theorem.
-/
structure ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec where
  exists_candidate_of_carrier :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
      {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face},
      ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc →
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
        IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ

def chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_cofaceExtension
    (hext :
      ChosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν ρ hρsub hρmil
  rcases hext.exists_sameLevelCoface_of_carrier ν hρsub hρmil with ⟨μ, hne, hlevel, hρμ⟩
  exact ⟨μ, hne, hlevel, hρμ.1⟩

def chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_ambientFacetExit
    (hexit :
      ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_cofaceExtension
    (T := T) (φ := φ)
    (chosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec_of_ambientFacetExit
      (T := T) (φ := φ) hexit)

def chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_prefixExtension
    (hext :
      ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_ambientFacetExit
    (T := T) (φ := φ)
    (chosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec_of_prefixExtension
      (T := T) (φ := φ) hext)

/--
Uniqueness half of the filtered same-level continuation theorem.

Once an admissible normalized lower-milestone carrier and one same-level candidate are available,
this asks only that any other graph-relevant same-level candidate coincide with it.
-/
structure ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec where
  candidate_unique_of_not_openCrossing :
    ∀ (ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ)
      {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face},
      ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc →
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∀ {μ₁ μ₂ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ},
        IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ₁ →
        IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ₂ →
        μ₁ = μ₂

theorem exists_lowerMilestoneCarrier_of_not_openCrossing_of_reflection
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hclosed :
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level) :
    ∃ ρ : SubdivisionFace.CarrierCodimOneSubface ν.face,
      ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc ∧
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc := by
  rcases chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone
      (T := T) (φ := φ) (ν := ν) hupper with hopen | hlower
  · exact False.elim (hclosed hopen)
  · rcases exists_verticalAdj_of_contains_lowerMilestone_of_reflection
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hreflect hk hlower with ⟨μ, hμ⟩
    rcases hμ with ⟨hlevel, hμν, hμmil⟩
    let ρ : SubdivisionFace.CarrierCodimOneSubface ν.face :=
      SubdivisionFace.CarrierCodimOneSubface.ofIsCodimOneSubface hμν
    have hsucc : μ.level.succ = ν.level.castSucc := by
      apply Fin.ext
      exact hlevel
    refine ⟨ρ, ?_, ?_⟩
    · intro v hv i hi
      exact μ.subdivides v
        (by
          simpa [ρ, SubdivisionFace.CarrierCodimOneSubface.ofIsCodimOneSubface_carrier] using hv)
        i (by simpa [hsucc] using hi)
    · simpa [SubdivisionFace.ImageContainsMilestone, hsucc, ρ,
        SubdivisionFace.CarrierCodimOneSubface.ofIsCodimOneSubface_carrier] using hμmil

def chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierContinuation
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hexists :
      ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hupper hclosed
  rcases exists_lowerMilestoneCarrier_of_not_openCrossing_of_reflection
      (T := T) (φ := φ) hreflect hk hupper hclosed with ⟨ρ, hρsub, hρmil⟩
  rcases hexists.exists_candidate_of_carrier ν hρsub hρmil with ⟨μ, hμ⟩
  exact ⟨ρ, hρsub, hρmil, μ, hμ⟩

def chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierCofaceExtension
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hext :
      ChosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierContinuation
    (T := T) (φ := φ) hreflect
    (chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_cofaceExtension
      (T := T) (φ := φ) hext)

def chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierAmbientFacetExit
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hexit :
      ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierContinuation
    (T := T) (φ := φ) hreflect
    (chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_ambientFacetExit
      (T := T) (φ := φ) hexit)

def chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierPrefixExtension
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hext :
      ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierContinuation
    (T := T) (φ := φ) hreflect
    (chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_prefixExtension
      (T := T) (φ := φ) hext)

def
    chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_existence_and_uniqueness
    (hexists :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec
        (T := T) (φ := φ))
    (huniq :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hupper hclosed
  rcases hexists.exists_candidate_of_not_openCrossing ν hk hupper hclosed with
    ⟨ρ, hρsub, hρmil, μ, hμ⟩
  refine ⟨ρ, hρsub, hρmil, ⟨μ, hμ, ?_⟩⟩
  intro μ' hμ'
  exact (huniq.candidate_unique_of_not_openCrossing ν hρsub hρmil
    (μ₁ := μ) (μ₂ := μ') hμ hμ').symm

def
    chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_reflection_and_fixedCarrierContinuation_and_uniqueness
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hexists :
      ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec
        (T := T) (φ := φ))
    (huniq :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_existence_and_uniqueness
    (T := T) (φ := φ)
    (chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierContinuation
      (T := T) (φ := φ) hreflect hexists)
    huniq

def
    chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_reflection_and_fixedCarrierCofaceExtension_and_uniqueness
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hext :
      ChosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec
        (T := T) (φ := φ))
    (huniq :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_reflection_and_fixedCarrierContinuation_and_uniqueness
    (T := T) (φ := φ) hreflect
    (chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_cofaceExtension
      (T := T) (φ := φ) hext)
    huniq

def
    chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_reflection_and_fixedCarrierAmbientFacetExit_and_uniqueness
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hexit :
      ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec
        (T := T) (φ := φ))
    (huniq :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_reflection_and_fixedCarrierContinuation_and_uniqueness
    (T := T) (φ := φ) hreflect
    (chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_ambientFacetExit
      (T := T) (φ := φ) hexit)
    huniq

def
    chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_reflection_and_fixedCarrierPrefixExtension_and_uniqueness
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hext :
      ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec
        (T := T) (φ := φ))
    (huniq :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_reflection_and_fixedCarrierContinuation_and_uniqueness
    (T := T) (φ := φ) hreflect
    (chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_prefixExtension
      (T := T) (φ := φ) hext)
    huniq

lemma isCodimOneSubface_of_sameLevelCarrierContinuationCandidate
    {ν μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (hμ : IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ) :
    ρ.toSubdivisionFace.IsCodimOneSubface μ.face := by
  rcases hμ with ⟨_, hlevel, hsubset⟩
  constructor
  · simpa using hsubset
  · calc
      ρ.carrier.card + 1 = ν.face.carrier.card := ρ.card
      _ = ν.level.1 + 2 := by rw [ν.face.card_eq_dim_succ, ν.face_dim]
      _ = μ.level.1 + 2 := by simpa [hlevel]
      _ = μ.face.carrier.card := by rw [μ.face.card_eq_dim_succ, μ.face_dim]

lemma horizontalAdj_of_sameLevelCarrierContinuationCandidate
    {ν μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (hρmil :
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc)
    (hμ : IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ) :
    ν.HorizontalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ μ := by
  rcases hμ with ⟨hμne, hlevel, hsubset⟩
  have hμ' : IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ :=
    ⟨hμne, hlevel, hsubset⟩
  refine ⟨hlevel.symm, ?_, ρ.toSubdivisionFace, ρ.isCodimOneSubface, ?_, ?_⟩
  · intro hface
    apply hμne
    exact Section5PositiveNode.ext
      (c := chosenMilestoneChain (φ := φ)) (φ := φ) hlevel hface.symm
  · exact isCodimOneSubface_of_sameLevelCarrierContinuationCandidate
      (T := T) (φ := φ) hμ'
  · refine ⟨chosenMilestoneChain (φ := φ).point ν.level.castSucc, ?_, ?_⟩
    · exact left_mem_segment ℝ
        (((chosenMilestoneChain (φ := φ)).point ν.level.castSucc :
            RentDivision (dimension + 1)) : RealPoint dimension)
        (((chosenMilestoneChain (φ := φ)).point ν.level.succ :
            RentDivision (dimension + 1)) : RealPoint dimension)
    · simpa [SubdivisionFace.ImageContainsMilestone] using hρmil

lemma adj_of_sameLevelCarrierContinuationCandidate
    {ν μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (hρmil :
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc)
    (hμ : IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ) :
    Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) (.positive μ) :=
  Or.inl <| horizontalAdj_of_sameLevelCarrierContinuationCandidate
    (T := T) (φ := φ) hρmil hμ

lemma exists_candidate_of_horizontalAdj_of_not_openCrossing
    {ν μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hadj : ν.HorizontalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ μ)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hclosed :
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level) :
    ∃ ρ : SubdivisionFace.CarrierCodimOneSubface ν.face,
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc ∧
      IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ := by
  rcases hadj with ⟨hlevel, hne, τ, hτν, hτμ, hτseg⟩
  have hτupper :
      ¬ τ.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ := by
    intro hτupper
    exact hupper <|
      SubdivisionFace.imageContainsMilestone_mono (T := T) hτν.1 hτupper
  have hτlower :
      τ.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc := by
    by_contra hτlower
    exact hclosed <|
      SubdivisionFace.imageMeetsOpenMilestoneSegment_mono (T := T) hτν.1 <|
        SubdivisionFace.imageMeetsOpenMilestoneSegment_of_meets_of_not_containsMilestones
          (T := T) (τ := τ) hτseg hτlower hτupper
  refine ⟨SubdivisionFace.CarrierCodimOneSubface.ofIsCodimOneSubface hτν, ?_, ?_⟩
  · simpa [SubdivisionFace.ImageContainsMilestone] using hτlower
  · refine ⟨?_, hlevel.symm, ?_⟩
    · intro hμeq
      apply hne
      simpa [hμeq]
    · simpa [SubdivisionFace.CarrierCodimOneSubface.ofIsCodimOneSubface_carrier]
        using hτμ.1

lemma not_exists_sameLevelCarrierContinuationCandidate_of_uniqueFacetContainingCarrier
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hνdim : ν.face.dim = dimension)
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (huniq :
      ∀ σ ∈ T.facets, ρ.carrier ⊆ σ → σ = ν.face.carrier) :
    ¬ ∃ μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      IsSameLevelCarrierContinuationCandidate (T := T) (φ := φ) ν ρ μ := by
  intro hμ
  rcases hμ with ⟨μ, hμne, hlevel, hρμ⟩
  rcases μ.face.subset_facet with ⟨σ, hσ, hμσ⟩
  have hσeq : σ = ν.face.carrier := huniq σ hσ (hρμ.trans hμσ)
  have hμdim : μ.face.dim = dimension := by
    calc
      μ.face.dim = μ.level.1 + 1 := μ.face_dim
      _ = ν.level.1 + 1 := by simpa [hlevel]
      _ = ν.face.dim := by rw [ν.face_dim]
      _ = dimension := hνdim
  have hμface :
      μ.face.carrier = ν.face.carrier := by
    calc
      μ.face.carrier = σ :=
        ambientFacet_eq_of_topDim (T := T) (φ := φ) μ hσ hμσ hμdim
      _ = ν.face.carrier := hσeq
  exact hμne <|
    Section5PositiveNode.ext
      (c := chosenMilestoneChain (φ := φ)) (φ := φ) hlevel
      (SubdivisionFace.ext hμface)

lemma not_horizontalAdj_of_not_openCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
    {ν μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hνdim : ν.face.dim = dimension)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hclosed :
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level)
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (huniqueCarrier :
      ∀ {ρ' : SubdivisionFace.CarrierCodimOneSubface ν.face},
        ρ'.toSubdivisionFace.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
        ρ' = ρ)
    (huniqFacet :
      ∀ σ ∈ T.facets, ρ.carrier ⊆ σ → σ = ν.face.carrier) :
    ¬ ν.HorizontalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ μ := by
  intro hadj
  rcases exists_candidate_of_horizontalAdj_of_not_openCrossing
      (T := T) (φ := φ) hadj hupper hclosed with
    ⟨ρ', hρ'mil, hcand⟩
  have hρeq : ρ' = ρ := huniqueCarrier hρ'mil
  exact
    not_exists_sameLevelCarrierContinuationCandidate_of_uniqueFacetContainingCarrier
      (T := T) (φ := φ) hνdim huniqFacet <|
    by
      refine ⟨μ, ?_⟩
      simpa [hρeq] using hcand

lemma not_verticalAdj_of_topDim_as_lower
    {ν μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hνdim : ν.face.dim = dimension) :
    ¬ ν.VerticalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ μ := by
  intro h
  rcases h with ⟨hlevel, -, -⟩
  have hνlevel : ν.level.1 + 1 = dimension := by
    simpa [ν.face_dim] using hνdim
  omega

/--
Boundary-only unique lower-milestone carriers give an exact one-neighbor obstruction in the
top-dimensional no-open-crossing branch.

This is compatible with the paper's current local hypotheses unless an additional geometric input
rules it out: every adjacent node collapses to the single vertical neighbor determined by the
unique lower-milestone carrier.
-/
theorem eq_verticalNeighbor_of_adj_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    (hνdim : ν.face.dim = dimension)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hclosed :
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level)
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (hρsub : ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρmil :
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc)
    (huniqueCarrier :
      ∀ {ρ' : SubdivisionFace.CarrierCodimOneSubface ν.face},
        ρ'.toSubdivisionFace.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
        ρ' = ρ)
    (huniqFacet :
      ∀ σ ∈ T.facets, ρ.carrier ⊆ σ → σ = ν.face.carrier)
    {w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ}
    (hadj : Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w) :
    w =
      .positive
        (verticalNeighborOfCodimOneSubfaceContainsLowerMilestone
          (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)
          hk ρ.isCodimOneSubface hρsub hρmil) := by
  cases w with
  | start =>
      have hstart :
          ν.IsStartIncident (T := T) (chosenMilestoneChain (φ := φ)) φ := hadj
      rcases hstart with ⟨hlevel, -⟩
      exact False.elim ((Nat.ne_of_gt hk) hlevel)
  | positive μ =>
      rcases hadj with hhor | hupperAdj | hlowerAdj
      · exact False.elim <|
          not_horizontalAdj_of_not_openCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
            (T := T) (φ := φ) hνdim hupper hclosed huniqueCarrier huniqFacet hhor
      · exact False.elim <|
          not_verticalAdj_of_topDim_as_lower (T := T) (φ := φ) hνdim hupperAdj
      ·
        let μ₀ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ :=
          verticalNeighborOfCodimOneSubfaceContainsLowerMilestone
            (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)
            hk ρ.isCodimOneSubface hρsub hρmil
        have hμ₀adj :
            μ₀.VerticalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ ν :=
          verticalNeighborOfCodimOneSubfaceContainsLowerMilestone_verticalAdj
            (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)
            hk ρ.isCodimOneSubface hρsub hρmil
        rcases hlowerAdj with ⟨hμlevel, hμν, hμmil⟩
        rcases hμ₀adj with ⟨hμ₀level, -, -⟩
        let ρ' : SubdivisionFace.CarrierCodimOneSubface ν.face :=
          SubdivisionFace.CarrierCodimOneSubface.ofIsCodimOneSubface hμν
        have hsucc : μ.level.succ = ν.level.castSucc := by
          apply Fin.ext
          exact hμlevel
        have hρ'mil :
            ρ'.toSubdivisionFace.ImageContainsMilestone (T := T)
              (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc := by
          simpa [ρ', hsucc] using hμmil
        have hρeq : ρ' = ρ := huniqueCarrier hρ'mil
        have hface : μ.face = ρ.toSubdivisionFace := by
          apply SubdivisionFace.ext
          calc
            μ.face.carrier = ρ'.carrier := by simp [ρ']
            _ = ρ.carrier := by simpa [hρeq]
            _ = ρ.toSubdivisionFace.carrier := by simp
        have hlevelEq : μ.level = μ₀.level := by
          apply Fin.ext
          omega
        have hμeq : μ = μ₀ := by
          apply Section5PositiveNode.ext
            (c := chosenMilestoneChain (φ := φ)) (φ := φ) hlevelEq
          simpa [μ₀, verticalNeighborOfCodimOneSubfaceContainsLowerMilestone] using hface
        simpa [μ₀] using congrArg Section5GraphNode.positive hμeq

theorem not_exists_two_distinct_neighbors_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    (hνdim : ν.face.dim = dimension)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hclosed :
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level)
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (hρsub : ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρmil :
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc)
    (huniqueCarrier :
      ∀ {ρ' : SubdivisionFace.CarrierCodimOneSubface ν.face},
        ρ'.toSubdivisionFace.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
        ρ' = ρ)
    (huniqFacet :
      ∀ σ ∈ T.facets, ρ.carrier ⊆ σ → σ = ν.face.carrier) :
    ¬ ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      a ≠ b ∧
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b := by
  intro h
  rcases h with ⟨a, b, hab, ha, hb⟩
  have ha' :=
    eq_verticalNeighbor_of_adj_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
      (T := T) (φ := φ) hk hνdim hupper hclosed hρsub hρmil huniqueCarrier huniqFacet ha
  have hb' :=
    eq_verticalNeighbor_of_adj_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
      (T := T) (φ := φ) hk hνdim hupper hclosed hρsub hρmil huniqueCarrier huniqFacet hb
  exact hab (ha'.trans hb'.symm)

/--
Exact compatible obstruction data for the current top-dimensional no-open-crossing door
interface.

If such data exists, the present formulation of
`ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec` is too strong: the node `ν`
cannot have two distinct graph neighbors.
-/
structure TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData where
  ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ
  hk : 0 < ν.level.1
  hνdim : ν.face.dim = dimension
  hupper :
    ¬ ν.face.ImageContainsMilestone (T := T)
      (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ
  hclosed :
    ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
      (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level
  ρ : SubdivisionFace.CarrierCodimOneSubface ν.face
  hρsub : ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc
  hρmil :
    ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
      (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc
  huniqueCarrier :
    ∀ {ρ' : SubdivisionFace.CarrierCodimOneSubface ν.face},
      ρ'.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ρ' = ρ
  huniqFacet :
    ∀ σ ∈ T.facets, ρ.carrier ⊆ σ → σ = ν.face.carrier

/--
Internal surrogate for paper lines 389--391 in the codimension-`1` face language used here.

Whenever a codimension-`1` face image meets `[b_k, b_{k+1}]`, one can choose a point on that
segment that already lies away from the boundary of the codimension-`1` face image.
-/
structure ChosenMilestoneChainCodimOneFaceSegmentInteriorWitnessSpec where
  exists_pointAwayFromBoundary_of_codimOne_face_meets_segment :
    ∀ {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
      {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face},
      ρ.toSubdivisionFace.ImageMeetsMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ x : RentDivision (dimension + 1),
        ((x : RealPoint dimension) ∈ (chosenMilestoneChain (φ := φ)).segment ν.level) ∧
        ρ.toSubdivisionFace.ImageContainsPointAwayFromBoundary (T := T) φ.vertexMap x

/--
Image-side segment-escape principle needed to rule out the packaged top-dimensional obstruction.

If a top-dimensional face has a boundary-only unique lower-milestone carrier and that carrier
already contains a segment point away from its own boundary, then the ambient top-dimensional face
must either contain the next milestone or meet the open segment.
-/
structure ChosenMilestoneChainTopDimBoundaryCarrierEscapeSpec where
  openCrossing_or_contains_upper_of_pointAwayFromBoundary_on_boundaryOnlyUniqueCarrier :
    ∀ {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ},
      ν.face.dim = dimension →
      {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face} →
      (∀ {ρ' : SubdivisionFace.CarrierCodimOneSubface ν.face},
        ρ'.toSubdivisionFace.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
        ρ' = ρ) →
      (∀ σ ∈ T.facets, ρ.carrier ⊆ σ → σ = ν.face.carrier) →
      {x : RentDivision (dimension + 1)} →
      ((x : RealPoint dimension) ∈ (chosenMilestoneChain (φ := φ)).segment ν.level) →
      ρ.toSubdivisionFace.ImageContainsPointAwayFromBoundary (T := T) φ.vertexMap x →
      ν.face.ImageMeetsOpenMilestoneSegment (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level ∨
        ν.face.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ

theorem not_boundaryOnlyUniqueCarrierCounterexampleData_of_segmentInteriorWitness_and_escape
    (hwitness :
      ChosenMilestoneChainCodimOneFaceSegmentInteriorWitnessSpec
        (T := T) (φ := φ))
    (hescape :
      ChosenMilestoneChainTopDimBoundaryCarrierEscapeSpec
        (T := T) (φ := φ))
    (hdata :
      TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData
        (T := T) (φ := φ)) :
    False := by
  have hρseg :
      hdata.ρ.toSubdivisionFace.ImageMeetsMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap hdata.ν.level := by
    refine ⟨chosenMilestoneChain (φ := φ).point hdata.ν.level.castSucc, ?_, ?_⟩
    · exact left_mem_segment ℝ
        (((chosenMilestoneChain (φ := φ)).point hdata.ν.level.castSucc :
            RentDivision (dimension + 1)) : RealPoint dimension)
        (((chosenMilestoneChain (φ := φ)).point hdata.ν.level.succ :
            RentDivision (dimension + 1)) : RealPoint dimension)
    · simpa [SubdivisionFace.ImageContainsMilestone] using hdata.hρmil
  rcases
      hwitness.exists_pointAwayFromBoundary_of_codimOne_face_meets_segment hρseg with
    ⟨x, hxseg, hxρ⟩
  rcases
      hescape.openCrossing_or_contains_upper_of_pointAwayFromBoundary_on_boundaryOnlyUniqueCarrier
        hdata.hνdim hdata.huniqueCarrier hdata.huniqFacet hxseg hxρ with
    hopen | hupper
  · exact hdata.hclosed hopen
  · exact hdata.hupper hupper

theorem not_topDimNoOpenCrossingDoorSpec_of_boundaryOnlyUniqueCarrierCounterexampleData
    (hdata :
      TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData
        (T := T) (φ := φ)) :
    ¬ ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec
      (T := T) (φ := φ) := by
  intro htop
  rcases
      htop.two_doors_of_missing_nextMilestone_positiveLevel_topDim_of_not_openCrossing
        hdata.ν hdata.hk hdata.hνdim hdata.hupper hdata.hclosed with
    ⟨a, b, hab, ha, hb, -⟩
  exact
    not_exists_two_distinct_neighbors_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
      (T := T) (φ := φ)
      hdata.hk hdata.hνdim hdata.hupper hdata.hclosed hdata.hρsub hdata.hρmil
      hdata.huniqueCarrier hdata.huniqFacet
      ⟨a, b, hab, ha, hb⟩

theorem existsUnique_graphNeighbor_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    (hνdim : ν.face.dim = dimension)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hclosed :
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level)
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (hρsub : ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρmil :
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc)
    (huniqueCarrier :
      ∀ {ρ' : SubdivisionFace.CarrierCodimOneSubface ν.face},
        ρ'.toSubdivisionFace.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
        ρ' = ρ)
    (huniqFacet :
      ∀ σ ∈ T.facets, ρ.carrier ⊆ σ → σ = ν.face.carrier) :
    ∃! w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w := by
  let μ :=
    verticalNeighborOfCodimOneSubfaceContainsLowerMilestone
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)
      hk ρ.isCodimOneSubface hρsub hρmil
  have hμadj : Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) (.positive μ) :=
    Or.inr <| Or.inr <|
      verticalNeighborOfCodimOneSubfaceContainsLowerMilestone_verticalAdj
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)
        hk ρ.isCodimOneSubface hρsub hρmil
  refine ⟨.positive μ, hμadj, ?_⟩
  intro w hw
  exact
    eq_verticalNeighbor_of_adj_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
      (T := T) (φ := φ)
      hk hνdim hupper hclosed hρsub hρmil huniqueCarrier huniqFacet hw

theorem existsUnique_verticalAdj_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
    {ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ}
    (hk : 0 < ν.level.1)
    (hνdim : ν.face.dim = dimension)
    (hupper :
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ)
    (hclosed :
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level)
    {ρ : SubdivisionFace.CarrierCodimOneSubface ν.face}
    (hρsub : ρ.toSubdivisionFace.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρmil :
      ρ.toSubdivisionFace.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc)
    (huniqueCarrier :
      ∀ {ρ' : SubdivisionFace.CarrierCodimOneSubface ν.face},
        ρ'.toSubdivisionFace.ImageContainsMilestone (T := T)
          (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
        ρ' = ρ)
    (huniqFacet :
      ∀ σ ∈ T.facets, ρ.carrier ⊆ σ → σ = ν.face.carrier) :
    ∃! μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      μ.VerticalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ ν := by
  let μ :=
    verticalNeighborOfCodimOneSubfaceContainsLowerMilestone
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)
      hk ρ.isCodimOneSubface hρsub hρmil
  have hμ :
      μ.VerticalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ ν :=
    verticalNeighborOfCodimOneSubfaceContainsLowerMilestone_verticalAdj
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)
      hk ρ.isCodimOneSubface hρsub hρmil
  refine ⟨μ, hμ, ?_⟩
  intro μ' hμ'
  have hEq :
      Section5GraphNode.positive μ' = Section5GraphNode.positive μ := by
    exact
      eq_verticalNeighbor_of_adj_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
        (T := T) (φ := φ)
        hk hνdim hupper hclosed hρsub hρmil huniqueCarrier huniqFacet
        (Or.inr <| Or.inr hμ')
  injection hEq

theorem existsUnique_graphNeighbor_of_boundaryOnlyUniqueCarrierCounterexampleData
    (hdata :
      TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData
        (T := T) (φ := φ)) :
    ∃! w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive hdata.ν) w :=
  existsUnique_graphNeighbor_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
    (T := T) (φ := φ)
    hdata.hk hdata.hνdim hdata.hupper hdata.hclosed
    hdata.hρsub hdata.hρmil hdata.huniqueCarrier hdata.huniqFacet

theorem existsUnique_verticalAdj_of_boundaryOnlyUniqueCarrierCounterexampleData
    (hdata :
      TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData
        (T := T) (φ := φ)) :
    ∃! μ : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      μ.VerticalAdj (T := T) (chosenMilestoneChain (φ := φ)) φ hdata.ν :=
  existsUnique_verticalAdj_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly
    (T := T) (φ := φ)
    hdata.hk hdata.hνdim hdata.hupper hdata.hclosed
    hdata.hρsub hdata.hρmil hdata.huniqueCarrier hdata.huniqFacet

/--
Weaker top-dimensional no-open-crossing interface matching the currently-supported alternatives.

At a positive-level top-dimensional node with no open crossing, either the desired two-door
conclusion holds, or Lean can package exact boundary-only unique-carrier counterexample data.
The right branch still gives a canonical unique vertical descent by
`existsUnique_verticalAdj_of_boundaryOnlyUniqueCarrierCounterexampleData`.
-/
structure ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingAlternativeSpec where
  two_doors_or_boundaryOnlyUniqueCarrierCounterexample_of_not_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ν.face.dim = dimension →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      (∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b) ∨
        ∃ hdata : TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData
          (T := T) (φ := φ),
          hdata.ν = ν

def chosenMilestoneChainPositiveLevelTopDimNoOpenCrossingAlternativeSpec_of_doorSpec
    (htop :
      ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingAlternativeSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hνdim hupper hclosed
  left
  exact
    htop.two_doors_of_missing_nextMilestone_positiveLevel_topDim_of_not_openCrossing
      ν hk hνdim hupper hclosed

/--
Weaker positive-level no-open-crossing interface for the chosen chain.

Below top dimension, the existing two-door theorem still applies. At top dimension, the local
theorem may instead fall into the exact boundary-only unique-carrier obstruction package.
-/
structure ChosenMilestoneChainPositiveLevelNoOpenCrossingAlternativeSpec where
  two_doors_or_topDimBoundaryOnlyUniqueCarrierCounterexample_of_not_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      (∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b) ∨
        ∃ hdata : TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData
          (T := T) (φ := φ),
          hdata.ν = ν

def chosenMilestoneChainPositiveLevelNoOpenCrossingAlternativeSpec_of_topDim_and_belowTopDim
    (htop :
      ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingAlternativeSpec
        (T := T) (φ := φ))
    (hbelow :
      ChosenMilestoneChainPositiveLevelBelowTopDimNoOpenCrossingDoorSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingAlternativeSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hupper hclosed
  by_cases htopdim : ν.face.dim = dimension
  · exact
      htop.two_doors_or_boundaryOnlyUniqueCarrierCounterexample_of_not_openCrossing
        ν hk htopdim hupper hclosed
  · have hbelowdim : ν.face.dim < dimension :=
      lt_of_le_of_ne ν.face.dim_le (fun h => htopdim h)
    left
    exact
      hbelow.two_doors_of_missing_nextMilestone_positiveLevel_belowTopDim_of_not_openCrossing
        ν hk hbelowdim hupper hclosed

def chosenMilestoneChainPositiveLevelNoOpenCrossingSpec_of_alternative_and_counterexampleExclusion
    (halt :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingAlternativeSpec
        (T := T) (φ := φ))
    (hexcl :
      ∀ _hdata : TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData
        (T := T) (φ := φ), False) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hupper hclosed
  rcases
      halt.two_doors_or_topDimBoundaryOnlyUniqueCarrierCounterexample_of_not_openCrossing
        ν hk hupper hclosed with
    hdoors | ⟨hdata, hdataEq⟩
  · exact hdoors
  · subst hdataEq
    exact False.elim (hexcl hdata)

def chosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec_of_filteredSpec
    (hfiltered :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec
      (T := T) (φ := φ) := by
  refine ⟨?_⟩
  intro ν hk hupper hclosed
  rcases hfiltered.exists_unique_candidate_of_not_openCrossing ν hk hupper hclosed with
    ⟨ρ, hρsub, hρmil, huniq⟩
  refine ⟨ρ, hρsub, hρmil, ?_⟩
  simpa [IsSameLevelCarrierContinuationCandidate] using huniq

def chosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec_of_existence_and_uniqueness
    (hexists :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec
        (T := T) (φ := φ))
    (huniq :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec_of_filteredSpec
    (T := T) (φ := φ)
    (chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_existence_and_uniqueness
      (T := T) (φ := φ) hexists huniq)

def
    chosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec_of_reflection_and_fixedCarrierContinuation_and_uniqueness
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hexists :
      ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec
        (T := T) (φ := φ))
    (huniq :
      ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec
        (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec
      (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec_of_existence_and_uniqueness
    (T := T) (φ := φ)
    (chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierContinuation
      (T := T) (φ := φ) hreflect hexists)
    huniq

def chosenMilestoneChainPositiveLevelLowerMilestoneSpec_of_doorSpec
    (hdoor : ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelLowerMilestoneSpec (T := T) (φ := φ) := by
  refine
    { two_doors_of_missing_nextMilestone_positiveLevel_contains_lowerMilestone := ?_ }
  intro ν hk hupper hlower _
  exact hdoor.two_doors_of_missing_nextMilestone_positiveLevel_contains_lowerMilestone
    ν hk hupper hlower

/--
The remaining next-milestone case once the away-from-boundary image condition has been supplied.
-/
structure ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec where
  two_doors_of_nextMilestone_awayFromBoundary :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ν.face.ImageContainsMilestoneAwayFromBoundary (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ IsTerminal (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

def chosenMilestoneChainPositiveLevelSpec_of_openCrossing_and_lowerMilestone_and_awayFromBoundary
    (hopen : ChosenMilestoneChainOpenCrossingSpec (T := T) (φ := φ))
    (hlower : ChosenMilestoneChainPositiveLevelLowerMilestoneSpec (T := T) (φ := φ))
    (haway : ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelSpec (T := T) (φ := φ) := by
  refine
    { two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor := ?_
      two_doors_of_nextMilestone_awayFromBoundary :=
        haway.two_doors_of_nextMilestone_awayFromBoundary }
  intro ν hk hupper hextra
  rcases chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone
      (T := T) (φ := φ) (ν := ν) hupper with hopen' | hlower'
  · exact hopen.two_doors_of_missing_nextMilestone_openCrossing ν hupper hopen'
  · exact hlower.two_doors_of_missing_nextMilestone_positiveLevel_contains_lowerMilestone
      ν hk hupper hlower' hextra

def chosenMilestoneChainPositiveLevelSpec_of_openCrossing_and_lowerMilestoneDoor_and_awayFromBoundary
    (hopen : ChosenMilestoneChainOpenCrossingSpec (T := T) (φ := φ))
    (hlower : ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec (T := T) (φ := φ))
    (haway : ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelSpec (T := T) (φ := φ) :=
  chosenMilestoneChainPositiveLevelSpec_of_openCrossing_and_lowerMilestone_and_awayFromBoundary
    (T := T) (φ := φ) hopen
    (chosenMilestoneChainPositiveLevelLowerMilestoneSpec_of_doorSpec
      (T := T) (φ := φ) hlower)
    haway

def chosenMilestoneChainPositiveLevelSpec_of_openCrossing_and_noOpenCrossing_and_awayFromBoundary
    (hopen : ChosenMilestoneChainOpenCrossingSpec (T := T) (φ := φ))
    (hclosed : ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec (T := T) (φ := φ))
    (haway : ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec (T := T) (φ := φ)) :
    ChosenMilestoneChainPositiveLevelSpec (T := T) (φ := φ) := by
  refine
    { two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor := ?_
      two_doors_of_nextMilestone_awayFromBoundary :=
        haway.two_doors_of_nextMilestone_awayFromBoundary }
  intro ν hk hupper _
  by_cases hopenν :
      ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level
  · exact hopen.two_doors_of_missing_nextMilestone_openCrossing ν hupper hopenν
  · exact hclosed.two_doors_of_missing_nextMilestone_positiveLevel_of_not_openCrossing
      ν hk hupper hopenν

def chosenMilestoneChainGraphLocalRestSpec_of_openCrossing_and_positiveLevel
    (hopen : ChosenMilestoneChainOpenCrossingSpec (T := T) (φ := φ))
    (hpositive : ChosenMilestoneChainPositiveLevelSpec (T := T) (φ := φ)) :
    ChosenMilestoneChainGraphLocalRestSpec (T := T) (φ := φ) := by
  refine
    { two_doors_of_missing_nextMilestone_openCrossing :=
        hopen.two_doors_of_missing_nextMilestone_openCrossing
      two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor :=
        hpositive.two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor
      two_doors_of_nextMilestone_awayFromBoundary :=
        hpositive.two_doors_of_nextMilestone_awayFromBoundary }

structure ChosenMilestoneChainGraphLocalSpec where
  start_neighbor : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ
  start_adj :
    Adj (T := T) (chosenMilestoneChain (φ := φ)) φ .start (.positive start_neighbor)
  start_unique :
    ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ .start w →
        w = .positive start_neighbor
  two_doors_of_missing_nextMilestone_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b
  two_doors_of_missing_nextMilestone_level_zero :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ν.level.1 = 0 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b
  two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      0 < ν.level.1 →
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      (∃ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        w ≠ .positive ν ∧
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w) →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b
  two_doors_of_nextMilestone_awayFromBoundary :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ν.face.ImageContainsMilestoneAwayFromBoundary (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ IsTerminal (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

def chosenMilestoneChainGraphLocalSpec_of_levelZeroBoundary_and_rest
    (hzero : ChosenMilestoneChainLevelZeroBoundarySpec (T := T) (φ := φ))
    (hrest : ChosenMilestoneChainGraphLocalRestSpec (T := T) (φ := φ)) :
    ChosenMilestoneChainGraphLocalSpec (T := T) (φ := φ) := by
  refine
    { start_neighbor := hzero.start_neighbor
      start_adj := hzero.start_adj
      start_unique := hzero.start_unique
      two_doors_of_missing_nextMilestone_openCrossing :=
        hrest.two_doors_of_missing_nextMilestone_openCrossing
      two_doors_of_missing_nextMilestone_level_zero :=
        hzero.two_doors_of_missing_nextMilestone_level_zero
      two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor :=
        hrest.two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor
      two_doors_of_nextMilestone_awayFromBoundary :=
        hrest.two_doors_of_nextMilestone_awayFromBoundary }

/--
This combines the primitive lower-door support contract with the remaining purely graph-local
Section 5 consequences for the chosen chain.
-/
structure ChosenMilestoneChainDoorSpec where
  start_neighbor : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ
  start_adj :
    Adj (T := T) (chosenMilestoneChain (φ := φ)) φ .start (.positive start_neighbor)
  start_unique :
    ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      Adj (T := T) (chosenMilestoneChain (φ := φ)) φ .start w →
        w = .positive start_neighbor
  two_doors_of_missing_nextMilestone_openCrossing :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageMeetsOpenMilestoneSegment (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b
  two_doors_of_missing_nextMilestone_contains_lowerMilestone :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ¬ ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ν.face.ImageContainsMilestone (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.castSucc →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b
  two_doors_of_nextMilestone_awayFromBoundary :
    ∀ ν : Section5PositiveNode (chosenMilestoneChain (φ := φ)) φ,
      ν.face.ImageContainsMilestoneAwayFromBoundary (T := T)
        (chosenMilestoneChain (φ := φ)) φ.vertexMap ν.level.succ →
      ¬ IsTerminal (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) →
      ∃ a b : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
        a ≠ b ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) a ∧
        Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) b ∧
        ∀ w : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
          Adj (T := T) (chosenMilestoneChain (φ := φ)) φ (.positive ν) w → w = a ∨ w = b

def chosenMilestoneChainDoorSpec_of_faceLocal_and_graphLocal
    (hlower :
      FaceLocalLowerPrefixCarrierSpec
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hgraph : ChosenMilestoneChainGraphLocalSpec (T := T) (φ := φ)) :
    ChosenMilestoneChainDoorSpec (T := T) (φ := φ) := by
  refine
    { start_neighbor := hgraph.start_neighbor
      start_adj := hgraph.start_adj
      start_unique := hgraph.start_unique
      two_doors_of_missing_nextMilestone_openCrossing :=
        hgraph.two_doors_of_missing_nextMilestone_openCrossing
      two_doors_of_missing_nextMilestone_contains_lowerMilestone := ?_
      two_doors_of_nextMilestone_awayFromBoundary :=
        hgraph.two_doors_of_nextMilestone_awayFromBoundary }
  intro ν hupper hlowerMil
  by_cases hk : 0 < ν.level.1
  · exact hgraph.two_doors_of_missing_nextMilestone_positiveLevel_of_extraNeighbor ν hk hupper
      (exists_graphNeighbor_of_contains_lowerMilestone_of_faceLocalSpec
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hlower hk hlowerMil)
  · exact hgraph.two_doors_of_missing_nextMilestone_level_zero ν
      (Nat.eq_zero_of_not_pos hk) hupper hlowerMil

def localDegreeHypotheses_of_geometricGenericity
    (hgen : GeometricGenericity (T := T) (c := c) (φ := φ)) :
    LocalDegreeHypotheses (T := T) (c := c) (φ := φ) := by
  refine
    { start_neighbor := hgen.start_neighbor
      start_adj := hgen.start_adj
      start_unique := hgen.start_unique
      nonterminal_two_neighbors := ?_ }
  intro ν hν
  by_cases hnext : ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.succ
  · exact hgen.two_doors_of_nextMilestone ν hnext hν
  · exact hgen.two_doors_of_missing_nextMilestone ν hnext

def geometricGenericity_of_milestoneSegmentTransversality
    (htrans : MilestoneSegmentTransversality (T := T) (c := c) (φ := φ)) :
    GeometricGenericity (T := T) (c := c) (φ := φ) :=
  htrans.toGeometricGenericity

def chosenMilestoneChain_geometricGenericity_of_doorSpec
    (hdoor : ChosenMilestoneChainDoorSpec (T := T) (φ := φ)) :
    GeometricGenericity
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) := by
  refine
    { start_neighbor := hdoor.start_neighbor
      start_adj := hdoor.start_adj
      start_unique := hdoor.start_unique
      two_doors_of_missing_nextMilestone := ?_
      two_doors_of_nextMilestone := ?_ }
  · intro ν hupper
    rcases chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone
        (T := T) (φ := φ) (ν := ν) hupper with hopen | hlower
    · exact hdoor.two_doors_of_missing_nextMilestone_openCrossing ν hupper hopen
    · exact hdoor.two_doors_of_missing_nextMilestone_contains_lowerMilestone ν hupper hlower
  · intro ν hnext hν
    exact hdoor.two_doors_of_nextMilestone_awayFromBoundary ν
      (chosenMilestoneChain_nextMilestoneAwayFromBoundary_of_nonterminal
        (T := T) (φ := φ) hnext hν) hν

lemma degree_start_eq_one
    [Fintype (Section5GraphNode c φ)] [DecidableRel (graph (T := T) c φ).Adj]
    (hdeg : LocalDegreeHypotheses (T := T) (c := c) (φ := φ)) :
    (graph (T := T) c φ).degree .start = 1 := by
  classical
  let G : SimpleGraph (Section5GraphNode c φ) := graph (T := T) c φ
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := G) (v := .start)]
  refine ⟨.positive hdeg.start_neighbor, hdeg.start_adj, ?_⟩
  intro w hw
  exact hdeg.start_unique w hw

lemma odd_degree_start
    [Fintype (Section5GraphNode c φ)] [DecidableRel (graph (T := T) c φ).Adj]
    (hdeg : LocalDegreeHypotheses (T := T) (c := c) (φ := φ)) :
    Odd ((graph (T := T) c φ).degree .start) := by
  rw [degree_start_eq_one (T := T) (c := c) (φ := φ) hdeg]
  decide

lemma degree_positive_eq_two
    [Fintype (Section5GraphNode c φ)] [DecidableRel (graph (T := T) c φ).Adj]
    (hdeg : LocalDegreeHypotheses (T := T) (c := c) (φ := φ))
    (ν : Section5PositiveNode c φ)
    (hν : ¬ IsTerminal (T := T) c φ (.positive ν)) :
    (graph (T := T) c φ).degree (.positive ν) = 2 := by
  classical
  let G : SimpleGraph (Section5GraphNode c φ) := graph (T := T) c φ
  rcases hdeg.nonterminal_two_neighbors ν hν with ⟨a, b, hab, hadja, hadjb, hall⟩
  have hfinset : G.neighborFinset (.positive ν) = ({a, b} : Finset (Section5GraphNode c φ)) := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    constructor
    · intro hw
      simpa [Finset.mem_insert, Finset.mem_singleton] using hall w hw
    · intro hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hadja
      · exact hadjb
  rw [← G.card_neighborFinset_eq_degree, hfinset]
  simp [hab]

lemma even_degree_of_not_terminal
    [Fintype (Section5GraphNode c φ)] [DecidableRel (graph (T := T) c φ).Adj]
    (hdeg : LocalDegreeHypotheses (T := T) (c := c) (φ := φ))
    (ν : Section5PositiveNode c φ)
    (hν : ¬ IsTerminal (T := T) c φ (.positive ν)) :
    Even ((graph (T := T) c φ).degree (.positive ν)) := by
  rw [degree_positive_eq_two (T := T) (c := c) (φ := φ) hdeg ν hν]
  decide

theorem exists_terminal_of_local_degree_lemmas
    [Fintype (Section5GraphNode c φ)] [DecidableRel (graph (T := T) c φ).Adj]
    (hstart : Odd ((graph (T := T) c φ).degree .start))
    (heven :
      ∀ v : Section5GraphNode c φ,
        v ≠ .start →
        ¬ IsTerminal (T := T) c φ v →
        Even ((graph (T := T) c φ).degree v)) :
    ∃ v : Section5GraphNode c φ, v ≠ .start ∧ IsTerminal (T := T) c φ v := by
  let G : SimpleGraph (Section5GraphNode c φ) := graph (T := T) c φ
  exact exists_terminal_of_odd_start_and_nonterminal_even G .start
    (IsTerminal (T := T) c φ) hstart heven

theorem exists_terminal_of_localDegreeHypotheses
    [Finite (Section5GraphNode c φ)]
    (hdeg : LocalDegreeHypotheses (T := T) (c := c) (φ := φ)) :
    ∃ v : Section5GraphNode c φ, v ≠ .start ∧ IsTerminal (T := T) c φ v := by
  classical
  letI := Fintype.ofFinite (Section5GraphNode c φ)
  refine exists_terminal_of_local_degree_lemmas (T := T) (c := c) (φ := φ)
    (odd_degree_start (T := T) (c := c) (φ := φ) hdeg) ?_
  intro v hv hterminal
  cases v with
  | start =>
      contradiction
  | positive ν =>
      exact even_degree_of_not_terminal (T := T) (c := c) (φ := φ) hdeg ν hterminal

theorem exists_terminal_of_geometricGenericity
    [Finite (Section5GraphNode c φ)]
    (hgen : GeometricGenericity (T := T) (c := c) (φ := φ)) :
    ∃ v : Section5GraphNode c φ, v ≠ .start ∧ IsTerminal (T := T) c φ v := by
  exact exists_terminal_of_localDegreeHypotheses (T := T) (c := c) (φ := φ)
    (localDegreeHypotheses_of_geometricGenericity (T := T) (c := c) (φ := φ) hgen)

theorem exists_terminal_of_milestoneSegmentTransversality
    [Finite (Section5GraphNode c φ)]
    (htrans : MilestoneSegmentTransversality (T := T) (c := c) (φ := φ)) :
    ∃ v : Section5GraphNode c φ, v ≠ .start ∧ IsTerminal (T := T) c φ v := by
  exact exists_terminal_of_geometricGenericity (T := T) (c := c) (φ := φ)
    (geometricGenericity_of_milestoneSegmentTransversality
      (T := T) (c := c) (φ := φ) htrans)

def chosenMilestoneChain_milestoneSegmentTransversality_of_geometricGenericity
    (hgen :
      GeometricGenericity
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)) :
    MilestoneSegmentTransversality
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) := by
  refine
    { toGeometricGenericity := hgen
      missing_nextMilestone_openCrossing_or_contains_lowerMilestone := ?_
      nextMilestone_awayFromBoundary_of_nonterminal := ?_ }
  · intro ν hupper
    exact chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone
      (T := T) (φ := φ) hupper
  · intro ν hcontains hν
    exact chosenMilestoneChain_nextMilestoneAwayFromBoundary_of_nonterminal
      (T := T) (φ := φ) hcontains hν

theorem exists_terminal_of_chosenMilestoneChain_geometricGenericity
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hgen :
      GeometricGenericity
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)) :
    ∃ v : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      v ≠ .start ∧
        IsTerminal (T := T) (chosenMilestoneChain (φ := φ)) φ v := by
  exact exists_terminal_of_milestoneSegmentTransversality
    (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)
    (chosenMilestoneChain_milestoneSegmentTransversality_of_geometricGenericity
      (T := T) (φ := φ) hgen)

theorem exists_terminal_of_chosenMilestoneChain_doorSpec
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hdoor : ChosenMilestoneChainDoorSpec (T := T) (φ := φ)) :
    ∃ v : Section5GraphNode (chosenMilestoneChain (φ := φ)) φ,
      v ≠ .start ∧
        IsTerminal (T := T) (chosenMilestoneChain (φ := φ)) φ v := by
  exact exists_terminal_of_chosenMilestoneChain_geometricGenericity
    (T := T) (φ := φ)
    (chosenMilestoneChain_geometricGenericity_of_doorSpec
      (T := T) (φ := φ) hdoor)

theorem exists_terminalMilestoneCell_of_chosenMilestoneChain_geometricGenericity
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hgen :
      GeometricGenericity
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ)) :
    ∃ σ ∈ T.facets,
      FacetImageContains σ φ.vertexMap
        ((chosenMilestoneChain (φ := φ)).point (Fin.last dimension)) := by
  rcases exists_terminal_of_chosenMilestoneChain_geometricGenericity
      (T := T) (φ := φ) hgen with ⟨v, hv, hterminal⟩
  cases v with
  | start =>
      contradiction
  | positive ν =>
      rcases hterminal with ⟨hνdim, hνimage⟩
      rcases ν.face.subset_facet with ⟨σ, hσ, hνσ⟩
      have hσeq : ν.face.carrier = σ :=
        ambientFacet_eq_of_topDim (T := T) (φ := φ) ν hσ hνσ hνdim
      refine ⟨σ, hσ, ?_⟩
      simpa [SubdivisionFace.ImageContainsMilestone, SubdivisionFace.ImageContains,
        SubdivisionFace.imagePoints, FacetImageContains, hσeq] using hνimage

theorem exists_barycenterPreimageCell_of_chosenMilestoneChain_doorSpec
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hdoor : ChosenMilestoneChainDoorSpec (T := T) (φ := φ)) :
    ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap := by
  rcases exists_terminalMilestoneCell_of_chosenMilestoneChain_geometricGenericity
      (T := T) (φ := φ)
      (chosenMilestoneChain_geometricGenericity_of_doorSpec
        (T := T) (φ := φ) hdoor) with ⟨σ, hσ, hσmil⟩
  have hσmil' :
      FacetImageContains σ φ.vertexMap
        ((chosenMilestoneChain (φ := φ)).point (Fin.last dimension)) := by
    simpa [chosenMilestoneChain_point] using hσmil
  refine ⟨σ, hσ, ?_⟩
  simpa [FacetImageContainsBarycenter, chosenMilestoneChain_point,
    chosenPrefixMilestonePoint_terminal_eq_barycenter (T := T) (φ := φ)] using hσmil'

theorem exists_barycenterPreimageCell_of_chosenMilestoneChain_specs
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hlower :
      FaceLocalLowerPrefixCarrierSpec
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hgraph : ChosenMilestoneChainGraphLocalSpec (T := T) (φ := φ)) :
    ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap := by
  exact exists_barycenterPreimageCell_of_chosenMilestoneChain_doorSpec
    (T := T) (φ := φ)
    (chosenMilestoneChainDoorSpec_of_faceLocal_and_graphLocal
      (T := T) (φ := φ) hlower hgraph)

theorem exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hgraph : ChosenMilestoneChainGraphLocalSpec (T := T) (φ := φ)) :
    ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap := by
  let hlarge :
      FaceLocalLargeLowerPrefixCarrierSpec
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) :=
    faceLocalLargeLowerPrefixCarrierSpec_of_positiveFaceLowerPrefixReflection
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hreflect
  let hlower :
      FaceLocalLowerPrefixCarrierSpec
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) :=
    faceLocalLowerPrefixCarrierSpec_of_largeLowerPrefixCarrierSpec
      (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ) hlarge
  exact exists_barycenterPreimageCell_of_chosenMilestoneChain_specs
    (T := T) (φ := φ) hlower hgraph

theorem exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec'
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hzero : ChosenMilestoneChainLevelZeroBoundarySpec (T := T) (φ := φ))
    (hrest : ChosenMilestoneChainGraphLocalRestSpec (T := T) (φ := φ)) :
    ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap := by
  exact exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec
    (T := T) (φ := φ) hreflect
    (chosenMilestoneChainGraphLocalSpec_of_levelZeroBoundary_and_rest
      (T := T) (φ := φ) hzero hrest)

theorem exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hzero : ChosenMilestoneChainLevelZeroBoundarySpec (T := T) (φ := φ))
    (hopen : ChosenMilestoneChainOpenCrossingSpec (T := T) (φ := φ))
    (hpositive : ChosenMilestoneChainPositiveLevelSpec (T := T) (φ := φ)) :
    ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap := by
  exact exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec'
    (T := T) (φ := φ) hreflect hzero
    (chosenMilestoneChainGraphLocalRestSpec_of_openCrossing_and_positiveLevel
      (T := T) (φ := φ) hopen hpositive)

theorem exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec'''
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hzero : ChosenMilestoneChainLevelZeroBoundarySpec (T := T) (φ := φ))
    (hopen : ChosenMilestoneChainOpenCrossingSpec (T := T) (φ := φ))
    (hlower : ChosenMilestoneChainPositiveLevelLowerMilestoneSpec (T := T) (φ := φ))
    (haway : ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec (T := T) (φ := φ)) :
    ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap := by
  exact exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''
    (T := T) (φ := φ) hreflect hzero hopen
    (chosenMilestoneChainPositiveLevelSpec_of_openCrossing_and_lowerMilestone_and_awayFromBoundary
      (T := T) (φ := φ) hopen hlower haway)

theorem exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''''
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hzero : ChosenMilestoneChainLevelZeroBoundarySpec (T := T) (φ := φ))
    (hopen : ChosenMilestoneChainOpenCrossingSpec (T := T) (φ := φ))
    (hlower : ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec (T := T) (φ := φ))
    (haway : ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec (T := T) (φ := φ)) :
    ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap := by
  exact exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''
    (T := T) (φ := φ) hreflect hzero hopen
    (chosenMilestoneChainPositiveLevelSpec_of_openCrossing_and_lowerMilestoneDoor_and_awayFromBoundary
      (T := T) (φ := φ) hopen hlower haway)

theorem exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec_noOpenCrossing
    [Finite (Section5GraphNode (chosenMilestoneChain (φ := φ)) φ)]
    (hreflect :
      PositiveFaceLowerPrefixReflection
        (T := T) (c := chosenMilestoneChain (φ := φ)) (φ := φ))
    (hzero : ChosenMilestoneChainLevelZeroBoundarySpec (T := T) (φ := φ))
    (hopen : ChosenMilestoneChainOpenCrossingSpec (T := T) (φ := φ))
    (hclosed : ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec (T := T) (φ := φ))
    (haway : ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec (T := T) (φ := φ)) :
    ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap := by
  exact exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''
    (T := T) (φ := φ) hreflect hzero hopen
    (chosenMilestoneChainPositiveLevelSpec_of_openCrossing_and_noOpenCrossing_and_awayFromBoundary
      (T := T) (φ := φ) hopen hclosed haway)

end Section5GraphNode

end GraphStructure

end RentalHarmony
