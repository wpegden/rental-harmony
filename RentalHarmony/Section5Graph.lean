import Mathlib.Analysis.Convex.Combination
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

end SubdivisionFace

end Faces

section PrefixGeometry

variable {dimension : ℕ}

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

end PrefixGeometry

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

/-- The image of a subdivision face meets one of the paper's barycenter segments. -/
def ImageMeetsPrefixBarycenterSegment (τ : SubdivisionFace T)
    (φ : Vertex → RentDivision (dimension + 1)) (k : Fin dimension) : Prop :=
  ∃ x : RentDivision (dimension + 1),
    ((x : RealPoint dimension) ∈ prefixBarycenterSegment (dimension := dimension) k) ∧
      τ.ImageContains (T := T) φ x

/-- The image of a subdivision face contains one of the paper's prefix-face barycenters. -/
def ImageContainsPrefixBarycenter (τ : SubdivisionFace T)
    (φ : Vertex → RentDivision (dimension + 1)) (k : Fin (dimension + 1)) : Prop :=
  τ.ImageContains (T := T) φ (prefixBarycenter (dimension := dimension) k)

end SubdivisionFace

end GraphData

end RentalHarmony
