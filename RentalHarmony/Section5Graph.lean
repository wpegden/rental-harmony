import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
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

/--
The chosen milestone lies in the image of a face, but not already in the image of any of its
codimension-`1` subfaces.

This is an image-side surrogate for the paper's relative-interior milestone condition.
-/
def ImageContainsMilestoneAwayFromBoundary (c : Section5MilestoneChain (dimension := dimension))
    (τ : SubdivisionFace T) (φ : Vertex → RentDivision (dimension + 1))
    (k : Fin (dimension + 1)) : Prop :=
  τ.ImageContainsMilestone (T := T) c φ k ∧
    ∀ ρ : SubdivisionFace T, ρ.IsCodimOneSubface τ → ¬ ρ.ImageContainsMilestone (T := T) c φ k

lemma imageMeetsMilestoneSegment_of_imageMeetsOpenMilestoneSegment
    {c : Section5MilestoneChain (dimension := dimension)} {τ : SubdivisionFace T}
    {φ : Vertex → RentDivision (dimension + 1)} {k : Fin dimension}
    (hτ : τ.ImageMeetsOpenMilestoneSegment (T := T) c φ k) :
    τ.ImageMeetsMilestoneSegment (T := T) c φ k := by
  rcases hτ with ⟨x, hxseg, -, -, himg⟩
  exact ⟨x, hxseg, himg⟩

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

theorem exists_verticalAdj_of_codimOneSubface_contains_lowerMilestone
    {ν : Section5PositiveNode c φ} (hk : 0 < ν.level.1)
    {ρ : SubdivisionFace T}
    (hρ : ρ.IsCodimOneSubface ν.face)
    (hρsub : ρ.SubdividesPrefixFace (T := T) ν.level.castSucc)
    (hρmil : ρ.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc) :
    ∃ μ : Section5PositiveNode c φ, μ.VerticalAdj (T := T) c φ ν := by
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
  refine ⟨
    { level := lowerLevel
      face := ρ
      face_dim := hρdim
      subdivides := by simpa [hsucc] using hρsub
      meets_segment := hρmeets }, ?_⟩
  refine ⟨?_, hρ, ?_⟩
  · simp [lowerLevel, Nat.sub_add_cancel hk_le]
  · simpa [hsucc] using hρmil

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

end Section5GraphNode

end GraphStructure

end RentalHarmony
