import Mathlib.Analysis.Convex.Combination
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

/-- The segment joining two successive milestones. -/
def segment (c : Section5MilestoneChain (dimension := dimension)) (k : Fin dimension) :
    Set (RealPoint dimension) :=
  _root_.segment ℝ
    (((c.point k.castSucc : RentDivision (dimension + 1)) : RealPoint dimension))
    (((c.point k.succ : RentDivision (dimension + 1)) : RealPoint dimension))

end Section5MilestoneChain

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

/-- The image of a subdivision face meets one of the chosen Section 5 milestone segments. -/
def ImageMeetsMilestoneSegment (c : Section5MilestoneChain (dimension := dimension))
    (τ : SubdivisionFace T) (φ : Vertex → RentDivision (dimension + 1)) (k : Fin dimension) :
    Prop :=
  ∃ x : RentDivision (dimension + 1),
    ((x : RealPoint dimension) ∈ c.segment k) ∧
      τ.ImageContains (T := T) φ x

/-- The image of a subdivision face contains one of the chosen Section 5 milestones. -/
def ImageContainsMilestone (c : Section5MilestoneChain (dimension := dimension))
    (τ : SubdivisionFace T) (φ : Vertex → RentDivision (dimension + 1))
    (k : Fin (dimension + 1)) : Prop :=
  τ.ImageContains (T := T) φ (c.point k)

end SubdivisionFace

end GraphData

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

end Section5GraphNode

end GraphStructure

end RentalHarmony
