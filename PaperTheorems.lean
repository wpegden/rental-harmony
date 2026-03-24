import Mathlib.Combinatorics.Hall.Basic
import RentalHarmony.PaperDefinitions
import RentalHarmony.Sperner

/-!
# Paper Theorems

Precise Lean propositions for the main claims of
`paper/arxiv-1702.07325.tex`, together with the first Hall-side combinatorial lemmas used by the
paper's general argument.
-/

noncomputable section

open scoped BigOperators

namespace RentalHarmony

universe u

section HallLemmas

/-- `choiceNeighbors` is exactly the finite union used in Hall's theorem. -/
theorem choiceNeighbors_eq_biUnion {rooms agents : ℕ}
    (choices : RoomChoiceFamily rooms agents) (A : Finset (Fin agents)) :
    choiceNeighbors choices A = A.biUnion choices := by
  ext r
  simp [choiceNeighbors]

/-- Hall's marriage theorem specialized to the room-choice family used in this project. -/
theorem hallCondition_iff_exists_injective_choice {rooms agents : ℕ}
    (choices : RoomChoiceFamily rooms agents) :
    HallCondition choices ↔
      ∃ assignment : Fin agents → Room rooms, IsRoomAssignment choices assignment := by
  simpa [HallCondition, IsRoomAssignment, choiceNeighbors_eq_biUnion] using
    (Finset.all_card_le_biUnion_card_iff_existsInjective' choices)

/-- Removing one room from every choice set removes that room from the total neighborhood. -/
theorem choiceNeighbors_avoiding_eq_erase {rooms agents : ℕ}
    (choices : RoomChoiceFamily rooms agents) (A : Finset (Fin agents))
    (forbidden : Room rooms) :
    choiceNeighbors (choicesAvoiding choices forbidden) A =
      (choiceNeighbors choices A).erase forbidden := by
  ext r
  simp [choiceNeighbors, choicesAvoiding, and_left_comm]

/-- The secretive Hall condition implies the ordinary Hall condition after one room is deleted. -/
theorem hallCondition_of_secretiveHallCondition {rooms agents : ℕ}
    {choices : RoomChoiceFamily rooms agents} (h : SecretiveHallCondition choices)
    (forbidden : Room rooms) : HallCondition (choicesAvoiding choices forbidden) := by
  intro A
  rw [choiceNeighbors_avoiding_eq_erase]
  exact (Nat.le_sub_of_add_le (h A)).trans Finset.pred_card_le_card_erase

/--
Under the secretive Hall condition, one can still choose injectively after forbidding one room.
-/
theorem secretiveHallCondition_exists_injective_choice_avoiding {rooms agents : ℕ}
    {choices : RoomChoiceFamily rooms agents} (h : SecretiveHallCondition choices)
    (forbidden : Room rooms) :
    ∃ assignment : Fin agents → Room rooms,
      IsRoomAssignmentAvoiding choices forbidden assignment := by
  rcases
      (hallCondition_iff_exists_injective_choice
        (choices := choicesAvoiding choices forbidden)).mp
      (hallCondition_of_secretiveHallCondition h forbidden) with ⟨assignment, hassignment⟩
  refine ⟨assignment, hassignment.1, ?_⟩
  intro i
  exact Finset.mem_erase.mp (hassignment.2 i)

/--
The paper's Hall step: if every subset of known roommates sees at least one more room than its own
size, then the secretive roommate may remove an arbitrary room and the others can still be matched
to acceptable rooms.
-/
theorem hasSecretiveEnvyFreeDivision_of_secretiveHallCondition {rooms : ℕ}
    (prefs : KnownPreferences rooms (rooms - 1)) (d : RentDivision rooms)
    (h : SecretiveHallCondition (acceptableChoiceFamily prefs d)) :
    HasSecretiveEnvyFreeDivision prefs := by
  refine ⟨d, ?_⟩
  intro forbidden
  rcases secretiveHallCondition_exists_injective_choice_avoiding
      (choices := acceptableChoiceFamily prefs d) h forbidden with ⟨assignment, hassignment⟩
  refine ⟨assignment, hassignment.1, ?_⟩
  intro i
  refine ⟨(hassignment.2 i).1, ?_⟩
  simpa [acceptableChoiceFamily] using (hassignment.2 i).2

end HallLemmas

section Section2

/-- Paper Section 2: Sperner's lemma for a simplex subdivision. -/
def sperner_exists_fully_labeled_simplex_statement (dimension : ℕ) : Prop :=
  ∀ {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (L : SpernerLabeling T),
      ∃ σ ∈ T.facets, FullyLabeledFacet σ L.label

/--
Paper Section 2 / Section 5 topological core:
the piecewise-linear face-preserving map built from a simplex subdivision is surjective.
-/
def facePreservingMap_surjective_statement (dimension : ℕ) : Prop :=
  ∀ {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (φ : PiecewiseLinearSimplexMap T),
      Function.Surjective φ.toFun

end Section2

section Section3

/--
Paper Section 3, first proof: the compressed triangle label sees all three labels while each of the
two known roommates sees at least two distinct room labels.
-/
def threeRoommates_compressedLabelLemma_statement : Prop :=
  ∀ {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision 2 Vertex) (Larry Moe : SpernerLabeling T),
      ∃ σ ∈ T.facets,
        FullyLabeledFacet σ (fun v ↦ compressedPreferenceLabel (Larry.label v) (Moe.label v)) ∧
        2 ≤ DistinctLabelCount σ Larry.label ∧
        2 ≤ DistinctLabelCount σ Moe.label

/-- Paper Section 3: the three-roommate case of secretive rental harmony. -/
def threeRoommates_secretiveRentalHarmony_statement : Prop :=
  ∀ prefs : KnownTolerantPreferences 3 2, HasSecretiveEnvyFreeDivision (forgetTolerance prefs)

end Section3

section Section4

/-- Paper Theorem 1.1 / Section 4: secretive rental harmony for `rooms` rooms and roommates. -/
def secretiveRentalHarmony_statement (rooms : ℕ) : Prop :=
  ∀ prefs : KnownTolerantPreferences rooms (rooms - 1),
    HasSecretiveEnvyFreeDivision (forgetTolerance prefs)

end Section4

section HallReductions

/--
Once the geometric argument produces a rent division satisfying the paper's strengthened Hall
condition, the general secretive rental-harmony theorem follows from the Hall lemmas above.
-/
theorem secretiveRentalHarmony_of_secretiveHallWitness
    {rooms : ℕ}
    (h : ∀ prefs : KnownTolerantPreferences rooms (rooms - 1),
      ∃ d : RentDivision rooms,
        SecretiveHallCondition (acceptableChoiceFamily (forgetTolerance prefs) d)) :
    secretiveRentalHarmony_statement rooms := by
  intro prefs
  rcases h prefs with ⟨d, hd⟩
  exact hasSecretiveEnvyFreeDivision_of_secretiveHallCondition
    (prefs := forgetTolerance prefs) d hd

/--
The three-roommate theorem is the first nontrivial instance of the same Hall reduction.
-/
theorem threeRoommates_secretiveRentalHarmony_of_secretiveHallWitness
    (h : ∀ prefs : KnownTolerantPreferences 3 2,
      ∃ d : RentDivision 3,
        SecretiveHallCondition (acceptableChoiceFamily (forgetTolerance prefs) d)) :
    threeRoommates_secretiveRentalHarmony_statement := by
  intro prefs
  rcases h prefs with ⟨d, hd⟩
  exact hasSecretiveEnvyFreeDivision_of_secretiveHallCondition
    (prefs := forgetTolerance prefs) d hd

end HallReductions

section Section5

/--
Paper Section 5: a face-preserving piecewise-linear map has a subdivision facet whose image
contains the barycenter of the ambient simplex.
-/
def exists_barycenterPreimageCell_of_facePreservingMap_statement (dimension : ℕ) : Prop :=
  ∀ {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (φ : PiecewiseLinearSimplexMap T),
      ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap

end Section5

section GeometricReductions

/--
Paper Section 5 reduces to surjectivity of the actual piecewise-linear simplex map.
-/
theorem facetImageContainsBarycenter_of_surjective
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (φ : PiecewiseLinearSimplexMap T)
    (h : Function.Surjective φ.toFun) :
    ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap := by
  rcases h (barycentricRentDivision (dimension + 1)) with ⟨x, hx⟩
  rcases φ.map_mem_facetImage x with ⟨σ, hσ, -, himage⟩
  refine ⟨σ, hσ, ?_⟩
  dsimp [FacetImageContainsBarycenter]
  simpa [hx] using himage

/--
Paper Section 5: once the global surjectivity statement is available, the barycenter-cell
statement follows immediately.
-/
theorem exists_barycenterPreimageCell_of_surjectiveStatement
    (dimension : ℕ)
    (h : @facePreservingMap_surjective_statement.{u} dimension) :
    @exists_barycenterPreimageCell_of_facePreservingMap_statement.{u} dimension := by
  intro Vertex _ _ T φ
  exact facetImageContainsBarycenter_of_surjective T φ (@h Vertex _ _ T φ)

/--
Paper Section 2: a barycenter-containing facet for the Sperner label map is automatically fully
labeled.
-/
theorem fullyLabeledFacet_exists_of_barycenterPreimage
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (L : SpernerLabeling T)
    (h : ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ (spernerVertexMap L).vertexMap) :
    ∃ σ ∈ T.facets, FullyLabeledFacet σ L.label := by
  rcases h with ⟨σ, hσfacet, hσbary⟩
  exact ⟨σ, hσfacet, fullyLabeledFacet_of_barycenter_mem_spernerImage L σ hσbary⟩

/--
If the Sperner vertex map extends to a surjective piecewise-linear simplex map, then one facet is
fully labeled.
-/
theorem fullyLabeledFacet_exists_of_surjective
    {dimension : ℕ} {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (L : SpernerLabeling T)
    (φ : PiecewiseLinearSimplexMap T) (hvertex : φ.vertexMap = (spernerVertexMap L).vertexMap)
    (h : Function.Surjective φ.toFun) :
    ∃ σ ∈ T.facets, FullyLabeledFacet σ L.label :=
  fullyLabeledFacet_exists_of_barycenterPreimage T L
    (by simpa [hvertex] using facetImageContainsBarycenter_of_surjective T φ h)

/--
Paper Section 2 reduces to two internal ingredients:
surjectivity of the face-preserving simplex maps, and existence of a piecewise-linear extension of
the Sperner vertex map.
-/
theorem sperner_exists_fully_labeled_simplex_of_surjectiveStatement
    (dimension : ℕ)
    (hSurj : @facePreservingMap_surjective_statement.{u} dimension)
    (hExt : ∀ {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
      (T : SimplicialSubdivision dimension Vertex) (L : SpernerLabeling T),
      ∃ φ : PiecewiseLinearSimplexMap T, φ.vertexMap = (spernerVertexMap L).vertexMap) :
    @sperner_exists_fully_labeled_simplex_statement.{u} dimension := by
  intro Vertex _ _ T L
  rcases hExt T L with ⟨φ, hvertex⟩
  exact fullyLabeledFacet_exists_of_surjective T L φ hvertex (@hSurj Vertex _ _ T φ)

end GeometricReductions

section Section6

/--
Paper Section 6, first theorem: one facet captures a generic point in the scaled simplex by the
convex hull of its label-count points.
-/
def multiLabeling_convexHullWitness_statement (m dimension : ℕ) : Prop :=
  ∀ {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (L : Fin m → SpernerLabeling T)
    (y : ScaledSimplexPoint m dimension),
      GenericScaledSimplexPoint y →
      ∃ σ ∈ T.facets,
        ((y.1 : RealPoint dimension) ∈
          convexHull ℝ (facetLabelCountPoints σ (fun j v ↦ (L j).label v)))

/--
Paper Section 6, second theorem: if `k_1 + ... + k_m = dimension + m`, then one facet exhibits at
least `k_j` distinct labels in the `j`th labeling for every `j`.
-/
def weightedLabeling_distinctLabelLowerBound_statement (m dimension : ℕ) : Prop :=
  ∀ {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (L : Fin m → SpernerLabeling T)
    (k : Fin m → ℕ),
      (∀ j, 0 < k j) →
      (∑ j, k j = dimension + m) →
      ∃ σ ∈ T.facets, ∀ j, k j ≤ DistinctLabelCount σ (L j).label

end Section6

end RentalHarmony
