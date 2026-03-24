import Mathlib.Combinatorics.Hall.Basic
import RentalHarmony.PaperDefinitions

/-!
# Paper Theorems

Precise Lean propositions for the main claims of
`paper/arxiv-1702.07325.tex`, together with the first Hall-side combinatorial lemmas used by the
paper's general argument.
-/

noncomputable section

open scoped BigOperators

namespace RentalHarmony

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
the piecewise-linear face-preserving map built from a simplex subdivision is surjective, stated
here as every point lying in the image of some facet.
-/
def facePreservingMap_surjective_statement (dimension : ℕ) : Prop :=
  ∀ {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (φ : PiecewiseLinearVertexMap T)
    (x : RentDivision (dimension + 1)),
      ∃ σ ∈ T.facets, FacetImageContains σ φ.vertexMap x

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

section Section5

/--
Paper Section 5: a face-preserving piecewise-linear vertex map has a facet whose image contains the
barycenter of the ambient simplex.
-/
def exists_barycenterPreimageCell_of_facePreservingMap_statement (dimension : ℕ) : Prop :=
  ∀ {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    (T : SimplicialSubdivision dimension Vertex) (φ : PiecewiseLinearVertexMap T),
      ∃ σ ∈ T.facets, FacetImageContainsBarycenter σ φ.vertexMap

end Section5

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
