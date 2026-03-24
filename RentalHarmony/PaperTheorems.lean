import RentalHarmony.PaperDefinitions

/-!
# Paper Theorems

Statement skeletons arranged by paper section.

During the planning phase this file records the intended declaration layout without fixing all
theorem propositions yet. The precise statements depend on the triangulation and label-map API that
will be added next.
-/

namespace RentalHarmony

section Section2

/- Paper Section 2: Sperner's lemma via face-preserving simplex maps. -/
-- Planned declarations:
-- * `facePreservingMap_surjective`
-- * `sperner_exists_fully_labeled_simplex`

end Section2

section Section3

/- Paper Section 3: the `n = 3` secretive-roommate case. -/
-- Planned declarations:
-- * `threeRoommates_compressedLabelLemma`
-- * `threeRoommates_secretiveRentalHarmony`

end Section3

section Section4

/- Paper Theorem 1.1 / Section 4: the general secretive-roommate theorem. -/
-- Planned declarations:
-- * `cyclicBoundaryRelabeling`
-- * `balancedCell_hasHallExpansion`
-- * `secretiveRentalHarmony`

end Section4

section Section5

/- Paper Section 5: algorithmic access to a barycenter-preimage cell. -/
-- Planned declarations:
-- * `exists_barycenterPreimageCell_of_facePreservingMap`
-- * `pathFollowing_findsBarycenterCell`

end Section5

section Section6

/- Paper Section 6: multiple-labeling generalizations of Sperner's lemma. -/
-- Planned declarations:
-- * `multiLabeling_convexHullWitness`
-- * `weightedLabeling_distinctLabelLowerBound`

end Section6

end RentalHarmony
