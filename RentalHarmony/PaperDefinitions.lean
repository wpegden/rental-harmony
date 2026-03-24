import Mathlib.Analysis.Convex.StdSimplex

/-!
# Paper Definitions

Core definitions and standing assumptions for the rental-harmony paper.

This file intentionally stays lightweight during the planning phase: it introduces the simplex-based
rent-division model and the roommate preference assumptions that are referenced throughout the
paper, while leaving triangulations and piecewise-linear maps to later files.
-/

noncomputable section

namespace RentalHarmony

/-- Bedroom indices in an `n`-bedroom apartment. -/
abbrev Room (n : ℕ) := Fin n

/-- A rent division is a point of the standard simplex on the room index type. -/
abbrev RentDivision (n : ℕ) := stdSimplex ℝ (Room n)

/-- The equal-rent point `(1 / n, ..., 1 / n)` in the standard simplex. -/
abbrev barycentricRentDivision (n : ℕ) [Nonempty (Room n)] : RentDivision n :=
  stdSimplex.barycenter

/--
A roommate's acceptable-room relation on the rent simplex.

The fields match the paper's standing assumptions, except that the "one-cent error margin"
condition will be recorded separately once triangulations are introduced.
-/
structure PreferenceProfile (n : ℕ) where
  Accepts : RentDivision n → Room n → Prop
  exists_acceptable : ∀ d, ∃ r, Accepts d r
  free_room_preferred :
    ∀ {d : RentDivision n} {free expensive : Room n},
      ((d : Room n → ℝ) free = 0) →
      0 < (d : Room n → ℝ) expensive →
      Accepts d free
  free_room_indifferent :
    ∀ {d : RentDivision n} {r s : Room n},
      ((d : Room n → ℝ) r = 0) →
      ((d : Room n → ℝ) s = 0) →
      (Accepts d r ↔ Accepts d s)

/-- The rooms acceptable to a roommate at a fixed rent division. -/
def acceptableRooms {n : ℕ} (P : PreferenceProfile n) (d : RentDivision n) : Set (Room n) :=
  {r | P.Accepts d r}

/-- The known roommates in the secretive-roommate problem. -/
abbrev KnownPreferences (n known : ℕ) := Fin known → PreferenceProfile n

end RentalHarmony
