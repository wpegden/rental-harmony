# Formalization Plan

## Scope
- Formalize the paper's main theorem (`Theorem~\ref{thm:secret}`) and the two multiple-labeling
  generalizations from Section 6.
- Keep the paper's three layers visible in Lean:
  simplex geometry/topology, combinatorial label counting, and Hall-style matching consequences.
- Reuse mathlib for standard-simplex facts and Hall's marriage theorem rather than reproving them.

## Core modeling choices
- Rooms: `Fin n`.
- Rent divisions: points of `stdSimplex ℝ (Fin n)`.
  This matches the paper's coordinate model directly and gives a ready-made barycenter.
- Known preferences: a relation `Accepts : RentDivision n → Fin n → Prop`.
- Paper assumptions to record explicitly:
  - every rent division has at least one acceptable room;
  - free rooms beat positive-price rooms;
  - indifference among free rooms;
  - the paper's "one-cent tolerance" should become a separate local-constancy / finite-scale
    assumption once triangulations are introduced.
- Keep two geometric interfaces separate:
  - rent divisions live in `stdSimplex`;
  - explicit simplices / barycentric facts can use `Affine.Simplex` if that becomes more convenient
    for subdivision cells.
- Revision forced by proof work:
  the current abstract subdivision API recording only `facets` and allowed boundary labels is not
  sufficient for the Section 2 / Section 5 existence theorems. The repaired interface must encode
  actual geometric realization data for subdivision vertices/cells, or an equivalent covering
  theorem for affine-on-cell maps.
  This repair is now in place via geometric vertex positions, simplex-cover data, and an actual
  `PiecewiseLinearSimplexMap`.
- Further revision forced by the extension proof:
  `boundaryFace` must record the exact outer face determined by zero coordinates, not merely a
  superset of allowed labels, and a `PiecewiseLinearSimplexMap` must record its actual vertex
  values. Without those two fields, even the 1-dimensional Section 2 statement is false.
- Further revision forced by the extension proof:
  subdivision vertices must have unique geometric positions. Otherwise two distinct interior
  vertices may occupy the same point and receive different Sperner labels, making any actual
  extension map impossible at that shared point.
- Further revision forced by the extension proof:
  every subdivision vertex must lie in some full-dimensional facet. Otherwise the `map_vertex`
  field can force a value at an isolated vertex that is not contained in the image simplex of any
  facet through that geometric point, so the extension lemma is again false.

## Mathlib dependencies to reuse
- `Mathlib.Analysis.Convex.StdSimplex`
  - `stdSimplex`, its convexity/compactness facts, `stdSimplex.map`, and
    `stdSimplex.barycenter`.
- `Mathlib.LinearAlgebra.AffineSpace.Simplex.*`
  - useful if we need affine-simplex centroid facts instead of coordinate-wise simplex points.
- `Mathlib.Combinatorics.Hall.Basic`
  - Hall's theorem for relations / finite families.
- `Mathlib.Combinatorics.SimpleGraph.Hall`
  - optional graph-flavored Hall interface if the matching step is more convenient that way.
- Basic finite combinatorics from `Fin`, `Fintype`, `Finset`, `Set.ncard`, and injective maps.

## Planned Lean files
- `PaperDefinitions.lean`
  - reviewer-facing statement file for room/rent/preference objects and the subdivision API.
- `PaperTheorems.lean`
  - reviewer-facing statement file for the paper's theorem propositions and first Hall lemmas.
- `RentalHarmony/PaperDefinitions.lean` and `RentalHarmony/PaperTheorems.lean`
  - thin library wrappers importing the root statement files.
- Probable later support files:
  - `RentalHarmony/Sperner.lean`
  - `RentalHarmony/Secretive.lean`
  - `RentalHarmony/Algorithm.lean`
  - `RentalHarmony/Generalizations.lean`

## Statement prerequisites
### Section 2: Sperner core
- Define a finite triangulation interface for the standard simplex.
- Define Sperner labelings relative to the outer simplex.
- Define the label-induced map / averaged map on subdivision simplices.
- Prove a surjectivity theorem for simplex self-maps that preserve faces setwise.
- Deduce existence of a fully labeled cell from the barycenter preimage.

### Section 3: `n = 3` secretive roommate
- Formalize the `9 -> 3` label-compression lemma from the paper's first proof.
- Prove that a cell carrying all three compressed labels yields the two-roommate Hall condition for
  the two remaining rooms.
- Keep this combinatorial consequence separate from the geometric existence lemma.

### Section 4: general `n`
- Formalize the cyclic boundary relabeling turning free-room choices into a Sperner labeling.
- Prove the key counting lemma:
  any `k` known roommates exhibit at least `k + 1` labels on the barycenter cell.
- Feed that counting lemma into Hall's theorem to obtain the secretive-roommate theorem.

### Section 5: algorithmic aspects
- Treat this as secondary until the main existence statements are in place.
- Preferred route:
  prove a reusable face-preserving surjectivity theorem and derive the algorithm later.
- Fallback route:
  formalize the paper's graph/path-following proof as a self-contained lemma.

### Section 6: multiple Sperner labelings
- First theorem:
  sum label maps into a lattice-point-valued simplex, apply the same barycenter/cell existence
  result, and extract the convex-hull witness.
- Second theorem:
  formalize the weighted-average argument with the `β_ij` counting lemma and again reuse the
  face-preserving surjectivity theorem.

## Dependency order
1. simplex/rent-division representation and preference assumptions
2. Hall-facing combinatorics for assigning rooms once label counts are known
3. abstract "balanced cell" consequences for Sections 3, 4, and 6
4. surjectivity / barycenter-preimage theorem for facewise-fixed simplex maps
5. main secretive-roommate theorem
6. Sperner and multiple-labeling corollaries
7. optional algorithmic extraction from Section 5

## Proof roadmap
### Main theorem
- Build `n - 1` label maps from the known roommates.
- Apply the cyclic boundary relabeling from the paper-check notes.
- Average the maps and find a cell containing a preimage of the barycenter.
- Prove the label-count growth lemma on that cell.
- Convert label-count growth into Hall's condition after the secretive roommate chooses a room.

### Surjectivity subproblem
- First attempt: prove a local theorem for continuous/affine-on-cells maps that preserve each face
  of the standard simplex setwise.
- If the topological route is awkward, switch to the paper's combinatorial path-following proof.
- Do not introduce axioms: this surjectivity lemma is the main internal theorem to supply.

### Generalizations
- Reuse the same balanced-cell existence result.
- Keep the lattice-point and weighted-average arguments finite and combinatorial after that point.

## Immediate next steps
- Use the new `exists_facet_weights` lemma in `RentalHarmony/Sperner.lean` to turn a
  `FacetContainsPoint` witness into an explicit center-of-mass formula on one facet.
- Use the new `vertex_in_some_facet` field and `exists_incident_facet_for_sperner_vertex` lemma to
  handle the vertex branch of the canonical Sperner extension.
- Prove that the corresponding center of mass of the labeled simplex vertices stays in the correct
  boundary face, giving the missing non-vertex facet-image point for the Sperner extension.
- Prove the actual `facePreservingMap_surjective_statement` for `PiecewiseLinearSimplexMap`.
- Prove the remaining Section 2 extension lemma:
  every Sperner labeling should admit a `PiecewiseLinearSimplexMap` whose vertex map is
  `spernerVertexMap L`.
- Feed those two ingredients into the now-proved statement-level wrappers in
  `PaperTheorems.lean` to obtain the barycenter-cell and Sperner statements.
- Turn the Hall witness wrapper theorems into actual proofs by extracting the paper's
  `k + 1`-labels-for-`k`-agents counting lemma from the geometric cell.

## Current input status
- No proposed axioms.
- No human input is required at the moment.
