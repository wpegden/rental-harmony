# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [ ] Prove the target statements presented in `PaperTheorems.lean`.
- [ ] Keep reusable proof infrastructure in separate support files when that yields a cleaner project structure.
- [ ] Maintain `TASKS.md` and `PLAN.md` as the proof frontier moves.
- [ ] Keep sorrys within the configured policy.
- [ ] Do not introduce unapproved axioms.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [ ] Prove the actual Section 5 surjectivity theorem for the barycentric-coordinate `PiecewiseLinearSimplexMap`.
- [ ] Prove the Section 5 graph path/parity lemma on the now-defined `Section5GraphNode` / `Section5GraphNode.graph`.
- [ ] Use the repaired extension theorem together with surjectivity to obtain the Section 5 barycenter-cell and Section 2 Sperner statements directly.
- [ ] Close the higher-dimensional contradiction.
  Current blocker: the topological route now needs a genuine noncontractibility theorem for
  `SimplexBoundary dimension`. The combinatorial route is now the active route, and its remaining
  blocker is the actual graph/path-following proof rather than missing face-poset or graph-definition support.
- [ ] Produce the Hall witnesses promised by the new wrapper theorems from the geometric label-count arguments.
- [ ] Connect the Section 6 lattice-point statements to actual label-count arguments.

## Completed
- [x] Added `RentalHarmony/Section5Graph.lean` with a lower-dimensional face-poset API:
  `SubdivisionFace`, nonempty subface closure, face geometry/image predicates, and codimension-`1`
  incidence lemmas.
- [x] Added the paper's prefix-face barycenters and segment-intersection predicates in
  `RentalHarmony/Section5Graph.lean`, so the Section 5 graph can now be stated directly in terms
  of faces whose images meet the segments `[b_{k-1}, b_k]`.
- [x] Defined the actual Section 5 graph object in `RentalHarmony/Section5Graph.lean`:
  `Section5PositiveNode`, `Section5GraphNode`, the horizontal/vertical/start adjacency predicates,
  and the resulting `SimpleGraph` `Section5GraphNode.graph`.
- [x] Built the explicit continuous barycenter-omission map from the simplex to `SimplexBoundary` and proved `boundary_contractible_of_omits_barycenter`.
- [x] Restricted face-preserving simplex maps and their straight-line homotopies to the boundary subtype, and packaged the resulting topological reduction theorem `boundary_contractible_of_nullhomotopic_boundaryExtension`.
- [x] Recorded the current higher-dimensional Section 5 blocker precisely: no ready-made
  noncontractibility theorem for `SimplexBoundary dimension` was found in the installed mathlib,
  and the paper's alternate graph proof would require a lower-dimensional face-incidence API that
  is not yet present in the current support layer.
- [x] Added the straight-line homotopy from `id` to any `PiecewiseLinearSimplexMap`, and proved every intermediate map still preserves boundary faces setwise.
- [x] Proved the dimension-1 Section 5 surjectivity theorem by transporting `PiecewiseLinearSimplexMap` to `unitInterval` and applying the intermediate value theorem.
- [x] Instantiated the Section 5 barycenter-cell and Section 2 Sperner wrapper theorems in dimension `1`.
- [x] Replaced the weak arbitrary-function `PiecewiseLinearSimplexMap` interface by a barycentric-coordinate model where `toFun` is the derived center of mass of the vertex images.
- [x] Refactored `SimplicialSubdivision` to carry global continuous barycentric-coordinate functions together with a chosen supporting facet.
- [x] Reproved the canonical Sperner extension for the repaired derived-map interface.
- [x] Proved the basic derived-map infrastructure for the new interface: vertex interpolation, facet-image witnesses, continuity, and boundary-face preservation.
- [x] Proved the canonical Sperner extension theorem: every Sperner labeling extends to a `PiecewiseLinearSimplexMap` with vertex map `spernerVertexMap L`.
- [x] Identified and repaired a fourth geometric interface bug: every subdivision vertex must belong to some facet, and added the corresponding incident-facet helper lemma for Sperner vertices.
- [x] Proved a reusable convex-combination lemma extracting facet weights from `FacetContainsPoint`.
- [x] Identified and repaired a third geometric interface bug: duplicated geometric vertices make the Sperner extension lemma false, so `vertexPos` must be injective.
- [x] Identified and repaired a second geometric interface bug: `boundaryFace` must describe the exact simplex face, and `PiecewiseLinearSimplexMap` must record its vertex values.
- [x] Reconnected the global Section 5 / Section 2 statement aliases to the proved local geometric reductions, after fixing the universe-polymorphic wrapper issue.
- [x] Identified a concrete 1-dimensional counterexample showing the current abstract subdivision / vertex-map API is too weak for the Section 2 and Section 5 existence statements.
- [x] Repaired the geometric interface by adding geometric vertex positions, simplex-cover data, and an actual `PiecewiseLinearSimplexMap`.
- [x] Added `RentalHarmony/Sperner.lean` with the first reusable geometric infrastructure for the Sperner map.
- [x] Proved the local geometric reductions: a facet-covering hypothesis gives a barycenter cell, and a barycenter cell for the Sperner map gives a fully labeled facet.
- [x] Added Hall-side wrapper theorems reducing the rental-harmony statements to secretive Hall witnesses.
- [x] Created root-level `PaperDefinitions.lean` and `PaperTheorems.lean` as the reviewer-facing statement files.
- [x] Added an explicit tolerance-profile structure so the paper's one-cent hypothesis now appears in the rental-harmony statements.
- [x] Tightened the surjectivity wrapper to the paper-facing piecewise-linear facet-image formulation.
- [x] Extended the definition API with Hall conditions, secretive assignments, simplex subdivisions, Sperner labelings, and label-count points.
- [x] Replaced theorem comments by precise proposition statements and proved the initial Hall-side combinatorial lemmas.
- [x] Drafted `repo/PLAN.md` from `repo/PAPERNOTES.md`, the paper, and the current mathlib support.
- [x] Identified reusable mathlib support for the project: `stdSimplex`, simplex barycenter facts, and Hall's marriage theorem.
- [x] Added compile-clean `RentalHarmony/PaperDefinitions.lean` and `RentalHarmony/PaperTheorems.lean` skeleton modules.
- [x] Checked every section of the paper for proof gaps, hidden assumptions, and theorem dependencies.
- [x] Identified the main clarification points for formalization: the one-cent tolerance usage, the cyclic relabeling/Sperner step, and the interior-point/facet arguments.
