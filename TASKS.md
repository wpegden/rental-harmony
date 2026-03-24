# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [x] Create `PaperDefinitions.lean` with the definitions needed to state the paper results.
- [x] Create `PaperTheorems.lean` with theorem statements as close to the paper as Lean allows.
- [x] Keep the files easy for a human to compare against the paper.
- [x] Make both files syntactically valid Lean.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [ ] Prove the statement wrappers in `PaperTheorems.lean` from the Hall lemmas and future Sperner/surjectivity results.
- [ ] Build the geometric side of the theory: subdivision cells, barycenter-containing facets, and face-preserving maps.
- [ ] Connect the Section 6 lattice-point statements to actual label-count arguments.

## Completed
- [x] Created root-level `PaperDefinitions.lean` and `PaperTheorems.lean` as the reviewer-facing statement files.
- [x] Extended the definition API with Hall conditions, secretive assignments, simplex subdivisions, Sperner labelings, and label-count points.
- [x] Replaced theorem comments by precise proposition statements and proved the initial Hall-side combinatorial lemmas.
- [x] Drafted `repo/PLAN.md` from `repo/PAPERNOTES.md`, the paper, and the current mathlib support.
- [x] Identified reusable mathlib support for the project: `stdSimplex`, simplex barycenter facts, and Hall's marriage theorem.
- [x] Added compile-clean `RentalHarmony/PaperDefinitions.lean` and `RentalHarmony/PaperTheorems.lean` skeleton modules.
- [x] Checked every section of the paper for proof gaps, hidden assumptions, and theorem dependencies.
- [x] Identified the main clarification points for formalization: the one-cent tolerance usage, the cyclic relabeling/Sperner step, and the interior-point/facet arguments.
