# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [x] Use `repo/paper/arxiv-1702.07325.tex`, `PAPERNOTES.md`, and the current repo state to build `PLAN.md`.
- [x] Produce a comprehensive roadmap for definitions, theorem statements, and proof dependencies.
- [x] Identify what can come from mathlib versus what must be formalized here.
- [x] Use `NEED_INPUT` for external-result or design-choice questions that need a human decision.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [ ] Turn the theorem comments in `RentalHarmony/PaperTheorems.lean` into precise Lean propositions.
- [ ] Implement the Hall-side combinatorial lemmas that convert label counts into envy-free assignments.
- [ ] Build the local triangulation / face-preserving map interface used by the Sperner arguments.

## Completed
- [x] Drafted `repo/PLAN.md` from `repo/PAPERNOTES.md`, the paper, and the current mathlib support.
- [x] Identified reusable mathlib support for the project: `stdSimplex`, simplex barycenter facts, and Hall's marriage theorem.
- [x] Added compile-clean `RentalHarmony/PaperDefinitions.lean` and `RentalHarmony/PaperTheorems.lean` skeleton modules.
- [x] Checked every section of the paper for proof gaps, hidden assumptions, and theorem dependencies.
- [x] Identified the main clarification points for formalization: the one-cent tolerance usage, the cyclic relabeling/Sperner step, and the interior-point/facet arguments.
