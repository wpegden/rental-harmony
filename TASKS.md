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
- [ ] Prove the actual milestone-chain geometric/transversality consequences that imply `Section5GraphNode.MilestoneSegmentTransversality`.
- [ ] Instantiate `Section5GraphNode.exists_terminal_of_milestoneSegmentTransversality` from the milestone-chain genericity proof to obtain the Section 5 terminal-node / barycenter-face existence statement.
- [ ] Finish the concrete `chosenMilestoneChain` transversality proof.
  Current blocker: the support-layer mismatch is now repaired, and the concrete chosen chain
  proves the corrected missing-next branch
  `missing_nextMilestone_openCrossing_or_contains_lowerMilestone`. The remaining work is to turn
  that lower-endpoint containment alternative into an actual codimension-`1` lower-prefix subface
  witness. Once such a subface is available, the new abstract bridge lemmas
  `exists_verticalAdj_of_codimOneSubface_contains_lowerMilestone` and
  `exists_graphNeighbor_of_codimOneSubface_contains_lowerMilestone` convert it into the needed
  vertical door / graph neighbor and the remaining two-neighbor packaging. The new reduction lemma
  `exists_codimOneSubface_contains_lowerMilestone_of_subset` shows that it is already enough to
  find a proper carrier subset of size at most `k + 1` whose image convex hull contains the lower
  milestone. The new theorem
  `exists_subset_contains_lowerMilestone_of_exists_upperCoord_ne_zero`
  (and its corollary
  `exists_codimOneSubface_contains_lowerMilestone_of_exists_upperCoord_ne_zero`)
  now discharge the whole subcase where some image vertex still has nonzero next-coordinate: then a
  codimension-`1` supporting face already exists. So the remaining geometric difficulty is now
  strictly sharper: handle only the complementary case where every image vertex of the positive face
  already lies in the lower target prefix face, and from that deduce a codimension-`1`
  lower-prefix supporting subface in the domain. The ambient transport step is now done:
  `PrefixFace.padLinear`, `PrefixFace.mem_affineSpan_prefixVertexFinset`, and
  `exists_subset_contains_lowerMilestone_of_all_imageVertices_lowerPrefix`
  formalize the target-side Carathéodory reduction for that all-image-lower case. So the remaining
  blocker is now purely domain-side and even sharper than before: produce a large enough
  lower-prefix carrier set in the domain, because the exact-cardinality bookkeeping is now
  packaged separately. The new theorems
  `exists_graphNeighbor_of_lowerPrefixSubset_contains_lowerMilestone`
  and
  `exists_graphNeighbor_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone`
  show that once a milestone-carrying support sits inside a lower-prefix carrier set of size at
  least `k + 1`, the codimension-`1`/vertical-door machinery finishes the neighbor construction.
  After rereading paper lines 385-393, the graph-side fork is now settled: the vertical edge is
  still an edge in `G`, so the lower face must itself be one of the previously declared graph
  vertices and therefore still satisfy the lower-prefix condition. So the remaining work is
  precisely to prove that such a large lower-prefix carrier set exists in the complementary
  all-image-lower case. The sharpened missing lemma is no longer graph-theoretic: it is a
  domain-side preimage/local-affinity statement showing that if a face image contains the lower
  milestone, then some actual preimage point in that face has barycentric support contained in the
  lower prefix face, yielding at least `k + 1` lower-prefix carrier vertices. Current exact
  obstacle: the existing `SimplicialSubdivision` API still does not prove that a point known to
  lie in the convex hull of a specified face or facet has its global `baryCoord` support inside
  that chosen face or facet, so the desired `SubdivisionFace.ImageContains -> ∃ x, φ.toFun x = ...`
  theorem is not yet derivable from the present local-barycentric infrastructure.
- [ ] Use the repaired extension theorem together with surjectivity to obtain the Section 5 barycenter-cell and Section 2 Sperner statements directly.
- [ ] Close the higher-dimensional contradiction.
  Current blocker: the topological route now needs a genuine noncontractibility theorem for
  `SimplexBoundary dimension`. The combinatorial route is now the active route, and its remaining
  blocker is now sharper: the parity argument is done, the graph has been repaired to use a
  generic milestone chain, and the local degree consequences are formalized abstractly as
  `Section5GraphNode.LocalDegreeHypotheses`, but the actual milestone-chain genericity proof that
  supplies those hypotheses is still open.
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
- [x] Proved the pure finite-graph parity backbone for the Section 5 combinatorial proof:
  if the start node has odd degree and every nonterminal node has even degree, then a terminal
  node exists.
- [x] Repaired the Section 5 graph support so it is parameterized by a generic
  `Section5MilestoneChain` instead of the exact prefix barycenters, keeping the start at `e_1`
  and the terminal target at the true simplex barycenter while allowing generic intermediate
  milestone points.
- [x] Added `Section5GraphNode.LocalDegreeHypotheses` and proved from it that the start node has
  odd degree and each nonterminal positive node has even degree.
- [x] Connected the local degree package to the finite-graph parity theorem via
  `Section5GraphNode.exists_terminal_of_localDegreeHypotheses`, so the remaining Section 5 gap is
  only the geometric proof of `LocalDegreeHypotheses`.
- [x] Added the case-split Section 5 genericity layer
  `Section5GraphNode.GeometricGenericity`, proved
  `Section5GraphNode.localDegreeHypotheses_of_geometricGenericity`, and derived the terminal-node
  wrapper `Section5GraphNode.exists_terminal_of_geometricGenericity`.
- [x] Added concrete milestone-segment transversality predicates
  `SubdivisionFace.ImageMeetsOpenMilestoneSegment` and
  `SubdivisionFace.ImageContainsMilestoneAwayFromBoundary`, together with the stronger support-layer
  package `Section5GraphNode.MilestoneSegmentTransversality` and the wrapper
  `Section5GraphNode.exists_terminal_of_milestoneSegmentTransversality`.
- [x] Built the explicit prefix-face equivalence in `RentalHarmony/Section5Graph.lean`:
  `PrefixFace.restrict`, `PrefixFace.pad`, and `PrefixFace.equivRentDivision` identify
  `PrefixFace k` with `RentDivision (k + 1)`.
- [x] Proved the finite-union avoidance theorem for proper affine subspaces in finite-dimensional
  affine spaces, and specialized it to the relative interior of the smaller simplex
  `RentDivision (k + 1)`.
- [x] Upgraded the smaller-simplex avoidance theorem to the actual convex-hull input needed for
  milestone perturbations: a finite family of convex hulls generated by at most `k` points can be
  avoided in the relative interior of `RentDivision (k + 1)`.
- [x] Transported the smaller-simplex convex-hull avoidance theorem back to ambient prefix faces:
  `PrefixFace.exists_smallPointInterior_not_mem_biUnion_convexHull_of_card_le` now chooses a
  prefix-face point whose restricted smaller-simplex coordinates lie in relative interior and whose
  ambient point avoids any finite family of convex hulls generated by at most `k` prefix-face
  points.
- [x] Defined the actual levelwise Section 5 forbidden families
  `milestoneForbiddenFaces` / `milestoneForbiddenFamily` from lower-dimensional face images inside
  each prefix face, proved their cardinality bounds, and derived the concrete choice theorem
  `exists_prefixMilestonePoint_avoiding_forbiddenFamily`.
- [x] Assembled those levelwise choices into the concrete Section 5 milestone object
  `chosenMilestoneChain`, with fixed start point `e_1`, fixed terminal barycenter, and chosen
  intermediate prefix-face milestones.
- [x] Proved the nonterminal away-from-boundary half of the concrete Section 5 transversality
  goal for `chosenMilestoneChain`:
  `chosenMilestoneChain_nextMilestoneAwayFromBoundary_of_nonterminal` now turns the forbidden-family
  avoidance theorem into the `ImageContainsMilestoneAwayFromBoundary` conclusion needed for the
  vertical-door side of the graph argument.
- [x] Reduced the remaining concrete open-segment goal to endpoint exclusion:
  `imageMeetsOpenMilestoneSegment_of_meets_of_not_containsMilestones`
  and
  `chosenMilestoneChain_openSegment_of_missingNextMilestone_of_not_lowerMilestone`
  isolate the exact missing statement as lower-milestone noncontainment.
- [x] Repaired the missing-next transversality field so it matches the paper's local geometry:
  `Section5GraphNode.MilestoneSegmentTransversality` now allows either an open crossing or lower
  milestone containment in the missing-next case, and
  `chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone`
  proves that corrected branch for the concrete chosen chain.
- [x] Added the abstract vertical-door bridge lemmas
  `exists_verticalAdj_of_codimOneSubface_contains_lowerMilestone` and
  `exists_graphNeighbor_of_codimOneSubface_contains_lowerMilestone`, which turn a codimension-`1`
  lower-prefix subface carrying the lower milestone into an actual graph neighbor in the Section 5
  graph.
- [x] Added the codimension-`1` support-reduction lemma
  `exists_codimOneSubface_contains_lowerMilestone_of_subset`, which erases one unused vertex once
  the lower milestone is known to lie in the image convex hull of a proper carrier subset.
- [x] Proved the ambient prefix-face affine-span transport and the target-side Carathéodory
  reduction for the complementary all-image-lower lower-door case:
  `PrefixFace.padLinear`, `PrefixFace.mem_affineSpan_prefixVertexFinset`,
  `affineIndependent_prefixVertexFinset`, and
  `exists_subset_contains_lowerMilestone_of_all_imageVertices_lowerPrefix`.
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
