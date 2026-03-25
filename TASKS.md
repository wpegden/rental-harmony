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
- [ ] Route-changed next-milestone entrance frontier:
  `exists_codimOneSubface_meets_segment_of_contains_lowerMilestone_of_largeLowerPrefixCarrierSpec`
  now discharges the lower-milestone-present subcase of the entrance-face theorem from the
  existing large-lower-prefix carrier API, and
  `chosenMilestoneChainNextMilestoneEntranceFaceSpec_of_largeLowerPrefixCarrier_and_endpointEntrance`
  reduces the full next-milestone entrance package to one exact complementary local bridge:
  `ChosenMilestoneChainNextMilestoneEndpointEntranceFaceSpec.
  exists_codimOneSubface_meets_segment_of_nextMilestone_awayFromBoundary_and_not_contains_lowerMilestone`.
  The new theorem
  `affineIndependent_image_of_imageContainsMilestoneAwayFromBoundary` now sharpens that endpoint
  case further: away-from-boundary at `b_k` already forces the image vertices of `σ` to form an
  affine-independent simplex, and
  the companion carrier-indexed theorems
  `affineIndependent_carrierImage_of_imageContainsPointAwayFromBoundary` and
  `affineIndependent_carrierImage_of_imageContainsMilestoneAwayFromBoundary`
  put the same fact in the exact indexing format needed for local face-wise simplex arguments.
  The stronger barycentric-coordinate / affine-basis packaging was tested but is not part of the
  checked frontier yet; the surviving Lean reduction is still the affine-independence step itself.
  Consequently,
  `chosenMilestoneChainNextMilestoneAffineIndependentEndpointEntrySpec_of_carrierAffineIndependentEndpointEntry`
  now converts a carrier-indexed local theorem directly into the older image-indexed endpoint
  statement, so future local simplex-entry work can stay in the more natural carrier format.
  Concretely, the exact remaining theorem can now be treated as
  `ChosenMilestoneChainNextMilestoneCarrierAffineIndependentEndpointEntrySpec.
  exists_codimOneSubface_meets_segment_of_affineIndependentCarrierImage_of_nextMilestone_awayFromBoundary_and_not_contains_lowerMilestone`,
  with the image-indexed spec retained only as a compatibility wrapper.
  Consequently,
  `chosenMilestoneChainNextMilestoneEndpointEntranceFaceSpec_of_affineIndependentEndpointEntry`
  reduces the remaining local geometry to the affine-simplex entry statement
  `ChosenMilestoneChainNextMilestoneAffineIndependentEndpointEntrySpec.
  exists_codimOneSubface_meets_segment_of_affineIndependentImage_of_nextMilestone_awayFromBoundary_and_not_contains_lowerMilestone`.
  So the first unresolved route-changed next-milestone theorem is no longer the whole entrance-face
  package, nor even the full endpoint-entry case, but specifically the affine-independent
  endpoint-entry case where `b_k` lies away from the boundary of `λ(σ)` and `σ` does not already
  contain `b_{k-1}`. After that, the second bridge remains
  `ChosenMilestoneChainNextMilestoneAmbientFacetFreshPrefixVertexSpec.
  exists_freshPrefixVertex_in_ambientFacet_of_entranceCarrier`.
- [ ] Exact higher-dimensional deleted-spur frontier:
  prove the two fields of
  `Section5GraphNode.ChosenMilestoneChainDeletedSpurNoEscapeSpec`.
  The parity restart and the terminal-extraction wrapper are now formalized, via
  `exists_terminal_of_positiveContinuationNeighbor_of_deletedSpurNoEscapeSpec_of_alternativeSpecs`
  and
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_deletedSpurNoEscapeSpec_of_two_lt_dimension`.
  So the remaining Section 5 backup-route work is no longer to build another graph theorem, but to
  prove exactly:
  `ChosenMilestoneChainDeletedSpurNoEscapeSpec.no_start_of_positiveContinuationNeighbor`
  and
  `ChosenMilestoneChainDeletedSpurNoEscapeSpec.no_boundaryOnlyUniqueCarrierCounterexampleNode_of_positiveContinuationNeighbor`.
  The new theorem
  `exists_terminal_of_positiveContinuationNeighbor_of_alternativeSpecs_of_belowTopDimPositiveTerminalSpec`
  now shows that both escape branches already collapse to the direct route
  `ChosenMilestoneChainBelowTopDimPositiveTerminalSpec.exists_terminal_of_positive_belowTopDim`.
  After the latest proof search, the first local statement that still does not crystallize from
  the current reduced-graph/component API is exactly
  `ChosenMilestoneChainDeletedSpurNoEscapeSpec.no_start_of_positiveContinuationNeighbor`.
  Unless the obstruction-exclusion field turns out to be substantially easier, this is now
  evidence that the direct-route theorem is the genuine remaining frontier and the deleted-spur
  no-escape fields are only alternate reformulations of that gap.
  The direct route is now sharper in Lean as well, but the original
  `ChosenMilestoneChainBelowTopDimPositiveLevelDescentSpec` turned out to be too strong at level
  `0`: a level-`0` positive node cannot have a lower positive neighbor. The realistic direct-route
  reduction is now
  `ChosenMilestoneChainBelowTopDimPositiveBaseCaseAndLevelDescentSpec`, with
  `chosenMilestoneChainBelowTopDimPositiveTerminalSpec_of_baseCaseAndLevelDescent` proving the
  global below-top-dimensional terminal theorem from:
  a separate level-`0` base case, plus strict lower-level positive continuation only at positive
  levels. The positive-level continuation theorem is now split further by
  `chosenMilestoneChainBelowTopDimPositiveBaseCaseAndLevelDescentSpec_of_largeLowerPrefixCarrierSpec_and_caseSplit`:
  the positive-level missing-next/no-open-crossing branch is already discharged by
  `exists_lowerLevel_positive_of_missingNextMilestone_positiveLevel_of_not_openCrossing_of_largeLowerPrefixCarrierSpec`.
  The new support lemmas `not_adj_positive_start_of_level_pos`,
  `level_relation_of_adj_positive_positive`, and
  `exists_two_distinct_positiveNeighbors_of_not_terminal_positiveLevel_belowTopDim_of_alternativeSpecs`
  show that in the remaining positive-level branches the current API already yields two distinct
  positive neighbors and only lacks a way to choose one with smaller level.
  After the latest proof search, the direct-route obstruction is sharper than a mere
  “choose the right neighbor” problem. The new lemmas
  `exists_lowerLevel_positive_of_contains_lowerMilestone_of_largeLowerPrefixCarrierSpec`,
  `not_exists_lowerLevel_positiveAdj_of_not_contains_lowerMilestone`, and
  `not_exists_lowerLevel_positive_of_not_contains_lowerMilestone`
  show that strict descent is available exactly when the current face contains the lower
  milestone, and impossible otherwise. So the first exact unresolved positive-level subcase is
  still
  `ChosenMilestoneChainBelowTopDimPositiveBaseCaseAndCaseSplitDescentSpec.exists_lowerLevel_positive_of_nextMilestone_not_terminal_belowTopDim`,
  but now in the more precise form: no current theorem derives
  `ξ.face.ImageContainsMilestone ... ξ.level.castSucc` from the next-milestone away-from-boundary
  hypotheses. The corresponding open-crossing branch has the same shape. The support layer now
  packages this exact sharper frontier as
  `ChosenMilestoneChainBelowTopDimPositiveBaseCaseAndCaseSplitLowerMilestoneSpec`, and
  `chosenMilestoneChainBelowTopDimPositiveBaseCaseAndCaseSplitDescentSpec_of_largeLowerPrefixCarrierSpec_and_caseSplitLowerMilestone`
  shows that proving those containment fields is sufficient for the older descent interface.
  The new theorem `contains_lowerMilestone_of_exists_lowerLevel_positive` records the converse:
  any successful strict-descent proof in these branches must first force lower-milestone
  containment. A fresh direct proof attempt of the next-milestone field still bottoms out at the
  same precise point: all available codimension-`1` / lower-carrier lemmas
  (`exists_subset_contains_lowerMilestone_of_exists_upperCoord_ne_zero`,
  `exists_codimOneSubface_contains_lowerMilestone_of_exists_upperCoord_ne_zero`,
  `exists_verticalAdj_of_contains_lowerMilestone_of_largeLowerPrefixCarrierSpec`, etc.)
  already assume lower-milestone containment and therefore cannot derive it from the
  next-milestone away-from-boundary hypotheses.
  The latest route-change experiment sharpens this further: paper lines 383--396 and the raw Lean
  definition of `ImageContainsMilestoneAwayFromBoundary` point more naturally to an entrance
  codimension-`1` face / same-level continuation witness for the segment ending at `b_k`, not to
  the stronger claim that the whole face already contains `b_{k-1}`. So
  `ChosenMilestoneChainBelowTopDimPositiveBaseCaseAndCaseSplitLowerMilestoneSpec.contains_lowerMilestone_of_nextMilestone_not_terminal_belowTopDim`
  now looks like a sufficient strengthening of the manuscript's geometry rather than its exact
  local statement. If no new geometric bridge upgrades away-from-boundary to lower-milestone
  containment, the next correction should be to replace this next-milestone field by a more
  paper-faithful entrance-door / same-level continuation theorem and rework the direct route from
  that statement instead.
  That route change is now partially formalized. The new structures
  `ChosenMilestoneChainNextMilestoneEntranceFaceSpec` and
  `ChosenMilestoneChainNextMilestoneAmbientFacetPrefixExtensionSpec` isolate the two local inputs
  suggested by paper lines 383--396: first, an entrance codimension-`1` face whose image still
  meets the same segment `[b_{k-1}, b_k]`; second, a current-prefix ambient-facet extension from
  that entrance face to a distinct same-level coface. The reduction theorem
  `chosenMilestoneChainNextMilestoneSameLevelContinuationSpec_of_entranceFace_and_prefixExtension`
  then packages these into the manuscript-faithful local consequence
  `ChosenMilestoneChainNextMilestoneSameLevelContinuationSpec`, namely a same-level horizontal
  continuation in the next-milestone-away-from-boundary branch. So the exact next-milestone
  frontier is no longer "prove lower-milestone containment directly", but rather to prove those
  entrance-face / current-prefix extension inputs and then rebuild the below-top-dimensional
  direct route from the resulting same-level continuation theorem.
  The second bridge has now been sharpened once more. The new theorem
  `exists_sameLevelPrefixFace_in_ambientFacet_of_freshPrefixVertex_of_entranceCarrier` and the
  reduction
  `chosenMilestoneChainNextMilestoneAmbientFacetPrefixExtensionSpec_of_freshPrefixVertex`
  show that the ambient-facet extension input can itself be reduced to a simpler current-prefix
  witness: given an entrance carrier `ρ`, it is enough to find one fresh ambient-facet vertex
  outside `ν.face.carrier` whose singleton still subdivides the current prefix face
  `conv{e_1, ..., e_{k+1}}`. The new theorem
  `affineIndependent_image_of_imageContainsMilestoneAwayFromBoundary` now sharpens the first
  bridge too: the remaining entrance theorem should be treated as a genuine affine-simplex entry
  problem, formalized by
  `ChosenMilestoneChainNextMilestoneAffineIndependentEndpointEntrySpec.
  exists_codimOneSubface_meets_segment_of_affineIndependentImage_of_nextMilestone_awayFromBoundary_and_not_contains_lowerMilestone`,
  rather than as unrestricted convex-hull geometry. The second bridge is still naturally viewed
  through the fresh-prefix-vertex reformulation.
  The new carrier-image simplex lemmas
  `SubdivisionFace.imageContains_of_mem_closedInterior_carrierImageSimplex`,
  `SubdivisionFace.range_faceOpposite_carrierImageSimplex_points`,
  `SubdivisionFace.mem_convexHull_range_of_mem_closedInterior`, and
  `SubdivisionFace.mem_interior_carrierImageSimplex_of_imageContainsPointAwayFromBoundary_of_pos`
  now tighten this further: in positive dimension, the away-from-boundary hypothesis at `b_k`
  literally upgrades `b_k` to an interior point of the affine simplex built from the carrier
  image of `σ`. So the first unresolved next-milestone bridge is now exactly the simplex-entry
  theorem that if `b_{k-1}` is not already in `λ(σ)` but `b_k` is an interior point of that
  carrier-image simplex, then the segment `[b_{k-1}, b_k]` meets some codimension-`1` face.
  The new theorem
  `SubdivisionFace.not_mem_closedInterior_carrierImageSimplex_of_not_imageContains`
  and the wrapper
  `chosenMilestoneChainNextMilestoneCarrierAffineIndependentEndpointEntrySpec_of_carrierImageSimplexInteriorEntry`
  now make that reduction literal inside Lean: the current endpoint-entry package is implied by
  the exact local simplex theorem
  `ChosenMilestoneChainNextMilestoneCarrierImageSimplexInteriorEntrySpec.
  exists_codimOneSubface_meets_segment_of_mem_interior_carrierImageSimplex_and_lowerMilestone_not_mem_closedInterior`.
  The exact remaining direct-route subcases are therefore:
  the level-`0` base case, the positive-level next-milestone lower-milestone-containment branch,
  and the positive-level open-crossing lower-milestone-containment branch.
- [ ] Finish the positive-level no-open-crossing support at the exact graph interface.
  Top-dimensional branch:
  stop treating
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec`
  as the exact frontier. The new obstruction theorem
  `not_exists_smaller_support_of_pair_of_mem_openSegment` shows that one-vertex-drop can fail on a
  nondegenerate two-point support inside the first codimension-`1` face image, while paper lines
  395--396 only require the local door count in the `¬ openCrossing` branch. The new reductions
  `chosenMilestoneChain_contains_lowerMilestone_of_missingNextMilestone_of_not_openCrossing`,
  `chosenMilestoneChainPositiveLevelNoOpenCrossingSpec_of_lowerMilestoneDoorSpec`, and
  `chosenMilestoneChainPositiveLevelNoOpenCrossingSpec_of_topDim_and_belowTopDim` move the exact
  top-dimensional frontier to
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec`.
  The current support-pruning chain remains a stronger sufficient route, but it is now known to be
  overkill unless the Section 5 hypotheses exclude the segment-support obstruction. The new
  theorems
  `eq_verticalNeighbor_of_adj_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly`
  and
  `not_exists_two_distinct_neighbors_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly`
  now isolate an exact compatible failure pattern for the corrected interface as well: if the
  lower-milestone codimension-`1` carrier is unique and lies in only one ambient facet, then every
  neighbor of `ν` collapses to the single canonical vertical door. So the next top-dimensional
  proof search must either derive two doors directly from the paper's lines 395--396 geometry or
  prove that this boundary-only unique-carrier pattern is excluded by the actual Section 5
  hypotheses. The new structure
  `TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData` and theorem
  `not_topDimNoOpenCrossingDoorSpec_of_boundaryOnlyUniqueCarrierCounterexampleData`
  now package this as exact compatible counterexample data for the current interface: if such data
  can actually arise from the intended genericity assumptions, then
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec` is too strong
  as stated. The new internal specs
  `ChosenMilestoneChainCodimOneFaceSegmentInteriorWitnessSpec` and
  `ChosenMilestoneChainTopDimBoundaryCarrierEscapeSpec` now isolate the exact local geometric input
  missing from Lean's current support layer: a codimension-`1` face meeting `[b_k,b_{k+1}]`
  should carry a segment point away from its own boundary, and such a point on a boundary-only
  unique carrier of a top-dimensional face should force either an open crossing or containment of
  `b_{k+1}`. Their combined theorem
  `not_boundaryOnlyUniqueCarrierCounterexampleData_of_segmentInteriorWitness_and_escape`
  shows that this witness-plus-escape pair is precisely what would kill the packaged obstruction.
  The exact downstream blocker is now formalized too. The weaker abstract package
  `LocalDegreeOrDescentHypotheses` and the chosen-chain constructor
  `chosenMilestoneChain_localDegreeOrDescentHypotheses_of_alternativeSpecs`
  show that Lean already supports a "two doors or unique forced vertical descent" continuation law.
  Meanwhile
  `not_localDegreeHypotheses_of_boundaryOnlyUniqueCarrierCounterexampleData`,
  `degree_positive_eq_one_of_boundaryOnlyUniqueCarrierCounterexampleData`, and
  `not_even_degree_of_boundaryOnlyUniqueCarrierCounterexampleData`
  show that the packaged obstruction makes a nonterminal node of graph degree `1`. So the next
  proof obligation is not another local exclusion theorem by default; it is the graph-level
  contraction/descent lemma that replaces the old even-degree use of
  `LocalDegreeHypotheses.nonterminal_two_neighbors`. The new abstract parity theorem
  `exists_terminal_or_boundary_of_odd_start_and_nonterminal_even_off_boundary` and its chosen-chain
  instantiation
  `exists_terminal_or_boundaryOnlyUniqueCarrierCounterexampleData_of_alternativeSpecs`
  now isolate the exact minimal replacement statement already supported by Lean: from the corrected
  local interface one can prove "terminal node or explicit packaged obstruction." The next step is
  still to turn that disjunction into a pure terminal-existence theorem by contracting or bypassing
  the obstruction branch. The new structure
  `ChosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec` and reduction
  `exists_terminal_of_chosenMilestoneChain_alternativeSpecs_and_bypass`
  now package that missing step as one clean theorem: given a way to consume explicit obstruction
  data, the whole chosen-chain terminal-existence argument goes through again. The new theorems
  `existsUnique_graphNeighbor_ne_counterexampleNode_of_verticalAdj_boundaryOnlyUniqueCarrierCounterexampleData`,
  `exists_terminal_of_boundaryOnlyUniqueCarrierCounterexampleData_of_exists_terminal_of_continuationNeighbor`,
  and
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_continuationNeighborTerminal`
  sharpen that frontier once more: after descending to the canonical vertical neighbor `μ`, Lean
  can now isolate a unique continuation door `w ≠ ν`. So the exact remaining bypass theorem is no
  longer "get a terminal from the vertical neighbor" but "get a terminal after following the
  continuation neighbor of that vertical descent." The new theorems
  `not_adj_positive_start_of_verticalAdj_boundaryOnlyUniqueCarrierCounterexampleData_of_two_lt_dimension`,
  `exists_terminal_of_boundaryOnlyUniqueCarrierCounterexampleData_of_exists_terminal_of_positiveContinuationNeighbor_of_two_lt_dimension`,
  and
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_positiveContinuationNeighborTerminal_of_two_lt_dimension`
  sharpen the split further: for `2 < dimension` the continuation door cannot be `.start`, so only
  a positive continuation node remains. The new theorems
  `eq_counterexampleNode_of_upperAdj_verticalNeighbor_of_boundaryOnlyUniqueCarrierCounterexampleData`
  and
  `level_lt_of_positiveContinuationNeighbor_of_verticalAdj_boundaryOnlyUniqueCarrierCounterexampleData`
  sharpen this again: the distinct continuation node after the canonical descent cannot be another
  top-dimensional upper coface, because the obstruction's unique ambient-facet hypothesis forces
  any such upper coface to be the original node `ν`. So in the higher-dimensional branch the
  continuation node is automatically positive and strictly lower-level, and
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_lowerLevelPositiveContinuationNeighborTerminal_of_two_lt_dimension`
  shows that the exact remaining bypass theorem is now a lower-level continuation statement.
  The new lemmas
  `face_dim_lt_of_positiveContinuationNeighbor_of_verticalAdj_boundaryOnlyUniqueCarrierCounterexampleData`
  and
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_belowTopDimPositiveTerminal_of_two_lt_dimension`
  sharpen that one notch further: for `2 < dimension`, it is enough to prove terminal existence
  from an arbitrary below-top-dimensional positive node. The unresolved graph-level gap is
  therefore concentrated in the residual low-dimensional start-continuation case and in supplying
  that below-top-dimensional positive-node terminal theorem. The latest restart analysis sharpens
  the likely minimal missing abstraction further: a direct parity restart from the obstruction node
  `ν` is too weak because the global odd start `.start` remains another odd vertex of the full
  graph, so the proof can escape there. The graph theorem that now looks exact is a
  component-restricted parity restart after deleting the obstruction spur `{ν, μ}` consisting of
  the degree-`1` obstruction node and its canonical vertical neighbor. In that reduced graph, the
  continuation node `ξ` should become the new odd start, and a terminal or smaller obstruction
  should follow inside its connected component. So the next proof search should either formalize
  that reduced-graph/component theorem or show that the stronger current reduction to arbitrary
  below-top-dimensional positive nodes is nevertheless derivable from the existing Section 5 local
  API. The Lean reduction is now packaged explicitly by
  `ChosenMilestoneChainBelowTopDimPositiveTerminalSpec` and
  `exists_terminal_of_chosenMilestoneChain_alternativeSpecs_of_belowTopDimPositiveTerminal_of_two_lt_dimension`:
  in dimensions `2 < dimension`, the whole remaining higher-dimensional proof is reduced to
  proving `exists_terminal_of_positive_belowTopDim`. Lean now also proves
  `degree_positive_eq_two_of_not_terminal_belowTopDim_positive_of_alternativeSpecs`, so a direct
  full-graph parity restart from an arbitrary below-top-dimensional positive node cannot work:
  such a node is even-degree unless it is already terminal. The backup component-restricted parity
  restart therefore still looks like the minimal abstract repair. The first attempted
  `ConnectedComponent` transport theorem really does break exactly at the coercion/typeclass
  mismatch between `↥C` and `↑C.supp`, so the backup route has now been repackaged without that
  wrapper: the new abstract theorem
  `exists_terminal_or_boundary_in_induce_of_odd_start_and_nonterminal_even_off_boundary`
  restarts parity directly on an induced subgraph of an arbitrary subset. So the next backup-step
  theorem is no longer a degree-transport lemma; it is to identify the connected-component support
  of the continuation node in the graph with the obstruction spur `{ν, μ}` deleted and then apply
  this induced-subgraph parity theorem there. The new wrapper theorem
  `exists_terminal_or_boundary_in_connectedComponent_of_odd_start_and_nonterminal_even_off_boundary`
  now removes the old subtype/coercion bookkeeping from that route as well, so the next exact
  setup problem is narrower: define the deleted-spur continuation component and verify its odd
  start / even off-boundary hypotheses without letting the restart escape back through the
  original odd node `.start`. The first reduced-graph setup lemmas are now in place:
  `boundaryOnlyUniqueCarrierDeletedSpurSupport`,
  `IsBoundaryOnlyUniqueCarrierDeletedSpurBoundary`, and
  `boundaryOnlyUniqueCarrierDeletedSpurBoundary_iff_eq_positiveContinuationNeighbor`
  show that after deleting `{ν, μ}`, the only remaining support vertex touching that deleted spur
  is the continuation node `ξ`; moreover `not_isBoundaryOnlyUniqueCarrierDeletedSpurBoundary_start`
  shows that `.start` is not such a boundary vertex. So the exact remaining backup-route gap is
  now sharper still: prove that `ξ` is odd in the reduced component and that every other
  nonterminal vertex in that component is even, while controlling `.start` as a possible interior
  escape rather than a spur boundary point. The reduced graph itself is now explicit too:
  `boundaryOnlyUniqueCarrierDeletedSpurSubgraph` deletes the vertices `{ν, μ}` from the chosen
  chain graph, `twoNeighborSpec_of_not_terminal_belowTopDim_positive_of_alternativeSpecs`
  packages the existing below-top-dimensional two-door API in one reusable theorem, and
  `existsUnique_adj_boundaryOnlyUniqueCarrierDeletedSpurSubgraph_of_positiveContinuationNeighbor_of_alternativeSpecs`
  proves that the continuation node `ξ` has a unique surviving neighbor in that deleted-spur
  subgraph. Meanwhile
  `neighborSet_boundaryOnlyUniqueCarrierDeletedSpurSubgraph_eq_of_mem_support_of_not_boundary`
  shows that any reduced-support vertex not touching the deleted spur keeps exactly its full-graph
  neighbor set. So the next exact theorem is now the component-level restart:
  use those lemmas to show the connected component of `ξ` in the deleted-spur subgraph has odd
  start `ξ`, even nonterminal vertices away from the deleted-spur boundary, and no fatal escape to
  another odd obstruction such as `.start`. The new theorems
  `mem_boundaryOnlyUniqueCarrierDeletedSpurSupport_of_mem_connectedComponent_boundaryOnlyUniqueCarrierDeletedSpurSubgraph`,
  `exists_terminal_or_start_or_boundaryOnlyUniqueCarrierCounterexampleNode_in_deletedSpurComponent_of_positiveContinuationNeighbor_of_alternativeSpecs`,
  and
  `exists_terminal_of_positiveContinuationNeighbor_of_no_start_or_boundaryOnlyUniqueCarrierCounterexampleEscape_in_deletedSpurComponent_of_alternativeSpecs`
  now package that restart precisely: inside the deleted-spur continuation component, Lean already
  proves a terminal node unless the component escapes either to `.start` or to another
  `IsBoundaryOnlyUniqueCarrierCounterexampleNode`. So the exact higher-dimensional frontier is no
  longer the parity restart itself; it is to rule out those two explicit escape branches and then
  repackage the result as the final bypass theorem.
  Below-top-dimensional branch:
  finish the exact lower-dimensional no-open-crossing route, equivalently
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelBelowTopDimNoOpenCrossingDoorSpec`,
  by finding a fresh ambient-facet vertex whose singleton already subdivides the larger prefix
  face `ν.level.succ`.
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
  theorem is not yet derivable from the present local-barycentric infrastructure. The direct proof
  now reduces to one missing support theorem:
  `x ∈ convexHull (facetVertexPoints T σ) -> supportingFacet x ⊆ σ`
  or equivalently
  `x ∈ convexHull (facetVertexPoints T σ) -> baryCoord v x = 0` for all `v ∉ σ`. Focused recovery
  experiment result: a purely image-local support witness from `Finset.mem_convexHull'` is not
  enough for Section 5, because `boundary_preserving` only implies `imageSupport ⊆ domainSupport`;
  it does not let zero image coordinates force lower-prefix domain vertices. The next recovery route
  is blocked too under the current API: proving a facet-restriction theorem for `φ.toFun` would
  need nondegenerate facets and unique containing facets on relative interiors, but
  `SimplicialSubdivision` currently stores neither affine independence of facet vertex positions nor
  any uniqueness theorem for relative-interior points.
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
- [x] Introduced the spec-first recovery layer in `RentalHarmony/Section5Graph.lean`:
  `Section5GraphNode.FaceLocalLowerPrefixCarrierSpec` now isolates the exact missing lower-door
  consequence as an internal contract, and the new downstream reductions show that once
  `GeometricGenericity` is available for `chosenMilestoneChain`, the already-proved explicit
  milestone lemmas rebuild `MilestoneSegmentTransversality`, terminal-node existence, and a
  terminal-milestone facet.
- [x] Closed the small endpoint wrapper from the concrete chosen chain to the paper's barycenter:
  `prefixBarycenter_last_eq_barycentricRentDivision`,
  `chosenMilestoneChain_terminal_eq_barycenter`, and
  `exists_barycenterPreimageCell_of_chosenMilestoneChain_doorSpec`
  now show that under the isolated door-count contract, the Section 5 pipeline reaches a true
  `FacetImageContainsBarycenter` conclusion rather than only a terminal-milestone facet.
- [ ] Current concrete frontier: prove or supply the two remaining internal contracts for the
  higher-dimensional Section 5 proof.
  First, the primitive lower-door support theorem now appears explicitly as
  `Section5GraphNode.FaceLocalLargeLowerPrefixCarrierSpec.exists_support_in_largeLowerPrefixCarrier_of_contains_lowerMilestone`,
  from which the older graph-neighbor contract
  `Section5GraphNode.FaceLocalLowerPrefixCarrierSpec.exists_graphNeighbor_of_contains_lowerMilestone`
  is now derived automatically.
  Second, the remaining graph-local start/door-count package is now isolated as
  `Section5GraphNode.ChosenMilestoneChainGraphLocalSpec`, whose level-`0` and positive-level
  missing-next branches combine with the lower-door support contract to derive the older
  `Section5GraphNode.ChosenMilestoneChainDoorSpec` and hence the barycenter-cell wrapper.
- [ ] Recovery-attempt outcome: the suggested weaker vertex-level converse also fails under the
  current abstract support API. From
  `(((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0`
  for `v ∈ ν.face.carrier`, the repo still cannot prove
  `(((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0`,
  because `PiecewiseLinearVertexMap.boundary_preserving` only gives the forward implication
  "domain zero coordinate implies image zero coordinate". So the first irreducible missing lemma is
  now a face-local lower-prefix reflection theorem: if a point or carrier support in the image of
  a positive face lies in the lower target prefix face, then some carrier subset or subface of that
  positive face already lies in the lower domain prefix face and still maps onto that point.
- [ ] Recovery-attempt outcome: the exact missing face-local theorem now has a concrete 2D
  countermodel shape under the current abstract axioms. A facet with lower-domain vertices
  `A = e_0`, `B = (1/2,1/2,0)` and interior vertex `C = (1/3,1/3,1/3)` can satisfy the current
  one-way boundary conditions with images `φ(A)=e_0`, `φ(B)=e_0`, `φ(C)=(1/2,1/2,0)`, so the full
  face image contains the lower milestone while every lower-domain carrier subset or subface maps
  only to `e_0`. This means the needed lower-prefix reflection must stay as an explicit extra
  hypothesis or be added to a stronger support-layer structure; it is not derivable from the
  present `boundary_preserving` API alone.
- [x] Replaced further proof-search on that false theorem by an explicit stronger internal
  interface. `Section5GraphNode.PositiveFaceLowerPrefixReflection` now carries exactly the
  face-local lower-prefix reflection property justified by the recorded countermodel, and
  `faceLocalLargeLowerPrefixCarrierSpec_of_positiveFaceLowerPrefixReflection` plus
  `exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec` show that the downstream
  Section 5 parity pipeline closes cleanly under this one extra contract together with the existing
  graph-local spec.
- [ ] Direct attempt on the remaining graph-local input now bottoms out first at the level-`0`
  missing-next branch. To prove
  `ChosenMilestoneChainGraphLocalSpec.two_doors_of_missing_nextMilestone_level_zero`, one needs a
  1-dimensional lower-boundary subdivision theorem saying that a start-incident edge on the first
  prefix face which contains `c_0` but misses `c_1` has exactly one second door besides `.start`.
  The current abstract `SubdivisionFace` / adjacency API does not yet provide the needed interval-
  decomposition / unique-continuation fact for such lower-edge faces.
- [ ] The latest direct experiment suggests that this level-`0` theorem is itself false under the
  current abstract face API: several distinct lower-edge faces `{e_0,B_i}` can all be start-
  incident and pairwise horizontally adjacent through the shared codimension-`1` face `{e_0}`.
  So the remaining graph-local package now also needs either an explicit lower-boundary interval
  uniqueness hypothesis or a stronger subdivision-complex support layer ruling out such overlap.
- [x] Isolated that level-`0` input as its own minimal internal contract in
  `RentalHarmony/Section5Graph.lean`. The new
  `Section5GraphNode.ChosenMilestoneChainLevelZeroBoundarySpec` and
  `Section5GraphNode.ChosenMilestoneChainGraphLocalRestSpec` show that the barycenter-cell
  conclusion already follows from `PositiveFaceLowerPrefixReflection`, the normalized level-`0`
  boundary continuation theorem, and the remaining positive-level/open-crossing graph-local data,
  via `exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec'`.
- [x] Tightened that split further: the start-node existence/uniqueness fields also belong to the
  same lower-boundary interval model, so they now live in
  `Section5GraphNode.ChosenMilestoneChainLevelZeroBoundarySpec`. The remaining
  `ChosenMilestoneChainGraphLocalRestSpec` is now purely the non-boundary part of the graph-local
  package: open-crossing continuation and the positive-level missing-next / away-from-boundary
  cases.
- [ ] Direct attempt on the higher-dimensional remainder now bottoms out first at
  `ChosenMilestoneChainGraphLocalRestSpec.two_doors_of_missing_nextMilestone_openCrossing`. The
  present abstract API allows a positive face image to degenerate onto the milestone segment, in
  which case several codimension-`1` subfaces can also meet that segment and there is no abstract
  reason for exactly two doors. So the remaining rest spec also appears to require an explicit
  transversality / nondegeneracy input on higher-dimensional face images.
- [x] Isolated that higher-dimensional degeneracy as its own minimal contract in
  `RentalHarmony/Section5Graph.lean`. The new
  `Section5GraphNode.ChosenMilestoneChainOpenCrossingSpec` packages exactly the open-crossing
  two-door claim, while `Section5GraphNode.ChosenMilestoneChainPositiveLevelSpec` keeps the
  remaining positive-level continuation fields. The theorem
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''`
  now shows that the downstream barycenter-cell conclusion already follows from
  `PositiveFaceLowerPrefixReflection`, the level-`0` boundary contract, this new open-crossing
  contract, and the positive-level continuation package.
- [x] Reduced the positive-level continuation contract further using the already-proved split
  `chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone`.
  The new `Section5GraphNode.ChosenMilestoneChainPositiveLevelLowerMilestoneSpec` records only the
  missing-next / lower-milestone continuation branch, and
  `Section5GraphNode.ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec` isolates the
  next-milestone / away-from-boundary branch. The wrapper
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec'''`
  shows that these two sharper contracts, together with the existing reflection, level-`0`
  boundary, and open-crossing specs, are already sufficient for the barycenter-cell conclusion.
- [x] Tightened the lower-milestone positive-level contract once more: the auxiliary hypothesis
  "some extra neighbor exists" is not part of the true remaining theorem, so the support file now
  exposes the stronger/minimal interface
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec` with that premise
  removed. The new wrapper
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''''`
  shows that the barycenter-cell theorem now depends only on the bare lower-endpoint two-door
  statement, not on an additional externally supplied neighbor witness.
- [x] Reduced that positive-level missing-next branch one step further by using the actual
  dichotomy already proved in the file: either there is an open crossing or there is not. The new
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec` packages exactly the
  complement of the already-isolated open-crossing case, and
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec_noOpenCrossing`
  shows that the downstream barycenter-cell theorem now depends on the no-open-crossing branch
  rather than on the older lower-milestone door formulation.
- [ ] Direct attempt on `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec`
  now isolates a new support-layer gap: the current `SubdivisionFace` API treats codimension-`1`
  faces only as arbitrary nonempty subsets of facets, so it provides no simplicial-complex
  incidence uniqueness. In the no-open-crossing lower-endpoint case, one needs at least a theorem
  saying that the codimension-`1` face carrying the lower milestone is geometrically unique and is
  incident to exactly one other relevant positive face. Without that, several syntactically
  distinct codimension-`1` subsets or several cofaces through the same lower milestone can create
  spurious extra doors, so the no-open-crossing branch is not derivable from the current abstract
  face/incidence layer alone.
- [x] Introduced the carrier-normalized codimension-`1` support object
  `SubdivisionFace.CarrierCodimOneSubface` and the carrier-level continuation contract
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec`.
  This packages the next blocker at the right layer: not raw `SubdivisionFace` syntax, but the
  unique same-level continuation across a normalized codimension-`1` carrier face that contains
  the lower milestone.
- [ ] Focused recovery result: even after carrier normalization, the current
  `SimplicialSubdivision` API still permits genuine coface multiplicity. A codimension-`1` carrier
  set can lie in three or more facets because `facets` is only a covering family of
  `(dimension + 1)`-element finsets; there is no simplicial-complex / pseudomanifold axiom saying
  such a carrier has exactly two incident cofaces. So the new
  `ChosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec` is not derivable from
  the present abstract support layer either; it is now the exact missing carrier-incidence
  theorem.
- [x] Sharpened that no-open-crossing carrier-incidence frontier once more. The support file now
  isolates only graph-relevant same-level continuations across the normalized codimension-`1`
  carrier face via
  `Section5GraphNode.IsSameLevelCarrierContinuationCandidate` and
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec`, and
  proves
  `Section5GraphNode.chosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec_of_filteredSpec`.
  So the old carrier-continuation theorem now reduces to uniqueness among graph doors compatible
  with the chosen-milestone geometry, not among all abstract cofaces of the carrier.
- [x] Added the local bridge lemmas needed to work with that filtered continuation statement:
  `SubdivisionFace.imageContains_mono`,
  `SubdivisionFace.imageContainsMilestone_mono`,
  `SubdivisionFace.imageMeetsMilestoneSegment_mono`,
  `SubdivisionFace.imageMeetsOpenMilestoneSegment_mono`,
  `Section5GraphNode.horizontalAdj_of_sameLevelCarrierContinuationCandidate`,
  `Section5GraphNode.adj_of_sameLevelCarrierContinuationCandidate`, and
  `Section5GraphNode.exists_candidate_of_horizontalAdj_of_not_openCrossing`.
  So the no-open-crossing positive-level branch is no longer blocked on translating between
  carrier-level witnesses and actual graph doors.
- [ ] Current exact blocker: prove that filtered same-level continuation theorem, or keep it as the
  minimal extra internal contract. In the no-open-crossing positive-level lower-endpoint case, one
  must still show existence and uniqueness of a graph-relevant same-level continuation through the
  normalized lower-milestone carrier: once a same-level horizontal neighbor exists, the new lemmas
  extract such a candidate automatically, but the current abstract support layer still does not
  force that candidate to exist or be unique. This is now the sharpest remaining statement on that
  branch.
- [x] Formalized the exact output of the lower-prefix reflection machinery:
  `exists_verticalAdj_of_lowerPrefixSubset_contains_lowerMilestone`,
  `exists_verticalAdj_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone`,
  `exists_verticalAdj_of_contains_lowerMilestone_of_largeLowerPrefixCarrierSpec`, and
  `exists_verticalAdj_of_contains_lowerMilestone_of_reflection` show that the current
  lower-prefix support contract yields a downward vertical neighbor by construction.
- [ ] Recovery-attempt result: the suggested graph-neighbor classification route cannot produce the
  missing same-level continuation. Reflection does not hand back an unspecified graph neighbor that
  might be horizontal; it directly constructs a downward vertical neighbor. So the next minimal
  missing theorem is an independent same-level continuation-existence statement alongside that
  already-known vertical door, not a reclassification lemma for the reflection neighbor.
- [x] Countermodel-style dependency check: after the new bridge lemmas, the local data they leave
  behind really is too weak to force same-level continuation. A toy local skeleton with one
  positive node `ν`, one normalized codimension-`1` carrier `ρ ⊆ ν.face`, and one lower positive
  node `λ` with `λ.VerticalAdj ν`, but with no same-level positive node through `ρ`, is consistent
  with all currently formalized post-bridge facts. So same-level continuation existence is
  genuinely independent of the current reflected-neighbor / bridge layer and should remain the next
  minimal internal contract unless the subdivision API is strengthened.
- [ ] Direct proof attempt on that filtered theorem now isolates the first missing half even more
  sharply: existence of a second same-level positive coface through the normalized lower-milestone
  carrier. The current `SimplicialSubdivision` API only records `subset_facet :
  ∃ σ ∈ facets, carrier ⊆ σ`, so from a codimension-`1` carrier `ρ ⊆ ν.face` it provides one
  ambient facet but no theorem that some other same-level graph face also contains `ρ`. The new
  extraction/promotion lemmas show that uniqueness only becomes relevant after such a same-level
  horizontal continuation exists, so the first irreducible no-open-crossing obstruction is now
  same-level continuation existence rather than candidate translation.
- [x] Refactor that filtered no-open-crossing theorem into the actual two subproblems that remain:
  `ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec` and
  `ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec`, together with
  `chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_existence_and_uniqueness`.
  This records that the present frontier is only the existence half; uniqueness is now a separate,
  downstream contract rather than part of one coarse blocked theorem.
- [x] Thread the downstream carrier-continuation wrapper through that split interface via
  `chosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec_of_existence_and_uniqueness`.
  This makes the remaining dependency explicit in the support layer: downstream code no longer
  needs the old monolithic filtered theorem.
- [ ] Uniqueness check result: there is still no ambient same-level codimension-`1` coface
  uniqueness theorem in the current repo. The available lemmas build codimension-`1` faces and
  promote horizontal doors to candidates, but nothing yet proves that two same-level candidates
  through the same normalized carrier must coincide. So `ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec`
  remains an explicit local input unless a stronger simplicial-complex uniqueness theorem is added.
- [x] Refine the primary existence frontier further: with
  `exists_lowerMilestoneCarrier_of_not_openCrossing_of_reflection`,
  `ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec`, and
  `chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierContinuation`,
  the reflection contract now supplies the normalized lower-milestone carrier automatically. The
  remaining existence input is only a same-level continuation through that fixed carrier.
- [x] Thread the carrier-continuation wrapper through this sharper split as well via
  `chosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec_of_reflection_and_fixedCarrierContinuation_and_uniqueness`.
  After reflection is fixed, the no-open-crossing branch is now explicitly parameterized by only
  two local inputs: fixed-carrier continuation existence and fixed-carrier uniqueness.
- [x] Thread the monolithic filtered wrapper through the same sharper split via
  `chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_reflection_and_fixedCarrierContinuation_and_uniqueness`.
  The whole no-open-crossing wrapper chain is now explicit from reflection down to the old
  filtered theorem.
- [ ] Direct support search for the new primary theorem turns up nothing: there is still no lemma
  extending a normalized codimension-`1` prefix-face carrier to a same-level prefix-face coface.
  So the exact remaining existence gap is now a fixed-carrier same-level continuation theorem, not
  carrier construction or door translation.
- [x] The failed proof step is now pinned down exactly. The current face API has
  `SubdivisionFace.subdividesPrefixFace_of_subface`, which only pushes prefix-face information
  downward to smaller carriers, and `subset_facet`, which only places a carrier inside some ambient
  facet. There is no upward extension theorem turning a codimension-`1` prefix-face carrier into a
  distinct same-level prefix-face coface, and that is exactly what
  `ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec` now asks for.
- [x] Repackage that same obstruction in the paper's geometric language:
  `ChosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec` now isolates the facet-local
  statement “extend this fixed codimension-`1` carrier to a distinct same-level coface,” and the
  candidate-level continuation theorem is proved to follow from it via
  `chosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec_of_cofaceExtension`.
- [x] Route the no-open-crossing filtered wrapper chain through this coface-extension interface as
  well, via `chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec_of_reflection_and_fixedCarrierCofaceExtension`
  and `chosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec_of_reflection_and_fixedCarrierCofaceExtension_and_uniqueness`.
- [x] Push the same obstruction one layer further down to the single-simplex viewpoint suggested by
  the paper: `ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec` now asks for a
  second same-level coface inside one ambient facet `σ` containing `ν.face`, and the coface-
  extension / filtered-wrapper chain is routed through it via
  `chosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec_of_ambientFacetExit` and the
  corresponding no-open-crossing wrapper theorems.
- [x] Separate the remaining domain-side extension theorem from the image-side positivity step:
  `ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec` now asks only for
  a same-level prefix-face coface inside the ambient facet `σ`, and the ambient-facet exit /
  coface-extension / filtered-wrapper chain is routed through it. Once such a face exists, the
  lower-milestone carrier automatically makes it a positive graph node.
- [x] Prove the first genuinely new geometric helper toward that theorem:
  `exists_sameLevelPrefixFace_in_ambientFacet_of_freshPrefixVertex` now constructs the required
  same-level face explicitly from one fresh vertex of the ambient facet already lying in the larger
  prefix face, and
  `chosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec_of_freshPrefixVertex`
  shows the full prefix-extension contract follows from this concrete vertex-existence lemma.
- [x] Record the exact obstruction to pushing that fresh-vertex route further without a new
  geometric idea: the new lemmas `ambientFacet_eq_of_topDim` and
  `no_freshAmbientFacetVertex_of_topDim` show that if `ν.face` is already top-dimensional, then
  any ambient facet `σ` containing `ν.face` is forced to equal `ν.face`, so there is no fresh
  vertex in `σ \ ν.face.carrier` to feed into
  `exists_sameLevelPrefixFace_in_ambientFacet_of_freshPrefixVertex`. The fresh-prefix-vertex route
  is therefore inherently a below-top-dimensional argument and cannot settle
  `ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec` uniformly on its
  own.
- [x] Complete the dimension split around that obstruction without changing the formal interface:
  `exists_freshAmbientFacetVertex_of_lt_topDim` now shows that below top dimension a fresh ambient-
  facet vertex exists automatically by cardinality, while
  `not_exists_sameLevelPrefixFace_in_ambientFacet_of_topDim` shows the current ambient-facet
  prefix-extension conclusion is actually impossible in the top-dimensional branch. So the
  remaining below-top-dimensional issue is no longer plain freshness, but specifically choosing a
  fresh ambient-facet vertex that also lies in the larger prefix face `ν.level.succ`.
- [x] Move the lower-milestone proof frontier to the correct layer after that diagnosis:
  `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneDoorSpec` and
  `ChosenMilestoneChainPositiveLevelBelowTopDimLowerMilestoneDoorSpec` now isolate the genuinely
  different top-dimensional and below-top-dimensional door arguments, and
  `chosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec_of_topDim_and_belowTopDim` recombines
  them into the unchanged paper-facing
  `ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec`.
- [x] Isolated the first missing top-dimensional input as
  `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec`, and proved the
  reusable bridge from two distinct codimension-`1` lower-milestone carriers to two distinct
  vertical graph neighbors via
  `verticalNeighborOfCodimOneSubfaceContainsLowerMilestone` and
  `exists_two_distinct_verticalNeighbors_of_topDimLowerMilestoneCarrierMultiplicity`.
- [x] Sharpened that top-dimensional gap once more: reflection now yields the first normalized
  lower-prefix carrier automatically via `exists_lowerMilestoneCarrier_of_reflection`, and the new
  contract `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierSpec` isolates only
  the missing second carrier. The theorem
  `chosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec_of_reflection_and_secondCarrier`
  rebuilds the older multiplicity package from this sharper input, and
  `exists_two_distinct_verticalNeighbors_of_reflection_and_topDimLowerMilestoneSecondCarrier`
  lands directly at the two-vertical-door target.
- [x] Proved that two distinct codimension-`1` lower-prefix carriers of the same face already
  force the whole face into that lower prefix face:
  `SubdivisionFace.mem_of_mem_codimOneSubface_or_other`,
  `SubdivisionFace.subdividesPrefixFace_of_two_distinct_codimOneSubfaces`, and
  `faceSubdividesLowerPrefix_of_reflection_and_topDimLowerMilestoneSecondCarrier`.
  So the remaining top-dimensional second-carrier gap is no longer domain-side lower-prefix
  bookkeeping; it is the image-side existence of a second milestone-carrying codimension-`1`
  subface once the whole top-dimensional face already lies in the lower prefix face. This exact
  image-side frontier is now packaged as
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec`,
  and
  `exists_second_codimOneSubface_of_faceSubdividesLowerPrefix`
  reduces it back to the older second-carrier theorem by recovering the lower-prefix condition on
  the second codimension-`1` subface from codimension-`1` incidence alone. The precise remaining
  local lemma is now one step lower still:
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec`
  asks for an arbitrary point already lying in the image of one codimension-`1` subface of a
  top-dimensional face in the lower prefix face to lie in the image of a second distinct
  codimension-`1` subface as well, and
  `chosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec_of_boundaryPointMultiplicity`
  recovers the milestone-specific contract from this point-level statement. The new theorem
  `exists_second_codimOneSubface_imageContains_of_subset_in_codimOneSubface` now makes that
  multiplicity statement constructive: it is enough to shrink the image support inside the first
  codimension-`1` subface by one additional vertex. This sharper frontier is packaged as
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec`, and
  `chosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec_of_supportShrink`
  derives the point-level multiplicity contract from it. The support file now lowers the frontier
  once more to the exact one-step Carathéodory move:
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec`, and
  `chosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec_of_oneVertexDrop`
  shows that this one-vertex-drop theorem already implies the older support-shrink contract.
  The new theorem
  `exists_smaller_support_of_mem_convexHull_of_not_affineIndependent_image` and its wrapper
  `chosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec_of_affineDependentImage`
  sharpen the remaining local content again: it is enough to prove that the image support inside
  the first codimension-`1` face is affinely dependent. The new theorem
  `not_exists_smaller_support_of_pair_of_mem_openSegment` isolates the simplest obstruction:
  a two-point open-segment support in that face cannot satisfy one-vertex-drop. The route change
  is now formalized too: the new theorems
  `existsUnique_graphNeighbor_of_boundaryOnlyUniqueCarrierCounterexampleData` and
  `existsUnique_verticalAdj_of_boundaryOnlyUniqueCarrierCounterexampleData` show that the packaged
  top-dimensional obstruction is a genuine forced-descent node with one canonical lower neighbor,
  while the new weaker interfaces
  `ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingAlternativeSpec` and
  `ChosenMilestoneChainPositiveLevelNoOpenCrossingAlternativeSpec` separate the exact two cases
  now supported by Lean: either the desired two-door conclusion, or exact
  `TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData`. The reduction
  `chosenMilestoneChainPositiveLevelNoOpenCrossingSpec_of_alternative_and_counterexampleExclusion`
  records the exact remaining global gap: to recover the old no-open-crossing theorem one must
  either exclude the packaged obstruction from the intended geometry, or replace the downstream
  parity pipeline by a contraction lemma that consumes this forced-descent alternative.
- [x] Split the literal next-milestone simplex-entry theorem into a proved facet-membership step
  and one sharper remaining boundary-entry step. The new generic simplex theorem
  `Affine.Simplex.exists_mem_faceOpposite_closedInterior_of_mem_closedInterior_of_not_mem_interior`
  proves that every point of `closedInterior \ interior` lies in the closed interior of some
  opposite face. The new reduction
  `chosenMilestoneChainNextMilestoneCarrierImageSimplexInteriorEntrySpec_of_boundaryEntry`
  uses this to show that the current entrance-face target is implied by the exact sharper local
  statement
  `ChosenMilestoneChainNextMilestoneCarrierImageSimplexBoundaryEntrySpec.
  exists_boundaryPoint_wbtw_of_mem_interior_carrierImageSimplex_and_lowerMilestone_not_mem_closedInterior`.
  So the unresolved next-milestone geometry is now no longer generic barycentric-to-facet support;
  it is specifically the existence of a first boundary point of the carrier-image simplex on the
  segment `[b_{k-1}, b_k]`. The new support theorem
  `SubdivisionFace.isClosed_closedInterior_carrierImageSimplex` verifies that the carrier-image
  simplex closed interior is an honest closed convex set, but a direct `IsClosed.exists_wbtw_isVisible`
  proof attempt fails for the exact structural reason now to record: `b_k ∈ sx.interior` is only
  relative interior data for the lower-dimensional simplex `sx`, not ambient-topological interior.
  So the next local bridge is either a boundary-entry theorem stated after restricting to the
  affine span of `sx`, or an additional theorem that `b_{k-1}` already lies in that affine span.
