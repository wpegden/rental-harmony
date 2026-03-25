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
- Further revision forced by the surjectivity proof:
  `PiecewiseLinearSimplexMap` cannot be modeled only by a function `toFun`, vertex values, and the
  existence of some facet-image witness for each point. That permits discontinuous step maps on the
  1-simplex, so the Section 5 surjectivity theorem is false. The map object must be strengthened to
  encode genuine affine-on-cells / continuity data.
  The chosen repair is now in place:
  the subdivision itself carries global continuous barycentric-coordinate functions together with a
  chosen supporting facet. A `PiecewiseLinearSimplexMap` is reduced back to its
  boundary-preserving vertex data, and the actual `toFun` is derived as the corresponding finite
  center of mass in the codomain simplex.

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
- Latest Section 5 reduction:
  the concrete chosen-chain proof no longer needs an all-at-once lower-door theorem.
  `exists_subset_contains_lowerMilestone_of_exists_upperCoord_ne_zero` and
  `exists_codimOneSubface_contains_lowerMilestone_of_exists_upperCoord_ne_zero`
  now settle the subcase where a positive face carrying the lower milestone still has some image
  vertex with nonzero next-coordinate. The remaining case split is therefore precise:
  either an upper-coordinate survives and codimension-`1` support follows immediately, or every
  image vertex already lies in the lower target prefix face and one must extract a lower-prefix
  domain subface from that stronger geometric situation.
- Latest support-layer status for that remaining case:
  the ambient transport and target-side support reduction are now formalized.
  `PrefixFace.padLinear`, `PrefixFace.mem_affineSpan_prefixVertexFinset`,
  `PrefixFace.mem_affineSpan_prefixVertexFinset_of_coord_eq_zero`,
  `affineIndependent_prefixVertexFinset`, and
  `exists_subset_contains_lowerMilestone_of_all_imageVertices_lowerPrefix`
  reduce the all-image-lower branch to a proper target-side support of size at most `k + 1`.
  So the remaining local theorem is now sharper: turn that proper target support into a proper
  carrier subset whose vertices already lie in the lower domain prefix face, then invoke the
  existing codimension-`1` / vertical-door bridge lemmas.
- Latest Section 5 graph-level reduction:
  in the higher-dimensional obstruction branch (`2 < dimension`), the continuation node after the
  canonical vertical descent is now proved to be positive, strictly lower-level, and
  below-top-dimensional. This yields the clean reduction
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_belowTopDimPositiveTerminal_of_two_lt_dimension`.
  This remaining direct-route input is now packaged explicitly as
  `ChosenMilestoneChainBelowTopDimPositiveTerminalSpec`, and
  `exists_terminal_of_chosenMilestoneChain_alternativeSpecs_of_belowTopDimPositiveTerminal_of_two_lt_dimension`
  shows that it is enough for pure terminal existence under the current alternative local API.
  Lean now also proves
  `degree_positive_eq_two_of_not_terminal_belowTopDim_positive_of_alternativeSpecs`, so the direct
  full-graph route really does fail at the first parity step: an arbitrary below-top-dimensional
  nonterminal positive node is even-degree, not an odd start. The likely minimal replacement is
  still a parity theorem on the connected component of the continuation node in the graph obtained
  by deleting the obstruction spur `{ν, μ}`. A first attempt to package that via
  `ConnectedComponent.toSimpleGraph` failed exactly at a coercion/typeclass transport between
  `↥C` and `↑C.supp`, so the backup route is now recast in a simpler form: the new abstract lemma
  `exists_terminal_or_boundary_in_induce_of_odd_start_and_nonterminal_even_off_boundary`
  restarts parity directly on induced subgraphs of arbitrary subsets. The remaining backup plan is
  therefore to identify the relevant deleted-spur connected-component support as such a subset and
  instantiate this induced-subgraph theorem there, unless a stronger local Section 5 continuation
  principle eliminates the restart entirely. The latest infrastructure step packages the same idea
  at connected-component granularity as
  `exists_terminal_or_boundary_in_connectedComponent_of_odd_start_and_nonterminal_even_off_boundary`,
  so the next backup-route work is no longer subtype transport but the concrete deleted-spur setup:
  define the continuation component, prove the continuation node is odd in the reduced graph, and
  show every other nonterminal nonboundary vertex in that component is even without reopening a
  path to the original odd start `.start`. The first local reduced-graph ingredients are now
  formalized:
  `boundaryOnlyUniqueCarrierDeletedSpurSupport`,
  `IsBoundaryOnlyUniqueCarrierDeletedSpurBoundary`, and
  `boundaryOnlyUniqueCarrierDeletedSpurBoundary_iff_eq_positiveContinuationNeighbor`
  identify the deleted-spur boundary inside that reduced support exactly with the continuation node
  `ξ`, and `not_isBoundaryOnlyUniqueCarrierDeletedSpurBoundary_start` records that `.start` is not
  one of those deleted-spur boundary contacts. The reduced graph itself is now explicit as
  `boundaryOnlyUniqueCarrierDeletedSpurSubgraph`, and the new theorems
  `twoNeighborSpec_of_not_terminal_belowTopDim_positive_of_alternativeSpecs`,
  `existsUnique_adj_boundaryOnlyUniqueCarrierDeletedSpurSubgraph_of_positiveContinuationNeighbor_of_alternativeSpecs`,
  and
  `neighborSet_boundaryOnlyUniqueCarrierDeletedSpurSubgraph_eq_of_mem_support_of_not_boundary`
  show respectively that below-top-dimensional nonterminal positive nodes still have an exact
  two-neighbor description in the full chosen-chain graph, that the continuation node `ξ` has a
  unique surviving neighbor after deleting `{ν, μ}`, and that any reduced-support vertex not
  touching the deleted spur keeps exactly its full-graph neighbor set. So the next backup step is
  now even sharper: instantiate the connected-component parity theorem on the component of `ξ` in
  this deleted-spur subgraph, using unique reduced adjacency for oddness at `ξ` and preserved
  neighbor sets for evenness away from the deleted-spur boundary, while ruling out any residual
  escape to `.start` or another odd obstruction inside that component. This restart is now proved
  up to those exact escape cases:
  `mem_boundaryOnlyUniqueCarrierDeletedSpurSupport_of_mem_connectedComponent_boundaryOnlyUniqueCarrierDeletedSpurSubgraph`
  shows that the whole continuation component stays inside the deleted-spur support, and
  `exists_terminal_or_start_or_boundaryOnlyUniqueCarrierCounterexampleNode_in_deletedSpurComponent_of_positiveContinuationNeighbor_of_alternativeSpecs`
  proves that the component already contains either a genuine terminal node, `.start`, or another
  `IsBoundaryOnlyUniqueCarrierCounterexampleNode`. The immediate corollary
  `exists_terminal_of_positiveContinuationNeighbor_of_no_start_or_boundaryOnlyUniqueCarrierCounterexampleEscape_in_deletedSpurComponent_of_alternativeSpecs`
  shows that the only remaining higher-dimensional work is to exclude those two escape branches,
  after which the deleted-spur bypass theorem can be repackaged cleanly. That repackaging is now
  explicit: `ChosenMilestoneChainDeletedSpurNoEscapeSpec` records exactly those two exclusions,
  `exists_terminal_of_positiveContinuationNeighbor_of_deletedSpurNoEscapeSpec_of_alternativeSpecs`
  turns that no-escape input into terminal existence from the positive continuation node, and
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_deletedSpurNoEscapeSpec_of_two_lt_dimension`
  turns it into the full higher-dimensional bypass theorem. So the exact remaining proof frontier
  is no longer the deleted-spur parity restart itself, but the two specific no-escape fields of
  `ChosenMilestoneChainDeletedSpurNoEscapeSpec`. The latest comparison theorem
  `exists_terminal_of_positiveContinuationNeighbor_of_alternativeSpecs_of_belowTopDimPositiveTerminalSpec`
  also shows that these two escape branches are not separate from the older direct route: if the
  below-top-dimensional positive-node terminal theorem is available, then both `.start`-escape and
  further-obstruction escape in the deleted-spur component are already harmless. After the latest
  proof search, the first local deleted-spur field that still does not crystallize from the
  current reduced-graph/component API is exactly
  `ChosenMilestoneChainDeletedSpurNoEscapeSpec.no_start_of_positiveContinuationNeighbor`. Unless
  `no_boundaryOnlyUniqueCarrierCounterexampleNode_of_positiveContinuationNeighbor` turns out to be
  substantially easier, this is now strong evidence that the genuine remaining higher-dimensional
  frontier is the older direct-route theorem
  `ChosenMilestoneChainBelowTopDimPositiveTerminalSpec.exists_terminal_of_positive_belowTopDim`,
  with the deleted-spur no-escape fields serving only as alternate local reformulations of that
  same gap. This direct route has now been corrected and sharpened further:
  the original everywhere-strict
  `ChosenMilestoneChainBelowTopDimPositiveLevelDescentSpec` is too strong at level `0`, so the
  realistic reduction is
  `ChosenMilestoneChainBelowTopDimPositiveBaseCaseAndLevelDescentSpec`, proved sufficient by
  `chosenMilestoneChainBelowTopDimPositiveTerminalSpec_of_baseCaseAndLevelDescent`.
  Moreover,
  `chosenMilestoneChainBelowTopDimPositiveBaseCaseAndLevelDescentSpec_of_largeLowerPrefixCarrierSpec_and_caseSplit`
  now discharges the positive-level missing-next/no-open-crossing branch from the existing
  large-lower-prefix carrier API via
  `exists_lowerLevel_positive_of_missingNextMilestone_positiveLevel_of_not_openCrossing_of_largeLowerPrefixCarrierSpec`.
  The new graph-interface lemmas `not_adj_positive_start_of_level_pos`,
  `level_relation_of_adj_positive_positive`, and
  `exists_two_distinct_positiveNeighbors_of_not_terminal_positiveLevel_belowTopDim_of_alternativeSpecs`
  further show that the remaining positive-level next/open branches already have two distinct
  positive continuation neighbors, but the latest support lemmas sharpen the issue further:
  `exists_lowerLevel_positive_of_contains_lowerMilestone_of_largeLowerPrefixCarrierSpec`
  proves strict descent once lower-milestone containment is known, while
  `not_exists_lowerLevel_positive_of_not_contains_lowerMilestone` shows strict descent is
  impossible if the current face does not contain that lower milestone. So the first exact
  positive-level subcase that still does not crystallize from the current API is still
  `ChosenMilestoneChainBelowTopDimPositiveBaseCaseAndCaseSplitDescentSpec.exists_lowerLevel_positive_of_nextMilestone_not_terminal_belowTopDim`,
  but now in the more precise form that the next-milestone away-from-boundary branch lacks any
  theorem forcing lower-milestone containment. The open-crossing branch has the same remaining
  shape. This sharper state is now formalized directly by
  `ChosenMilestoneChainBelowTopDimPositiveBaseCaseAndCaseSplitLowerMilestoneSpec`; the reduction
  theorem
  `chosenMilestoneChainBelowTopDimPositiveBaseCaseAndCaseSplitDescentSpec_of_largeLowerPrefixCarrierSpec_and_caseSplitLowerMilestone`
  shows that those exact containment fields are enough to recover the older strict-descent
  interface, and `contains_lowerMilestone_of_exists_lowerLevel_positive` records the converse
  necessity of lower-milestone containment for any descent proof. A fresh direct proof attempt of
  the next-milestone containment field still fails at the same exact boundary: every current
  codimension-`1` / lower-carrier theorem already takes lower-milestone containment as an input,
  so the existing support layer has no lemma that starts from next-milestone-away-from-boundary
  data and produces `ξ.face.ImageContainsMilestone ... ξ.level.castSucc`. So the sharpest current
  direct-route frontier is now the trio of remaining local
  subcases: the level-`0` base case, the positive-level next-milestone lower-milestone-containment
  branch, and the positive-level open-crossing lower-milestone-containment branch.
  The latest stuck-recovery route change also suggests that this frontier may be slightly too
  strong. Reading the manuscript's higher-dimensional trap-door paragraph together with the raw
  Lean definition of `ImageContainsMilestoneAwayFromBoundary`, the next-milestone branch appears
  to describe a segment ending inside `λ(σ)` and hence a unique entrance codimension-`1` face,
  i.e. a same-level continuation witness, rather than immediate lower-milestone containment of
  `σ` itself. So if no new geometry upgrades away-from-boundary to lower containment, the next
  repair may be to replace
  `contains_lowerMilestone_of_nextMilestone_not_terminal_belowTopDim`
  by a more paper-exact entrance-door / same-level continuation theorem and then rebuild the
  below-top-dimensional continuation argument from that interface.

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
- The straight-line homotopy from `id` to such a map is now formalized in
  `RentalHarmony/Sperner.lean`, and every intermediate map still preserves every coordinate face.
  So the topological route has sharpened:
  the boundary restriction of the map and of the straight-line homotopy are now formalized, and
  `boundary_contractible_of_nullhomotopic_boundaryExtension` packages the contradiction step.
  The barycenter-specific omitted-point extension is now also formalized:
  `projectAwayBarycenterContinuous` and `boundary_contractible_of_omits_barycenter` reduce any
  barycenter-omitting face-preserving map to contractibility of `SimplexBoundary dimension`.
  The remaining choice is now explicit: either prove the boundary noncontractible in Lean and
  finish the topological contradiction, or abandon the topological route and switch to the paper's
  trap-door/path-following proof.
- Latest status:
  a direct search through the installed mathlib did not find an immediately usable Brouwer fixed
  point theorem, no-retraction theorem, or noncontractibility result for spheres / simplex
  boundaries. So the topological route is now blocked on importing or developing a serious external
  topological invariant, not on another local project lemma.
- If the topological route is awkward, switch to the paper's combinatorial path-following proof.
  That switch is also now clearer in scope:
  before proving the graph/parity argument, add a support-layer API for lower-dimensional faces and
  codimension-`1` incidence inside subdivisions, since the current interface only packages
  full-dimensional facets plus supporting-facet witnesses.
- This combinatorial pivot is now underway:
  `RentalHarmony/Section5Graph.lean` introduces `SubdivisionFace` as a nonempty subset of a facet,
  proves closure under taking nonempty subfaces, and packages codimension-`1` incidence. The next
  step is to define the actual graph vertices from Section 5 using these faces and the segments
  `[b_{k-1}, b_k]`, then prove the degree/parity walk lemma.
  The barycenter side of that vocabulary is now started as well:
  the support file contains `prefixBarycenter`, `prefixBarycenterSegment`,
  `SubdivisionFace.SubdividesPrefixFace`, and the corresponding image-intersection predicates.
- The graph-definition step is now complete as well:
  `Section5PositiveNode` packages positive-dimensional graph vertices, `Section5GraphNode` adds
  the special start node, and `Section5GraphNode.graph` is the resulting `SimpleGraph` carrying
  the paper's start, horizontal, and vertical adjacencies.
- The parity backbone is now separated cleanly from the geometry:
  `exists_terminal_of_odd_start_and_nonterminal_even` is a reusable finite-graph lemma stating
  that once the start node is odd and all nonterminal nodes are even, a terminal node must exist.
  So the remaining Section 5 work is no longer an undifferentiated path-following proof; it is the
  local geometric degree analysis needed to instantiate that parity theorem.
- The next blocker is now precise:
  the paper's local degree counts are proved only after a generic perturbation of the barycenters
  so that the relevant segments meet codimension-`1` faces in relative interior points and avoid
  lower-dimensional degeneracies. The current Lean graph still uses the exact `prefixBarycenter`
  chain, so before the local degree lemmas can be proved honestly, the support layer must expose a
  generic milestone chain or an equivalent perturbation hypothesis.
- That support-layer repair is now in place:
  `RentalHarmony/Section5Graph.lean` introduces `Section5MilestoneChain`, which keeps the start at
  `e_1` and the terminal milestone at the true simplex barycenter while allowing generic
  intermediate points that stay inside the corresponding prefix outer faces. The Section 5 graph
  itself is now parameterized by such a chain.
- The next abstraction layer is now in place too:
  `Section5GraphNode.LocalDegreeHypotheses` isolates exactly the local "one door at the start, two
  doors at every nonterminal room" consequences that the paper's geometric genericity argument is
  supposed to provide. From those hypotheses, the support file already proves the odd/even degree
  lemmas needed by the finite-graph parity theorem.
- The abstract graph conclusion is now packaged too:
  `Section5GraphNode.exists_terminal_of_localDegreeHypotheses` combines those odd/even degree
  lemmas with the parity theorem and yields a terminal top-dimensional face as soon as the
  milestone-chain geometry supplies `LocalDegreeHypotheses`.
- The next abstraction layer is now in place as well:
  `Section5GraphNode.GeometricGenericity` splits the paper's local Section 5 reasoning into the
  two geometric cases actually used in the manuscript:
  the next milestone is absent from the current face image, or it lies in that image and the face
  is not terminal. The support file proves
  `Section5GraphNode.localDegreeHypotheses_of_geometricGenericity` and the direct wrapper
  `Section5GraphNode.exists_terminal_of_geometricGenericity`.
- The concrete geometric target is now sharper still:
  `SubdivisionFace.ImageMeetsOpenMilestoneSegment` and
  `SubdivisionFace.ImageContainsMilestoneAwayFromBoundary` formalize the paper's open-segment and
  relative-interior-style conditions, and `Section5GraphNode.MilestoneSegmentTransversality`
  packages them on top of `GeometricGenericity`. The support file already derives
  `Section5GraphNode.exists_terminal_of_milestoneSegmentTransversality`, so the remaining Section 5
  work is now the actual convex-geometric proof of this transversality package for a suitable
  milestone chain.
- Latest status after repairing the missing-next branch:
  the graph-side consequence of a lower-endpoint door is now formalized abstractly.
  `exists_verticalAdj_of_codimOneSubface_contains_lowerMilestone` and its graph-level corollary
  `exists_graphNeighbor_of_codimOneSubface_contains_lowerMilestone` show that once a positive node
  admits a codimension-`1` subface in the lower prefix face whose image contains `b_k`, the
  Section 5 graph already has the required vertical door. So the remaining missing-next work is no
  longer graph bookkeeping; it is the geometric existence of that codimension-`1` lower-prefix
  subface for the concrete `chosenMilestoneChain`.
- The geometric subface step is now reduced further:
  `exists_codimOneSubface_contains_lowerMilestone_of_subset` proves that any proper carrier subset
  of a positive node whose image convex hull already contains `b_k` can be turned into an actual
  codimension-`1` face carrying `b_k` by erasing one unused vertex. So the remaining concrete
  work is to produce such a proper supporting subset and simultaneously ensure it subdivides the
  lower prefix face.
- Latest blocker after pushing on that proof directly:
  mathlib does provide full-dimensional interior lemmas such as
  `interior_convexHull_nonempty_iff_affineSpan_eq_top`, but the milestone-chain argument needs
  finite-union avoidance inside the lower-dimensional prefix faces `conv{e_1, ..., e_k}`.
  The current project does not yet identify those prefix faces with smaller standard simplices, and
  there is no ready-made theorem in the installed library giving "a finite union of proper convex
  hulls cannot cover the relative interior of a simplex face". So the next proof step is now a
  support theorem of that exact kind, not another graph or parity lemma.
- That support-theorem route is now started concretely:
  `RentalHarmony/Section5Graph.lean` defines the bundled subtype `PrefixFace k` and the map
  `Section5MilestoneChain.prefixPoint`, which packages every milestone as a point of its ambient
  prefix face. The explicit restriction/padding equivalence
  `PrefixFace.equivRentDivision : PrefixFace k ≃ RentDivision (k + 1)` is now formalized, so the
  next missing lemma on this route was the finite-union avoidance theorem inside those smaller
  simplices / prefix faces.
- That smaller-simplex avoidance step is now formalized as well:
  `RentalHarmony/Section5Graph.lean` proves that any finite union of proper affine subspaces
  misses some point of the relative interior of `RentDivision (k + 1)`. The remaining milestone
  geometry is therefore one notch more specific: replace the finitely many lower-dimensional convex
  hulls arising from face images by proper affine subspaces of the smaller simplex, then transport
  the resulting avoided point back through `PrefixFace.equivRentDivision`.
- The convex-hull upgrade is now formalized too:
  `RentalHarmony/Section5Graph.lean` proves that any finite family of convex hulls generated by at
  most `k` points can be avoided in the relative interior of `RentDivision (k + 1)`. The
  remaining milestone-chain work is now the point transport / bookkeeping step: move those avoided
  smaller-simplex points back to the ambient prefix faces through `PrefixFace.equivRentDivision`
  and package them into a `Section5MilestoneChain` satisfying
  `Section5GraphNode.MilestoneSegmentTransversality`.
- That transport step is now also formalized abstractly:
  `PrefixFace.exists_smallPointInterior_not_mem_biUnion_convexHull_of_card_le` packages the
  smaller-simplex avoidance theorem directly on ambient prefix faces. So the remaining Section 5
  milestone work is now purely about the paper's actual forbidden families: identify, for each
  prefix level, the finite family of lower-dimensional face-image convex hulls to avoid, then use
  the transported prefix-face theorem to choose the milestone points and assemble the resulting
  `Section5MilestoneChain`.
- The forbidden-family identification is now formalized too:
  `RentalHarmony/Section5Graph.lean` defines `milestoneForbiddenFaces` and
  `milestoneForbiddenFamily`, proves the needed `≤ k` cardinality bound on every member of that
  family, and packages the resulting point choice as
  `exists_prefixMilestonePoint_avoiding_forbiddenFamily`. So the remaining Section 5 work is now
  the actual assembly step: combine those levelwise choices with the fixed start vertex and fixed
  terminal barycenter, then prove the resulting chain satisfies
  `Section5GraphNode.MilestoneSegmentTransversality`.
- That assembly is now in code:
  `chosenPrefixMilestonePoint` and `chosenMilestoneChain` provide the concrete milestone chain with
  fixed endpoints and chosen intermediate prefix-face points. The remaining Section 5 work is now
  purely the final transversality proof for that specific chain.
- The first half of that final proof is now done:
  `chosenMilestoneChain_nextMilestoneAwayFromBoundary_of_nonterminal` proves the
  `ImageContainsMilestoneAwayFromBoundary` clause for every nonterminal positive graph node in the
  concrete chain. So the remaining Section 5 milestone work is now the complementary open-segment
  clause together with the short graph-genericity packaging needed to build a full
  `Section5GraphNode.MilestoneSegmentTransversality` witness for `chosenMilestoneChain`.
- The next reduction step is now formalized too:
  `imageMeetsOpenMilestoneSegment_of_meets_of_not_containsMilestones`
  shows that the concrete open-segment goal is equivalent to excluding both segment endpoints from
  the face image, and
  `chosenMilestoneChain_openSegment_of_missingNextMilestone_of_not_lowerMilestone`
  specializes this to the chosen chain. This sharpened the remaining blocker enough to reveal a
  likely support-layer mismatch: the current
  `MilestoneSegmentTransversality.open_crossing_of_missing_nextMilestone` field demands more than
  the paper's local graph argument, because Section 5 still allows the lower endpoint `b_k` to act
  as a vertical door when the next milestone `b_{k+1}` is absent.
- That support-layer mismatch is now repaired locally:
  `MilestoneSegmentTransversality` no longer forces an open crossing in the missing-next case.
  Instead its explicit missing-next field allows either an open crossing or lower-milestone
  containment, exactly matching the paper's possibility of a vertical door at `b_k`. The concrete
  theorem
  `chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone`
  now proves this corrected branch for the chosen chain.
- The remaining Section 5 work is therefore no longer to repair the support target, but to bridge
  that lower-milestone-containment alternative to an actual vertical-door / two-neighbor
  consequence inside `GeometricGenericity`, then package the full concrete chosen-chain witness and
  feed it through the existing terminal-node and surjectivity wrappers.
- The latest domain-side reduction now makes that bridge target exact:
  `exists_graphNeighbor_of_lowerPrefixSubset_contains_lowerMilestone` shows that once one has an
  exact-size lower-prefix carrier subset of a positive face whose image convex hull contains the
  lower milestone, the codimension-`1` / vertical-door machinery is complete. So the remaining
  chosen-chain gap is no longer a vague lower-door existence statement. The new enlargement lemma
  `exists_graphNeighbor_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone` now isolates
  the real remaining issue even more tightly: it is enough to show that the lower-milestone
  support extracted in the all-image-lower case sits inside some lower-prefix carrier set of size
  at least `k + 1`.
- Rereading the manuscript settles that fork in favor of the stronger condition. In lines 385-393
  of the paper, the vertical clause still describes an edge of the already-defined graph `G`, so
  the lower `(k-1)`-face must itself be one of the graph vertices and thus still subdivide the
  lower prefix face. Therefore the frontier is no longer a graph-interface question. The exact
  missing ingredient is now a domain-side local-affinity/preimage theorem: from
  `ν.face.ImageContainsMilestone ... ν.level.castSucc`, extract an actual preimage point in
  `ν.face` whose positive barycentric support lies in the lower prefix face, yielding the needed
  lower-prefix carrier set of cardinality at least `k + 1`.
- The latest proof search isolates the real missing local statement even further. To derive that
  preimage point from `SubdivisionFace.ImageContains`, the current abstract subdivision data would
  need a compatibility theorem saying that when a point lies in the convex hull of a specified
  face or facet, its global `baryCoord` support can be taken inside that chosen face or facet.
  Without such a local-barycentric compatibility result, the repo does not yet justify the desired
  face-local affine/preimage theorem.
- Concretely, the direct proof attempt reduces to one missing support-file theorem of the form
  `x ∈ convexHull (facetVertexPoints T σ) -> supportingFacet x ⊆ σ` or equivalently
  `x ∈ convexHull (facetVertexPoints T σ) -> baryCoord v x = 0` for every `v ∉ σ`.
  The present `SimplicialSubdivision` API does not include that property, so the current Section 5
  frontier is blocked exactly on this local-barycentric compatibility theorem.
- The suggested fallback of using a purely image-local support witness from
  `Finset.mem_convexHull'` does not by itself solve the all-image-lower case. Such a witness only
  gives weights on image vertices, while the current `boundary_preserving` field is one-way and
  cannot turn zero image coordinates into zero domain coordinates. So the real missing ingredient
  remains a genuine domain preimage point with face-local barycentric support, or an explicit local
  affine API strong enough to recover one.
- The second stuck-recovery route is blocked for a similar reason. The present
  `SimplicialSubdivision` interface does not assert that facet vertex positions are affinely
  independent, that a facet convex hull is a genuine simplex with dense relative interior, or that
  a relative-interior point chooses a unique containing facet. Without those properties, the
  proposed proof that `φ.toFun` restricts on each facet to the corresponding local affine map
  cannot be carried out from the current abstractions.
- The third recovery suggestion also fails at the level of project structure: there is no concrete
  subdivision object anywhere in the repo to instantiate a richer geometric bundle against. The
  entire Section 5 and Sperner development is parameterized by an arbitrary
  `SimplicialSubdivision`, so any successful repair now has to strengthen that abstract support
  layer itself or thread stronger internal assumptions through the support lemmas.
- The latest spec-first refactor made that architecture gap explicit instead of leaving it diffused
  through `Section5Graph.lean`. The exact remaining lower-door contract is now recorded as
  `Section5GraphNode.FaceLocalLowerPrefixCarrierSpec.exists_graphNeighbor_of_contains_lowerMilestone`.
  This is the smallest compile-tested assumption under which the blocked lower-milestone branch can
  be resumed without changing the paper-facing files.
- The same refactor also showed that the rest of the Section 5 parity pipeline is already
  downstream-ready once a graph-local genericity package is supplied. Under an assumed
  `GeometricGenericity` for `chosenMilestoneChain`, the current repo now reconstructs
  `MilestoneSegmentTransversality`, proves terminal-node existence, and extracts a subdivision facet
  whose image contains the chain's terminal milestone. So the remaining hidden blockers are now
  sharply separated into:
  1. the lower-door support contract above;
  2. the start / two-door graph-local consequences needed to build
     `Section5GraphNode.ChosenMilestoneChainDoorSpec` for `chosenMilestoneChain`.
- That final endpoint wrapper is now finished. The new lemmas
  `prefixBarycenter_last_eq_barycentricRentDivision` and
  `chosenMilestoneChain_terminal_eq_barycenter` identify the last chosen milestone with the
  ambient simplex barycenter, and
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_doorSpec`
  shows that once the two remaining internal contracts are supplied, the whole Section 5 pipeline
  reaches the paper-faithful `FacetImageContainsBarycenter` conclusion.
- The lower-door contract has now been sharpened one step further. The genuinely geometric missing
  input is no longer phrased as a graph-neighbor theorem, but as the new internal support bundle
  `Section5GraphNode.FaceLocalLargeLowerPrefixCarrierSpec`, whose single field supplies the exact
  data consumed by
  `exists_graphNeighbor_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone`. The older
  contract `FaceLocalLowerPrefixCarrierSpec` is now just a derived wrapper.
- The second remaining contract has also been split into the graph-local shape actually forced by
  the current proofs. `Section5GraphNode.ChosenMilestoneChainGraphLocalSpec` separates the
  missing-next/lower-milestone branch into a level-`0` base case and a positive-level theorem that
  turns one known extra neighbor into the full two-door conclusion. Together with
  `FaceLocalLowerPrefixCarrierSpec`, it now derives the old `ChosenMilestoneChainDoorSpec`, and
  the new theorem
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_specs`
  shows that these two refined contracts already suffice for the downstream Section 5 barycenter
  cell conclusion.
- Recovery attempt 1 on the current stuck episode ruled out the suggested weaker vertex-level
  route. The repo cannot prove a converse of the form
  "image vertex has zero `ν.level.succ` coordinate implies domain vertex has zero
  `ν.level.succ` coordinate", even when the vertex lies in a chosen positive face, because the
  abstract field `PiecewiseLinearVertexMap.boundary_preserving` is only one-way. So the real
  remaining theorem is not a pointwise carrier-vertex lemma but a genuinely face-local lower-prefix
  reflection statement for positive faces: lower-target-prefix image support must yield a lower-
  domain-prefix carrier subset or subface whose image still contains the same lower milestone.
- Recovery attempt 2 indicates that this is not merely an unproved theorem but a likely false one
  for the current abstract API. The 2D configuration with lower-edge vertices
  `A = e_0`, `B = (1/2,1/2,0)`, interior vertex `C = (1/3,1/3,1/3)`, and images
  `φ(A)=e_0`, `φ(B)=e_0`, `φ(C)=(1/2,1/2,0)` satisfies the present one-way boundary conditions
  while making the full face image contain the lower milestone and every lower-domain carrier
  subset image miss it. So the correct project plan is no longer to derive the missing reflection
  theorem from the current fields, but to keep it as an explicit internal hypothesis or strengthen
  the abstract subdivision / PL-map support layer so that such counterexamples are ruled out by
  construction.
- Recovery attempt 3 has now implemented that architectural repair. The new internal bundle
  `Section5GraphNode.PositiveFaceLowerPrefixReflection` states exactly the necessary face-local
  reflection property for positive faces. From it one immediately derives
  `FaceLocalLargeLowerPrefixCarrierSpec`, and the new theorem
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec`
  confirms that the rest of the higher-dimensional Section 5 argument already runs cleanly under
  this single stronger interface together with `ChosenMilestoneChainGraphLocalSpec`.
- A direct attempt on the remaining concrete chosen-chain graph-local package shows that the first
  unresolved field is now genuinely 1-dimensional: the level-`0` missing-next case needs an
  interval-style lower-boundary continuation theorem for subdivision faces on the first prefix
  edge. Concretely, if a start-incident edge contains `c_0` but misses `c_1`, one needs a proof
  that it has exactly one second graph door besides `.start`. The present `SubdivisionFace` and
  `Adj` APIs do not yet package that boundary-interval decomposition fact.
- A concrete overlap countermodel shape now suggests this level-`0` theorem is also not derivable
  from the current abstract face API. Distinct lower-edge faces `{e_0,B_i}` coming from different
  facets can all be start-incident and horizontally adjacent through the shared vertex `{e_0}`,
  so one can get more than one "second door" unless the first prefix face is known to decompose as
  a genuine 1-dimensional simplicial complex / interval subdivision. Therefore the remaining plan
  is not to force `ChosenMilestoneChainGraphLocalSpec.two_doors_of_missing_nextMilestone_level_zero`
  from the present definitions, but to treat that interval-uniqueness property as additional
  internal support data or to strengthen the subdivision-face layer accordingly.
- That reduction has now been implemented explicitly. The normalized 1-dimensional continuation
  input is isolated as `Section5GraphNode.ChosenMilestoneChainLevelZeroBoundarySpec`, while the
  remaining start/open-crossing/positive-level data sits in
  `Section5GraphNode.ChosenMilestoneChainGraphLocalRestSpec`. The new wrapper
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec'`
  shows that these two graph-local pieces together with `PositiveFaceLowerPrefixReflection` are
  exactly sufficient for the downstream Section 5 barycenter-cell conclusion.
- The level-`0` boundary split has now been tightened once more: the start-node existence and
  uniqueness fields are also part of the same boundary interval model, so they have moved into
  `ChosenMilestoneChainLevelZeroBoundarySpec`. This leaves
  `ChosenMilestoneChainGraphLocalRestSpec` as a genuinely higher-dimensional remainder consisting
  only of the open-crossing branch and the positive-level continuation statements.
- A first direct attempt on that higher-dimensional remainder shows that the open-crossing branch is
  not derivable from the present abstract image model either. If all image vertices of a positive
  face lie on the milestone segment, then the full face and multiple codimension-`1` subfaces can
  all meet the same open segment point, so a raw "exactly two doors" theorem fails without an
  additional transversality / nondegeneracy hypothesis. Therefore the next support-layer question is
  no longer about lower-boundary interval geometry, but about imposing or isolating the minimal
  higher-dimensional transversality input needed for `ChosenMilestoneChainGraphLocalRestSpec`.
- That higher-dimensional input is now isolated explicitly as
  `Section5GraphNode.ChosenMilestoneChainOpenCrossingSpec`, while the still-separate positive-level
  continuation data is packaged as `Section5GraphNode.ChosenMilestoneChainPositiveLevelSpec`. The
  wrapper `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''`
  confirms that the full downstream Section 5 barycenter-cell pipeline now closes under four
  explicit internal contracts only: lower-prefix reflection, the normalized level-`0` boundary
  model, the open-crossing transversality input, and the remaining positive-level continuation
  package.
- The positive-level continuation package has now been reduced one step further using the proved
  theorem `chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone`.
  The genuinely remaining positive-level inputs are now only
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelLowerMilestoneSpec` and
  `Section5GraphNode.ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec`; the open-crossing
  branch no longer belongs to that package. The new wrapper
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec'''`
  shows that these sharper contracts suffice for the downstream barycenter-cell theorem.
- The lower-endpoint positive-level branch has now been sharpened again: the auxiliary hypothesis
  that some extra graph neighbor already exists is no longer part of the minimal frontier.
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec` packages the bare
  two-door conclusion for the lower-milestone case itself, and the wrapper
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''''`
  shows that this stronger/minimal contract is exactly what the downstream Section 5 pipeline
  needs.
- The positive-level missing-next case can now be phrased even more sharply. Since the support file
  already proves `chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone`,
  the residual branch after the fixed open-crossing contract is simply the complement
  "not open crossing". This is now isolated as
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec`, and
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec_noOpenCrossing`
  shows that the Section 5 barycenter-cell pipeline closes under that sharper complement-case
  contract together with the existing reflection, level-`0` boundary, open-crossing, and
  away-from-boundary inputs.
- A direct check of that complement-case branch now identifies the next missing abstract theorem:
  genuine codimension-`1` incidence uniqueness in the prefix-face subdivision. The current
  `SubdivisionFace` layer only remembers that a face is a nonempty subset of some facet, so it
  does not know that a geometric codimension-`1` face should have a unique carrier representation
  or exactly two incident cofaces. The no-open-crossing positive-level theorem therefore appears to
  need a stronger simplicial-complex/pseudomanifold incidence API, or an explicit local contract
  asserting that the lower-milestone codimension-`1` face has unique continuation.
- The first repair step for that issue is now in place. The support file contains a normalized
  codimension-`1` carrier object `SubdivisionFace.CarrierCodimOneSubface`, together with the new
  carrier-level contract
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec`.
  So the remaining no-open-crossing frontier is now phrased at the correct carrier/incidence layer:
  prove unique same-level continuation across the normalized lower-milestone codimension-`1` face,
  then use it to recover the graph-door count.
- A direct check at that carrier level shows the new contract is genuinely independent of the
  current abstract subdivision fields. Even after quotienting away raw-face syntax, the
  `SimplicialSubdivision` API still allows a codimension-`1` carrier finset to be contained in
  three or more facets, because no pseudomanifold or simplicial-complex incidence axiom is
  recorded. So the remaining plan is now explicit: either strengthen the subdivision layer with
  codimension-`1` coface uniqueness, or keep
  `ChosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec` as the minimal extra
  internal hypothesis.
- The next refinement sharpens that requirement to the graph-relevant part actually used by the
  Section 5 parity argument. `RentalHarmony/Section5Graph.lean` now defines
  `Section5GraphNode.IsSameLevelCarrierContinuationCandidate` and packages the filtered theorem
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec`,
  which asks only for uniqueness among same-level positive cofaces through the normalized carrier
  that could contribute a second graph door. The older carrier-continuation contract is now derived
  from this filtered version by
  `Section5GraphNode.chosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec_of_filteredSpec`.
  So the remaining no-open-crossing plan is now even sharper: prove or assume filtered
  graph-relevant continuation uniqueness, not blanket coface uniqueness in the subdivision.
- The first local proof obligations around that filtered statement are now discharged. Monotonicity
  lemmas for `ImageContains*` and `ImageMeets*` along carrier inclusions are formalized, and the
  support file now proves that a filtered candidate gives an actual same-level horizontal graph
  door, while any horizontal same-level door in the no-open-crossing branch yields a normalized
  lower-milestone carrier candidate. So the remaining plan is no longer to bridge carrier geometry
  to graph adjacency; it is specifically to prove existence and uniqueness of those graph-relevant
  same-level candidates.
- A direct attempt on that existence/uniqueness theorem identifies the first missing half: same-
  level continuation existence. Once a same-level horizontal door is present, the new lemmas
  recover the filtered candidate automatically, so uniqueness is not the immediate blocker. The
  actual obstruction is earlier: from a normalized codimension-`1` carrier inside `ν.face`, the
  current `SimplicialSubdivision` API gives only one containing facet via `subset_facet`, not a
  second same-level positive coface. So the next viable plan is to supply exactly that local
  same-level continuation-existence theorem, or to keep it as the minimal no-open-crossing
  internal contract if it cannot be proved from the present abstract subdivision data.
- The latest recovery attempt also closes off one tempting false route. The support file now
  formalizes that the existing lower-prefix reflection machinery yields a downward vertical
  neighbor, via
  `exists_verticalAdj_of_contains_lowerMilestone_of_largeLowerPrefixCarrierSpec` and
  `exists_verticalAdj_of_contains_lowerMilestone_of_reflection`. So the remaining no-open-crossing
  existence problem is not to reclassify that reflected neighbor as horizontal; it is to find an
  additional same-level continuation beyond the already-known vertical door.
- The countermodel-style check for the post-bridge local interface goes through conceptually as
  well: once one forgets the ambient subdivision and keeps only `ν`, the normalized carrier `ρ`,
  and the already-proved downward vertical door, there is no remaining formal invariant that forces
  a same-level continuation. So the roadmap should now treat same-level continuation existence as a
  genuinely new local theorem (or contract), not as something recoverable from the present bridge
  lemmas plus reflection.
- Do not introduce axioms: this surjectivity lemma is the main internal theorem to supply.

### Generalizations
- Reuse the same balanced-cell existence result.
- Keep the lattice-point and weighted-average arguments finite and combinatorial after that point.

## Immediate next steps
- Use the new barycentric-coordinate model to prove the global Section 5 surjectivity theorem for
  face-preserving simplex self-maps.
- The supporting-facet, continuity, and derived `toFun` lemmas are now proved, as is the rebuilt
  Sperner extension theorem.
- The dimension-`1` surjectivity base case is now proved by transporting the simplex to
  `unitInterval` and applying the intermediate value theorem, so the next geometric step is the
  higher-dimensional argument rather than more interval infrastructure.
- The new homotopy and boundary-restriction infrastructure shows exactly where the higher-
  dimensional proof now stops:
  either add a noncontractibility theorem for `SimplexBoundary dimension`, or switch routes and
  formalize the Section 5 face-incidence graph after extending the support layer with an explicit
  face-poset / adjacency API.
- The face-poset / adjacency API is now present in `RentalHarmony/Section5Graph.lean`, so the next
  concrete proof step is no longer another interface change: the Section 5 graph itself is now
  formalized, the finite-graph parity lemma is proved, and the graph is parameterized by the
  paper's perturbed milestone chain. The abstract graph conclusion is now packaged twice:
  once at the degree level by `Section5GraphNode.exists_terminal_of_localDegreeHypotheses`, and
  once at the paper-faithful case-split level by `Section5GraphNode.exists_terminal_of_geometricGenericity`.
  The new concrete target `Section5GraphNode.MilestoneSegmentTransversality` sharpens this one
  step further, so the next missing proof is now exactly the geometric claim that a suitably
  generic milestone chain has open segment crossings and away-from-boundary milestone hits in the
  sense recorded there. At the moment this reduces to a missing support theorem about choosing
  points in the relative interior of prefix simplex faces away from finitely many lower-dimensional
  convex hulls. That smaller-simplex convex-hull avoidance theorem is now proved, so the next
  missing argument is the proof that the concrete chain `chosenMilestoneChain` witnesses
  `Section5GraphNode.MilestoneSegmentTransversality`. The away-from-boundary half of that claim is
  now formalized, and the remaining open-segment half has been reduced to lower-milestone
  exclusion. That reduction in turn suggests that the current transversality package is too strong
  for the paper's actual argument, so the next step is likely to weaken/refactor the missing-next
  case so it counts doors at `b_k` rather than forbidding them outright.
- Then feed surjectivity into the already-proved wrappers in `PaperTheorems.lean` to recover the
  barycenter-cell and Sperner statements.
- Turn the Hall witness wrapper theorems into actual proofs by extracting the paper's
  `k + 1`-labels-for-`k`-agents counting lemma from the geometric cell.
- The no-open-crossing positive-level continuation theorem has now been split into its true two
  local ingredients:
  `ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec` and
  `ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec`. This confirms that the
  current blocker is specifically existence of a same-level continuation through the normalized
  lower-milestone carrier; uniqueness is a separate later step.
- The downstream carrier-continuation layer now runs through that split interface, so the support
  dependency is explicit. A scan of the current development still shows no theorem giving
  same-level codimension-`1` coface uniqueness, so unless such a simplicial-complex uniqueness
  lemma is added, `ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec` should
  be treated as a separate local input after the existence half.
- The existence half has now been sharpened once more. Using the fixed reflection contract,
  `exists_lowerMilestoneCarrier_of_not_openCrossing_of_reflection` manufactures the normalized
  lower-milestone carrier automatically, so the remaining existence theorem is only
  `ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec`: continue through a
  given carrier. The carrier-continuation wrapper has been rethreaded through this sharper split,
  leaving exactly fixed-carrier existence plus fixed-carrier uniqueness as the no-open-crossing
  local inputs after reflection.
- The filtered wrapper itself is now also routed through this sharper split, so the remaining
  dependency chain is fully explicit. A direct repo search still finds no theorem extending a
  codimension-`1` prefix-face carrier to a same-level prefix-face coface, which is exactly the
  content now isolated in `ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec`.
- More precisely, the present API only has the downward lemma
  `SubdivisionFace.subdividesPrefixFace_of_subface` plus raw ambient-facet existence
  `subset_facet`; it has no upward extension theorem from a codimension-`1` prefix-face carrier to
  a distinct same-level prefix-face coface. That asymmetry is now the concrete proof-theoretic
  reason the fixed-carrier continuation theorem remains open.
- That missing step is now also packaged in a more geometric, facet-local form as
  `ChosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec`. The existing continuation and
  filtered-wrapper theorems are routed through this coface-extension interface, so the remaining
  support dependency can now be stated either combinatorially or in the paper's same-level
  coface-extension language without changing the downstream wrapper chain.
- The same gap is now isolated one layer lower in the single-simplex language suggested by the
  paper: `ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec` asks for a second
  same-level coface inside one ambient facet `σ` containing `ν.face`. The existing coface-
  extension and no-open-crossing wrapper chain is routed through that ambient-facet interface, so a
  future simplex-level segment-exit lemma can plug in without changing downstream statements.
- Even that ambient-facet theorem has now been split into a purely domain-side extension statement
  `ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec` plus automatic
  image-side promotion: once a same-level face inside `σ` contains the lower-milestone carrier, it
  automatically becomes a positive node by monotonicity of `ImageContainsMilestone`. The remaining
  local geometric burden is therefore the existence of that same-level prefix-face coface.
- The direct proof is now reduced one concrete step further without changing the interface: the new
  helper `exists_sameLevelPrefixFace_in_ambientFacet_of_freshPrefixVertex` shows that a single
  fresh vertex of the ambient facet already lying in the larger prefix face is enough to build the
  required same-level coface explicitly. Thus the unresolved content of
  `ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec` is now exactly the
  existence of such a fresh prefix-face vertex in the chosen ambient facet.
- A new obstruction lemma now shows that this fresh-vertex reduction is not uniform in dimension:
  `ambientFacet_eq_of_topDim` and `no_freshAmbientFacetVertex_of_topDim` prove that when the
  current positive face is already top-dimensional, any ambient facet containing it must equal it,
  so there is no fresh ambient-facet vertex at all. Therefore the current reduction can only solve
  the below-top-dimensional part directly; the full prefix-extension theorem still needs either a
  separate top-dimensional continuation argument or a different uniform geometric input.
- The complementary branch is now sharper too:
  `exists_freshAmbientFacetVertex_of_lt_topDim` proves that below top dimension a fresh ambient-
  facet vertex exists automatically by card-counting. Combined with
  `not_exists_sameLevelPrefixFace_in_ambientFacet_of_topDim`, this means the remaining obstruction
  has bifurcated cleanly:
  in the below-top-dimensional branch, only the extra prefix-face condition on that fresh vertex is
  still missing;
  in the top-dimensional branch, the current ambient-facet prefix-extension conclusion itself is
  impossible and must eventually be replaced by a different continuation statement.
- The support layer now reflects that route change explicitly at the two-door level rather than at
  the impossible ambient-facet continuation level.
  `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneDoorSpec` isolates the direct
  top-dimensional door theorem still missing, while
  `ChosenMilestoneChainPositiveLevelBelowTopDimLowerMilestoneDoorSpec` isolates the surviving
  below-top-dimensional continuation route. The original paper-facing lower-milestone contract is
  recovered by `chosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec_of_topDim_and_belowTopDim`.
- The top-dimensional branch has now been sharpened once more to the exact first missing local
  input. `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec` asks only
  for two distinct codimension-`1` lower-prefix carriers of the top-dimensional face that both
  contain the lower milestone. The new constructor
  `verticalNeighborOfCodimOneSubfaceContainsLowerMilestone` and theorem
  `exists_two_distinct_verticalNeighbors_of_topDimLowerMilestoneCarrierMultiplicity` show that
  this multiplicity statement is already sufficient to produce two distinct vertical graph doors.
  So the remaining top-dimensional work is no longer general graph bookkeeping; it is the
  geometric multiplicity theorem for lower-milestone codimension-`1` subfaces.
- That top-dimensional multiplicity theorem has now been reduced one step further. The reflection
  layer already provides the first normalized lower-prefix carrier by
  `exists_lowerMilestoneCarrier_of_reflection`, so the genuinely remaining local input is now
  `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierSpec`: given one such carrier
  in a top-dimensional positive face that misses the next milestone, produce a second distinct
  lower-prefix codimension-`1` carrier containing the same lower milestone. The new reductions
  `chosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec_of_reflection_and_secondCarrier`
  and
  `exists_two_distinct_verticalNeighbors_of_reflection_and_topDimLowerMilestoneSecondCarrier`
  show that this sharper second-carrier theorem is exactly what remains before the top-dimensional
  branch reaches the two-door target.
- A new codimension-`1` coverage lemma now sharpens that frontier further.
  `SubdivisionFace.mem_of_mem_codimOneSubface_or_other` and
  `SubdivisionFace.subdividesPrefixFace_of_two_distinct_codimOneSubfaces` prove that if one face
  has two distinct codimension-`1` subfaces both lying in the same prefix outer face, then the
  whole face already lies in that prefix face. Consequently
  `faceSubdividesLowerPrefix_of_reflection_and_topDimLowerMilestoneSecondCarrier` shows that any
  successful proof of the top-dimensional second-carrier theorem automatically forces the entire
  top-dimensional positive face into the lower prefix face. So the remaining top-dimensional gap is
  now explicitly image-side: once all vertices of `ν.face` are in the lower prefix face, prove
  that the lower milestone is carried by a second codimension-`1` subface besides the reflected
  one.
- That image-side frontier is now isolated explicitly in Lean as
  `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec`. The reduction
  `exists_second_codimOneSubface_of_faceSubdividesLowerPrefix` shows that once the whole
  top-dimensional face already subdivides the lower prefix face, it is enough to find a second
  codimension-`1` subface whose image contains the lower milestone; the lower-prefix carrier
  condition for that second subface is then recovered automatically from
  `SubdivisionFace.subdividesPrefixFace_of_subface`. So the next proof search should stay on this
  image-side convex-geometry statement rather than reopen domain-side carrier bookkeeping.
- The frontier has now been lowered to the exact point-level version of that image statement.
  `ChosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec` asks for a point `x`
  already lying in the image of one codimension-`1` subface of a top-dimensional positive face in
  the lower prefix face to lie in the image of a second distinct codimension-`1` subface as well.
  The theorem
  `chosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec_of_boundaryPointMultiplicity`
  specializes this directly to the lower milestone `b_k`. So the next proof search should target
  this point-on-two-face-images lemma, which is the sharp local image-side convex-geometry gap now
  exposed by the Lean development.
- That point-level gap is now reduced one step further by a reusable constructive bridge.
  `exists_second_codimOneSubface_imageContains_of_subset_in_codimOneSubface` proves that if a
  point already lies in the image of one codimension-`1` subface and its image support can be
  shrunk inside that subface by one more vertex, then the point automatically lies in the image of
  a second distinct codimension-`1` subface of the ambient top-dimensional face. The new contract
  `ChosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec` packages exactly that
  support-shrinking existence statement, and
  `chosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec_of_supportShrink` reduces
  the earlier point-on-two-face-images contract to it. So the next proof search should target this
  support-shrink existence theorem rather than the two-face conclusion directly.
- That support-shrink theorem is now reduced once more to the exact local support-pruning step.
  `ChosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec` asks: inside a fixed
  codimension-`1` face image already carrying a point `x`, and for any supporting vertex set
  inside that face, remove one additional vertex while keeping `x` in the same image convex hull.
  The new reduction
  `chosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec_of_oneVertexDrop`
  shows that iterating this one-step drop recovers the full support-shrink contract. So the
  remaining top-dimensional proof search should now target this single-vertex support-reduction
  lemma.
- The support-pruning frontier is now factored through its exact affine-dependence criterion.
  `exists_smaller_support_of_mem_convexHull_of_not_affineIndependent_image` proves that any point
  in the convex hull of a finite vertex image set already admits a one-vertex drop as soon as that
  image set is affinely dependent, and
  `chosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec_of_affineDependentImage`
  specializes this to the current top-dimensional codimension-`1` face setting. So the remaining
  proof search should now target the image-side statement that the support inside the first
  codimension-`1` face image is affinely dependent under the Section 5 hypotheses.
- The sharpest obstruction to that route is now formalized too.
  `not_exists_smaller_support_of_pair_of_mem_openSegment` proves that if the first codimension-`1`
  face image carries the point `x` by a nondegenerate two-point segment support, then one-vertex
  drop is impossible. So the next proof search should either derive affine dependence from the
  Section 5 hypotheses or prove that this nondegenerate segment case cannot occur in the relevant
  top-dimensional branch.
- The latest interface correction shows that this support-pruning route is stronger than the graph
  actually needs. The graph only consumes the `¬ openCrossing` branch, and paper lines 395--396
  ask only for the local door count there. The new reductions
  `chosenMilestoneChain_contains_lowerMilestone_of_missingNextMilestone_of_not_openCrossing`,
  `chosenMilestoneChainPositiveLevelNoOpenCrossingSpec_of_lowerMilestoneDoorSpec`, and
  `chosenMilestoneChainPositiveLevelNoOpenCrossingSpec_of_topDim_and_belowTopDim`
  move the exact frontier to a top-dimensional no-open-crossing theorem rather than the stronger
  one-vertex-drop / second-carrier route. So the next proof search should either prove
  `ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec` directly or isolate a compatible
  counterexample pattern showing that even this corrected top-dimensional interface still needs
  revision.
- That compatible counterexample pattern is now formalized precisely. The new theorems
  `not_exists_sameLevelCarrierContinuationCandidate_of_uniqueFacetContainingCarrier`,
  `eq_verticalNeighbor_of_adj_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly`,
  and
  `not_exists_two_distinct_neighbors_of_topDim_noOpenCrossing_of_uniqueLowerMilestoneCarrier_boundaryOnly`
  show that if the only codimension-`1` lower-milestone carrier of a top-dimensional positive face
  lies in a unique ambient facet, then there is no same-level continuation through it and every
  graph neighbor collapses to the single canonical vertical door. So the next exact top-dimensional
  proof step is not more support pruning; it is to prove that the actual Section 5 hypotheses rule
  out this boundary-only unique-carrier pattern, or else to revise the interface again.
- That reassessment point is now packaged explicitly as data. The structure
  `TopDimNoOpenCrossingBoundaryOnlyUniqueCarrierCounterexampleData` records exactly the local
  hypotheses needed for the one-door obstruction, and
  `not_topDimNoOpenCrossingDoorSpec_of_boundaryOnlyUniqueCarrierCounterexampleData` shows that any
  realization of this data outright refutes the current theorem
  `ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingDoorSpec`. So the current top-dimensional
  frontier is now binary rather than diffuse:
  either derive from the intended genericity hypotheses that such data cannot occur, or revise the
  theorem statement before returning to the below-top-dimensional branch.
- The missing local geometry is now isolated more sharply as a two-step paper-faithful interface.
  `ChosenMilestoneChainCodimOneFaceSegmentInteriorWitnessSpec` packages lines 389--391 as an
  image-side surrogate: when a codimension-`1` face meets `[b_k,b_{k+1}]`, it already contains a
  segment point away from its own boundary. `ChosenMilestoneChainTopDimBoundaryCarrierEscapeSpec`
  then isolates the remaining top-dimensional segment-crossing statement: on a boundary-only unique
  lower-milestone carrier, such a point forces either an open crossing of the ambient top-dimensional
  face or containment of `b_{k+1}`. The theorem
  `not_boundaryOnlyUniqueCarrierCounterexampleData_of_segmentInteriorWitness_and_escape`
  proves that exactly this witness-plus-escape package rules out the current obstruction.
- The route change prompted by that obstruction is now also explicit in Lean. The new theorems
  `existsUnique_graphNeighbor_of_boundaryOnlyUniqueCarrierCounterexampleData` and
  `existsUnique_verticalAdj_of_boundaryOnlyUniqueCarrierCounterexampleData` prove that the
  packaged top-dimensional counterexample is not just a failure of degree `2`; it is a genuine
  one-door forced-descent node with a canonical lower vertical neighbor. The new weaker interfaces
  `ChosenMilestoneChainPositiveLevelTopDimNoOpenCrossingAlternativeSpec` and
  `ChosenMilestoneChainPositiveLevelNoOpenCrossingAlternativeSpec` record exactly the current
  local alternatives now supported by Lean: either two doors, or exact boundary-only unique-carrier
  counterexample data. The reduction
  `chosenMilestoneChainPositiveLevelNoOpenCrossingSpec_of_alternative_and_counterexampleExclusion`
  then identifies the precise downstream gap. To recover the old graph-local theorem one must
  either derive a genuine exclusion of the packaged obstruction from the paper's geometry, or
  replace the present parity/local-degree package by a contraction argument that consumes this
  forced-descent alternative.
- The parity mismatch is now isolated exactly rather than heuristically. The abstract structure
  `LocalDegreeOrDescentHypotheses` and the concrete theorem
  `chosenMilestoneChain_localDegreeOrDescentHypotheses_of_alternativeSpecs`
  show that the chosen-chain geometry already reaches the correct local continuation interface
  supported by Lean. On the other hand,
  `not_localDegreeHypotheses_of_boundaryOnlyUniqueCarrierCounterexampleData`,
  `degree_positive_eq_one_of_boundaryOnlyUniqueCarrierCounterexampleData`, and
  `not_even_degree_of_boundaryOnlyUniqueCarrierCounterexampleData`
  prove that a boundary-only unique-carrier obstruction is a genuine nonterminal degree-`1` node.
  So the exact remaining Section 5 theorem is now the graph-level contraction/descent step that
  bypasses such nodes in the terminal-node existence argument; the current parity package fails
  there for a precise structural reason, not because of another unresolved local geometry detail.
- The first replacement theorem for that failed parity package is now formalized too.
  `exists_terminal_or_boundary_of_odd_start_and_nonterminal_even_off_boundary`
  is the abstract finite-graph version: once odd nonterminal nodes are allowed only inside a
  designated boundary predicate, parity yields either a terminal node or a boundary node. Its
  chosen-chain specialization
  `exists_terminal_or_boundaryOnlyUniqueCarrierCounterexampleData_of_alternativeSpecs`
  shows that the present Section 5 local hypotheses already imply the exact disjunction
  "terminal face or packaged boundary-only unique-carrier obstruction." This makes the remaining
  contraction lemma precise: consume the right-hand branch of that theorem.
- That final reduction is now packaged as an explicit support theorem rather than only as prose.
  `ChosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec` is the minimal remaining graph-level
  interface: from explicit packaged obstruction data, produce a terminal node anyway. The theorem
  `exists_terminal_of_chosenMilestoneChain_alternativeSpecs_and_bypass`
  shows that once such a bypass spec is proved, the current chosen-chain alternative local theory
  is already sufficient for terminal-node existence.
- The bypass frontier is now sharpened one more step inside the obstruction branch itself.
  `existsUnique_graphNeighbor_ne_counterexampleNode_of_verticalAdj_boundaryOnlyUniqueCarrierCounterexampleData`
  proves that once one descends from a packaged obstruction node `ν` to its canonical vertical
  neighbor `μ`, that lower node has a unique continuation neighbor distinct from `ν`. The new
  reductions
  `exists_terminal_of_boundaryOnlyUniqueCarrierCounterexampleData_of_exists_terminal_of_continuationNeighbor`
  and
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_continuationNeighborTerminal`
  show that pure terminal existence now reduces exactly to proving eventual terminal existence from
  that continuation neighbor. So the remaining Section 5 gap is no longer an unspecified bypass;
  it is the continuation-neighbor theorem after the forced vertical descent.
- That continuation split is now sharper in the high-dimensional range. The theorems
  `not_adj_positive_start_of_verticalAdj_boundaryOnlyUniqueCarrierCounterexampleData_of_two_lt_dimension`,
  `exists_terminal_of_boundaryOnlyUniqueCarrierCounterexampleData_of_exists_terminal_of_positiveContinuationNeighbor_of_two_lt_dimension`,
  and
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_positiveContinuationNeighborTerminal_of_two_lt_dimension`
  show that when `2 < dimension`, the continuation door after the forced descent cannot be
  `.start`; it must be another positive graph node. So the genuinely unresolved bypass issue is
  now split cleanly:
  in higher dimensions, prove eventual terminal existence from that positive continuation node;
  in the lowest top-dimensional case, understand or exclude the residual start-continuation
  configuration.
- The higher-dimensional positive-continuation branch is now sharper again.
  `eq_counterexampleNode_of_upperAdj_verticalNeighbor_of_boundaryOnlyUniqueCarrierCounterexampleData`
  proves that a descended node `μ` cannot have a second upper neighbor distinct from the original
  obstruction node `ν`: the boundary-only unique ambient-facet clause forces any upper coface of
  `μ.face` to be `ν.face` itself. Therefore every distinct continuation after the forced descent
  must live at strictly lower level, which is formalized in
  `level_lt_of_positiveContinuationNeighbor_of_verticalAdj_boundaryOnlyUniqueCarrierCounterexampleData`.
  The reduction
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_lowerLevelPositiveContinuationNeighborTerminal_of_two_lt_dimension`
  packages the exact new frontier: in higher dimensions, it now suffices to prove terminal
  existence from a strictly lower-level positive continuation node.
- That frontier is now cut down one more step.
  `face_dim_lt_of_positiveContinuationNeighbor_of_verticalAdj_boundaryOnlyUniqueCarrierCounterexampleData`
  turns the strict level drop into an honest below-top-dimensional face inequality, and
  `chosenMilestoneChainBoundaryOnlyUniqueCarrierBypassSpec_of_belowTopDimPositiveTerminal_of_two_lt_dimension`
  shows that the whole higher-dimensional obstruction branch disappears as soon as one proves a
  single abstract theorem: every below-top-dimensional positive chosen-chain node eventually leads
  to a terminal node. This is now the exact remaining high-dimensional graph theorem.

## Current input status
- No proposed axioms.
- No human input is required at the moment.
