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

## Current input status
- No proposed axioms.
- No human input is required at the moment.
