# Paper Notes

## Corrections And Clarifications
- `Introduction`, `Section 3`, and `Section 4`: the "one-cent error margin" hypothesis is doing real work. The proofs sample preferences at the vertices of a sufficiently fine triangulation and then treat those labels as simultaneously valid for one actual rent division coming from the simplex they span. In Lean, this should be encoded as a finite triangulation scale/tolerance assumption, not left informal.
- `Section 2, Proof 2` (around lines 194-208): the implication "boundary degree one => surjective" is deferred to `Section 5`. For formalization, isolate a separate lemma for piecewise-linear self-maps of a simplex that preserve every face setwise.
- `Section 3, Proof 1` (around lines 232-240): the compression from pair labels `(a,b)` to single labels `1,2,3` hides a real combinatorial lemma. A small triangle carrying all three compressed labels forces:
  Larry to accept at least two rooms;
  Moe to accept at least two rooms;
  across Larry and Moe, all three rooms to occur.
  Together with the tolerance assumption, this is what lets one pass from nearby sampled vertices to one fair rent division.
- `Section 3, Proof 2` (around lines 260-265): the choices at the three original vertices must be fixed in a cyclic pattern so that the averaged map has degree one on the boundary. This is allowed because both known roommates are indifferent among the two free rooms at each original vertex.
- `Section 4` (around lines 283-302): the cyclic relabeling argument needs to be unpacked carefully. For a proper face `σ = conv {e_i | i ∈ I}`, the vertex labels induced by the cycle `π` are `π(I)`. Because `π` is a single `n`-cycle, `π(I)` cannot be contained in `I`; hence some vertex of `σ` is labeled by a free room. Since roommates are indifferent among free rooms, every subdivision vertex on that face may be assigned such a free-room label. After relabeling the outer simplex vertices by `π`, each roommate's labeling is genuinely Sperner.
- `Section 4` (around lines 304-315): once `λ(x)` is the barycenter, `x` must lie in a full-dimensional simplex `τ`, not merely an arbitrary face of the triangulation. Otherwise `λ(x)` would lie in the convex hull of too few room labels. This full-dimensionality is used implicitly when Hall's theorem is invoked.
- `Section 5`: the 2-dimensional path-following proof is believable after the stated generic perturbation, but the higher-dimensional argument is only a sketch. For a formal proof, one should either:
  make the graph/parity argument explicit in all dimensions, including the degree counts for the graph `G`; or
  replace this section by a separate topological surjectivity lemma already available in mathlib, if that is allowed by the project style.
- Formalization note after early proof work:
  the first abstract Lean interface for `SimplicialSubdivision` / `PiecewiseLinearVertexMap` was
  too weak for the Section 2 and Section 5 existence statements. A concrete counterexample existed
  already in dimension `1`: take two subdivision vertices, let both have `boundaryFace = {0}`, let
  the unique facet be the whole `2`-element vertex set, and map both vertices to the simplex
  vertex `e_0`. This satisfied the old `boundary_preserving` field, but no facet image contained
  the barycenter and no Sperner labeling could be fully labeled. The interface has now been
  repaired by adding geometric vertex positions, simplex-cover data, and an actual
  `PiecewiseLinearSimplexMap` with a cellwise image-realization field.
- Formalization note after attempting the Sperner extension lemma:
  the repaired interface still needed two more exactness fields. First, `boundaryFace` cannot be
  merely a superset of the allowable labels; it must be the exact outer face determined by the
  zero coordinates of the subdivision vertex. Otherwise a 1-simplex with the two genuine boundary
  vertices `e_0, e_1` but `boundaryFace = {0,1}` at both ends admits the constant label `0`, which
  is a Lean-checkable counterexample to the current Section 2 statement. Second,
  `PiecewiseLinearSimplexMap` must remember that its underlying map sends each subdivision vertex
  to the prescribed `vertexMap`; without that interpolation field, the desired extension lemma is
  not even stated accurately. These exactness requirements are now part of the paper-facing
  definitions.
- Formalization note after continuing the extension proof:
  even with the exact-face repair, the extension lemma is still false unless subdivision vertices
  have unique geometric positions. A Lean-checkable counterexample uses two distinct interior
  vertices placed at the same barycentric point of a 1-simplex and labeled `0` and `1`. The new
  `map_vertex` field then forces any extension map to take the same input point to both simplex
  vertices simultaneously. The paper-facing subdivision interface therefore also needs
  `vertexPos` to be injective.
- Formalization note after continuing the extension proof further:
  the repaired interface still needed one more simplicial-complex incidence condition:
  every subdivision vertex must belong to at least one full-dimensional facet. Otherwise one can
  add an "isolated" interior vertex that is not used by any facet, label it by a room absent from
  the image labels of every facet containing that geometric point, and then the `map_vertex` field
  forces a value that no `map_mem_facetImage` witness can realize. The paper-facing subdivision
  interface therefore now also records `vertex_in_some_facet`.
- Formalization note after proving the Sperner extension:
  the current `PiecewiseLinearSimplexMap` interface is still too weak for the Section 5
  surjectivity theorem. A Lean-checkable 1-dimensional counterexample uses the honest boundary
  subdivision with vertices `e_0, e_1` and the map `f(x) = e_0` if `x_0 = 1`, `f(x) = e_1`
  otherwise. This satisfies the current fields:
  `map_vertex` holds at the two subdivision vertices;
  `map_mem_facetImage` holds because the unique facet image is the whole interval;
  `boundary_preserving` holds because `f(e_0) = e_0` and every other point is sent to `e_1`.
  But `f` is not surjective. So the surjectivity statement is false under the current encoding
  until `PiecewiseLinearSimplexMap` is strengthened to record actual affine-on-cells / continuity
  data, not only pointwise facet-image membership.
- Formalization note after the coherent repair:
  the paper-facing interface now rules out that step-map counterexample by construction. A
  subdivision records global continuous barycentric-coordinate functions together with a chosen
  supporting facet, and a `PiecewiseLinearSimplexMap` is no longer an arbitrary function but the
  derived center-of-mass map from its vertex images. The basic interpolation lemmas
  (`map_vertex`, `map_mem_facetImage`, continuity, boundary-face preservation) and the canonical
  Sperner extension have all been rebuilt against this stronger interface.
- Formalization note after the first surjectivity progress:
  the repaired interface is now strong enough to prove the full Section 5 surjectivity statement
  in dimension `1`. The proof transports `RentDivision 2` to `unitInterval` using
  `stdSimplexHomeomorphUnitInterval`, proves that a face-preserving map fixes the two endpoints,
  and applies the intermediate value theorem. So the remaining difficulty is genuinely
  higher-dimensional.
- Formalization note after the next topological reduction:
  in the repaired barycentric-coordinate model, the straight-line homotopy from `id` to a
  face-preserving `PiecewiseLinearSimplexMap` automatically stays face-preserving, because
  vanishing coordinates remain zero under convex combination. This part of the Section 5
  topological argument is now formalized. So the higher-dimensional frontier has narrowed further:
  either formalize an explicit deformation from the simplex minus the barycenter onto the boundary
  and combine it with noncontractibility of the boundary, or return to the paper's trap-door
  argument.
- Formalization note after the boundary restriction step:
  the topological route is now packaged more tightly. The boundary subtype
  `SimplexBoundary dimension`, the restriction of a face-preserving simplex map to that boundary,
  and the restricted straight-line homotopy are all formalized. Moreover
  `boundary_contractible_of_nullhomotopic_boundaryExtension` shows that the whole contradiction
  reduces to one concrete object: if an omitted positive interior point gives a continuous map from
  the full simplex into its boundary extending that boundary restriction, then the boundary would
  be contractible. So the next missing ingredient is the explicit omitted-point extension, not more
  homotopy bookkeeping.
- `Section 5` also has a minor notation slip: around line 387, "The vertex `e_1` of `Δ_n`" should be `Δ_{n-1}`.
- `Section 6`, first theorem (around lines 449-463): the proof implicitly upgrades the face `τ` containing `x` to a facet. The hypothesis that `y` is not in the convex hull of any `n` lattice points rules out lower-dimensional faces, since those would map into convex hulls of at most `n` lattice points.
- `Section 6`, second theorem (around lines 487-490): the counting step should be written explicitly. If fewer than `k_j` indices `i` had `β_ij > 0`, then `∑_i β_ij ≤ (k_j - 1) / (n + 1) < α_j`, contradicting `∑_i β_ij = α_j`.
- Minor typos worth ignoring in Lean but noting for completeness:
  around line 167, "a room with only door" should read "a room with only one door";
  around line 439, the displayed parenthetical should likely read `λ_1(v_1) = λ_2(v_1) = 1`.

## Open Questions
- No fatal mathematical gap found in this pass.
- The higher-dimensional algorithm in `Section 5` is the least formal part of the paper; it appears repairable, but a Lean development should plan to restate and prove that surjectivity result independently rather than following the paper literally line by line.
- Current proof frontier:
  the modeling repair is now complete: the derived-map barycentric-coordinate interface is in
  place, and the canonical Sperner extension theorem has been reproved on top of it. The
  dimension-`1` surjectivity base case and its Section 5 / Section 2 wrappers are now proved, and
  the straight-line face-preserving homotopy to `id` is also formalized, as are the boundary
  restriction and boundary-contractibility reduction steps. The barycenter-specific omitted-point
  map is now formalized as well, and `boundary_contractible_of_omits_barycenter` shows that any
  face-preserving simplex self-map omitting the barycenter would force `SimplexBoundary dimension`
  to be contractible. So the remaining higher-dimensional Section 5 choice is now clean: either
  prove that boundary noncontractible in Lean, or abandon the topological route and formalize the
  paper's trap-door/path-following proof instead, followed by the Hall-witness extraction in
  Sections 3 and 4.
- Formalization note after the latest higher-dimensional proof search:
  the topological route has now been pushed far enough that the next missing step is no longer a
  local lemma inside this project. A direct search through the installed mathlib for Brouwer fixed
  point, "no retraction from ball to sphere", or explicit noncontractibility statements for spheres
  / simplex boundaries did not produce an off-the-shelf theorem that can close
  `boundary_contractible_of_omits_barycenter`. So, under the current library state, the topological
  route appears to require a substantial independent development of sphere noncontractibility rather
  than one more project-specific argument.
- Formalization note after the latest Section 5 support reduction:
  the lower-door problem has now split into two genuinely different geometric subcases. If a
  positive face contains the lower milestone and some image vertex still has nonzero next-coordinate,
  then one can formally restrict the convex-hull witness to the zero next-coordinate image points
  and obtain a proper support of size at most `k + 1`; this is now packaged as
  `exists_subset_contains_lowerMilestone_of_exists_upperCoord_ne_zero`, with the immediate
  codimension-`1` corollary
  `exists_codimOneSubface_contains_lowerMilestone_of_exists_upperCoord_ne_zero`.
  So the only remaining Section 5 support-selection issue is the complementary case where every
  image vertex of the positive face already lies in the lower target prefix face. The manuscript
  does not spell out this case separately, but Lean now forces it to be handled explicitly.
- Formalization note about the alternate Section 5 proof:
  the paper's higher-dimensional trap-door/path-following proof is not blocked by mathematics, but
  it does use more combinatorial structure than the current Lean support files expose. The graph
  `G` in Section 5 ranges over faces of many dimensions and counts incidences through shared
  codimension-`1` faces. The present `SimplicialSubdivision` interface records full-dimensional
  facets, geometric barycentric coordinates, and supporting facets, but not an explicit face poset
  or codimension-`1` adjacency API. So switching to the paper's route is now a real support-layer
  project, not just a short replacement proof.
- Formalization note after the combinatorial pivot:
  that missing support layer is now started in `RentalHarmony/Section5Graph.lean`. A
  `SubdivisionFace` is formalized as a nonempty subset of one facet, together with geometric and
  image-containment predicates and codimension-`1` incidence lemmas. This is enough structure to
  begin stating the Section 5 graph `G` faithfully; the remaining work is the actual path/parity
  argument, not another subdivision-interface repair.
- Formalization note after the next Section 5 support step:
  the same support file now also contains the paper's prefix-face barycenters and the segment
  predicates needed for graph vertices. Concretely, `prefixBarycenter` formalizes the barycenter
  of `conv{e_1, ..., e_k}` in Lean's `0`-based indexing, and `prefixBarycenterSegment` plus
  `SubdivisionFace.ImageMeetsPrefixBarycenterSegment` package the condition
  `λ(σ) ∩ [b_{k-1}, b_k] ≠ ∅`. So the next missing ingredient is the actual graph definition and
  parity/path-following proof.
- Formalization note after the latest Section 5 support step:
  the actual graph `G` is now formalized in `RentalHarmony/Section5Graph.lean`. The Lean object
  has a special `start` node for `e_1`, positive-dimensional nodes `Section5PositiveNode` for
  faces subdividing the prefix outer faces with the required segment-intersection witness, and a
  `SimpleGraph` structure whose edges are exactly the paper's three cases:
  start-to-edge incidence at `e_1`,
  same-dimensional adjacency through a shared codimension-`1` face meeting `[b_{k-1}, b_k]`,
  and vertical adjacency through a codimension-`1` incident face containing `b_k`.
  So the remaining combinatorial work is no longer another modeling repair: it is the actual
  degree/parity argument on this graph.
- Formalization note after the latest graph proof step:
  the parity half of that argument is now isolated cleanly from the geometry.
  `exists_terminal_of_odd_start_and_nonterminal_even` proves, for any finite graph, that if the
  designated start vertex has odd degree and every nonterminal vertex has even degree, then some
  terminal vertex exists. Applied to the Section 5 graph, this reduces the remaining work to the
  local geometric degree lemmas rather than a separate global path-construction formalization.
- Formalization note after trying to prove those local degree lemmas directly:
  the current `Section5GraphNode.graph` is still built from the exact prefix barycenters
  `b_k`, but the paper's degree count is only claimed after a generic perturbation of those
  barycenters. This is explicit in Section 5: in dimension `2` the proof assumes no subdivision
  vertex maps to the segment between successive barycenters, and in higher dimensions it assumes
  that when a codimension-`1` face image meets `[b_k, b_{k+1}]`, it does so through a point in the
  relative interior of that face. Without such a perturbation/genericity layer, the current Lean
  graph is too rigid for the local degree lemmas: degeneracies where a segment hits a lower-
  dimensional face are not excluded, so the start/nonterminal odd-even classification is not
  presently derivable from the support-file definitions alone.
- Formalization note after the latest Section 5 repair:
  that genericity issue is now surfaced explicitly in the support layer.
  `RentalHarmony/Section5Graph.lean` introduces `Section5MilestoneChain`, and the graph,
  adjacency predicates, and terminal-node theorem are all parameterized by that chain rather than
  the exact prefix barycenters. The start milestone is fixed to `e_1`, the final milestone is
  fixed to the true barycenter of the full simplex, and only the intermediate milestones are left
  generic inside their prefix faces. So the remaining Section 5 work is now correctly targeted:
  prove the local odd/even degree lemmas for this repaired graph, not for the old exact-barycenter
  object.
- Formalization note after the latest graph-theoretic step:
  the remaining local degree analysis has now been factored into a clean interface.
  `Section5GraphNode.LocalDegreeHypotheses` packages the paper's intended local consequences of
  genericity: a unique door out of the start room and exactly two doors out of each nonterminal
  room. The support file then proves the corresponding odd/even graph-degree lemmas from that
  package. So the next missing ingredient is not more graph arithmetic; it is the actual convex-
  geometric proof that a generic milestone chain satisfies those local hypotheses.
- Formalization note after the latest Section 5 abstraction step:
  the purely graph-theoretic part is now closed under that interface.
  `Section5GraphNode.exists_terminal_of_localDegreeHypotheses` combines the local odd/even degree
  consequences with the finite-graph parity theorem and directly yields a terminal node, i.e. a
  top-dimensional subdivision face whose image contains the final milestone. So the remaining
  Section 5 gap is now purely geometric: prove that a suitably generic milestone chain satisfies
  `LocalDegreeHypotheses`.
- Formalization note after the latest case-split repair:
  the support layer now exposes a more paper-faithful local target than `LocalDegreeHypotheses`.
  `Section5GraphNode.GeometricGenericity` separates the two local situations used in Section 5:
  either the next milestone is absent from the current face image and the milestone segment crosses
  through two doors, or the next milestone lies in the current face image and the face is either
  terminal or again has two continuation doors. The support file proves both
  `Section5GraphNode.localDegreeHypotheses_of_geometricGenericity` and
  `Section5GraphNode.exists_terminal_of_geometricGenericity`, so the remaining Section 5 work is
  now even sharper: prove that a generic milestone chain satisfies `GeometricGenericity`.
- Formalization note after the latest geometric-target refinement:
  the remaining Section 5 goal is now phrased with explicit transversality predicates rather than
  only casewise graph consequences. `SubdivisionFace.ImageMeetsOpenMilestoneSegment` records that
  a face image hits a milestone segment away from the segment endpoints, and
  `SubdivisionFace.ImageContainsMilestoneAwayFromBoundary` records that a milestone lies in a face
  image but not already in the image of any codimension-`1` subface. These are packaged in
  `Section5GraphNode.MilestoneSegmentTransversality`, which extends
  `Section5GraphNode.GeometricGenericity` and already yields
  `Section5GraphNode.exists_terminal_of_milestoneSegmentTransversality`. So the remaining Section 5
  work is now the actual convex-geometric proof that a suitably perturbed milestone chain satisfies
  these transversality predicates.
- Formalization note after the latest direct search for that proof:
  the remaining obstacle is now a specific missing support theorem, not another unclear proof plan.
  The installed mathlib does contain full-dimensional results such as
  `interior_convexHull_nonempty_iff_affineSpan_eq_top`, but the milestone perturbation argument
  lives inside the lower-dimensional prefix faces `conv{e_1, ..., e_k}`. I did not find a ready-
  made identification of those prefix faces with smaller standard simplices, nor a theorem stating
  that the relative interior of such a simplex face cannot be covered by finitely many convex hulls
  of at most `k` points. Without one of those support results, the existence of a milestone chain
  satisfying `Section5GraphNode.MilestoneSegmentTransversality` is currently blocked.
- Formalization note after the latest support-theorem attempt:
  the repaired missing-next branch is now partly pushed through the graph interface.
  `chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone` proves the
  paper-faithful disjunction for the concrete chosen milestones, and the new lemmas
  `exists_verticalAdj_of_codimOneSubface_contains_lowerMilestone` and
  `exists_graphNeighbor_of_codimOneSubface_contains_lowerMilestone` show that any codimension-`1`
  lower-prefix subface carrying the lower milestone already yields the desired vertical door in the
  Section 5 graph. So the remaining blocker is sharper than before: one must still prove that such
  a codimension-`1` lower-prefix subface exists in the concrete chosen-chain situation when the
  lower milestone lies in the image of a positive node.
- Formalization note after the latest reduction:
  the codimension-`1` face-existence step itself is now split into a purely combinatorial part and
  the genuinely geometric prefix-face part. The new theorem
  `exists_codimOneSubface_contains_lowerMilestone_of_subset` shows that if the lower milestone lies
  in the convex hull of the images of any proper subset of a positive face's vertices, then one can
  erase an unused vertex and obtain an actual codimension-`1` face still carrying that milestone.
  So the remaining difficulty is to choose a proper supporting subset that also comes from vertices
  lying in the lower prefix face; the graph-side padding/erasure step is no longer missing.
  the prefix-face route is now started in Lean. `RentalHarmony/Section5Graph.lean` defines the
  bundled subtype `PrefixFace k` for the outer face `conv{e_1, ..., e_{k+1}}`, and
  `Section5MilestoneChain.prefixPoint` upgrades each milestone to an element of that subtype.
- Formalization note after the latest prefix-face transport step:
  the target-side part of the remaining all-image-lower lower-door case is now formalized.
  `PrefixFace.padLinear` and `PrefixFace.mem_affineSpan_prefixVertexFinset` identify each ambient
  prefix-face point with the affine span of the corresponding ambient prefix vertices, and
  `exists_subset_contains_lowerMilestone_of_all_imageVertices_lowerPrefix` applies Carathéodory to
  show that if every image vertex already lies in the lower target prefix face, then the lower
  milestone is still carried by a proper image support of size at most `k + 1`. The manuscript
  still leaves one genuinely domain-side step implicit: convert that proper target support into a
  proper carrier subset whose vertices lie in the lower prefix face of the domain simplex.
- Formalization note after the latest prefix-face step:
  that restriction/padding support theorem is now fully formalized.
  `RentalHarmony/Section5Graph.lean` defines `PrefixFace.restrict`, `PrefixFace.pad`, and the
  explicit equivalence `PrefixFace.equivRentDivision : PrefixFace k ≃ RentDivision (k + 1)`.
  The finite-sum reindexing proof is now packaged inside the support file rather than left in
  scratch. So the remaining milestone-chain blocker is no longer face identification; it is the
  actual finite-union avoidance theorem in the relative interior of the smaller simplex, which can
  now be transported back to the ambient prefix face through this equivalence.
- Formalization note after the latest smaller-simplex step:
  that affine-subspace avoidance theorem is now proved. `RentalHarmony/Section5Graph.lean`
  formalizes that a proper affine subspace of a finite-dimensional affine space has empty interior,
  proves the corresponding finite-union avoidance lemma, and specializes it to the relative
  interior of the smaller simplex `RentDivision (k + 1)` by working inside the affine-span subtype
  of `stdSimplex`. So the remaining milestone-chain blocker is now even more concrete: show that
  the finitely many forbidden lower-dimensional convex hulls in the Section 5 perturbation
  argument are contained in finitely many proper affine subspaces of the relevant smaller simplex,
  and then transport the avoided interior point back through `PrefixFace.equivRentDivision`.
- Formalization note after the latest convex-hull step:
  that containment upgrade is now also proved in the smaller-simplex setting.
  `RentalHarmony/Section5Graph.lean` shows that any finite family of convex hulls generated by at
  most `k` points can be avoided in the relative interior of `RentDivision (k + 1)`, by first
  proving that `≤ k` points cannot span the full affine hull of the smaller simplex and then
  applying the affine-subspace avoidance theorem already in place. So the remaining Section 5
  blocker is no longer a finite-avoidance statement at all; it is the concrete transport from
  those smaller-simplex avoided points back to ambient prefix-face milestones and the packaging of
  that choice into `Section5GraphNode.MilestoneSegmentTransversality`.
- Formalization note after the latest prefix-face transport step:
  that transport is now proved abstractly too.
  `PrefixFace.exists_smallPointInterior_not_mem_biUnion_convexHull_of_card_le` uses
  `PrefixFace.restrict`, `PrefixFace.pad`, and the restriction linear map to pull any finite
  convex-hull avoidance problem on a prefix face down to the smaller simplex and then push the
  chosen point back to the ambient simplex. So the remaining Section 5 milestone blocker is now
  exactly the paper's bookkeeping step: specify the actual finite forbidden convex-hull families
  attached to each prefix level and assemble the resulting avoided prefix-face points into a
  `Section5MilestoneChain` satisfying `Section5GraphNode.MilestoneSegmentTransversality`.
- Formalization note after the latest forbidden-family step:
  those actual levelwise forbidden families are now defined.
  `RentalHarmony/Section5Graph.lean` introduces `milestoneForbiddenFaces` and
  `milestoneForbiddenFamily` from lower-dimensional subdivision-face images in each prefix face,
  proves every member is generated by at most `k` prefix-face points, and derives
  `exists_prefixMilestonePoint_avoiding_forbiddenFamily`. So the remaining Section 5 milestone
  blocker is now only the final assembly/transversality argument: splice these levelwise choices
  together with the fixed start point `e_1` and fixed terminal barycenter, and prove the resulting
  chain satisfies `Section5GraphNode.MilestoneSegmentTransversality`.
- Formalization note after the latest chain-construction step:
  that assembly is now done as well.
  `RentalHarmony/Section5Graph.lean` now defines `chosenPrefixMilestonePoint` and
  `chosenMilestoneChain`, combining the fixed start point `e_1`, the fixed terminal barycenter,
  and the levelwise avoiding choices from `exists_prefixMilestonePoint_avoiding_forbiddenFamily`.
  So the remaining Section 5 blocker is now exactly the final geometric proof that this concrete
  chain satisfies the open-segment and away-from-boundary clauses of
  `Section5GraphNode.MilestoneSegmentTransversality`.
- Formalization note after the latest transversality step:
  one half of that final concrete milestone proof is now complete.
  `chosenMilestoneChain_nextMilestoneAwayFromBoundary_of_nonterminal` shows that whenever a
  nonterminal positive graph node contains its next milestone, that milestone is not already in
  the image of any codimension-`1` subface. This is exactly the paper's "milestone in relative
  interior rather than on a boundary door" condition for the vertical case. So the remaining
  Section 5 blocker is now narrower than before: prove the complementary open-segment crossing
  statement for faces missing the next milestone, then package the resulting concrete chain into a
  full `Section5GraphNode.MilestoneSegmentTransversality` witness and push it through the already
  formalized terminal-node / parity wrappers.
- Formalization note after the latest open-segment reduction:
  the remaining missing-next-milestone case has now been reduced to one precise endpoint
  obstruction.
  `imageMeetsOpenMilestoneSegment_of_meets_of_not_containsMilestones`
  shows that an open crossing follows as soon as both endpoints are excluded from the face image,
  and
  `chosenMilestoneChain_openSegment_of_missingNextMilestone_of_not_lowerMilestone`
  specializes this to the chosen milestone chain. But this sharpened reduction also exposed a
  likely support-layer mismatch with the paper: Section 5 allows the lower endpoint `b_k` to serve
  as a vertical door when `b_{k+1}` is absent, whereas the current field
  `MilestoneSegmentTransversality.open_crossing_of_missing_nextMilestone` rules that case out
  completely. So the remaining blocker may be a local-definition repair rather than one more
  convexity lemma.
- Formalization note after the latest local repair:
  that support-layer mismatch is now fixed. The explicit missing-next branch of
  `MilestoneSegmentTransversality` no longer demands an open crossing outright; it now allows the
  lower milestone `b_k` to lie in the face image, matching the paper's vertical-door case. The
  concrete theorem
  `chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone`
  proves exactly this corrected alternative for the chosen chain. So the remaining Section 5
  blocker has shifted again: prove that the lower-milestone-containment alternative yields the
  actual vertical-door / two-neighbor consequence needed by `GeometricGenericity`, then package
  the chosen chain into the existing terminal-node framework.
- Formalization note after the latest prefix-vertex bookkeeping step:
  the remaining lower-door obstruction is now sharper on the ambient-geometry side.
  `RentalHarmony/Section5Graph.lean` now contains the compile-clean helper lemmas
  `restrictLinear_prefixVertex`, `prefixVertex_injective`, `prefixVertexFinset`, and
  `prefixVertexFinset_card`, which identify the first `k + 1` outer simplex vertices as an
  explicit finite ambient set and record how `restrictLinear` sees them. This makes the next
  missing theorem concrete: build a clean ambient padding / affine-span transport statement for
  `PrefixFace k`, so that the all-image-lower-prefix lower-door case can be reduced to a
  Carathéodory support argument inside that lower target prefix face.
- Formalization note after the latest lower-prefix subset bridge:
  the remaining all-image-lower obstacle is now isolated in its exact final form.
  `exists_graphNeighbor_of_lowerPrefixSubset_contains_lowerMilestone`
  packages the existing codimension-`1` and vertical-door lemmas and shows that an exact-size
  lower-prefix carrier subset already suffices to produce the required graph neighbor. So the
  unresolved part of Section 5 is now no longer "some lower door exists" in the abstract; it is
  specifically the extraction of a carrier subset of size `k + 1` whose vertices lie in the lower
  prefix face and whose image convex hull still contains the lower milestone in the complementary
  all-image-lower case.
- Formalization note after the latest exact-size packaging repair:
  the exact-cardinality part of that lower-door step is now factored out cleanly.
  `exists_graphNeighbor_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone`
  enlarges any milestone-carrying lower-prefix support inside a larger lower-prefix carrier set to
  the exact cardinality `k + 1`, then invokes the existing codimension-`1` / vertical-door bridge.
  So the remaining obstacle is no longer finitary bookkeeping. It is the genuinely geometric
  question whether, in the all-image-lower case, one can always find a lower-prefix carrier set of
  size at least `k + 1` containing the needed support.
- Manuscript clarification after rereading lines 385-393:
  the stronger lower-prefix requirement remains the right Lean target. The vertical clause
  ("there is an edge between `k`-face `σ` and `(k-1)`-face `τ` if ... `b_k ∈ λ(τ)`") still defines
  an edge in the already-declared graph `G`, whose vertices were introduced one sentence earlier as
  faces subdividing the chosen prefix chain and intersecting the relevant barycenter segments. So
  formally `τ` must still be a vertex of `G`, hence must still subdivide the lower prefix face;
  the paper simply omits restating that hypothesis in the vertical-edge sentence.
- Formalization blocker after settling that fork:
  the missing theorem is now a domain-side local-affinity/preimage statement, not another graph
  lemma. To finish the all-image-lower case, one needs to turn
  `ν.face.ImageContainsMilestone (T := T) c φ.vertexMap ν.level.castSucc` into an actual point
  `x ∈ ν.face` with `φ.toFun x = c.point ν.level.castSucc`; then the existing barycentric-support
  lemma `vertexPos_coord_eq_zero_of_baryCoord_ne_zero_of_coord_eq_zero` would show that every
  vertex of `T.supportingFacet x` with positive barycentric weight lies in the lower prefix face,
  yielding the desired large lower-prefix carrier set. The current repo does not yet package this
  face-local affine-preimage theorem for `SubdivisionFace.ImageContains`.
- Sharpened support-layer diagnosis after trying to prove that theorem directly:
  the present `SimplicialSubdivision` interface still lacks a local-barycentric compatibility
  statement. In particular, there is currently no theorem saying that if a point lies in the
  convex hull of a specified subdivision face or facet, then the global barycentric support chosen
  by `T.baryCoord` or `T.supportingFacet` can be taken inside that same face or facet. Without
  that compatibility, even a facet-level converse to `map_mem_facetImage` is not yet derivable
  from the existing API, so the intended `SubdivisionFace.ImageContains -> ∃ x, φ.toFun x = ...`
  step remains blocked on genuinely missing local affine infrastructure rather than on the Section 5
  graph bookkeeping itself.
- More precise API mismatch from the latest direct attempt:
  the current abstract data only provide
  `T.supportingFacet_mem : supportingFacet x ∈ facets` and
  `T.baryCoord_supported : baryCoord v x ≠ 0 -> v ∈ supportingFacet x`.
  They do not provide any face-local converse such as
  `x ∈ convexHull (facetVertexPoints T σ) -> supportingFacet x ⊆ σ`
  or even
  `x ∈ convexHull (facetVertexPoints T σ) -> baryCoord v x = 0` for `v ∉ σ`.
  This is exactly the theorem needed to convert a specified face-image containment witness into a
  preimage whose barycentric support stays inside that chosen face.
- Recovery experiment conclusion:
  replacing the global `supportingFacet` route by a face-local convex-combination witness on the
  image does not by itself unblock the Section 5 lower-door proof. A witness from
  `Finset.mem_convexHull'` on `ν.face.imagePoints` only certifies weights on image vertices, and
  `boundary_preserving` is one-way: it says `imageSupport ⊆ domainSupport`, but zero image
  coordinates do not force zero domain coordinates. So a purely image-local support witness cannot
  prove that the corresponding domain vertices lie in the lower prefix face. The blocked step
  really does require a genuine domain preimage point with face-local barycentric support, or a
  stronger local affine API that supplies such a point.
- Recovery attempt 2 diagnosis:
  the suggested relative-interior / continuity route also stops at the abstract subdivision API.
  `SimplicialSubdivision` records only that each facet has `dimension + 1` vertices and covers the
  simplex; it does not assert that the geometric points of a facet are affinely independent, that
  its convex hull is a genuine `dimension`-simplex, or that a point in the relative interior of a
  facet determines that facet uniquely. Without those nondegeneracy/uniqueness properties, there is
  no available path to prove that `φ.toFun` agrees on a chosen facet with the corresponding local
  affine extension and then extend by continuity. So the current obstruction is not just a missing
  lemma name; the existing abstract `SimplicialSubdivision` interface is too weak for both the
  global-support route and the relative-interior affine-restriction route.
- Recovery attempt 3 diagnosis:
  the suggested "prove a stronger geometric bundle only for the concrete subdivision used in the
  repo" also does not fit the current development. There is no concrete subdivision implementation
  anywhere in the repo to instantiate such a bundle against; all of `Section5Graph.lean`,
  `Sperner.lean`, and `PaperTheorems.lean` are parameterized by an arbitrary
  `SimplicialSubdivision`. So unblocking Section 5 now requires strengthening the core abstract
  support layer itself (or adding equivalent internal assumptions throughout), not merely proving a
  richer theorem package for some hidden concrete instance.
- Recovery attempt 4 outcome:
  the spec-first route does work as an architectural reduction. The exact missing lower-door input
  is now formalized as the internal contract
  `Section5GraphNode.FaceLocalLowerPrefixCarrierSpec.exists_graphNeighbor_of_contains_lowerMilestone`.
  This makes precise what the abstract support layer still lacks: not "some local geometry" in
  general, but exactly a graph-neighbor consequence for lower-milestone containment in a positive
  node.
- The same refactor also exposed the next hidden boundary cleanly. Once one assumes
  `GeometricGenericity` for the concrete chain `chosenMilestoneChain`, the rest of the Section 5
  combinatorial pipeline already goes through in Lean: the explicit milestone lemmas upgrade that
  genericity package to `MilestoneSegmentTransversality`, the parity theorem produces a terminal
  node, and one extracts a facet whose image contains the chain's terminal milestone. Therefore the
  remaining obstacles are now separated into explicit theorem statements rather than one vague
  stuck region:
  1. the lower-door contract above;
  2. the start / two-door graph-local consequences needed to build `GeometricGenericity` for
     `chosenMilestoneChain`.
- Formalization note after the latest endpoint cleanup:
  the third blocker in that list is now gone. `prefixBarycenter_last_eq_barycentricRentDivision`
  proves that the last prefix barycenter is the true simplex barycenter, and
  `chosenMilestoneChain_terminal_eq_barycenter` plus
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_doorSpec`
  show that once the lower-door contract and the chosen-chain door-count package are supplied, the
  Section 5 parity pipeline already yields the paper's barycenter-containing facet statement.
- Formalization note after the latest support-contract refinement:
  the lower-door blocker is now stated at the genuinely geometric level actually used by the proof.
  `Section5GraphNode.FaceLocalLargeLowerPrefixCarrierSpec` asks directly for a large lower-prefix
  carrier set and a milestone-carrying support set inside it, and the old
  `FaceLocalLowerPrefixCarrierSpec.exists_graphNeighbor_of_contains_lowerMilestone` is now derived
  from that sharper input by the existing enlargement lemma
  `exists_graphNeighbor_of_subset_in_largeLowerPrefixSubset_contains_lowerMilestone`. So the
  remaining abstract support gap is no longer "produce a graph neighbor somehow", but the more
  precise large-lower-prefix carrier statement.
- Formalization note after the latest graph-local refinement:
  the second unresolved Section 5 contract is now also stated in a sharper form.
  `Section5GraphNode.ChosenMilestoneChainGraphLocalSpec` isolates the remaining start/door-count
  work into the exact cases forced by the current lower-door API: an open-crossing branch, a
  level-`0` lower-milestone branch, a positive-level branch that turns one supplied extra neighbor
  into the full two-door conclusion, and the away-from-boundary next-milestone branch. The old
  `ChosenMilestoneChainDoorSpec` is now derived from
  `ChosenMilestoneChainGraphLocalSpec` plus `FaceLocalLowerPrefixCarrierSpec`, and the wrapper
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_specs` shows that these
  two refined contracts already suffice for the downstream barycenter-cell statement.
- Recovery attempt 1 on the new stuck episode: the weaker vertex-level reflection route also fails
  under the current abstract interface. Even if one assumes for a carrier vertex
  `v ∈ ν.face.carrier` that the image vertex `φ.vertexMap v` already lies in the lower target
  prefix face, i.e.
  `(((φ.vertexMap v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0`,
  the repo has no converse theorem forcing
  `(((T.vertexPos v : RentDivision (dimension + 1)) : RealPoint dimension) ν.level.succ) = 0`.
  This is not a missed local lemma: `PiecewiseLinearVertexMap.boundary_preserving` only states the
  forward implication "domain zero coordinate implies image zero coordinate". So the true missing
  support-layer input is now sharper than before:
  for a positive face whose image contains the lower milestone, one needs a face-local lower-prefix
  reflection theorem producing a carrier subset or subface that already lies in the lower domain
  prefix face and whose image still contains that lower milestone. Without such a converse, even a
  minimal-support convex-hull witness in the image does not force the corresponding carrier
  vertices back into the lower domain prefix face.
- Recovery attempt 2 on the same stuck episode produced a concrete algebraic countermodel shape for
  that missing theorem. In dimension `2`, take a subdivision whose boundary vertices include
  `A = e_0`, `D = e_1`, `E = e_2`, together with a lower-edge midpoint
  `B = (1/2, 1/2, 0)` and an interior vertex `C = (1/3, 1/3, 1/3)`, and triangulate using the
  four facets `{A,B,C}`, `{B,D,C}`, `{D,E,C}`, and `{E,A,C}`. On the positive face `{A,B,C}`,
  define the vertex map by `φ(A) = e_0`, `φ(B) = e_0`, `φ(C) = (1/2, 1/2, 0)`, and keep the other
  boundary vertices fixed. This satisfies the current one-way boundary conditions:
  `A` and `D` are forced to `e_0` and `e_1`, `E` is forced to `e_2`, `B` only has to keep the
  last coordinate zero, and the interior vertex `C` is unconstrained. But the image of the full
  face `{A,B,C}` contains the lower milestone `(1/2, 1/2, 0)`, while every carrier subset or
  subface lying entirely in the lower domain prefix edge is contained in `{A,B}` and therefore has
  image hull `{e_0}` only. So the desired lower-prefix reflection statement is not a consequence
  of the current abstract boundary axioms; it must remain an explicit extra hypothesis or be built
  into a stronger support layer.
- Recovery attempt 3 implemented that repair explicitly in Lean. The new internal structure
  `Section5GraphNode.PositiveFaceLowerPrefixReflection` records exactly the missing semantic input:
  for a positive face whose image contains the lower milestone, there is a lower-prefix carrier
  support inside that face whose image still contains the milestone. The theorem
  `faceLocalLargeLowerPrefixCarrierSpec_of_positiveFaceLowerPrefixReflection` shows this is exactly
  what the old carrier-set interface needed, and
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec`
  confirms that once this reflection property and the graph-local door-count package are supplied,
  the downstream Section 5 parity argument again reaches a barycenter-containing facet with no
  further hidden blockers.
- Direct attempt after that repair: the first unresolved field of
  `Section5GraphNode.ChosenMilestoneChainGraphLocalSpec` is the level-`0` missing-next branch. The
  proof wants a 1-dimensional lower-boundary decomposition theorem: a start-incident subdivision
  edge on the first prefix face that contains `c_0` but misses `c_1` should have exactly one
  continuation door besides `.start`. The current `SubdivisionFace` / `Adj` API does not encode
  this interval-style uniqueness for lower-edge faces, so the remaining graph-local package is now
  blocked first on that explicit 1-dimensional boundary theorem rather than on the older
  higher-dimensional reflection issue.
- A concrete countermodel shape explains why that level-`0` theorem is not derivable from the
  current abstract face data alone. In dimension `2`, place three distinct subdivision vertices
  `B_1,B_2,B_3` on the lower edge between `e_0` and `e_1`, and allow three distinct facets whose
  carriers contain `{e_0,B_i}` together with separate interior vertices. Then the three level-`0`
  faces `{e_0,B_i}` are all start-incident and all miss a first milestone `c_1` chosen farther
  along the lower edge. Because `SubdivisionFace` is defined as an arbitrary nonempty subset of a
  facet and the current graph only checks shared codimension-`1` subfaces, these three lower-edge
  faces can all be horizontally adjacent through the shared vertex `{e_0}`. So a start-incident
  edge can have more than one second door unless one adds an interval-decomposition / simplicial-
  complex uniqueness theorem for the first prefix face. This shows that
  `ChosenMilestoneChainGraphLocalSpec.two_doors_of_missing_nextMilestone_level_zero` is another
  genuinely independent geometric-combinatorial input under the present abstract API.
- Following that diagnosis, the level-`0` boundary theorem is now isolated in Lean as the smaller
  internal contract `Section5GraphNode.ChosenMilestoneChainLevelZeroBoundarySpec`, separated from
  the remaining start/open-crossing/positive-level fields in
  `Section5GraphNode.ChosenMilestoneChainGraphLocalRestSpec`. The theorem
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec'`
  confirms that this finer factorization is sufficient: once one supplies
  `PositiveFaceLowerPrefixReflection`, the normalized level-`0` boundary continuation input, and
  the remaining graph-local data, the downstream Section 5 parity argument again reaches a
  barycenter-containing facet with no further hidden blockers.
- A further direct check shows that the start-node data is also part of the same 1-dimensional
  boundary issue: the same overlapping lower-edge countermodel that breaks unique continuation can
  also create several distinct start-incident faces. Accordingly, the Lean factorization now places
  `start_neighbor`, `start_adj`, and `start_unique` inside
  `ChosenMilestoneChainLevelZeroBoundarySpec`. The remaining
  `ChosenMilestoneChainGraphLocalRestSpec` is therefore a cleaner higher-dimensional remainder:
  only the open-crossing branch and the positive-level missing-next / away-from-boundary
  continuation data are still outside the boundary contract.
- Direct attempt on that higher-dimensional remainder immediately hits the same modeling pattern at
  `ChosenMilestoneChainGraphLocalRestSpec.two_doors_of_missing_nextMilestone_openCrossing`. The
  current abstract API allows a positive face image to collapse onto the milestone segment itself:
  one can place all image vertices of a simplex on the line segment `[c_k,c_{k+1}]`, so the face
  meets the open segment, but several codimension-`1` subfaces also meet that same segment. In
  such a degenerate configuration there is no reason for exactly two doors to survive. So the
  higher-dimensional rest package also needs a genuine transversality / nondegeneracy hypothesis on
  face images, not merely the existing combinatorial face-inclusion data.
- Following that diagnosis, the Lean support layer now isolates the open-crossing branch as its own
  minimal contract. `Section5GraphNode.ChosenMilestoneChainOpenCrossingSpec` records exactly the
  missing higher-dimensional transversality claim for faces whose images meet the open milestone
  segment, while `Section5GraphNode.ChosenMilestoneChainPositiveLevelSpec` keeps the separate
  positive-level continuation data. The theorem
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''`
  shows that once those two inputs are supplied alongside
  `PositiveFaceLowerPrefixReflection` and the level-`0` boundary contract, the downstream Section 5
  parity argument again reaches a barycenter-containing facet with no further hidden blockers.
- The positive-level package can also be reduced using already-proved geometry: for a positive node
  missing the next milestone, the support file already proves
  `chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone`. So the
  genuinely unresolved positive-level continuation is not the whole old package, but only two
  sharper branches: the lower-endpoint continuation case
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelLowerMilestoneSpec` and the
  next-milestone interior case
  `Section5GraphNode.ChosenMilestoneChainNextMilestoneAwayFromBoundarySpec`. The new wrapper
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec'''`
  confirms that these are the exact remaining higher-dimensional inputs after factoring out the
  open-crossing branch.
- The lower-endpoint branch itself is now expressed in its minimal form. The auxiliary premise
  "there exists some extra graph neighbor" has been removed from the paper-facing internal
  frontier: `Section5GraphNode.ChosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec` records
  the bare theorem that a positive-level face which contains the lower milestone but misses the
  next one has exactly two continuation doors. The wrapper
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec''''`
  shows that once this lower-endpoint two-door statement and the separate away-from-boundary case
  are supplied, the downstream parity argument again reaches a barycenter-containing facet.
- The missing-next positive-level branch can now be stated in an even sharper way: because the
  support file already proves
  `chosenMilestoneChain_missingNextMilestone_openCrossing_or_contains_lowerMilestone`, the
  residual branch after fixing `ChosenMilestoneChainOpenCrossingSpec` is simply the complement
  case "no open crossing". This is now recorded as
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingSpec`, and the wrapper
  `Section5GraphNode.exists_barycenterPreimageCell_of_chosenMilestoneChain_reflectionSpec_noOpenCrossing`
  confirms that the downstream parity argument uses exactly that complement-case input together
  with the separate away-from-boundary theorem, not a broader mixed positive-level package.
- A direct attempt on that no-open-crossing branch exposes a new support-layer deficiency. The
  current `SubdivisionFace` notion is purely "nonempty subset of one facet", so it has no built-in
  simplicial-complex incidence uniqueness: the same geometric codimension-`1` face may appear via
  several carrier subsets, and nothing says a codimension-`1` face in the interior of a prefix
  subdivision has exactly two incident cofaces. But the no-open-crossing lower-endpoint argument
  needs precisely that kind of uniqueness/continuation statement at the codimension-`1` face
  carrying the lower milestone. So the next missing theorem is no longer about lower-prefix
  reflection or open-segment geometry; it is about codimension-`1` incidence uniqueness in the
  subdivision-face layer.
- Following the stuck-recovery prompt, the support file now also contains a carrier-normalized
  codimension-`1` object `SubdivisionFace.CarrierCodimOneSubface`. This removes dependence on how a
  raw `SubdivisionFace` was manufactured and packages only the carrier-level codimension-`1` data.
  The remaining no-open-crossing hypothesis is therefore stated more cleanly as
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingCarrierContinuationSpec`:
  a normalized codimension-`1` carrier face containing the lower milestone should admit a unique
  same-level continuation coface. This is the next exact abstract theorem to prove or assume.
- A direct attempt on that carrier-normalized statement shows that the normalization fixes only the
  subset-presentation problem, not the true incidence problem. The current `SimplicialSubdivision`
  structure still records `facets` only as a covering family of `(dimension + 1)`-element finite
  sets, so the same codimension-`1` carrier finset may belong to three or more facets. Thus even
  at the carrier layer there is no theorem that a lower-milestone codimension-`1` face has a
  unique same-level continuation coface. The remaining obstruction is therefore a genuine missing
  pseudomanifold/simplicial-complex incidence axiom, not another artifact of raw `SubdivisionFace`
  syntax.
- A follow-up refinement shows that generic coface uniqueness is stronger than the Section 5 proof
  actually needs. The support file now defines the graph-filtered predicate
  `Section5GraphNode.IsSameLevelCarrierContinuationCandidate` and the sharper contract
  `Section5GraphNode.ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredContinuationSpec`.
  This asks only for uniqueness among same-level positive cofaces through the normalized
  codimension-`1` carrier that could contribute a second graph door in the no-open-crossing
  branch. The old carrier-continuation theorem is now derived from this filtered version, so the
  precise remaining question is whether chosen-milestone geometry plus existing carrier-containment
  lemmas already force at most one graph-relevant same-level continuation. If not, exactly that
  filtered continuation statement should remain as the next minimal internal hypothesis.
- The next local bridge step is now formalized and no longer part of the blocker. The support file
  proves monotonicity of `ImageContains*` and `ImageMeets*` under carrier inclusion, shows that a
  filtered same-level candidate really yields a horizontal graph door, and conversely shows that
  any same-level horizontal door in the no-open-crossing branch automatically determines a
  normalized lower-milestone carrier candidate. So the remaining question is not how to pass
  between carrier witnesses and graph adjacency; it is exactly whether the chosen-milestone
  geometry forces existence and uniqueness of such graph-relevant same-level candidates.
- A direct attempt on that filtered theorem shows that the proof stalls before uniqueness enters.
  The current `SimplicialSubdivision` structure only says a face carrier lies in some facet
  (`subset_facet`), not that a codimension-`1` carrier lying on the lower milestone has a second
  same-level continuation coface inside the relevant prefix-face subdivision. Since the new bridge
  lemmas already turn any same-level horizontal door into a filtered candidate automatically, the
  first irreducible no-open-crossing gap is now existence of that second same-level continuation,
  not its uniqueness once found.
- The next recovery experiment also rules out a plausible shortcut through the existing lower-door
  support theorem. The new theorems
  `exists_verticalAdj_of_contains_lowerMilestone_of_largeLowerPrefixCarrierSpec` and
  `exists_verticalAdj_of_contains_lowerMilestone_of_reflection` show that the current reflection
  machinery constructs a downward vertical neighbor by design. So one cannot hope to obtain the
  missing filtered same-level continuation merely by classifying that reflected neighbor: the
  reflection contract already fixes its type. The genuine remaining theorem is additional
  same-level continuation existence beside that vertical door.
- A countermodel-style dependency check confirms that this is a real independence issue at the
  current abstraction level. After the new bridge lemmas, the remaining local interface can be
  caricatured by a positive node `ν`, a normalized codimension-`1` carrier `ρ`, and one lower
  positive node giving a downward vertical door. No currently formalized post-bridge theorem forces
  a same-level continuation in that reduced setting, so the missing no-open-crossing existence
  theorem is not an artifact of proof search; it is genuinely new local data absent from the
  present support layer.
- The development now reflects that diagnosis explicitly: the older filtered continuation package
  has been split into `ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredExistenceSpec` and
  `ChosenMilestoneChainPositiveLevelNoOpenCrossingFilteredUniquenessSpec`. So the remaining missing
  theorem is no longer phrased as one opaque "exists unique continuation" block; it is precisely
  the existence half for a same-level continuation through the normalized lower-milestone carrier.
- The carrier-continuation wrapper has now been rewritten through that split interface as well, so
  the support-layer dependency is explicit. A scan of the current repo still finds no ambient
  theorem saying that two same-level positive cofaces through the same normalized codimension-`1`
  carrier must coincide. Thus the uniqueness half is not currently derivable from the existing
  bridge lemmas alone; it should remain a separate local contract unless a stronger coface
  uniqueness theorem is formalized.
- The primary existence half is now sharper too. Once `PositiveFaceLowerPrefixReflection` is fixed,
  the theorem `exists_lowerMilestoneCarrier_of_not_openCrossing_of_reflection` shows that the
  normalized codimension-`1` carrier is already available in the no-open-crossing branch. So the
  genuinely remaining existence input is not “find a carrier and a continuation,” but only “find a
  same-level continuation through this fixed carrier,” formalized as
  `ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec`.
- The wrapper chain has been updated to reflect that sharper split all the way back to the older
  filtered theorem. A direct search of the current repo still finds no theorem extending a fixed
  codimension-`1` prefix-face carrier to a same-level prefix-face coface, so the present
  existence blocker is now isolated exactly at that fixed-carrier continuation step.
- Concretely, the current API only contains the downward propagation lemma
  `SubdivisionFace.subdividesPrefixFace_of_subface` and raw ambient facet existence via
  `subset_facet`. What is missing is the converse-style upward extension theorem: from a
  codimension-`1` carrier already known to lie in the relevant prefix face, produce a distinct
  same-level coface that still lies in that prefix face. This is the exact mathematical content of
  `ChosenMilestoneChainPositiveLevelFixedCarrierContinuationExistenceSpec`.
- That same obstruction is now also recorded in a more geometric form as
  `ChosenMilestoneChainPositiveLevelFixedCarrierCofaceExtensionSpec`: extend a fixed codimension-`1`
  carrier to a distinct same-level coface. The continuation and filtered-wrapper chain is already
  routed through that interface, so the remaining local input can now be stated directly in the
  paper's facet-local language.
- The same remaining gap is now also isolated at the level of one ambient simplex as
  `ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetExitSpec`: after choosing a facet `σ`
  with `ν.face ⊆ σ`, the paper's geometric picture predicts that the milestone segment exits `σ`
  through a second codimension-`1` facet distinct from `ν.face`. The coface-extension and
  no-open-crossing wrapper chain is now routed through that ambient-facet formulation as well.
- That ambient-facet formulation has now been sharpened once more to
  `ChosenMilestoneChainPositiveLevelFixedCarrierAmbientFacetPrefixExtensionSpec`: the genuinely
  missing step is only the existence of a same-level prefix-face coface inside `σ`. The image-side
  fact that this coface is again a positive graph node is automatic from lower-milestone
  monotonicity once the carrier inclusion is known.
- A first concrete step toward that theorem is now formalized: the helper
  `exists_sameLevelPrefixFace_in_ambientFacet_of_freshPrefixVertex` shows that if the chosen
  ambient facet `σ` contains one extra vertex outside `ν.face` that already lies in the larger
  prefix face, then the required same-level prefix-face coface can be built explicitly. The
  remaining obstruction is therefore the existence of such a fresh prefix-face vertex, not the
  coface construction itself.
- That reduction now has a precise built-in limitation. The new lemmas
  `ambientFacet_eq_of_topDim` and `no_freshAmbientFacetVertex_of_topDim` show that if `ν.face` is
  already top-dimensional, then every ambient facet `σ` containing `ν.face` is actually equal to
  `ν.face`, so no vertex of `σ` lies outside `ν.face.carrier`. Hence the fresh-prefix-vertex route
  cannot prove the full theorem uniformly; it only addresses the below-top-dimensional case and
  leaves a genuinely separate top-dimensional continuation problem.
- The complementary branch is now understood more precisely as well. The new lemma
  `exists_freshAmbientFacetVertex_of_lt_topDim` shows that once `ν.face.dim < dimension`, a fresh
  vertex of the ambient facet exists automatically by cardinality. So below top dimension the
  remaining missing input is not “find any fresh ambient-facet vertex,” but “find one whose
  singleton already lies in the larger prefix face `ν.level.succ`.” Conversely,
  `not_exists_sameLevelPrefixFace_in_ambientFacet_of_topDim` shows that the current ambient-facet
  prefix-extension conclusion itself is impossible in the top-dimensional branch, not merely
  unproved.
- The lower-milestone recovery route is therefore now split at the correct level. Rather than keep
  pushing the impossible top-dimensional continuation theorem, the support file now isolates
  `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneDoorSpec` for the top-dimensional branch
  and `ChosenMilestoneChainPositiveLevelBelowTopDimLowerMilestoneDoorSpec` for the genuinely
  below-top-dimensional continuation argument, with
  `chosenMilestoneChainPositiveLevelLowerMilestoneDoorSpec_of_topDim_and_belowTopDim` recombining
  them into the unchanged lower-milestone door theorem used downstream.
- The top-dimensional branch has now been sharpened further to a purely codimension-`1`
  multiplicity question. The new internal contract
  `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec` asks only for two
  distinct codimension-`1` lower-prefix subfaces of a top-dimensional positive face whose images
  both contain the lower milestone. Lean now shows that this is already enough for the graph step:
  `verticalNeighborOfCodimOneSubfaceContainsLowerMilestone` constructs the corresponding vertical
  neighbor from each such carrier, and
  `exists_two_distinct_verticalNeighbors_of_topDimLowerMilestoneCarrierMultiplicity` upgrades the
  pair of distinct carriers to two distinct vertical doors. So the remaining top-dimensional gap
  is exactly the geometric multiplicity of lower-milestone codimension-`1` carriers, not another
  graph-theoretic conversion lemma.
- That top-dimensional gap is now sharper still. The reflection contract already gives one
  normalized lower-prefix codimension-`1` carrier via
  `exists_lowerMilestoneCarrier_of_reflection`, so the true remaining local theorem is not
  “produce both carriers at once” but only
  `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierSpec`: starting from one
  lower-prefix carrier in a top-dimensional positive face missing the next milestone, produce a
  second distinct lower-prefix codimension-`1` carrier that also contains the lower milestone. The
  new reductions
  `chosenMilestoneChainPositiveLevelTopDimLowerMilestoneCarrierMultiplicitySpec_of_reflection_and_secondCarrier`
  and
  `exists_two_distinct_verticalNeighbors_of_reflection_and_topDimLowerMilestoneSecondCarrier`
  show that this second-carrier theorem is exactly the remaining top-dimensional input before the
  graph already has two distinct vertical doors.
- The new codimension-`1` coverage lemma sharpens that top-dimensional gap again. Lean now proves
  `SubdivisionFace.mem_of_mem_codimOneSubface_or_other` and
  `SubdivisionFace.subdividesPrefixFace_of_two_distinct_codimOneSubfaces`: if a face has two
  distinct codimension-`1` subfaces both lying in the same lower prefix face, then every vertex of
  the whole face already lies in that lower prefix face. Therefore
  `faceSubdividesLowerPrefix_of_reflection_and_topDimLowerMilestoneSecondCarrier` shows that any
  proof of the current second-carrier theorem must automatically force the entire top-dimensional
  positive face into the lower prefix face. The remaining top-dimensional content is now clearly
  image-side rather than domain-side: once all vertices of `ν.face` lie in the lower prefix face,
  show that the lower milestone lies in the image of a second codimension-`1` subface besides the
  reflected one.
- That last reformulation is now formalized as its own internal contract:
  `ChosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec`. The theorem
  `exists_second_codimOneSubface_of_faceSubdividesLowerPrefix` proves that this image-side
  statement is exactly enough to recover the older second-carrier theorem, because once
  `ν.face.SubdividesPrefixFace ... ν.level.castSucc` is known, any codimension-`1` subface of
  `ν.face` automatically inherits the same lower-prefix property by
  `SubdivisionFace.subdividesPrefixFace_of_subface`. So the genuine remaining top-dimensional gap
  is no longer “find another lower-prefix carrier” but “inside a top-dimensional face whose whole
  image already lies in the lower prefix face, show that the lower milestone is carried by a
  second distinct codimension-`1` subface.”
- That gap is now isolated one step more cleanly as a point-level multiplicity statement.
  `ChosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec` removes the milestone
  specialization entirely: inside a top-dimensional positive face already known to subdivide the
  lower prefix face, if some point `x` lies in the image of one codimension-`1` subface, then it
  should lie in the image of a second distinct codimension-`1` subface as well. The theorem
  `chosenMilestoneChainPositiveLevelTopDimLowerMilestoneSecondCarrierImageSpec_of_boundaryPointMultiplicity`
  shows that the current milestone-specific second-carrier problem is now exactly this
  point-on-two-face-images lemma applied to `x = b_k`. So the remaining top-dimensional blocker is
  now stated at the sharpest image-side level reached so far.
- The support layer now reduces even that point-level blocker to a more constructive image-support
  question. `exists_second_codimOneSubface_imageContains_of_subset_in_codimOneSubface` proves that
  once a point already lies in the image of one codimension-`1` subface, a second distinct
  codimension-`1` subface is automatic as soon as one can shrink the supporting vertex set inside
  the first subface by one additional vertex. This is recorded abstractly as
  `ChosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec`, and
  `chosenMilestoneChainPositiveLevelTopDimBoundaryPointMultiplicitySpec_of_supportShrink` derives
  the earlier point-on-two-face-images contract from it. So the genuine remaining top-dimensional
  content is now the sharp support-shrinking lemma inside one codimension-`1` face image, not yet
  another graph or carrier-construction step.
- The support-shrinking frontier is now reduced one step further to the exact local support-drop
  move. `ChosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec` asks that whenever
  a point `x` lies in the image convex hull of a finite support `s` inside a fixed codimension-`1`
  subface image, one can replace `s` by a strictly smaller support `s'` with
  `s'.card + 1 ≤ s.card` while keeping `x` in the same image convex hull. The reduction
  `chosenMilestoneChainPositiveLevelTopDimBoundaryPointSupportShrinkSpec_of_oneVertexDrop` shows
  that iterating this one-step drop recovers the older support-shrink contract, so the remaining
  top-dimensional blocker is now exactly this local convex-support pruning lemma.
- The support-pruning lemma is now itself reduced to a precise affine-dependence criterion.
  `exists_smaller_support_of_mem_convexHull_of_not_affineIndependent_image` proves that a
  one-vertex drop exists whenever the current image support is already affinely dependent, and
  `chosenMilestoneChainPositiveLevelTopDimBoundaryPointOneVertexDropSpec_of_affineDependentImage`
  turns that into the current top-dimensional codimension-`1` face contract. So the sharp
  remaining top-dimensional question is no longer raw support pruning, but whether the image
  support inside the first codimension-`1` face is forced to be affinely dependent by the Section 5
  hypotheses.
- The simplest obstruction to that affine-dependence route is now also isolated formally.
  `not_exists_smaller_support_of_pair_of_mem_openSegment` proves that a nondegenerate two-point
  support carrying `x` along an open segment in the first codimension-`1` face image makes
  one-vertex drop impossible. So any successful completion of the current top-dimensional branch
  must either rule out that segment case from the Section 5 hypotheses or replace the current
  support-pruning target by a weaker route.
