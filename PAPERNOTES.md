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
  size at least `k + 1` containing the needed support. The paper's Section 5 wording at lines
  389-393 only says there is a graph edge from a `k`-face `σ` to a `(k-1)`-face `τ` when `τ` is a
  face of `σ` and `b_k ∈ λ(τ)`; it does not explicitly restate that `τ` must itself subdivide the
  lower prefix face. That omission may matter formally here, because the current Lean graph still
  encodes that stronger domain-side lower-prefix condition.
