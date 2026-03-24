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
