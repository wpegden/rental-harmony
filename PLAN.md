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
  formalized, and the finite-graph parity lemma is proved. The next missing step is a support-file
  repair: parameterize the graph by the paper's perturbed milestone points (or equivalent
  genericity hypotheses), and only then prove the local odd/even degree lemmas.
- Then feed surjectivity into the already-proved wrappers in `PaperTheorems.lean` to recover the
  barycenter-cell and Sperner statements.
- Turn the Hall witness wrapper theorems into actual proofs by extracting the paper's
  `k + 1`-labels-for-`k`-agents counting lemma from the geometric cell.

## Current input status
- No proposed axioms.
- No human input is required at the moment.
