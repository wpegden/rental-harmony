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
- Formalization note after theorem stating / early proof work:
  the current abstract `SimplicialSubdivision` / `PiecewiseLinearVertexMap` API in Lean is too weak
  for the Section 2 and Section 5 existence statements. A concrete counterexample exists already in
  dimension `1`: take two subdivision vertices, let both have `boundaryFace = {0}`, let the unique
  facet be the whole `2`-element vertex set, and map both vertices to the simplex vertex `e_0`.
  This satisfies the present `boundary_preserving` field, but no facet image contains the
  barycenter and no Sperner labeling can be fully labeled. So the paper statements are currently
  encoded against an interface that omits essential triangulation / piecewise-linear hypotheses.
  The next repair must strengthen the geometric interface rather than continue searching for a
  proof of the present statement.
- `Section 5` also has a minor notation slip: around line 387, "The vertex `e_1` of `Δ_n`" should be `Δ_{n-1}`.
- `Section 6`, first theorem (around lines 449-463): the proof implicitly upgrades the face `τ` containing `x` to a facet. The hypothesis that `y` is not in the convex hull of any `n` lattice points rules out lower-dimensional faces, since those would map into convex hulls of at most `n` lattice points.
- `Section 6`, second theorem (around lines 487-490): the counting step should be written explicitly. If fewer than `k_j` indices `i` had `β_ij > 0`, then `∑_i β_ij ≤ (k_j - 1) / (n + 1) < α_j`, contradicting `∑_i β_ij = α_j`.
- Minor typos worth ignoring in Lean but noting for completeness:
  around line 167, "a room with only door" should read "a room with only one door";
  around line 439, the displayed parenthetical should likely read `λ_1(v_1) = λ_2(v_1) = 1`.

## Open Questions
- No fatal mathematical gap found in this pass.
- The higher-dimensional algorithm in `Section 5` is the least formal part of the paper; it appears repairable, but a Lean development should plan to restate and prove that surjectivity result independently rather than following the paper literally line by line.
- Current Lean-interface blocker:
  before the Section 5 theorem can be proved, the subdivision / PL-map API must be strengthened to
  encode actual simplex geometry (or an equivalent covering / realization theorem). With the
  present abstract data alone, the stated existence theorem is false.
