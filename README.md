# two-doors-proof

This project formalizes the two first-nonzero-layer proofs from `editorial.md`
for the already contracted simple dual graph.

## Modules

- `TwoDoorsProof.Basic`: contracted dual graph, blocking configurations, and
  the fact that a valid configuration yields a simple path containing both
  special edges.
- `TwoDoorsProof.WalkSum`: finite weighted-walk sums, closed-segment reversal,
  and characteristic-two cancellation under a fixed-point-free involution.
- `TwoDoorsProof.Palindrome`: the first-non-palindromic-interval scan and
  its stability under closed-interval reversal.
- `TwoDoorsProof.Contraction`: remove palindromic closed segments without
  deleting edges used at most once, and construct a shorter target path if the
  scan finds no non-palindromic interval.
- `TwoDoorsProof.Determinant`: the marked directed-edge determinant identity
  and cancellation of non-involutive permutation terms by inversion.
- `TwoDoorsProof.Marked`: two independent square-zero markers, edge-weight
  products and extraction of the coefficient that counts walks using each
  special edge exactly once.
- `TwoDoorsProof.MatrixWalk`: weighted adjacency matrix powers enumerate
  all fixed-length walks, including their formal-marker weights.
- `TwoDoorsProof.MatrixSeries`: the formal matrix geometric series and the
  adjugate identity relating its entries to a determinant and cofactor.
- `TwoDoorsProof.DeterminantMatching`: cancellation of changed square-zero
  edge-pairs in symmetric characteristic-two determinants; the marked
  determinant equals the ordinary-edge determinant, which has constant
  coefficient one and is the image of a series over the base ring.
- `TwoDoorsProof.DeterminantGenerating`: coefficientwise extraction of the
  two markers and the actual determinant generating identity linking the
  target-walk series, ordinary denominator, and marked cofactor numerator.
- `TwoDoorsProof.DeterminantPaths`: explicit list-level facts for the
  permutation cycle containing the added directed edge.
- `TwoDoorsProof.PathComplement`: a fully proved decomposition of a
  permutation with `σ t = s` into the distinguished simple cycle
  `s → ... → t → s` and an independent permutation on the complementary
  vertex subtype.
- `TwoDoorsProof.FintypePath`: a finite encoding of all admissible directed
  path lists, with an injective code into a finite sigma type.
- `TwoDoorsProof.PermutationTerms`: a finite bijection between permutations
  satisfying `σ t = s` and a directed path list together with a permutation
  of its complement; it factors the corresponding Leibniz monomial and sums
  these terms over each path's complementary determinant.
- `TwoDoorsProof.CofactorPaths`: the direct characteristic-two cofactor
  expansion as a sum over simple path cycles and determinants of their
  complementary principal submatrices.
- `TwoDoorsProof.PathCycleWeights`: resolvent submatrix identities, the
  explicit power-series weight of a distinguished path cycle, and the
  constant coefficient of a complementary resolvent determinant.
- `TwoDoorsProof.ComplementDenominator`: the complementary determinant
  comparison between marked and ordinary edge weights, including its
  realization as a coefficientwise constant-marker image.
- `TwoDoorsProof.DeterminantPathExpansion`: the complete marked cofactor
  expansion into distinguished path weights and ordinary complementary
  denominators; a bijection from admissible path lists to graph walks;
  and a direct proof that the numerator's coefficients through the shortest
  target length equal the corresponding sums of target-path weights.
- `TwoDoorsProof.ConcreteDeterminant`: a low-layer certificate constructed
  directly from the cofactor path expansion, with first-nonzero and
  no-target-path theorems independent of the palindrome-reversal certificate.
- `TwoDoorsProof.Shortest`: first-layer lemmas and the concrete palindrome
  reversal certificate, together with the generic determinant certificate
  interface used by the direct construction.
- `TwoDoorsProof.Weights`: uniqueness of a simple path from its undirected-edge
  multiset, its independent-variable monomial, and the nonzero first layer
  for both first-nonzero proofs.

Both routes prove the same criterion over independent edge-weight variables:
all shorter target-walk sums vanish, while the shortest target layer is a
nonzero sum of distinct simple-path monomials. They also prove vanishing at
every length when there is no target simple path. The determinant route obtains
its numerator coefficients from the path/complement determinant expansion,
not from the palindrome-reversal involution.

The planar grid-to-dual correspondence, wall contraction and door
preprocessing, randomized finite-field evaluation, and algorithmic complexity
claims are outside this Lean development; its input is an already contracted
simple graph with two distinct special edges.

Build with:

```text
lake build
```
