# two-doors-proof

This project formalizes the proof architecture in `editorial.md`.

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
- `TwoDoorsProof.Shortest`: first-layer lemmas and the concrete palindrome
  reversal certificate; the determinant/path expansion certificate is still
  an unconstructed assumption.
- `TwoDoorsProof.Weights`: uniqueness of a simple path from its undirected-edge
  multiset, its independent-variable monomial, and the nonzero first layer
  supplied by the concrete palindrome-reversal proof.

The cofactor numerator's path/complement-matching expansion, its resulting
concrete shortest-layer certificate, and the upstream planar-grid duality are
not yet formalized. The second proof is therefore still incomplete.

Build with:

```text
lake build
```
