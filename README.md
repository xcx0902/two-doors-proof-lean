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
- `TwoDoorsProof.Shortest`: first-layer lemmas and the concrete palindrome
  reversal certificate; the determinant/path expansion certificate is still
  an unconstructed assumption.
- `TwoDoorsProof.Weights`: uniqueness of a simple path from its undirected-edge
  multiset, its independent-variable monomial, and the nonzero first layer
  supplied by the concrete palindrome-reversal proof.

The complete determinant path/matching expansion and the upstream planar-grid
duality are not yet formalized.

Build with:

```text
lake build
```
