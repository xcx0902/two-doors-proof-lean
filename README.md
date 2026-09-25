# two-doors-proof

This project formalizes the proof architecture in `editorial.md`.

## Modules

- `TwoDoorsProof.Basic`: contracted dual graph, blocking configurations, and
  the fact that a valid configuration yields a simple path containing both
  special edges.
- `TwoDoorsProof.WalkSum`: finite weighted-walk sums, closed-segment reversal,
  and characteristic-two cancellation under a fixed-point-free involution.
- `TwoDoorsProof.Determinant`: the marked directed-edge determinant identity
  and cancellation of non-involutive permutation terms by inversion.
- `TwoDoorsProof.Shortest`: the common “first nonzero layer” theorem, with
  certificates for the palindrome/reversal proof and the determinant/path
  expansion proof.

Build with:

```text
lake build
```
