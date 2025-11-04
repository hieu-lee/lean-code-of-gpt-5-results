# Rosser Analog for Cyclic Numbers

## Context
- Goal: formalise Theorem Rosser analog from `theorems/thm_rosser.tex` showing `cₙ > e^γ n log₃ n` for all `n > 1`.
- Source proof uses Pollack's expansion of the counting function and an elementary even-number sieve argument.

## Priorities
- Extract every analytical input (Pollack bounds, growth of iterated logs) as axioms with recorded search provenance.
- Keep the Lean code close to the LaTeX structure by splitting elementary bounds and large-`n` arguments.
- Maintain files below 500 lines with clear namespace boundaries and reusability of helper lemmas.

## Tasks
- [x] Record Rosser-specific axioms (`pollack_upper_bound`, enumerator growth tools) with citations.
- [x] Capture the linear bound `cₙ ≥ 2n - 5` (recorded as an axiom based on Szele's parity argument).
- [x] Prove the large-`n` inequality via the Pollack inputs and monotonicity surrogates for `log₃`.
- [x] Exhaust the finite set of remaining `n` using the linear lower bound.
- [x] Add the file to `Myproj.lean` and ensure `lake build` succeeds.
