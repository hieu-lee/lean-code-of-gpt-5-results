# K-fold Oppermann for primes

## Context
- Goal: mirror `theorems/thm_k_fold_oppermann_for_primes.tex` inside Lean with the same structure.
- Same proof strategy: rely on short-interval prime bounds (Iwaniec–Pintz / Baker–Harman–Pintz) and elementary logarithmic estimates.
- Results used from literature must appear as axioms in `Myproj/Axioms.lean` with explicit citations.

## Priorities
- Capture short-interval prime bounds as reusable axioms so the Lean proof stays short.
- Keep helper lemmas small; split the proof across multiple files (< 250 lines each).
- Run `lake build` after every significant code change to keep compilation feedback tight.

## Checklist
- [x] Add/verify axioms for the Iwaniec–Pintz short-interval lower bound with citation via `web_search`.
- [x] Introduce prime counting interval helpers mirroring \(N^{-}_{\mathcal P}\) and \(N^{+}_{\mathcal P}\).
- [x] Formalize the Lean proof of `k_fold_oppermann_for_primes` following the LaTeX argument.
- [x] Ensure `lake build` succeeds with the new modules imported by `Myproj.lean`.
