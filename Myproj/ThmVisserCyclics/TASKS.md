# Visser Analog for Cyclics

## Context
- Goal: formalise Theorem \ref{thm:visser_cyclics} from `theorems/thm_visser_cyclics.tex`, proving the eventual bound `√(c_{n+1}) - √(c_n) < ε`.
- Mirror the LaTeX proof: linear-sieve lower bound, removal of exceptional integers, Mertens’ product asymptotic, and the final enumerator argument.
- Keep every Lean source in this folder comfortably under 500 lines; split helper lemmas if a file grows too large.

## Key Considerations
- Record each analytic input (linear sieve, Brun–Titchmarsh, divisor-sum clean-up, Mertens) as axioms with precise bibliographic comments and the search commands used.
- Work with the real-variable counting function `C(x)` and bridge to the enumerator via existing axioms to control the gaps between cyclic numbers.
- After each substantive change, run `lake build` to maintain a compiling project before layering more code.

## Action Items

### Setup
- [x] Create folder structure and seed this task tracker.
- [x] Catalogue all literature results required by the proof and encode them as reusable axioms with sources.

### Proof Development
- [x] Derive the short-interval lower bound `(A)` from the axioms and make it available as a helper lemma.
- [x] Formalise the main theorem showing `√(c_{n+1}) - √(c_n) < ε` for large `n`, following the LaTeX steps.

### Verification
- [x] Run `lake build` after major code additions and record any blockers for future iterations.

## Notes / Next Steps
- The short-interval lemma `(A)` is now proved directly from the sieve axioms with explicit helper lemmas (`sqrt_log_tendsto_atTop`, `sqrt_log_le_log`, Mertens-factor expansion).
- The main gap estimate `visser_gap_bound` compiles; the threshold `N` packages both the analytic size condition and the eventual positivity from `cyclicEnumerator_gap_bound`.
- Potential refinements: tighten the algebra inside `Main.lean` by factoring shared positivity lemmas, and keep an eye on file size—split out auxiliary real-analysis facts if the file grows further.
