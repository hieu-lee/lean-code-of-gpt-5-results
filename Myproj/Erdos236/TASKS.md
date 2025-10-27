# Erdős Problem 236 Formalization Tasks

## Context
- Goal: formalize the proof from `erdos problems/conj8.md` showing `f(n) = o(log n)` via an explicit `O((log n)^{1/2} log log n)` bound.
- Port the argument into Lean with files capped at 250 lines while matching the textual proof structure.
- Follow the project guidance in `NOTICE.md`, including frequent `lake build` runs and centralized axioms.

## Key Considerations
- Extract every classical analytic input (large sieve, prime counting bounds, distribution of powers modulo primes) as general axioms with documented web citations.
- Keep helper lemmas localized inside this folder; reuse existing number-theoretic utilities from `Myproj.Definitions` where possible.
- Maintain clear separation between arithmetic setup (definitions, counting lemmas) and the additive large sieve estimate.

## Action Items

### Setup
- [x] Create `Myproj/Erdos236` workspace folder and this task tracker.
- [x] Add Lean module skeletons (`Axioms.lean`, helpers, proof file) and update project imports.

### Axioms and References
- [x] Use `web_search` to source citations for the additive large sieve inequality and standard prime-counting bounds, then record them as general axioms with comments.

### Helper Development
- [x] Define the counting objects (`f`, `S`, residue class data) and derive the inequalities leading up to the large sieve bound (`representation_le_sieve_add`, `sieveCount_log_bound`, etc.). See `Myproj/Erdos236/Bounds.lean:23-205` and `Myproj/Erdos236/LargeSieve.lean:20-242`.
- [x] Implement algebraic manipulations translating the sieve estimate into the final asymptotic for `f` (see `Myproj/Erdos236/Main.lean:577`).

### Main Proof
- [x] Assemble the full Lean proof of the upper bound `f(n) ≪ (log n)^{1/2} log log n`, concluding `f(n) = o(log n)` (`Myproj/Erdos236/Main.lean:611`).

### Verification
- [x] Run `lake build` after substantive edits and once the proof file is complete (`lake build` succeeds as of `Myproj/Erdos236/Main.lean` revision with `representation_three_pivot`).

## Notes / Future Work
- Consider isolating reusable sieve infrastructure if future Erdős problems require similar arguments.
- Revisit the axiomatized results for potential internal proofs once a mathlib strategy is clear.
