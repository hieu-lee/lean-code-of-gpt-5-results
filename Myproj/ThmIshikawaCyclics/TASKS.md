# Ishikawa Analog for Cyclic Numbers

## Context
- Goal: formalise Theorem\ref{thm:ishikawa} from `theorems/thm_ishikawa.tex`, proving `c_n + c_{n+1} > c_{n+2}` for all `n > 2` with the stated base equalities.
- Strategy: mirror the LaTeX proof exactly—dyadic prime-gap lemma from Nagura's theorem plus the enumerator check supplied by Szele's criterion.
- Constraint: keep each Lean file in this folder below 500 lines and run `lake build` after every substantial edit.

## Key Considerations
- Encode every external number-theoretic input (Nagura, Szele) as axioms with detailed citations and the `web_search` command used.
- Use existing cyclic-number infrastructure (`Myproj.CyclicNumbers`) for enumerator facts; avoid duplicating definitions.
- Prepare helper lemmas for translating counting facts into enumerator inequalities while keeping arguments on `ℕ` whenever possible.

## Action Items

### Setup
- [x] Create the folder structure and this tracker.
- [x] List all required classical results and add them as axioms with full bibliographic notes.

### Formalisation
- [x] Prove the dyadic gap lemma using the Nagura axiom and translate it to cyclic enumerator inequalities.
- [x] Implement the main Ishikawa inequality, covering the large-`x` case via the gap lemma and checking the finite prefix from Szele's list.
- [x] Package parity arguments ensuring strictness for `n \ge 3`.

### Verification
- [x] Run `lake build` after each major change and document blockers for the next iteration if any arise.

## Notes / Next Steps
- Pending once axioms are in place and the large-scale inequality proof is underway.
