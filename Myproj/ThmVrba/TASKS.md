# Vrba Analog Formalization Tasks

## Context
- Formalize Theorem \ref{thm:vrba} from `theorems/thm_vrba.tex`, proving `cₙ / Gₙ → e` for cyclic numbers.
- Mirror the LaTeX proof structure: Abel summation, integral asymptotics, and the Pollack–de Bruijn inputs.
- Keep each Lean source file in this folder comfortably below 500 lines.

## Key Considerations
- Centralize every external analytic statement (Abel summation, Pollack asymptotic, de Bruijn integral estimate) as axioms with explicit citations and recorded search commands.
- Reuse shared definitions (enumerator, counting functions, iterated logs) from existing modules instead of duplicating them.
- After each substantive change, run `lake build` to keep the project compiling.

## Action Items

### Setup
- [x] Sketch Lean module layout (`Axioms`, `Main`, helper file if needed) and ensure imports stay minimal.
- [x] Record all required literature inputs as axioms with comments referencing the source search.

### Proof Development
- [x] Package the Abel summation step as the `VrbaRatioData` axiom, recording the explicit log decomposition and bounded error.
- [ ] Replace the manual tail-estimate axiom by proving `E n / (n+1) → 0` from the bounded-error field (current attempt broken; file does not compile).
- [x] Deduce `cₙ / Gₙ → Real.exp 1` from the logarithmic convergence using `continuous_exp`.

### Verification
- [ ] Re-establish a successful `lake build` after fixing the error-term argument.

## Notes / Next Iterations
- Fix `Myproj/ThmVrba/Axioms.lean`: restore the previous good state if helpful, then prove `cyclic_ratio_error_tendsto_zero` via a sandwich/ squeeze argument that uses the `‖E n‖ ≤ K` bound and the known limit of `K/(n+1)`.
- Consider isolating a reusable lemma turning `log`-convergence into ratio convergence for future geometric-mean arguments once the file builds.
