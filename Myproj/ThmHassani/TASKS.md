## Context
- Goal: formalize Hassani analog theorem showing `A_n / G_n → e / 2` by mirroring the LaTeX proof in `theorems/thm_hassani.tex`.
- Setup: follow project guidelines (centralized axioms/definitions, short files, frequent `lake build`).

## Priorities
- Extract every standard analytic result (Abel summation, Karamata, slowly varying facts) as axioms with precise citations.
- Keep the formal proof parallel to the LaTeX argument: define `S` and `J`, express partial summation, and transfer asymptotics along the cyclic sequence.
- Maintain small, composable lemmas so no file exceeds 500 lines.

## Tasks
- [x] Inventory the LaTeX proof to list required lemmas/axioms and identify matching mathlib content.
- [x] Draft `Axioms.lean` with cited statements (Abel summation, Karamata integral theorem, slowly varying closure properties, cyclic asymptotics).
- [x] Implement helper lemmas/definitions (partial sums, enumerations) needed for the main proof.
- [x] Formalize the main theorem in `Main.lean`, mirroring the LaTeX structure step-by-step.
- [x] Run `lake build` (and targeted `lake env lean`) after major edits to ensure typechecking.
- [ ] Integrate the Hassani theorem into the project overview (README + theorem index).
- [ ] Compare the new axioms with Vrba/Dusart stacks to see whether any can be derived rather than assumed.
- [ ] Collect downstream corollaries (e.g. bounds for the median cyclic number) now that the limit result is in place.
