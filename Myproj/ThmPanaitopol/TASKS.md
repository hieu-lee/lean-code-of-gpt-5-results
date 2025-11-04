# Panaitopol Counterexample Formalization

## Context
- Goal: verify Theorem~\ref{thm:panaitopol} from `theorems/thm_panaitopol.tex` by formalizing the fact that `c₃₅ = 91` using the project conventions for cyclic numbers.
- Outcome: Lean proof that reproduces the LaTeX argument, relying on documented axioms for classical number theoretic inputs.

## Key Considerations
- Reuse existing cyclic-number infrastructure (`Myproj.Definitions.Cyclics`, enumerator axioms) wherever possible.
- Introduce only standard classification results for cyclic numbers as new axioms, each with explicit citations and recorded search commands.
- Keep the new Lean files modular (< 500 lines) and runnable with `lake build` after each major edit.

## Upcoming Tasks
- [x] Catalogue required classical facts from the proof (classification of cyclic numbers, enumerations) and collect citations via web search commands.
- [x] Design Lean scaffolding: axioms module, auxiliary lemmas for enumerating cyclic numbers up to 91, and main theorem file.
- [x] Implement the proof that exactly 35 cyclic numbers are ≤ 91, concluding `cyclicEnumerator 35 = 91`.
- [ ] Integrate the new module into `Myproj.lean` and ensure `lake build` succeeds.
