# Erdős Problem 236 Task Tracker

## Advisor Directive (2025-02)
- Re-express the main asymptotic statement in `Myproj/Erdos236/Main.lean` so that it matches the `formal-conjectures` version verbatim.
- Eliminate reliance on custom axioms by rebuilding every ingredient from Mathlib where possible (long-term).

## Current Steps
1. **Mirror Statement** — introduce the exact definition of `f` and theorem `erdos_236` from `FormalConjectures/ErdosProblems/236.lean`, then re-prove the result using the existing infrastructure. ☑ _Done (2025-02-15)_
2. **Discharge Axioms** — replace each placeholder axiom in `Axioms.lean` with Mathlib proofs or references once available. ☐ _In progress_

## Notes
- Align `primeCount` with `Nat.primeCounting` to leverage existing Mathlib lemmas; remove or justify the Rosser–Schoenfeld style bounds once proven internally.
- Investigate Mathlib's `NumberTheory` library (e.g. `PrimeCounting`, `PrimeNumberTheorem`, Chebyshev bounds) to obtain replacements for `primeCount_upper` / `primeCount_lower`; document constants and thresholds used.
- Search for an additive large sieve statement in Mathlib or formalize the required inequality directly so that `additiveLargeSieve` is no longer an axiom.
- `lake build` last succeeded after mirroring the main theorem (2025-02-15); keep rebuilding after substantive edits.
- Track progress on axiom removal with inline comments in `Axioms.lean` and update this tracker once each ingredient is discharged.
