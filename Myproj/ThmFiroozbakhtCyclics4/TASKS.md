## Context
- Goal: formalize `thm_firoozbakht_cyclics_4.tex` by translating the monotonicity argument for `A_𝒞(k)` into Lean.
- Key ingredients: primes are cyclic (Szele 1947) and Rosser–Schoenfeld's upper bound for the nth prime to control tails.

## Priorities
- Introduce axioms with explicit literature citations for the prime-cyclic inclusion and Rosser–Schoenfeld estimate.
- Define the normalised cyclic enumerator `aₙ(k)` and the maximum `A_𝒞(k)` using Lean's real sup over a finite window.
- Keep files short by isolating axioms, helper lemmas, and the main proof across separate modules.

## Upcoming Tasks
- [x] Record the supporting axioms (prime containment, Rosser–Schoenfeld bound, positivity) with search-command comments.
- [x] Implement the Lean proof that `A_𝒞(k)` is achieved on a finite window and strictly decreases with `k`.
- [x] Hook the new module into `Myproj.lean` and verify with `lake build`.
