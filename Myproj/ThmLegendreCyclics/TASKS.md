# Legendre Cyclics Formalization Tasks

## Context
- Formalize the full proof of Theorem~\ref{thm:legendre_cyclics} (Legendre analog for cyclic integers) using the structure from myproj/theorems/thm_legendre_cyclics.tex.
- Ensure every external analytic-number-theory input (sieve bounds, Mertens product, Brun--Titchmarsh, Buchstab estimates, etc.) is stated as an axiom with bibliographic citation.
- Keep each Lean source file in this folder short (\(<250\) lines) while mirroring the LaTeX proof steps.

## Key Considerations
- Reuse shared notions from `Myproj.Definitions` and existing helper lemmas where possible; only introduce new local helpers if they are theorem-specific.
- Aggressively isolate imported classical results into axioms with precise hypotheses to minimize proof obligations.
- Leverage `lake build` after every substantial change to maintain a clean build cadence.

## Action Items

### Global
- [x] Catalogue external results in the LaTeX proof and encode them as axioms with citations in `Myproj/Axioms.lean`.
- [x] Sketch and create modules (axioms, definitions, main proof) keeping files short.
- [x] Run `lake build` after each substantial step.

### Axioms (`Myproj/Axioms.lean`)
- [x] Add Selberg sieve + Mertens product lower bound (Step 1) as an axiom.
- [x] Add squarefree-loss bound (Step 2) as an axiom.
- [x] Add obstruction bound via weighted Brun–Titchmarsh + Buchstab (Step 3) as an axiom.
- [x] Combine Steps 1–3 into a single axiom `legendre_good_candidates_lower_bound` with explicit constant `(e^{-γ}/8) · n / log n`.
- [x] Add small-`n` finite verification axiom.
- [x] Add Szele criterion for squarefree integers `squarefree_cyclic_iff_no_arrow`.

### Definitions (`Myproj/Definitions/LegendreCyclics.lean`)
- [x] Define `legendreInterval`, `legendreZ`, `legendreZRough`, `legendreRoughSet`.
- [x] Define local `squarefreeNat` and sets `legendreSquarefreeRough`, `legendreObstructedSet`.
- [x] Add lemma `no_square_between_consecutive_squares` (used in Step 2’s contradiction).

### Main proof (`Myproj/ThmLegendreCyclics/Main.lean`)
- [x] Implement the large-`n` case using the tightened axiom and Szele’s criterion.
- [x] Integrate the finite verification for small `n`.
- [x] Keep the file short and focused on orchestration.

### Verification
- [x] `lake build` passes for the whole project.

## Notes / Next Iterations
- Consider refining constants further by threading the `H = 2n+1` dependence explicitly if we want the best possible prefactor.
- If needed, add a helper counting lemma to bound cardinals in filtered finsets directly rather than using contradiction for nonempty differences.
