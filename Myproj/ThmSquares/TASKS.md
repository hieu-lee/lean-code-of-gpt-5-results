# Cyclic Squares Formalization Tasks

## Context
- Formalize Theorem~\ref{thm:squares} from `theorems/thm_squares.tex`, matching the proof structure line-for-line inside Lean.
- Use axiomatized classical results (Pollack asymptotic, de Haan/Bingham--Goldie--Teugels increment theorem, iterated-log drift) with explicit citations, keeping Lean files compact (<250 lines).
- Maintain the cadence of `lake build` after every substantial edit to stay aligned with NOTICE.md guidelines.

## Key Considerations
- Reuse existing definitions for iterated logarithms where possible; introduce only theorem-specific helpers in local files.
- Every external analytic-number-theory input must appear as a general axiom annotated with a detailed source comment (include the retrieval URL from web searches).
- Keep the proof modular: isolate the asymptotic manipulation lemmas from the final statement for readability and reuse.

## Action Items

### Setup
- [x] Create `ThmSquares` workspace folder and this task log.
- [x] Add Lean module skeletons (`Auxiliary.lean`, `Main.lean`) tied into `Myproj.lean` if necessary.

### Axioms (`Myproj/Axioms.lean`)
- [x] Record Pollack's refined expansion with the $O(1/L^3)$ remainder and uniformity in fixed-scale comparisons (cite Pollack 2022 via retrieved URL).
- [x] Introduce an axiom placing `C` in de Haan's $\Pi$-variation class with auxiliary function `a(x)` (cite Bingham--Goldie--Teugels Thm. 3.7.2 and supporting search transcript).
- [x] State the local increment theorem for $\Pi$-variation (BGT 3.7.2) specialized to our auxiliary function.

### Definitions / Helpers
- [x] Add a short Lean file defining the auxiliary function `auxCyclic n` and its iterated-log shorthand, plus basic algebraic rewrites used in the main proof.
- [x] Prove the lemmas translating the asymptotic conclusion into the exact expression in Theorem~\ref{thm:squares}.

### Main Proof (`ThmSquares/Main.lean`)
- [x] Import the helper file, apply the local increment axiom with $h = (n+1)^2 - n^2`, and complete the algebraic simplification to the stated asymptotic.
- [x] Ensure the Lean statement mirrors the LaTeX theorem exactly (with `∼` on sequences indexed by `n : ℕ`).

### Verification
- [x] Run `lake build` after significant changes and once at the end to confirm the project compiles.

## Notes / Future Work
- Consider abstracting the uniform increment axiom into a reusable lemma for other powers (e.g., cubes) once the square case is settled.
- We may later formalize the Taylor expansion proof internally, but for now we rely on Pollack (2022) plus Bingham--Goldie--Teugels.
