## Context

Goal: formalize `theorems/thm_infinitely_many_sg_cyclics.tex` in Lean, following the proof structure (Steps 1–5) and keeping files short (<250 lines).

Key idea in the TeX proof:
- Define a “good” set `𝒢(x)` by starting from simultaneous roughness conditions for `n` and `2n+1` (Step 1), then removing the exceptional sets where squarefreeness fails (Step 2) or Szele obstructions occur for `n` (Step 3) or `2n+1` (Step 4).
- Show `#𝒢(x) ≫ x / log log x`, hence `𝒢(x)` is nonempty for large `x`.
- For `n ∈ 𝒢(x)`, deduce both `n` and `2n+1` are cyclic (Szele criterion), so there are infinitely many SG cyclics (Step 5).

Important for this formalization:
- Keep analytic/prime-distribution inputs as axioms with careful citations (CRT counting, Mertens-type product, Brun–Titchmarsh, etc.).
- Keep the *set-theoretic* and *logical* glue (from “not in bad set” to “squarefree/no obstruction” to “cyclic”) fully formalized.
- Prefer `Finset`-based counting and simple `Nat` lemmas; avoid large analysis developments.

## Tasks

- [x] Create Lean modules for this theorem (Axioms/Definitions/Main).
- [x] Add cited axioms needed for Steps 1–4 (with sources found via web).
- [x] Define `y(x)`, `S0`, `S1`, `B_n`, `B_{2n+1}`, `G(x)` as in the TeX.
- [x] Prove: `n ∈ G(x)` ⇒ `squarefree n` and `squarefree (2n+1)`.
- [x] Prove: `n ∈ G(x)` ⇒ “no Szele obstruction” for `n` and for `2n+1`.
- [x] Use Szele characterization axiom (`squarefree_cyclic_iff_no_arrow`) to deduce cyclicity.
- [x] Prove Step 5: `n ∈ G(x)` ⇒ `isSGCyclicNumber n`.
- [x] Prove infinitude: from eventual lower bound on `#G(x)` get infinitely many SG cyclics.
- [x] Update `Myproj/Axioms.lean` and `Myproj.lean` to import the new modules.
- [x] Run `lake build` after each major edit; keep all files <250 lines.
