## Context

Goal: formalize `theorems/thm_dusart_cyclics.tex` in Lean inside
`Myproj/ThmDusartCyclics`, following the proof exactly:

1. Pollack-style asymptotic + de Bruijn inversion gives
   `c_n = e^gamma n (L3(n) + O(1))`.
2. Therefore `c_n / (e^gamma n) <= L3(n) + K` eventually.
3. Since `L4(n) -> +infinity`, eventually `L4(n) > K`.
4. Hence eventually
   `c_n < e^gamma n (L3(n) + L4(n))`,
   contradicting the proposed universal lower bound.

## Important Notes

- Keep files short/medium (strictly under 250 lines each).
- Aggressively extract literature inputs as general axioms with detailed
  source comments.
- Do not axiomatize specialized numeric instances; axioms must be general.
- Run `lake build` after each major step.
- Keep theorem statement/proof shape aligned with the TeX source.

## Tasks

- [x] Create theorem folder files (`Axioms.lean`, `Main.lean`, `TASKS.md`).
- [x] Add detailed citation-backed axioms in `Axioms.lean` from web search.
- [x] Implement full contradiction proof in `Main.lean`.
- [x] Update project imports (`Myproj/Axioms.lean`, `Myproj.lean`).
- [x] Preserve compatibility with `Myproj/ThmDusartCyclics.lean`.
- [x] Run `lake build` after each major phase and fix breakages.
- [x] Final pass: verify each file in this folder is <250 lines.
