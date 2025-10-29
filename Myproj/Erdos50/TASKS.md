# Context
- Formalize the proof of Erdős problem 50 in Lean inside `Myproj` project.
- Source materials: `erdos problems/erdos50.md` (LaTeX-style proof) and `erdos problems/erdos50.txt` (problem statement variant).

# Focus Points
- Extract every referenced classical theorem/result as axioms with bibliographic comments.
- Keep Lean files short (< 500 lines) by splitting helper lemmas if necessary.
- Run `lake build` after major edits to ensure the project stays consistent.

# To-Do
- [x] Review `erdos50.md` and `erdos50.txt` to outline the proof structure and identify external results.
- [x] Draft the Lean file skeleton, including imports, namespace, and theorem statement.
- [x] Enumerate needed axioms with literature citations and add them to `Myproj/Axioms.lean` if missing.
- [x] Implement helper definitions/lemmas in `Myproj/Definitions.lean` (or local file) as required by the proof.
- [x] Formalize each step of the proof, mirroring the structure of the provided argument.
- [x] Run `lake build` iteratively until the new code typechecks.
- [x] Document any remaining gaps or follow-ups in `TASKS.md` for future iterations.

## Notes
- Confirm in the next pass that the axioms suffice to link `schoenbergF` to the empirical measures when refining the formalisation beyond the high-level Vitali step.
