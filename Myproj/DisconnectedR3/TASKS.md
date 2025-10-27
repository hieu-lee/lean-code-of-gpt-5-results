# Context
- Goal: formalize the expander counterexample for connectedness of `R₃(G)` (from `chosen_graph_result.json`) inside Lean.
- Source proof structure: build Ramanujan expanders, lift to a fibered graph `Y`, and exhibit two NSD weightings with one isolated.

# What Matters Most
- Extract every external theorem (Ramanujan existence, spectral bounds, NSD triangle gadget facts) as axioms with detailed literature citations obtained via `web_search`.
- Keep Lean files short (<250 lines) and modular: separate axioms, constructions, and the main proof.
- Run `lake build` after each substantial edit to catch issues promptly.

# TODO
- [x] Create the `DisconnectedR3` workspace with planning notes.
- [x] Record the necessary axioms with references and encode helper definitions.
- [x] Formalize the full graph argument proving the disconnectedness of `R₃(Y_N)`.
- [x] Integrate the module into `Myproj.lean` and confirm with `lake build`.
