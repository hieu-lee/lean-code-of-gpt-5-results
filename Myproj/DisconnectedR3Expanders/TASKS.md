# Context
- Goal: formalize the obstruction to universal spectral gaps for neighbor-sum distinguishing reconfiguration graphs R₃(G).
- Source: `research mode traces/chosen_graph_result.json` (Ramanujan base graph, fibered construction, triangle gadget, isolated weighting).

# Priorities
- Capture the reconfiguration framework (edge weightings, vertex sums, NSD property, single-edge updates).
- Encode the Ramanujan-based fiber construction and spectral gap lower bound exactly as in the written proof.
- Show ω, ω′ weightings satisfy the advertised properties and force a disconnected R₃(Y).

# Todo
- [x] Specify the background axioms (Ramanujan families, singular value facts, triangle gadget check) with citations.
- [x] Build Lean definitions for the fibered graph Y, vertex sums, and the reconfiguration graph R₃.
- [ ] Formalize ω, ω′ and prove ω is isolated while ω′ is NSD, yielding the main theorem.
- [ ] Integrate the new files into `Myproj.lean` and run `lake build` cleanly.
