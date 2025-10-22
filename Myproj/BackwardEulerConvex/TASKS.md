# Proximal Backward Euler Convexity

Goal: formalize the convexity of the objective values along the implicit gradient step, matching the proof in `research mode traces/chosen_convex_result.json`.

What seems critical now:
- Express the proximal-point recurrence with short helper definitions (`sₙ`, `Δₙ`, `δₙ`).
- Capture the convex/strongly convex gradient inequalities as axioms with clear citations.
- Keep every Lean file under 250 lines and test frequently with `lake build`.

Upcoming steps:
- [x] Introduce axioms for the gradient inequalities (convex + strongly convex cases).
- [x] Implement `BackwardEulerConvex/Main.lean` proving `δₙ ≥ 0` and the strict decrease under strong convexity.
- [x] Import the new module in `Myproj.lean` and ensure the project builds (`lake build`).
