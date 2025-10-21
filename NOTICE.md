NOTICE: Guidelines for Formalizing LaTeX Proofs in Lean (Asymptotics, Regular Variation, Counting)

This project collects practical tips to keep future Lean formalizations smooth when translating LaTeX proofs that use asymptotics, regular variation, and counting arguments. These notes are based on issues we actually hit and fixed.

Project Structure
- Keep general results in `Myproj/Axioms.lean` with citation comments. Never axiomatize a specialized consequence; only the general theorem.
- Put reusable definitions and helper lemmas in `Myproj/Definitions.lean`.
- Keep theorem‑specific proof code in a dedicated file (e.g. `Myproj/AsymptoticKCyclicsBetweenCubes.lean`) and import both `Axioms` and `Definitions`.
- Keep `Myproj.lean` importing the key modules so `lake build` compiles the whole project.

Axioms and Citations
- When a result is cited (e.g., Bingham–Goldie–Teugels 1989: “slowly varying ⇒ n^ε L(n) → ∞”), state it as a general axiom with clear commentary (source, exact statement, hypotheses).
- Do not axiomatize derived conclusions you need in your proof; instead, prove their hypotheses, then apply the general axiom.

Definitions and Reusable Lemmas
- Centralize shared objects (intervals, counts, witnesses) in `Definitions.lean`.
- Add small algebraic helper lemmas you’ll need repeatedly (these paid off):
  - `rpow_bound_sub_of_mul_bound`: from `x^a * L ≤ c * x^b` and `x > 0` deduce `x^(a-b) * L ≤ c`.
  - `rpow_scale_bound_of_mul_bound`: from `x^(2ε) * L ≤ c` and `x > 0` deduce `x^ε * L ≤ c * x^(−ε)`.
- Prefer `calc` and local equalities for algebra; avoid long `simp` chains on commutative products.

Handling Limits and Filters
- Prefer `tendsto_iff_norm_sub_tendsto_zero` to extract “eventually small” inequalities without metric‑ball gymnastics.
- Use `tendsto_rpow_neg_atTop` (mathlib) composed with `tendsto_natCast_atTop_atTop` to derive sequence limits on `ℕ`.
- Keep your filter domains consistent: stay on `ℕ` unless the proof really moves to `ℝ`.

Real Powers (`Real.rpow`) Tips
- Choose the identity with the right hypothesis:
  - `rpow_add hxpos y z` needs `0 < x`; gives `x^(y+z) = x^y * x^z`.
  - `rpow_neg hx_nonneg y` needs `0 ≤ x`; gives `x^(−y) = (x^y)⁻¹`.
  - `rpow_natCast` bridges `x^n` and `x.rpow n`.
- Before rewriting with `rpow` lemmas, make positivity explicit (`0 < (N : ℝ)`).
- Avoid converting `(N:ℝ)^2` back and forth repeatedly; rewrite once via a local equality and reuse it.

Eventual Positivity and Casting
- Keep “eventually” statements on `ℕ` where your data live (counts indexed by `N : ℕ`), and cast to `ℝ` only locally.
- When using inequalities across casts, prefer `exact_mod_cast` or build them in `ℝ` directly to avoid `norm_cast` headaches.

Avoiding `simp` Pitfalls
- Prefer targeted `rw` or `calc` over `simp` for algebra; `simp` can loop on commutative rearrangements or `rpow`↔`pow` conversions.
- Avoid `simp [mul_comm, mul_assoc, mul_left_comm]` globally; keep rearrangements local and explicit.
- If you need to rewrite only one side of an inequality, introduce a local `have` and rewrite once with `rw`.

Asymptotics and Regular Variation
- Model “A ~ f” as a ratio limit plus eventual positivity of the denominator (needed to derive numeric bounds).
- To get a practical bound, use a concrete inequality on `|A/f − 1|` and an elementary step to deduce `f ≤ 2A` eventually.
- Model regular variation as `∃ L, SlowlyVarying L ∧ EventuallyPositive L ∧ (∀ᶠ N, f N = N^ρ * L N)`.

Workflow and Build
- After writing/editing a lemma, run `lake build` to typecheck before layering more changes.
- For a single file check: `lake env lean Myproj/SomeFile.lean` if the project is already built; otherwise prefer `lake build`.
- Use ripgrep to locate definitions/lemmas quickly, e.g. `rg -n "rpow_add|rpow_neg|tendsto_rpow_neg_atTop" .lake/packages/mathlib/Mathlib`.

Linting and Style
- Break long docstrings and signatures to respect line length.
- If a parameter is kept to mirror a LaTeX statement but unused, prefix it with `_` and add a short comment explaining why.
- Heed linter hints like “try simp instead of simpa,” but prefer `rw`/`calc` when clearer.

Debugging Patterns That Help
- `ℕ` vs `ℝ`: keep events/quantifiers on `ℕ`, push casts to the last possible step.
- Division/inversion in inequalities: avoid `field_simp` unless necessary; use rpow algebra or monotone lemmas (`div_le_div_of_nonneg_right`, `mul_le_mul_of_nonneg_left`) with explicit positivity.
- Limits across domains: compose with `tendsto_natCast_atTop_atTop` to move from `ℝ` statements to sequences over `ℕ`.

Template for New Theorem Files
- Header: imports (mathlib analysis/filters), then `Axioms`, `Definitions`.
- `namespace`, `noncomputable section`, `open Filter`, `open scoped BigOperators`.
- Local helpers (events, small inequalities like ratio bounds).
- Theorem statement mirroring the LaTeX.
- Proof structure: bounds → assume RV + asymptotics → extract `L` and equality event → peel powers and scale with helper lemmas → contradict slowly varying growth (BGT) → finish.

Common Gotchas
- Mixing `𝓝` and `nhds`: if symbol resolution fails, use `nhds`.
- Using `rpow_add`/`rpow_neg` without the required `0 < x` / `0 ≤ x` hypotheses.
- Letting `simp` rewrite both sides of an inequality blindly; use `rw` at the exact subterm instead.
- Forgetting eventual positivity when applying bounds derived from asymptotic equivalence.

Task-Specific Difficulties (Carneiro analog for cyclics) and How To Avoid Them

- Heavy first mathlib build and timeouts
  - Difficulty: `lake env lean …` and `lake build` hit timeouts on the first run building mathlib.
  - Avoid: fetch caches before building (`lake exe cache get`), or run `lake build` once and then use `lake env lean <file>` for iterative checks. Keep imports minimal in theorem files.

- Missing imports causing unknown identifiers
  - Difficulty: `Nat.coprime`, `isCyclicNumber`, `consecutiveCyclic`, `Real.log`, `Real.sqrt` were reported unknown in `Axioms.lean`.
  - Avoid: ensure `Axioms.lean` imports `Myproj.Definitions` if it refers to project definitions; add `Mathlib.Analysis.SpecialFunctions.Log.Basic` and `…Sqrt` when axioms mention `log`/`sqrt`.

- Using non-existent modules from mathlib
  - Difficulty: Importing `Mathlib.Data.Nat.GCD` failed (module doesn’t exist); we only needed `Nat.gcd`.
  - Avoid: Prefer core/standard imports (e.g. `Mathlib.Tactic` or `Mathlib.Data.Nat.Basic`) unless a specific file is required. Use ripgrep in `.lake/packages/mathlib/Mathlib` to confirm a path before importing.

- Axiom hygiene and placement
  - Difficulty: Initially introduced concrete axioms (e.g., `cyclic7`, `notCyclic8`, …) which go against the guideline “axiomatize general results only.” Also risked duplicating axioms across files.
  - Avoid: Put only general results in `Myproj/Axioms.lean` (with citations). Derive small instances inside theorem files using general axioms (e.g., compute φ(8), gcd facts, then conclude cyclicity). Before adding an axiom, check `Axioms.lean` to prevent duplicates.

- Reconciling goal shapes in numeric steps
  - Difficulty: Had a mismatch between a bound with `4` and a goal phrased as `11 − 7`.
  - Avoid: Add a local rewrite `(11 - 7 : ℝ) = 4` (via `norm_num`) before `simpa`. When mirroring LaTeX arithmetic, insert explicit casts/rewrites to match both sides syntactically.

- Case analysis on small natural intervals
  - Difficulty: `interval_cases` usage was finicky; easier to perform manual case splits with `eq_or_lt_of_le` and `le_antisymm`.
  - Avoid: For tiny ranges (here 7 < m < 11), step through `m = 8 ∨ m = 9 ∨ m = 10` using basic `Nat` lemmas; this is more robust.

- Leveraging decision procedures
  - Tip: Many small facts (primality of small numbers, gcd of small naturals) are solvable with `by decide`. Use them to keep the proof concise and deterministic.

- Deriving analytic bounds vs. axiomatizing them
  - Difficulty: We initially kept a small numeric axiom `sqrt7log7_lt_4` to speed things up.
  - Avoid: Prefer deriving `log 7 < 2` via `Real.log_lt_iff_lt_exp` and a general axiom like `exp_two_gt_seven`, then conclude `√(7 log 7) < 4` using monotonicity of `mul` and `sqrt` and the inequality `14 < 16`.

- Build tooling gotcha
  - Difficulty: `lean --make` is not a Lean 4 CLI flag; using it produced errors.
  - Avoid: Use `lake build` to build targets or `lake env lean <file>` to typecheck a file. For faster iteration, rely on the project build cache rather than invoking Lean with custom flags.

Task-Specific Difficulties (Dusart analog for cyclics) and How To Avoid Them

- Axioms file independence and namespaces
  - Difficulty: “Function expected” errors in `Axioms.lean` when axioms referenced project defs (`L3`, `cyclicCountUpTo`) by short names inside binders; stray `namespace`/`end` placements and unterminated docstrings also caused parser errors.
  - Avoid: Keep `Axioms.lean` independent of project defs; state axioms using explicit expressions (e.g., write `fun n ↦ log (log (log (n : ℝ)))` directly). If an axiom must reference project names, fully qualify (e.g., `Myproj.cyclicCounting`) and make sure surrounding `namespace … end` blocks are correct. Place long standalone axioms (like Pollack) outside the namespace or qualify every symbol.

- Euler–Mascheroni constant name
  - Difficulty: Using `Real.eulerMascheroniConstant` requires importing `Mathlib.NumberTheory.Harmonic.EulerMascheroni`; missing the import produced unknown identifiers deep in proofs.
  - Avoid: Either import the module, or introduce an abstract constant `eulerMascheroni : ℝ` in `Axioms.lean` to decouple theorem files from mathlib’s naming.

- Counting/enumerating interface
  - Difficulty: Switching between “existence of an enumerator” and a fixed enumerator name led to awkward `rcases` failures when the existence statement wasn’t a proper `Prop` or was out of scope.
  - Avoid: Provide both a named enumerator `cyclicEnumerator : ℕ → ℝ` and a relation axiom `cyclic_enumerator_pair : CountingEnumeratingPair cyclicCounting cyclicEnumerator`. If you prefer existence instead, phrase it as `∃ c, CountingEnumeratingPair cyclicCounting c` (a `Prop`) and keep it in `Axioms.lean`.

- Use norms `‖·‖` in axioms
  - Difficulty: `Real.abs` wasn’t always available without extra imports; axioms failed to parse.
  - Avoid: State analytic error bounds using `‖ · ‖` and ensure `Mathlib.Data.Real.Basic` is imported where needed.

- Iterated logs `L3`, `L4`
  - Difficulty: Referring to `Myproj.L3` inside `Axioms.lean` caused scope and resolution issues.
  - Avoid: In axioms, write the iterated log explicitly. In theorem files, define local `L₃, L₄` helpers if convenient and prove `L₄ → ∞` via composition of `tendsto_log_atTop`.

- From `|x − y| ≤ K` to an upper bound
  - Difficulty: Using `sub_le_iff_le_add` in the wrong direction produced type mismatches.
  - Avoid: Use `abs_le.mp hx` to get the pair of bounds; then `linarith` to deduce `x ≤ y + K`.

- Multiplying inequalities
  - Difficulty: Needed `βn > 0` to multiply by `βn`; deriving it from `n ≥ 2` and `exp(·) > 0` was fussy.
  - Avoid: Prove `0 < n` from `2 ≤ n` with `lt_of_lt_of_le (by decide : 0 < 2) h`, cast to `ℝ`, and use `mul_pos`/`mul_nonneg` as appropriate. Prefer `mul_le_mul_of_nonneg_right` when you only have nonnegativity.

- Local notation vs local defs
  - Difficulty: Using local notation (e.g., `local notation "L₃" => …`) triggered quotation precheck errors in some contexts.
  - Avoid: Prefer short local `def L₃ (n : ℕ) : ℝ := …`/`def L₄ …` instead of `local notation`.

- Event extraction from filters
  - Difficulty: Combining multiple eventual statements is error-prone when indices differ.
  - Avoid: Use `eventually_atTop.1` to extract indices, take `N0 := max …`, and rewrite all eventual claims at `N0` with the appropriate `≤` proofs.

- Build cadence and timeouts
  - Difficulty: First-time `lake env lean` on a new file often times out while mathlib builds.
  - Avoid: Run `lake build` once to prime caches; then iterate with `lake env lean <file>`. Keep imports minimal in the new theorem file.

- Lint/style pragmatism
  - Difficulty: Long lines and `simp` vs `simpa` warnings were noisy but harmless.
  - Avoid: Break lines near 100 chars; prefer `simp` for direct simplifications; heed linter hints only after the file typechecks.
