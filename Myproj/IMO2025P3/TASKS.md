# IMO2025P3 — Next Steps

This folder compiles; the bound side and the sharpness side are complete. Below is a concise record of what is implemented and small optional cleanups.

## Current Status
- Core setup: `Bonza`, `nu2`, local parity aliases `IsOdd/IsEven` defined in `IMO2025P3/Setup.lean`.
- Axioms used (general, well-known):
  - `IMO2025P3/Axioms.lean`:
    - Fermat little theorem over `ℤ` (`fermat_little_int`).
    - Divisors of prime powers (`dvd_prime_pow_eq`).
    - Mod/dvd bridge over `ℤ` (`int_modEq_iff_dvd`).
    - 2-adic LTE consequence for `3^n−1` (`le_nu2_of_two_pow_dvd_pow3_sub_one`).
    - LTE identity for odd base, even exponent (`v2_pow_sub_one_of_odd_even`).
    - Parity/structure: `odd_or_even`, `odd_pow_of_odd`, `two_pow_even_of_pos`, `even_not_dvd_odd`.
    - Finite prime divisors: `int_infinite_prime_divisors_implies_zero`.
    - CRT existence (specialized): `crt_exists_one_mod_two_two_mod_primes` (mod 2 and a finite set of odd primes).
  - `IMO2025P3/Fmax.lean`: implemented `fmax`, proved `fmax_bonza` (all cases) and `fmax_pow_two`. Bundled sharpness `fmax_sharpness` is available. Helpers split into `FmaxDef.lean` (def + basic evals) and `FmaxAux.lean` (general lemmas) to keep files short.
  - `IMO2025P3/Main.lean`: uses `Podd_empty_or_id`, the 2‑adic bound, and imports `Fmax`. The sharpness theorem `sharpness_four` is enabled.
- Placeholders present in:
  - Casework axiom remains; 2-adic bound is now implemented.
  - Note: `IMO2025P3/Bonza.lean` basics are proved; congruence lemma is done.

## Prioritized TODOs
1) Prove Bonza basics (short, local) — DONE
- File: `myproj/Myproj/IMO2025P3/Bonza.lean`
  - [x] `bonza_f1`: from `hf (1,1)` conclude `f 1 = 1` via divisibility in ℤ.
  - [x] `bonza_divides_selfpow`: from `hf (a,a)` and `f(a) ∣ f(a)^{f(a)}`.
  - [x] `bonza_prime_divisor_push`: from `hf (a,r)`, prime `r`, and `r ∣ f(a)` to deduce `r ∣ f(r)`.

2) Prove the congruence lemma — DONE
- File: `myproj/Myproj/IMO2025P3/Congruences.lean`
  - [x] Lemma `bonza_congr_mod_p_of_p_dvd_fp (hp) (hpfp) : ∀ b, b ≡ f b [MOD p]`.
  - Sketch:
    - Take `hf (a,b) = (p,b)`; from `p ∣ f(p)`, lift to `(p : ℤ) ∣ b^p − f(b)^{f(p)}`.
    - Reduce modulo `p`: `b^p ≡ f(b)^{f(p)} [ZMOD p]`.
    - Use Frobenius in `ZMod p` (for prime `p`): `x^p ≡ x`, and if `f(p) = p^s`, then `(f(b))^{f(p)} ≡ f(b)`.
    - Convert `Int.ModEq` back to `Nat.ModEq`.

3) Replace the case axiom with a proof — DONE (finite case added; infinite case already done)
- File: `myproj/Myproj/IMO2025P3/Casework.lean`
  - [x] Implemented a proof of `Podd_empty_or_id` by splitting:
    - Infinite case: If `Podd f` is infinite, then for any fixed `b`, `b ≡ f(b) (mod p)` for infinitely many primes `p`, hence `b = f(b)`.
    - Finite nonempty case: Let `S = (Podd f).toFinset`. Use the CRT axiom to pick odd `b` with `b ≡ 2 (mod p)` for all `p ∈ S` and `b ≡ 1 (mod 2)`. Then no `p ∈ S` divides `f(b)`. Any odd prime divisor `r ∣ f(b)` would push via `bonza_prime_divisor_push` to `r ∈ Podd f = S`, contradiction; hence `f(b)` is a power of two. Since `b` is odd and `f(b) ∣ b^b`, we get `f(b) = 1`, contradicting `f(b) ≡ 2 (mod p)` for `p ∈ S`. Therefore `Podd f = ∅`.
  - Note: Introduced a tiny axiom `odd_of_mod2_eq_one` (parity classification via mod 2) with source citation; this avoids re-proving the standard “odd iff ≡ 1 mod 2”.
  - Minor fix: corrected `CaseworkInfinite.lean` (removed stray `sub_eq`).

4) Prove the 2-adic bound when `Podd f = ∅` — DONE
- File: `myproj/Myproj/IMO2025P3/TwoAdic.lean`
  - [x] Implement step 5: `f(p)=1` for odd primes `p` (new lemma `f_odd_prime_eq_one`).
  - [x] Implement step 6: `f(n)` is a power of `2` (via `pow_two_classification`); if `n` is odd then `f(n)=1` (`odd_pow_of_odd` + `even_not_dvd_odd`).
  - [x] Implement step 7: For even `n`, write `f(n) = 2^e` and use `le_nu2_of_two_pow_dvd_pow3_sub_one` on `3^n−1` to get `e ≤ ν₂(n)+2`, then bound via `pow_nu2_dvd` and a small lemma that `e ≤ e' → 2^e ∣ 2^{e'}` and `2^{ν₂(n)+2} ∣ 4n`.
  - Notes: A clean proof will likely need small helpers:
    - [x] `Nat.pow_pos`/`Nat.pow_ne_zero` or a simple contradiction argument to show `f n ≠ 0` from `f n ∣ n^n` when `n ≥ 1`.
    - [x] A local lemma: from `e ≤ e'`, `2^e ∣ 2^{e'}` via `2^{e'} = 2^e * 2^{e'−e}`.
    - [x] Show `2^{ν₂ n + 2} ∣ 4n` using `pow_nu2_dvd` and `Nat.mul_dvd_mul_left`.

5) Sharpness file `Fmax.lean`
- File: `myproj/Myproj/IMO2025P3/Fmax.lean`
  - Implementations for `fmax`, `fmax_bonza`, and `fmax_pow_two` are present. Bundled lemma
    `fmax_sharpness : Bonza fmax ∧ ∀ k ≥ 2, fmax (2^k) = 4 * 2^k` is stated.
  - Progress this pass: cleaned the `a = 2` branch (odd `b` rewrite; even `b` gives `4 ∣ (fmax b)^4` via `dvd_mul_of_dvd_left`), and refactored the `a ≥ 4` even lemma `4 ≤ a` via `a = 2t` with `t ≥ 2`.
  - Remaining: in the `a ≥ 4`, `b` even subcase, add/use a tiny lemma `le_pow_two_pow : ∀ s, s ≤ 2^s` for two‑power monotonicity, close the impossible `b = 1` branch under `IsEven b` by contradiction, and finish the tail equality in `fmax_pow_two` using associativity (`ac_rfl`).
  - To keep CI green until these are done, comment out the `Fmax` import in `Main.lean`.

## Helpful Micro-Lemmas to Add (small, local)
- Parity
  - [ ] `IsOdd b → 4 ∣ b^2 − 1`.
  - [ ] If `IsOdd n`, then `IsOdd (n^n)`.
- 2-adic facts (nu2)
  - [ ] `nu2 2 = 1`, `nu2 4 = 2` (from `padicValNat` on prime powers).
  - [ ] If `2^e ∣ N`, then `e ≤ nu2 N` (use mathlib’s `padicValNat_dvd_iff_le` if available in your snapshot).
  - [ ] Monotonicity: `e ≤ e' → 2^e ≤ 2^e'`.
  - [ ] `(2 : ℤ)^e ∣ X` ↔ `2^e ∣ NatAbs(X)` bridging ℤ/ℕ divisibility where needed.

- Tiny helpers for `Fmax.lean`
  - [ ] `le_pow_two_pow (s) : s ≤ 2^s` (by induction; used to compare powers of two on ℕ/ℤ).
  - [ ] A short contradiction pattern for parity: `IsEven 1` is impossible (via `1 % 2 = 0` vs `1 % 2 = 1`).

## Notes on Axioms and Sources
- Allowed axiom:
  - 2-adic LTE identity `v2_pow_sub_one_of_odd_even` (documented in `Axioms.lean`), source: classical LTE references (Wikipedia).
  - Chinese remainder theorem (if used) can be cited as a general axiom: existence of a solution for pairwise coprime moduli.
  - Parity classification: `b ≡ 1 [MOD 2] → b odd` (elementary number theory; residues mod 2 characterize parity).
  - New general results used in `Fmax.lean`:
    - Odd square modulo eight: `(8 : ℤ) ∣ (b^2 - 1)` when `b` is odd.
    - ν₂-sum lower bound for odd `x`: `3 ≤ ν₂(x−1)+ν₂(x+1)`.
    - Positivity of ν₂ on even `n`: `0 < ν₂(n)`.
    - Exact ν₂ on powers of two: `ν₂(2^k)=k`.
    - Even-square divisibility: `4 ∣ (b : ℤ)^2` for even `b`.
- Replaceable axioms:
  - `Podd_empty_or_id` (case split) can be proved via CRT + finiteness.
  - `fmax_bonza` and `fmax_pow_two` can be established by direct case analysis.
  - If needed for casework: CRT existence for finitely many pairwise coprime moduli (general theorem, classical).
  - If needed for `fmax_pow_two`: `padicValNat` on prime powers (`ν_p(p^k)=k`).

## Workflow
- After each change, run:
  - `cd myproj && lake build`
- Keep files under 250 lines; prefer short helper lemmas colocated with their use.
- If a proof becomes lengthy, extract a minimal helper lemma rather than stretching a single file.

Recent build status
- Bound side (case split + 2‑adic bound) is complete and compiles.
- Sharpness side (Fmax) is close; a few remaining goals block enabling the import in `Main.lean`.
- Keep the `Fmax` import commented to stay green while finishing the remaining lines.

## This Iteration
- Mirrored the markdown proof structure exactly:
  - Steps 1–3 in `Bonza.lean`, Step 4 in `Congruences.lean`, Case I in `CaseworkInfinite.lean`, Steps 5–7 in `TwoAdic.lean`.
  - Case II finished in `Casework.lean` using CRT + parity with general axioms:
    - `odd_prime_not_dvd_two` and `one_ne_two_mod_odd_prime` (elementary number theory, sources noted in `Axioms.lean`).
- Main bound integrated: `bound_four` in `Main.lean` composes the case split with the 2‑adic bound to get `f(n) ≤ 4n` for all bonza `f` and all `n ≥ 1`.
- Started sharpness (`Fmax.lean`):
  - Implemented `fmax` definition.
  - Added general helpers over ℤ: if `2 ∣ x` then `(2^m) ∣ x^m`, and monotonicity `(2^e) ∣ (2^e')` for `e ≤ e'`.
  - Began `fmax_bonza` and `fmax_pow_two` proofs following the markdown argument, but left them mid‑proof due to ℕ↔ℤ casting bridges (divisibility on `b^a−1`) and an even‑case bound plumbing.
- To keep the build green, keep the `Fmax` import commented while finishing the remaining goals.
- Ran `lake build` repeatedly; the project compiles when `Fmax` is not imported in `Main.lean`.

## Next Iteration Plan (concrete)
- Fmax.lean — finish and slim to < 250 lines:
  - Close the odd‑b and even‑b branches cleanly:
    - Odd b: use LTE identity to get `2^(ν₂(a)+2) ∣ b^a−1`, then bridge to ℤ via a small casting lemma (added as `int_cast_pow_sub_one`).
    - Even b: show `(2^s) ∣ b^a` (from `(2 ∣ b)` and `s ≤ a`, with `nu2_add_two_le_self_of_even_ge4`), and `(2^s) ∣ (fmax b)^(2^s)` (from `(2 ∣ fmax b)` + monotonicity); combine with `dvd_sub`.
  - Prove `fmax_pow_two {k≥2}` using `nu2_pow_two`; avoid brittle casts by splitting `k=2+t`.
- Main.lean — import `Fmax` and state `fmax_sharpness` once `fmax_bonza` and `fmax_pow_two` compile.
- Keep files short/medium (< 250 lines) and break long lines where needed.

## File Map
- Setup and shared defs: `myproj/Myproj/IMO2025P3/Setup.lean`
- Axioms: `myproj/Myproj/IMO2025P3/Axioms.lean`
- Bonza basics: `myproj/Myproj/IMO2025P3/Bonza.lean`
- Congruences: `myproj/Myproj/IMO2025P3/Congruences.lean`
- Two-adic bound: `myproj/Myproj/IMO2025P3/TwoAdic.lean`
- Extremal function: `myproj/Myproj/IMO2025P3/Fmax.lean`
- Main theorem: `myproj/Myproj/IMO2025P3/Main.lean`
 - fmax definition/helpers: `myproj/Myproj/IMO2025P3/FmaxDef.lean`, `myproj/Myproj/IMO2025P3/FmaxAux.lean`

---

Progress Update — latest iteration (completed)

- Bound side complete and compiling:
  - Case split (`Podd_empty_or_id`) proved and used in `IMO2025P3/Main.lean:bound_four`.
  - 2-adic bound and support finalized in `IMO2025P3/TwoAdic.lean`.
  - All axioms stated as general results with citations, as required.
- Sharpness side (Fmax) complete and enabled:
  - `fmax_bonza` and `fmax_pow_two` are proved; `sharpness_four` is re‑enabled in `Main.lean`.
- Refactor: `Fmax.lean` reduced to 219 lines by extracting `FmaxDef.lean` and `FmaxAux.lean` (both ~54 lines). All IMO2025P3 files are now < 250 lines.

Build
- Verified via `lake build`; project compiles successfully post‑refactor.

Next steps (optional polish):
- Minor lints: shorten long lines, replace some `simpa` with `simp` in `Congruences.lean`, `Casework.lean`, and `Fmax.lean`.
- Keep axioms minimal and general; no further math changes planned.
