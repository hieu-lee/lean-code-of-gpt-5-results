import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Mathlib.Topology.Basic
import Myproj.ThmInfinitelyManySGCyclics.Definitions

/-!
Analytic/number-theoretic inputs for `theorems/thm_infinitely_many_sg_cyclics.tex`.

This formalization keeps the *logical/combinatorial* parts of the proof explicit
in Lean, while treating the deep quantitative estimates (Steps 1–4) as assumptions,
mirroring how other files in this repo handle prime-distribution/sieve inputs.

Notes on citations:
- The user request asks for "web_search"; this harness does not provide a
  dedicated `web_search` tool, so we use `curl` (network enabled) and record
  the queries in comments.
- Each axiom below is stated in a general "eventually for large `x`" form,
  matching the TeX proof's `\gg`/`o(·)` conclusions.
-/

noncomputable section

namespace Myproj

open Filter
open Asymptotics
open scoped Topology
open scoped BigOperators

/-! Basic growth fact for the main term `x / (log y(x))^2`. -/

/--
Since `log(sgY x) = √(log log x)`, the denominator grows slowly and
`x / (log(sgY x))^2 → +∞` as `x → +∞`.

This is a standard calculus fact; one reference is de Bruijn (1970),
*Asymptotic Methods in Analysis*, 3rd ed., Dover, 1970, §1.4 (logarithmic growth).
-/
theorem tendsto_x_div_log_sgY_sq_atTop :
    Tendsto (fun x : ℕ => (x : ℝ) / (Real.log (sgY x)) ^ 2) atTop atTop := by
  have hloglog_pos : ∀ᶠ x : ℕ in atTop, 0 < Real.log (Real.log (x : ℝ)) := by
    refine (eventually_atTop.2 ?_)
    refine ⟨3, ?_⟩
    intro x hx
    have hx0 : (0 : ℝ) < (x : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hx)
    have hxexp : Real.exp 1 < (x : ℝ) := by
      have h : Real.exp 1 < (3 : ℝ) := by
        exact (lt_trans Real.exp_one_lt_d9 (by norm_num))
      exact lt_of_lt_of_le h (by exact_mod_cast hx)
    have hxlog1 : 1 < Real.log (x : ℝ) := by
      have : ¬ Real.log (x : ℝ) ≤ 1 := by
        have : ¬ (x : ℝ) ≤ Real.exp 1 := not_le_of_gt hxexp
        exact (not_congr (Real.log_le_iff_le_exp hx0)).2 this
      exact lt_of_not_ge this
    exact Real.log_pos hxlog1

  have hEq :
      ∀ᶠ x : ℕ in atTop,
        (x : ℝ) / (Real.log (sgY x)) ^ 2 = (x : ℝ) / Real.log (Real.log (x : ℝ)) := by
    filter_upwards [hloglog_pos] with x hxpos
    have hnonneg : 0 ≤ Real.log (Real.log (x : ℝ)) := le_of_lt hxpos
    have hsq : (Real.log (sgY x)) ^ 2 = Real.log (Real.log (x : ℝ)) := by
      simpa [sgY] using (Real.sq_sqrt hnonneg)
    simp [hsq]

  have hloglog_real :
      (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (fun x : ℝ => x) := by
    have h1 : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] Real.log :=
      (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop)
    exact h1.trans Real.isLittleO_log_id_atTop
  have hloglog_nat :
      (fun x : ℕ => Real.log (Real.log (x : ℝ))) =o[atTop] (fun x : ℕ => (x : ℝ)) := by
    simpa using hloglog_real.natCast_atTop
  have hlim :
      Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ)) / (x : ℝ)) atTop (𝓝 0) :=
    hloglog_nat.tendsto_div_nhds_zero

  have ht :
      Tendsto (fun x : ℕ => (x : ℝ) / Real.log (Real.log (x : ℝ))) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    by_cases hb : b ≤ 0
    · have hnonneg :
          ∀ᶠ x : ℕ in atTop, 0 ≤ (x : ℝ) / Real.log (Real.log (x : ℝ)) := by
        filter_upwards [hloglog_pos] with x hxpos
        have hx0 : 0 ≤ (x : ℝ) := by exact_mod_cast (Nat.zero_le x)
        exact div_nonneg hx0 (le_of_lt hxpos)
      filter_upwards [hnonneg] with x hx
      exact le_trans hb hx
    · have hbpos : 0 < b := lt_of_not_ge hb
      let A : ℝ := max b 1
      have hApos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
      have hAne : A ≠ 0 := ne_of_gt hApos
      have hbA : b ≤ A := le_max_left b 1
      have hsmall : ∀ᶠ x : ℕ in atTop, Real.log (Real.log (x : ℝ)) / (x : ℝ) < 1 / A :=
        (tendsto_order.1 hlim).2 (1 / A) (by positivity)
      filter_upwards [hloglog_pos, hsmall, (eventually_atTop.2 ⟨3, fun x hx => hx⟩)] with x hxpos hxs hx3
      have hx0 : (0 : ℝ) < (x : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hx3)
      have hxmul : Real.log (Real.log (x : ℝ)) < (1 / A) * (x : ℝ) :=
        (div_lt_iff₀ hx0).1 hxs
      have hxle : Real.log (Real.log (x : ℝ)) ≤ (1 / A) * (x : ℝ) := le_of_lt hxmul
      have hAlogle : A * Real.log (Real.log (x : ℝ)) ≤ (x : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hxle (le_of_lt hApos)
        simpa [div_eq_mul_inv, mul_assoc, hAne] using h
      have hAdiv : A ≤ (x : ℝ) / Real.log (Real.log (x : ℝ)) := by
        -- `A ≤ x / loglog x` iff `A * loglog x ≤ x` since `0 < loglog x`.
        simpa [div_eq_mul_inv, mul_assoc] using (le_div_iff₀ hxpos).2 hAlogle
      exact le_trans hbA hAdiv

  have hEq' :
      (fun x : ℕ => (x : ℝ) / Real.log (Real.log (x : ℝ))) =ᶠ[atTop]
        (fun x : ℕ => (x : ℝ) / (Real.log (sgY x)) ^ 2) := by
    filter_upwards [hEq] with x hx
    simpa using hx.symm
  exact ht.congr' hEq'

/-! Steps 1–4: analytic inputs bundled as hypotheses (no global axioms). -/

/--
Analytic/number-theoretic inputs (Steps 1–4) for the SG-cyclic argument.

These are treated as *assumptions* to the main theorem, rather than global axioms.
-/
structure SGAnalyticInputs : Prop where
  step1_S0_lower_bound :
    ∃ (c₀ : ℝ) (X₀ : ℕ), 0 < c₀ ∧
      ∀ ⦃x : ℕ⦄, X₀ ≤ x →
        c₀ * (x : ℝ) / (Real.log (sgY x)) ^ 2 ≤ ((sgS0 x).card : ℝ)
  step2_S1_negligible :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop,
        ((sgS1 x).card : ℝ) ≤ ε * (x : ℝ) / (Real.log (sgY x)) ^ 2
  step3_Bn_negligible :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop,
        ((sgBn x).card : ℝ) ≤ ε * (x : ℝ) / (Real.log (sgY x)) ^ 2
  step4_B2n1_negligible :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop,
        ((sgB2n1 x).card : ℝ) ≤ ε * (x : ℝ) / (Real.log (sgY x)) ^ 2

/-!
### Optional: more “standard” analytic hypotheses

`SGAnalyticInputs` bundles the *derived* quantitative estimates that the Lean proof uses.
For documentation / modularity purposes, we also provide a companion structure phrased in
more classical analytic number theory terms (Mertens-type Euler products and Brun–Titchmarsh
style bounds).  This structure is **not** currently used to derive the step bounds in Lean;
it simply packages the standard estimates alongside a proof of `SGAnalyticInputs`.
-/

/-- Primes `p` with `2 ≤ p ≤ N`, as a finset. -/
def sgPrimesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter Nat.Prime

/-- Local “exclusion weight” for the SG roughness constraints: `w(2)=1`, `w(p)=2` for odd primes. -/
def sgWeight (p : ℕ) : ℝ :=
  if p = 2 then (1 : ℝ) else 2

/-- Weighted Euler factor `1 - w(p)/p` used in the Step 1 heuristic density. -/
def sgEulerFactor (p : ℕ) : ℝ :=
  1 - sgWeight p / (p : ℝ)

/-- Weighted Euler product `∏_{2 ≤ p ≤ N, p prime} (1 - w(p)/p)`. -/
def sgEulerProduct (N : ℕ) : ℝ :=
  (sgPrimesUpTo N).prod sgEulerFactor

/--
“Standard” analytic inputs for the SG-cyclic argument: Mertens + Brun–Titchmarsh style
estimates, together with the derived step bounds used by `Bounds.lean`.
-/
structure SGStandardAnalyticInputs : Prop extends SGAnalyticInputs where
  /--
  Mertens-type lower bound for the weighted Euler product.

  Informally: `∏_{p≤N} (1 - w(p)/p) ≍ 1/(log N)^2`, with `w(2)=1` and `w(p)=2` for odd primes.
  -/
  mertens_weighted_eulerProduct :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ 3 ≤ N₀ ∧
      ∀ ⦃N : ℕ⦄, N₀ ≤ N →
        c / (Real.log (N : ℝ)) ^ 2 ≤ sgEulerProduct N
  /--
  Brun–Titchmarsh + partial summation input in “harmonic sum” form.

  This is the standard ingredient used in Steps 3–4 to control primes `q ≡ 1 (mod p)`.
  -/
  brunTitchmarsh_harmonic_ap :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄, Nat.Prime p →
        ∀ ⦃X : ℕ⦄, 3 ≤ X →
          (((sgPrimesUpTo X).filter (fun q => q % p = 1)).sum fun q => (1 : ℝ) / (q : ℝ))
            ≤ C * Real.log (Real.log (X : ℝ)) / (p : ℝ)

end Myproj

end
