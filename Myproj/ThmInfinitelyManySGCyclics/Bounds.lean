import Mathlib.Tactic
import Mathlib.Order.Filter.AtTopBot.Basic
import Myproj.ThmInfinitelyManySGCyclics.Axioms
import Myproj.ThmInfinitelyManySGCyclics.Glue

/-!
Quantitative combination (Steps 1–4 ⇒ many good `n`).

The analytic estimates are bundled assumptions (`SGAnalyticInputs`); this file only combines them with finset
cardinality inequalities to obtain a clean lower bound on `#G(x)` and
deduce growth of the SG cyclic counting function.
-/

noncomputable section

namespace Myproj

open Filter
open scoped Classical

private def sgBad (x : ℕ) : Finset ℕ :=
  sgS1 x ∪ sgBn x ∪ sgB2n1 x

private lemma card_sgBad_le_sum (x : ℕ) :
    (sgBad x).card ≤ (sgS1 x).card + (sgBn x).card + (sgB2n1 x).card := by
  have h12 : (sgS1 x ∪ sgBn x).card ≤ (sgS1 x).card + (sgBn x).card :=
    Finset.card_union_le (sgS1 x) (sgBn x)
  have h123 : (sgBad x).card ≤ (sgS1 x ∪ sgBn x).card + (sgB2n1 x).card :=
    Finset.card_union_le (sgS1 x ∪ sgBn x) (sgB2n1 x)
  have h123' : (sgBad x).card ≤ (sgS1 x).card + (sgBn x).card + (sgB2n1 x).card := by
    refine le_trans h123 ?_
    -- expand the RHS using `h12`
    exact Nat.add_le_add_right (le_trans h12 le_rfl) _
  simpa [Nat.add_assoc] using h123'

lemma sgG_eventually_large (inputs : SGAnalyticInputs) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ᶠ x : ℕ in atTop,
        c * ((x : ℝ) / (Real.log (sgY x)) ^ 2) ≤ ((sgG x).card : ℝ) := by
  classical
  rcases inputs.step1_S0_lower_bound with ⟨c0, X0, hc0, hS0⟩
  have hS0' :
      ∀ᶠ x : ℕ in atTop,
        c0 * ((x : ℝ) / (Real.log (sgY x)) ^ 2) ≤ ((sgS0 x).card : ℝ) := by
    refine (eventually_atTop.2 ?_)
    refine ⟨X0, ?_⟩
    intro x hx
    simpa [mul_div_assoc] using hS0 hx
  let ε : ℝ := c0 / 8
  have hε : 0 < ε := by
    dsimp [ε]
    nlinarith [hc0]
  have hS1 := inputs.step2_S1_negligible ε hε
  have hBn := inputs.step3_Bn_negligible ε hε
  have hB2 := inputs.step4_B2n1_negligible ε hε
  refine ⟨c0 / 4, by nlinarith [hc0], ?_⟩
  filter_upwards [hS0', hS1, hBn, hB2] with x h0 h1 h2 h3
  have hsdiff :
      ((sgG x).card : ℝ)
        ≥ ((sgS0 x).card : ℝ) - ((sgBad x).card : ℝ) := by
    -- `S0 ⊆ G ∪ Bad`, hence `card(S0) ≤ card(G) + card(Bad)`.
    have hsubset : sgS0 x ⊆ (sgG x ∪ sgBad x) := by
      intro n hnS0
      by_cases hbad : n ∈ sgBad x
      · exact Finset.mem_union.2 (Or.inr hbad)
      · have : n ∈ sgG x := Finset.mem_sdiff.mpr ⟨hnS0, hbad⟩
        exact Finset.mem_union.2 (Or.inl this)
    have hcard1 : (sgS0 x).card ≤ (sgG x ∪ sgBad x).card :=
      Finset.card_le_card hsubset
    have hcard2 : (sgG x ∪ sgBad x).card ≤ (sgG x).card + (sgBad x).card :=
      Finset.card_union_le (sgG x) (sgBad x)
    have hcard : ((sgS0 x).card : ℝ) ≤ ((sgG x).card : ℝ) + ((sgBad x).card : ℝ) := by
      exact_mod_cast (le_trans hcard1 hcard2)
    linarith
  have hbad :
      ((sgBad x).card : ℝ) ≤ (3 * ε) * ((x : ℝ) / (Real.log (sgY x)) ^ 2) := by
    have hbadNat : (sgBad x).card ≤ (sgS1 x).card + (sgBn x).card + (sgB2n1 x).card :=
      card_sgBad_le_sum x
    have hbadR :
        ((sgBad x).card : ℝ)
          ≤ ((sgS1 x).card : ℝ) + ((sgBn x).card : ℝ) + ((sgB2n1 x).card : ℝ) := by
      exact_mod_cast hbadNat
    set t : ℝ := (x : ℝ) / (Real.log (sgY x)) ^ 2
    have h1t : ((sgS1 x).card : ℝ) ≤ ε * t := by
      simpa [t, mul_div_assoc] using h1
    have h2t : ((sgBn x).card : ℝ) ≤ ε * t := by
      simpa [t, mul_div_assoc] using h2
    have h3t : ((sgB2n1 x).card : ℝ) ≤ ε * t := by
      simpa [t, mul_div_assoc] using h3
    have hsum : ((sgS1 x).card : ℝ) + ((sgBn x).card : ℝ) + ((sgB2n1 x).card : ℝ)
        ≤ (ε * t) + (ε * t) + (ε * t) := by
      have h12 : ((sgS1 x).card : ℝ) + ((sgBn x).card : ℝ) ≤ (ε * t) + (ε * t) :=
        add_le_add h1t h2t
      have h123 :
          ((sgS1 x).card : ℝ) + ((sgBn x).card : ℝ) + ((sgB2n1 x).card : ℝ)
            ≤ ((ε * t) + (ε * t)) + (ε * t) :=
        add_le_add h12 h3t
      simpa [add_assoc] using h123
    have h3sum : (ε * t) + (ε * t) + (ε * t) = (3 * ε) * t := by ring
    have hsum' :
        ((sgS1 x).card : ℝ) + ((sgBn x).card : ℝ) + ((sgB2n1 x).card : ℝ) ≤ (3 * ε) * t := by
      simpa [h3sum] using hsum
    have : ((sgBad x).card : ℝ) ≤ (3 * ε) * t := le_trans hbadR hsum'
    simpa [t] using this
  have hG :
      ((sgG x).card : ℝ)
        ≥ c0 * ((x : ℝ) / (Real.log (sgY x)) ^ 2) - (3 * ε) * ((x : ℝ) / (Real.log (sgY x)) ^ 2) := by
    linarith [hsdiff, h0, hbad]
  -- `c0 - 3ε = (5/8)c0`, hence `c0/4` is safe.
  have : (c0 / 4) * ((x : ℝ) / (Real.log (sgY x)) ^ 2) ≤ ((sgG x).card : ℝ) := by
    have hcoef : (c0 / 4 : ℝ) ≤ (c0 - 3 * ε) := by
      dsimp [ε]
      nlinarith
    nlinarith [hG, hcoef]
  exact this

private lemma tendsto_mul_const_atTop {f : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : Tendsto f atTop atTop) :
    Tendsto (fun n => c * f n) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro a
  have hf' : ∀ᶠ n in atTop, a / c ≤ f n := (tendsto_atTop.1 hf) (a / c)
  have hc0 : 0 ≤ c := le_of_lt hc
  have hcne : c ≠ 0 := ne_of_gt hc
  filter_upwards [hf'] with n hn
  have hmul : c * (a / c) ≤ c * f n := mul_le_mul_of_nonneg_left hn hc0
  have hmul' : (c * a) / c ≤ c * f n := by
    simpa [mul_div_assoc] using hmul
  -- `(c * a) / c = a` since `c ≠ 0`.
  simpa [mul_div_cancel_left₀ a hcne] using hmul'

lemma sgCounting_tendsto_atTop (inputs : SGAnalyticInputs) :
    Tendsto (fun x : ℕ => (sgCounting x : ℝ)) atTop atTop := by
  rcases sgG_eventually_large inputs with ⟨c, hc, hG⟩
  have hf : Tendsto (fun x : ℕ => (x : ℝ) / (Real.log (sgY x)) ^ 2) atTop atTop :=
    tendsto_x_div_log_sgY_sq_atTop
  have hcf : Tendsto (fun x : ℕ => c * ((x : ℝ) / (Real.log (sgY x)) ^ 2)) atTop atTop :=
    tendsto_mul_const_atTop hc hf
  refine tendsto_atTop.2 ?_
  intro a
  have h1 : ∀ᶠ x : ℕ in atTop,
      a ≤ c * ((x : ℝ) / (Real.log (sgY x)) ^ 2) := (tendsto_atTop.1 hcf) a
  have h2 : ∀ᶠ x : ℕ in atTop,
      c * ((x : ℝ) / (Real.log (sgY x)) ^ 2) ≤ ((sgG x).card : ℝ) := by
        simpa [mul_div_assoc] using hG
  filter_upwards [h1, h2] with x hx1 hx2
  have hx3 : ((sgG x).card : ℝ) ≤ (sgCounting x : ℝ) := by
    exact_mod_cast sgCounting_ge_sgG x
  linarith

end Myproj

end
