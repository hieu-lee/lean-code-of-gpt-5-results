import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Order.Field
import Myproj.Definitions
import Myproj.CyclicNumbers.Axioms
import Myproj.ThmFiroozbakhtCyclics3.Axioms

/-
Core definitions and analytic axioms used to formalise the Vrba analog.
We expose the geometric mean of cyclic numbers, encode the Pollack/de Bruijn
asymptotic inputs, and prove that `log(cₙ / Gₙ) → 1`.
-/

noncomputable section

namespace Myproj

open scoped Topology
open Filter Real

/-- Sum of logarithms of the first `n` cyclic numbers (1-indexed). -/
def cyclicLogSum (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n)
    (fun k => Real.log (Myproj.cyclicEnumerator (Nat.succ k)))

/-- Geometric mean of the first `n` cyclic numbers. -/
def cyclicGeomMean (n : ℕ) : ℝ :=
  if h : n = 0 then 1
  else Real.exp ((1 / (n : ℝ)) * cyclicLogSum n)

/-- Ratio `cₙ / Gₙ` (indexed so that `cyclicRatio n = c_{n+1} / G_{n+1}`). -/
def cyclicRatio (n : ℕ) : ℝ :=
  Myproj.cyclicEnumerator n.succ / cyclicGeomMean n.succ

/-- Abel integral `∫ C(t)/t dt` treated as an opaque function. -/
axiom cyclicLogIntegral : ℝ → ℝ

/-- Compatibility between the enumerator and the real counting function. -/
axiom cyclicCountingReal_enumerator_eq {n : ℕ} (hn : 1 ≤ n) :
  Myproj.cyclicCountingReal (Myproj.cyclicEnumerator n) = (n : ℝ)

/--
Integral comparison (de Bruijn): `cyclicLogIntegral x / C(x) → 1` as `x → ∞`.
Search command recorded this run:
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=de+Bruijn+cyclic+numbers+integral"`
-/
axiom cyclic_integral_over_counting_ratio_tendsto :
  Tendsto (fun x : ℝ =>
      Myproj.cyclicLogIntegral x / Myproj.cyclicCountingReal x) atTop (𝓝 1)

/--
Refined Abel summation: up to a uniformly bounded error `E(n)`, the logarithm
of the ratio `cₙ/Gₙ` equals `cyclicLogIntegral(cₙ) / n`.
The error term comes with a uniform `O(1/n)` bound.

Search commands used while sourcing this fact:
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Abel+summation+cyclic+numbers+Pollack"`
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+partial+summation"`
-/
structure VrbaRatioData where
  E : ℕ → ℝ
  K : ℝ
  N₀ : ℕ
  K_nonneg : 0 ≤ K
  bounds :
    ∀ ⦃m : ℕ⦄, N₀ ≤ m →
      Real.log (cyclicRatio m)
        = Myproj.cyclicLogIntegral (Myproj.cyclicEnumerator m.succ)
            / (m.succ : ℝ)
          - E m / (m.succ : ℝ)
      ∧ ‖E m‖ ≤ K
  error_tendsto_zero :
    Tendsto (fun m : ℕ => E m / (m.succ : ℝ)) atTop (𝓝 0)

axiom cyclic_ratio_log_decomposition : VrbaRatioData

/-! ### Elementary positivity and growth properties -/

private def ratioData : VrbaRatioData := cyclic_ratio_log_decomposition

local notation "E" => ratioData.E
local notation "K" => ratioData.K
local notation "N₀" => ratioData.N₀
local notation "Bounds" => ratioData.bounds

/-- Positivity of `cyclicGeomMean n`. -/
lemma cyclicGeomMean_pos {n : ℕ} : 0 < cyclicGeomMean n := by
  by_cases hn : n = 0
  · simpa [cyclicGeomMean, hn]
  · have : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have : 0 < Real.exp ((1 / (n : ℝ)) * cyclicLogSum n) := Real.exp_pos _
    simpa [cyclicGeomMean, hn] using this

/-- Positivity of the ratio `cₙ / Gₙ`. -/
lemma cyclic_ratio_pos (n : ℕ) : 0 < cyclicRatio n := by
  have hnum : 0 < Myproj.cyclicEnumerator n.succ := by
    have hge : (n.succ : ℝ) ≤ Myproj.cyclicEnumerator n.succ :=
      cyclicEnumerator_ge_self n.succ
    have hpos : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact lt_of_lt_of_le hpos hge
  have hden : 0 < cyclicGeomMean n.succ := cyclicGeomMean_pos
  exact div_pos hnum hden

/-- The sequence `c_n` diverges to infinity. -/
lemma cyclicEnumerator_tendsto_atTop :
    Tendsto Myproj.cyclicEnumerator atTop atTop := by
  classical
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  refine (eventually_ge_atTop N).mono ?_
  intro n hn
  have hnb : b ≤ (N : ℝ) := by simpa using hN
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnc : (n : ℝ) ≤ Myproj.cyclicEnumerator n := cyclicEnumerator_ge_self n
  exact le_trans hnb (le_trans hNn hnc)

/-- `c_{n+1}` also diverges to infinity. -/
lemma cyclicEnumerator_succ_tendsto :
    Tendsto (fun n : ℕ => Myproj.cyclicEnumerator n.succ) atTop atTop :=
  (cyclicEnumerator_tendsto_atTop).comp
      (by
        refine tendsto_atTop.2 ?_
        intro N
        refine (eventually_ge_atTop N).mono ?_
        intro n hn
        exact le_trans hn (Nat.le_succ n))

/-- Limit of the integral term along the enumerator. -/
lemma cyclicLogIntegral_over_nat_tendsto :
    Tendsto (fun n : ℕ =>
        Myproj.cyclicLogIntegral (Myproj.cyclicEnumerator n.succ)
          / (n.succ : ℝ)) atTop (𝓝 1) := by
  classical
  have h :=
    cyclic_integral_over_counting_ratio_tendsto.comp
      cyclicEnumerator_succ_tendsto
  refine h.congr' ?_
  filter_upwards [Filter.univ_mem] with n _
  have hn : 1 ≤ n.succ := Nat.succ_le_succ (Nat.zero_le _)
  simpa [cyclicCountingReal_enumerator_eq hn]

/-- Error term `E(n)/(n+1)` tends to zero. -/
lemma cyclic_ratio_error_tendsto_zero :
    Tendsto (fun n : ℕ => E n / (n.succ : ℝ)) atTop (𝓝 0) := by
  classical
  have h_inv :
      Tendsto (fun n : ℕ => (n.succ : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp
      (by
        refine tendsto_atTop.2 ?_
        intro N
        refine (eventually_ge_atTop N).mono ?_
        intro n hn
        exact le_trans hn (Nat.le_succ n))
  have h_pos_limit :
      Tendsto (fun n : ℕ => K / (n.succ : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ((continuous_mul_left K).tendsto (0 : ℝ)).comp h_inv
  have h_neg_limit :
      Tendsto (fun n : ℕ => -(K / (n.succ : ℝ))) atTop (𝓝 0) := by
    simpa using h_pos_limit.neg
  have h_abs_bound :
      ∀ᶠ n in atTop, |E n| ≤ K :=
    (eventually_ge_atTop N₀).mono fun n hn => by
      have := Bounds hn
      simpa [Real.norm_eq_abs] using this.2
  have h_upper_event :
      ∀ᶠ n in atTop, E n / (n.succ : ℝ) ≤ K / (n.succ : ℝ) :=
    h_abs_bound.mono fun n habs => by
      have hle : E n ≤ K := (abs_le.mp habs).2
      have hspin : 0 ≤ (n.succ : ℝ)⁻¹ := by
        have hpos : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
        exact inv_nonneg.mpr (le_of_lt hpos)
      have := mul_le_mul_of_nonneg_right hle hspin
      simpa [div_eq_mul_inv] using this
  have h_lower_event :
      ∀ᶠ n in atTop, -(K / (n.succ : ℝ)) ≤ E n / (n.succ : ℝ) :=
    h_abs_bound.mono fun n habs => by
      have hle : -K ≤ E n := (abs_le.mp habs).1
      have hspin : 0 ≤ (n.succ : ℝ)⁻¹ := by
        have hpos : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
        exact inv_nonneg.mpr (le_of_lt hpos)
      have := mul_le_mul_of_nonneg_right hle hspin
      simpa [div_eq_mul_inv] using this
  refine Filter.Tendsto.squeeze' h_neg_limit h_pos_limit h_lower_event h_upper_event

/-- Convergence of logarithms of the ratio. -/
theorem cyclic_ratio_log_tendsto :
    Tendsto (fun n : ℕ => Real.log (cyclicRatio n)) atTop (𝓝 1) := by
  classical
  have hInt := cyclicLogIntegral_over_nat_tendsto
  have hErr := cyclic_ratio_error_tendsto_zero
  have hDiff :
      Tendsto (fun n : ℕ =>
        Myproj.cyclicLogIntegral (Myproj.cyclicEnumerator n.succ)
          / (n.succ : ℝ)
        - E n / (n.succ : ℝ)) atTop (𝓝 1) := by
    simpa using hInt.sub hErr
  refine hDiff.congr' ?_
  filter_upwards [(eventually_ge_atTop N₀)] with n hn
  obtain ⟨hEq, -⟩ := Bounds hn
  simpa using hEq.symm

end Myproj

end
