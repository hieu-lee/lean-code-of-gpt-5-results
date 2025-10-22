import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Topology.Basic
import Myproj.Definitions
import Myproj.CyclicNumbers.Axioms
import Myproj.ThmSquares.Axioms

/-
Auxiliary lemmas supporting the square-gap asymptotic for cyclic numbers.
-/

noncomputable section

namespace Myproj

open scoped Topology
open Filter Asymptotics

/-- Pollack's second-order correction term `1/L₃ n - γ / L₃(n)^2`. -/
def pollackCorrection (n : ℕ) : ℝ :=
  1 / Myproj.L3 n - Myproj.eulerMascheroni / (Myproj.L3 n) ^ 2

lemma pollackCorrection_apply (n : ℕ) :
    pollackCorrection n =
      1 / Myproj.L3 n - Myproj.eulerMascheroni / (Myproj.L3 n) ^ 2 := rfl

lemma cyclicCountingAux_square_eq {n : ℕ} (hn : 0 < n) :
    Myproj.cyclicCountingAux (n ^ 2)
        * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2
      = Real.exp (-Myproj.eulerMascheroni)
          * ((2 * n + 1 : ℕ) : ℝ)
          * pollackCorrection (n ^ 2) := by
  have hcast : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hpow : (n : ℝ) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ hcast
  have hnat : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
    simp [Nat.cast_pow, pow_two]
  simp [Myproj.cyclicCountingAux_apply, pollackCorrection,
    hnat, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hpow]

lemma eventually_pos_pollackCorrection :
    ∀ᶠ n : ℕ in atTop, 0 < pollackCorrection n := by
  rcases pollackCorrection_eventually_pos with ⟨N₀, hN₀⟩
  exact (eventually_ge_atTop N₀).mono (by
    intro n hn
    simpa [pollackCorrection_apply] using hN₀ hn)

lemma eventually_pos_pollackCorrection_square :
    ∀ᶠ n : ℕ in atTop, 0 < pollackCorrection (n ^ 2) := by
  rcases pollackCorrection_eventually_pos with ⟨N₀, hN₀⟩
  exact (eventually_ge_atTop N₀).mono (by
    intro n hn
    have hpow : N₀ ≤ n ^ 2 := le_trans hn (by simpa [pow_two] using Nat.le_mul_self n)
    simpa [pollackCorrection_apply] using hN₀ hpow)

lemma eventually_pos_aux_square :
    ∀ᶠ n : ℕ in atTop,
      0 <
        Myproj.cyclicCountingAux (n ^ 2) * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2 := by
  have hPollack := eventually_pos_pollackCorrection_square
  have hNat : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop (0 : ℕ)
  refine (hPollack.and hNat).mono ?_
  intro n h
  rcases h with ⟨hPollackPos, hnPos⟩
  have hn : 0 < n := hnPos
  have hExp : 0 < Real.exp (-Myproj.eulerMascheroni) := Real.exp_pos _
  have hNatReal : 0 < ((2 * n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (2 * n)
  have hPos :
      0 < Real.exp (-Myproj.eulerMascheroni)
            * ((2 * n + 1 : ℕ) : ℝ) * pollackCorrection (n ^ 2) :=
    mul_pos (mul_pos hExp hNatReal) hPollackPos
  have hEq := cyclicCountingAux_square_eq hn
  have : 0 <
      Myproj.cyclicCountingAux (n ^ 2) * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2 := by
    rw [hEq]
    simpa using hPos
  exact this

lemma eventually_pos_target :
    ∀ᶠ n : ℕ in atTop,
      0 < Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) * (n : ℝ) * pollackCorrection n := by
  have hPollack := eventually_pos_pollackCorrection
  have hNat : ∀ᶠ n : ℕ in atTop, 0 < (n : ℕ) := eventually_gt_atTop (0 : ℕ)
  refine (hPollack.and hNat).mono ?_
  intro n h
  rcases h with ⟨hPollackPos, hnPos⟩
  have hn : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hExp : 0 < Real.exp (-Myproj.eulerMascheroni) := Real.exp_pos _
  have hTwo : 0 < (2 : ℝ) := by norm_num
  have hTotal :
      0 < Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) * (n : ℝ) * pollackCorrection n :=
    by
      have hFirst : 0 < Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) := mul_pos hExp hTwo
      have hSecond : 0 < (n : ℝ) * pollackCorrection n := mul_pos hn hPollackPos
      simpa [mul_assoc, mul_comm, mul_left_comm] using mul_pos hFirst hSecond
  simpa using hTotal

lemma aux_ratio_rewrite :
    (fun n : ℕ =>
      (Myproj.cyclicCountingAux (n ^ 2) * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2)
        /
        (Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) * (n : ℝ) * pollackCorrection n))
      =ᶠ[atTop]
    (fun n : ℕ =>
      (((2 * n + 1 : ℕ) : ℝ) / (2 * (n : ℝ)))
        *
        (pollackCorrection (n ^ 2) / pollackCorrection n)) := by
  refine (eventually_gt_atTop (0 : ℕ)).mono ?_
  intro n hnpos
  have hn : 0 < n := Nat.succ_le_iff.mp hnpos
  have hEq := cyclicCountingAux_square_eq hn
  have hSimplifyNumerator :
      (Myproj.cyclicCountingAux (n ^ 2) * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2)
        /
        (Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) * (n : ℝ) * pollackCorrection n)
        =
      (Real.exp (-Myproj.eulerMascheroni) * ((2 * n + 1 : ℕ) : ℝ) * pollackCorrection (n ^ 2))
        /
        (Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) * (n : ℝ) * pollackCorrection n) := by
    rw [hEq]
  have hSimplifyRatio :
      (Real.exp (-Myproj.eulerMascheroni) * ((2 * n + 1 : ℕ) : ℝ) * pollackCorrection (n ^ 2))
        /
        (Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) * (n : ℝ) * pollackCorrection n)
        =
      (((2 * n + 1 : ℕ) : ℝ) / (2 * (n : ℝ))) *
        (pollackCorrection (n ^ 2) / pollackCorrection n) := by
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  exact hSimplifyNumerator.trans hSimplifyRatio

lemma aux_ratio_to_target :
    Tendsto (fun n : ℕ =>
      (Myproj.cyclicCountingAux (n ^ 2) * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2)
        /
      (Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) * (n : ℝ) * pollackCorrection n))
      atTop (𝓝 1) := by
  have h_prod :
      Tendsto (fun n : ℕ =>
        (((2 * n + 1 : ℕ) : ℝ) / (2 * (n : ℝ)))
          *
        (pollackCorrection (n ^ 2) / pollackCorrection n)) atTop (𝓝 1) := by
    have h₁ : Tendsto (fun n : ℕ =>
        ((2 * n + 1 : ℕ) : ℝ) / (2 * (n : ℝ))) atTop (𝓝 1) :=
      ratio_two_n_plus_one
    have h₂ :
        Tendsto (fun n : ℕ =>
          pollackCorrection (n ^ 2) / pollackCorrection n) atTop (𝓝 1) := by
      simpa [pollackCorrection_apply] using iterated_log_square_second_order
    simpa [one_mul] using h₁.mul h₂
  have hEq :
      (fun n : ℕ =>
        (Myproj.cyclicCountingAux (n ^ 2) * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2)
          /
          (Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) * (n : ℝ) * pollackCorrection n))
        =ᶠ[atTop]
      (fun n : ℕ =>
        (((2 * n + 1 : ℕ) : ℝ) / (2 * (n : ℝ)))
          *
          (pollackCorrection (n ^ 2) / pollackCorrection n)) := aux_ratio_rewrite
  exact Filter.Tendsto.congr' hEq.symm h_prod

end Myproj

end
