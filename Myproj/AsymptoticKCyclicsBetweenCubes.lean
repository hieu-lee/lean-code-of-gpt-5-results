import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Basic
import Mathlib.Tactic.Linarith
import Myproj.Axioms
import Myproj.Definitions

-- Silence minor style hints to keep focus on core math
set_option linter.unnecessarySimpa false

noncomputable section

namespace Myproj

open Filter
open scoped BigOperators

/-- Regular variation with index `ρ`.
The function eventually looks like `N^ρ * L(N)` with `L` slowly varying. -/
def RegularlyVarying (f : ℕ → ℝ) (ρ : ℝ) : Prop :=
  ∃ L : ℕ → ℝ, SlowlyVarying L ∧ EventuallyPositive L ∧
      (∀ᶠ N in atTop, f N = Real.rpow (N : ℝ) ρ * L N)

/-- Asymptotic equivalence `A ~ f`.
The ratio tends to `1` and the denominator is eventually positive. -/
def AsymptoticallyEquivalent (A f : ℕ → ℝ) : Prop :=
  Tendsto (fun N : ℕ => A N / f N) atTop (nhds (1 : ℝ)) ∧
    (∀ᶠ N in atTop, 0 < f N)

lemma ratio_bound {A f : ℕ → ℝ} {N : ℕ}
    (habs : |A N / f N - 1| < (1 : ℝ) / 2) (hf : 0 < f N) : f N ≤ 2 * A N := by
  have hx := abs_lt.mp habs
  have hx_gt : (1 : ℝ) / 2 < A N / f N := by
    linarith [hx.1]
  have hfnz : f N ≠ 0 := ne_of_gt hf
  have hmul : (1 : ℝ) / 2 * f N < A N := by
    have := mul_lt_mul_of_pos_right hx_gt hf
    simpa [div_eq_mul_inv, hfnz, mul_comm, mul_left_comm, mul_assoc] using this
  have hf_lt : f N < 2 * A N := by
    have := mul_lt_mul_of_pos_left hmul (by norm_num : (0 : ℝ) < 2)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  exact le_of_lt hf_lt

lemma eventually_le_of_asymptotic (A f : ℕ → ℝ)
    (h : AsymptoticallyEquivalent A f) : ∀ᶠ N in atTop, f N ≤ 2 * A N := by
  classical
  rcases h with ⟨hratio, hfpos⟩
  have hlimit : Tendsto (fun N : ℕ => ‖A N / f N - (1 : ℝ)‖) atTop (nhds (0 : ℝ)) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hratio)
  have happrox : ∀ᶠ N in atTop, ‖A N / f N - 1‖ < (1 : ℝ) / 2 := by
    have hhalf : 0 < (1 : ℝ) / 2 := by norm_num
    have hnhds : Metric.ball (0 : ℝ) ((1 : ℝ) / 2) ∈ nhds (0 : ℝ) :=
      Metric.ball_mem_nhds (0 : ℝ) hhalf
    have := hlimit.eventually hnhds
    simpa [Metric.ball, Real.dist_eq, Real.norm_eq_abs] using this
  filter_upwards [happrox, hfpos] with N hbound hfp
  exact ratio_bound (by simpa [Real.norm_eq_abs] using hbound) hfp

lemma eventually_cyclicCount_le (h : ℕ) :
    ∀ᶠ N in atTop, (cyclicCount h N : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
  have hN : ∀ᶠ N in atTop, 4 ≤ N := eventually_ge_atTop 4
  refine hN.mono ?_
  intro N hNge
  have hcard := cubeInterval_card_le_four_mul_sq (N := N) hNge
  have hcount : (cyclicCount h N : ℝ) ≤ (cubeInterval N).card := by
    exact_mod_cast cyclicCount_le_card h N
  exact (le_trans hcount hcard)

lemma eventually_pos_cast : ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) :=
  (eventually_ge_atTop 1).mono (fun N hN => by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have : 0 < (N : ℝ) := lt_of_lt_of_le (by norm_num) h1
    simpa using this)

/--
Main theorem: for any admissible offset `h ∈ {2,4,6}`, no regularly varying function with
index `ρ ∈ (2,5/2]` can be asymptotic to `A_h`.
-/
theorem asymptotic_k_fold_cyclics_between_cubes
    {h : ℕ}
    -- `_hh` is unused but kept to mirror the admissible `h ∈ {2,4,6}` in the .tex statement.
    (_hh : h = 2 ∨ h = 4 ∨ h = 6) :
    ¬ ∃ ρ : ℝ, 2 < ρ ∧ ρ ≤ (5 : ℝ) / 2 ∧
        ∃ f : ℕ → ℝ, RegularlyVarying f ρ ∧
          AsymptoticallyEquivalent (fun N => (cyclicCount h N : ℝ)) f := by
  classical
  intro hcontr
  rcases hcontr with ⟨ρ, hρ_lt, hρ_le, f, hRV, hAsym⟩
  obtain ⟨L, hslow, hLpos, hfeq⟩ := hRV
  set A : ℕ → ℝ := fun N => (cyclicCount h N : ℝ)
  have hA_le : ∀ᶠ N in atTop, A N ≤ 4 * (N : ℝ) ^ 2 := eventually_cyclicCount_le h
  have hf_le : ∀ᶠ N in atTop, f N ≤ 2 * A N := eventually_le_of_asymptotic A f hAsym
  have hfeq_ev : ∀ᶠ N in atTop, f N = Real.rpow (N : ℝ) ρ * L N := hfeq
  have hNat_pos : ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) := eventually_pos_cast
  set ε : ℝ := (ρ - 2) / 2 with hε
  have hε_pos : 0 < ε := by
    have htemp : 0 < ρ - 2 := sub_pos.mpr hρ_lt
    simpa [ε, hε] using half_pos htemp
  have hρ_decomp : ρ = 2 + 2 * ε := by
    have : ρ - 2 = 2 * ε := by simpa [ε, hε] using (by ring : (ρ - 2) = 2 * ((ρ - 2) / 2))
    calc
      ρ = ρ - 2 + 2 := by ring
      _ = 2 * ε + 2 := by simpa [this]
      _ = 2 + 2 * ε := by ring
  have hbound : ∀ᶠ (N : ℕ) in atTop,
      Real.rpow (N : ℝ) ρ * L N ≤ 8 * (N : ℝ) ^ 2 := by
    filter_upwards [hfeq_ev, hf_le, hA_le] with N hfeqN hf_leN hAleN
    have hmul : 2 * A N ≤ 2 * (4 * (N : ℝ) ^ 2) :=
      (mul_le_mul_of_nonneg_left hAleN (by norm_num : (0 : ℝ) ≤ 2))
    have hmul_id : 2 * (4 * (N : ℝ) ^ 2) = 8 * (N : ℝ) ^ 2 := by ring
    have hmul' : 2 * A N ≤ 8 * (N : ℝ) ^ 2 := by
      simpa [hmul_id] using hmul
    have hf_bound : f N ≤ 8 * (N : ℝ) ^ 2 := hf_leN.trans hmul'
    -- Prefer `simp` over `simpa` to satisfy the linter.
    have hf' := hf_bound
    -- Rewrite `f N` using the eventual equality from regular variation.
    rw [hfeqN] at hf'
    exact hf'
  have hineq : ∀ᶠ (N : ℕ) in atTop,
      Real.rpow (N : ℝ) (ρ - 2) * L N ≤ 8 := by
    filter_upwards [hbound, hNat_pos] with N hboundN hNpos
    have hxpow' : (N : ℝ) ^ 2 = Real.rpow (N : ℝ) 2 := by
      simpa using (Real.rpow_natCast (N : ℝ) 2).symm
    have hbound' : Real.rpow (N : ℝ) ρ * L N ≤ 8 * Real.rpow (N : ℝ) 2 := by
      -- Rewrite only the right-hand side once to avoid simp loops.
      have hb := hboundN
      -- `(N : ℝ) ^ 2 = (N : ℝ).rpow 2` by `hxpow'`.
      rw [hxpow'] at hb
      exact hb
    -- Use the algebraic helper to peel off the power `2`.
    exact rpow_bound_sub_of_mul_bound hNpos hbound'
  have hineq_eps : ∀ᶠ (N : ℕ) in atTop,
      Real.rpow (N : ℝ) ε * L N ≤ 8 * Real.rpow (N : ℝ) (-ε) := by
    have hρ_sub : ρ - 2 = 2 * ε := by
      have := hρ_decomp; linarith
    filter_upwards [hineq, hNat_pos] with N hineqN hNpos
    have hxineq : Real.rpow (N : ℝ) (2 * ε) * L N ≤ 8 := by
      -- Rewrite the exponent using `ρ - 2 = 2ε`.
      have hx := hineqN
      -- `hx` is `N^(ρ-2) * L N ≤ 8`.
      -- Replace `ρ - 2` with `2 * ε`.
      simpa [hρ_sub] using hx
    exact rpow_scale_bound_of_mul_bound hNpos hxineq
  have hlarge : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.rpow (N : ℝ) ε * L N :=
    (tendsto_atTop.1 (slowly_varying_pow_mul_tendsto_atTop hslow hLpos hε_pos)) 1
  -- Using that `x ↦ x^{-ε}` tends to `0` as `x → ∞`.
  have hneg : Tendsto (fun N : ℕ => Real.rpow (N : ℝ) (-ε)) atTop (nhds (0 : ℝ)) :=
    (tendsto_rpow_neg_atTop hε_pos).comp tendsto_natCast_atTop_atTop
  -- From this, deduce that eventually `8 * N^{-ε} < 1` without using metric balls.
  have hsmall : ∀ᶠ N : ℕ in atTop, 8 * Real.rpow (N : ℝ) (-ε) < 1 := by
    -- Since the limit is `0`, there exists an index after which `rpow (N) (-ε) < 1/8`.
    have hbase : ∀ᶠ N : ℕ in atTop, ‖Real.rpow (N : ℝ) (-ε) - 0‖ < (1 : ℝ) / 8 := by
      have hnhds : Metric.ball (0 : ℝ) ((1 : ℝ) / 8) ∈ nhds (0 : ℝ) :=
        Metric.ball_mem_nhds (0 : ℝ) (by norm_num)
      -- Use the limit `hneg : Tendsto (fun N => rpow ...) → 0` directly.
      have := hneg.eventually hnhds
      -- Convert the metric ball statement to a norm inequality.
      simpa [Metric.ball, Real.dist_eq, Real.norm_eq_abs, abs_abs] using this
    -- Convert the norm inequality to a simple bound and multiply by `8`.
    refine hbase.mono ?_
    intro N hN
    have hlt : Real.rpow (N : ℝ) (-ε) < (1 : ℝ) / 8 := by
      have := (abs_lt.mp (by simpa [Real.dist_eq, Real.norm_eq_abs] using hN)).2
      simpa using this
    have hpos8 : 0 < (8 : ℝ) := by norm_num
    have := mul_lt_mul_of_pos_left hlt hpos8
    simpa using this
  -- Extract a contradictory index using the three eventual properties.
  rcases (eventually_atTop.1 hlarge) with ⟨N₁, hN₁⟩
  rcases (eventually_atTop.1 hineq_eps) with ⟨N₂, hN₂⟩
  rcases (eventually_atTop.1 hsmall) with ⟨N₃, hN₃⟩
  let N0 : ℕ := Nat.max N₁ (Nat.max N₂ N₃)
  have hN1le : N₁ ≤ N0 := le_trans (Nat.le_max_left _ _) (le_of_eq rfl)
  have hN2le : N₂ ≤ N0 := by
    have : Nat.max N₂ N₃ ≤ N0 := Nat.le_max_right _ _
    exact le_trans (Nat.le_max_left _ _) this
  have hN3le : N₃ ≤ N0 := by
    have : Nat.max N₂ N₃ ≤ N0 := Nat.le_max_right _ _
    exact le_trans (Nat.le_max_right _ _) this
  have h1 : 1 ≤ Real.rpow (N0 : ℝ) ε * L N0 := hN₁ (b := N0) hN1le
  have h2 : Real.rpow (N0 : ℝ) ε * L N0 ≤ 8 * Real.rpow (N0 : ℝ) (-ε) := hN₂ (b := N0) hN2le
  have h3 : 8 * Real.rpow (N0 : ℝ) (-ε) < 1 := hN₃ (b := N0) hN3le
  have : 1 ≤ 8 * Real.rpow (N0 : ℝ) (-ε) := le_trans h1 h2
  exact (not_lt_of_ge this h3).elim

end Myproj
