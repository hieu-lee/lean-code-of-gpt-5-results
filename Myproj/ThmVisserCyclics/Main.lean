import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Myproj.Definitions
import Myproj.CyclicNumbers.Axioms
import Myproj.ThmFiroozbakhtCyclics3.Axioms
import Myproj.ThmVrba.Axioms
import Myproj.ThmVisserCyclics.Axioms

/-
Formal verification of Theorem \ref{thm:visser_cyclics}, following the
LaTeX argument with the short-interval estimate supplied by the axioms.
-/

noncomputable section

namespace Myproj
namespace Visser

open scoped Real Topology
open Filter

lemma sqrt_add_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Real.sqrt (a + b) - Real.sqrt a
      = b / (Real.sqrt (a + b) + Real.sqrt a) := by
  have hpos_ab : 0 < a + b := add_pos_of_nonneg_of_pos ha hb
  have hpos :
      0 < Real.sqrt (a + b) + Real.sqrt a :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hpos_ab) (Real.sqrt_nonneg _)
  have hsq₁ : (Real.sqrt (a + b)) ^ 2 = a + b := by
    simpa using Real.sq_sqrt (add_nonneg ha hb.le)
  have hsq₂ : (Real.sqrt a) ^ 2 = a := by
    simpa using Real.sq_sqrt ha
  have hmul :
      (Real.sqrt (a + b) - Real.sqrt a)
          * (Real.sqrt (a + b) + Real.sqrt a)
        = b := by
    have hdiff :
        (Real.sqrt (a + b) - Real.sqrt a)
            * (Real.sqrt (a + b) + Real.sqrt a)
          = (Real.sqrt (a + b)) ^ 2 - (Real.sqrt a) ^ 2 := by
      ring
    simpa [hdiff, hsq₁, hsq₂] using
      show (a + b) - a = b by ring
  exact (eq_div_iff_mul_eq (ne_of_gt hpos)).2 hmul

lemma eventually_abs_le_of_tendsto_zero {f : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hf : Tendsto f atTop (𝓝 0)) :
    ∃ Y : ℝ, ∀ x : ℝ, Y ≤ x → |f x| ≤ δ := by
  obtain ⟨Y, hY⟩ := (Metric.tendsto_atTop.1 hf) δ hδ
  have hY' : ∀ x : ℝ, Y ≤ x → |f x| ≤ δ := by
    intro x hx
    have hlt : dist (f x) 0 < δ := hY x hx
    exact (le_of_lt (by simpa [Real.dist_eq, sub_eq_add_neg, add_comm] using hlt))
  refine ⟨Y, ?_⟩
  intro x hx
  simpa [Real.dist_eq, sub_eq_add_neg, add_comm] using hY' x hx

theorem visser_gap_bound {ε : ℝ} (hε_pos : 0 < ε) (hε_small : ε < 1 / 2) :
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
      Real.sqrt (Myproj.cyclicEnumerator (n + 1))
        - Real.sqrt (Myproj.cyclicEnumerator n) < ε := by
  classical
  obtain ⟨R, X, hX_gt, hR_tendsto, hInterval⟩ := cyclic_short_interval_bound
  obtain ⟨Ngap, hgap_control⟩ := Myproj.cyclicEnumerator_gap_bound
  -- Error tolerance from the short-interval asymptotic.
  set δ : ℝ := Real.exp (-Myproj.eulerMascheroni) / 2
  have hδ_pos : 0 < δ := by
    have hexp_pos : (0 : ℝ) < Real.exp (-Myproj.eulerMascheroni) := Real.exp_pos _
    have := div_pos hexp_pos (by norm_num : (0 : ℝ) < 2)
    simpa [δ] using this
  obtain ⟨Y, hY⟩ := eventually_abs_le_of_tendsto_zero hδ_pos hR_tendsto
  -- Aggregate thresholds coming from the asymptotic and the error control.
  let X' : ℝ := max X Y
  have hX'_gt : 1 < X' := lt_of_lt_of_le hX_gt (le_max_left _ _)
  let N₀ : ℕ := max ⌈X'⌉₊ Ngap
  let N : ℕ := max N₀ 1
  have hN_pos : 1 ≤ N := le_max_right _ _
  refine ⟨N, ?_⟩
  intro n hnN
  -- Shorthand for the enumerator and the evaluation point.
  set c : ℕ → ℝ := Myproj.cyclicEnumerator
  have hc_ge_self : ∀ k : ℕ, (k : ℝ) ≤ c k := Myproj.cyclicEnumerator_ge_self
  let x : ℝ := c n
  have hx_nat_le : (n : ℝ) ≤ x := hc_ge_self n
  have hN_le : N ≤ n := hnN
  have hN0_le_n : N₀ ≤ n := (le_max_left _ _).trans hN_le
  have hceil_le : ⌈X'⌉₊ ≤ n :=
    (le_max_left ⌈X'⌉₊ Ngap).trans hN0_le_n
  have hNgap_le : Ngap ≤ n :=
    (le_max_right ⌈X'⌉₊ Ngap).trans hN0_le_n
  have hceil_cast : (⌈X'⌉₊ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hceil_le
  have hX'_le_nat : X' ≤ (n : ℝ) :=
    (Nat.le_ceil X').trans hceil_cast
  have hX'_le_x : X' ≤ x := hX'_le_nat.trans hx_nat_le
  have hX_le_x : X ≤ x := (le_max_left X Y).trans hX'_le_x
  have hY_le_x : Y ≤ x := (le_max_right X Y).trans hX'_le_x
  have hx_gt_one : 1 < x := lt_of_lt_of_le hX_gt hX_le_x
  have hx_pos : 0 < x := lt_trans zero_lt_one hx_gt_one
  have hx_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
  have hx_log_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hx_log_sqrt_pos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hx_log_pos
  have hε_lt_one : ε < 1 :=
    lt_of_lt_of_le hε_small (by norm_num : (1 / 2 : ℝ) ≤ 1)
  -- Short-interval lower bound at the point `x`.
  have hInterval_eval :
      (Real.exp (-Myproj.eulerMascheroni) + R x)
        * ((ε * Real.sqrt x) / Real.sqrt (Real.log x))
        ≤ Myproj.cyclicCountingReal (x + ε * Real.sqrt x)
            - Myproj.cyclicCountingReal x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hInterval (x := x) (ε := ε) hX_le_x hε_pos hε_lt_one
  -- Control the coefficient arising from the asymptotic.
  have hR_small : |R x| ≤ δ := hY x hY_le_x
  have hcoef_lb :
      Real.exp (-Myproj.eulerMascheroni) / 2 ≤
        Real.exp (-Myproj.eulerMascheroni) + R x := by
    set A := Real.exp (-Myproj.eulerMascheroni)
    have hlower : -(A / 2) ≤ R x := (abs_le.mp hR_small).1
    have hbound₀ := add_le_add_right hlower A
    have hbound : A + (-(A / 2)) ≤ A + R x := by
      simpa [add_comm, add_left_comm] using hbound₀
    have hrewrite : A + (-(A / 2)) = A / 2 := by
      ring
    simpa [A, hrewrite, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hbound
  have hweight_nonneg :
      0 ≤ (ε * Real.sqrt x) / Real.sqrt (Real.log x) := by
    have : 0 ≤ ε * Real.sqrt x := mul_nonneg hε_pos.le (Real.sqrt_nonneg _)
    exact div_nonneg this (Real.sqrt_nonneg _)
  have hmain :
      (Real.exp (-Myproj.eulerMascheroni) / 2)
          * (ε * Real.sqrt x) / Real.sqrt (Real.log x)
        ≤ Myproj.cyclicCountingReal (x + ε * Real.sqrt x)
            - Myproj.cyclicCountingReal x := by
    have hmul :
        (Real.exp (-Myproj.eulerMascheroni) / 2)
            * ((ε * Real.sqrt x) / Real.sqrt (Real.log x))
          ≤ Myproj.cyclicCountingReal (x + ε * Real.sqrt x)
              - Myproj.cyclicCountingReal x :=
      (mul_le_mul_of_nonneg_right hcoef_lb hweight_nonneg).trans hInterval_eval
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hmain_pos :
      0 < Myproj.cyclicCountingReal (x + ε * Real.sqrt x)
            - Myproj.cyclicCountingReal x := by
    have hfactor_pos :
        0 < (Real.exp (-Myproj.eulerMascheroni) / 2)
              * (ε * Real.sqrt x) / Real.sqrt (Real.log x) := by
      have hnum_pos :
          0 < (Real.exp (-Myproj.eulerMascheroni) / 2)
                * (ε * Real.sqrt x) :=
        mul_pos hδ_pos (mul_pos hε_pos hx_sqrt_pos)
      exact div_pos hnum_pos hx_log_sqrt_pos
    exact lt_of_lt_of_le hfactor_pos hmain
  -- Counting function bounds evaluated at `x`.
  have hn_pos : 1 ≤ n := hN_pos.trans hnN
  have hcount_x :
      Myproj.cyclicCountingReal x = n := by
    simpa [x] using
      Myproj.cyclicCountingReal_enumerator_eq (n := n) hn_pos
  have hcount_strict :
      (n : ℝ) < Myproj.cyclicCountingReal (x + ε * Real.sqrt x) := by
    have := add_lt_add_of_le_of_lt (le_of_eq hcount_x) hmain_pos
    simpa [hcount_x, add_comm, add_left_comm, add_assoc] using this
  have hsucc_le :
      c (n + 1) ≤ x + ε * Real.sqrt x :=
    enumerator_le_of_count_succ (n := n) (x := x + ε * Real.sqrt x) hcount_strict
  -- Translate the counting information to the enumerator gap.
  have hgap_le :
      c (n + 1) - c n ≤ ε * Real.sqrt x :=
    (sub_le_iff_le_add').2 hsucc_le
  -- Strict positivity of the gap.
  have hcount_succ :
      Myproj.cyclicCountingReal (c (n + 1)) = n + 1 := by
    simpa [Nat.succ_eq_add_one] using
      Myproj.cyclicCountingReal_enumerator_eq (n := n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))
  have hcount_pred :
      Myproj.cyclicCountingReal (c n) = n := hcount_x
  have hgappair := hgap_control hNgap_le
  have hgap_pos :
      0 < c (n + 1) - c n := hgappair.1
  -- Convert the gap to a statement on square roots.
  have hx_nonneg : 0 ≤ x := (Nat.cast_nonneg (n := n)).trans hx_nat_le
  have hsqrt_gap :
      Real.sqrt (c (n + 1)) - Real.sqrt x
        = (c (n + 1) - c n)
            / (Real.sqrt (c (n + 1)) + Real.sqrt x) := by
    have h := sqrt_add_sub hx_nonneg hgap_pos
    have hx_plus : x + (c (n + 1) - c n) = c (n + 1) := by
      simp [x, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [x, hx_plus] using h
  -- Positivity of the denominator and auxiliary bounds.
  have hc_succ_pos : 0 < c (n + 1) := by
    have hnat_pos : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact lt_of_lt_of_le hnat_pos (hc_ge_self (n + 1))
  have hden_pos :
      0 < Real.sqrt (c (n + 1)) + Real.sqrt x :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hc_succ_pos) (Real.sqrt_nonneg _)
  have hratio_le :
      (c (n + 1) - c n)
            / (Real.sqrt (c (n + 1)) + Real.sqrt x)
        ≤ (ε * Real.sqrt x)
            / (Real.sqrt (c (n + 1)) + Real.sqrt x) := by
    have hden_inv_nonneg :
        0 ≤ 1 / (Real.sqrt (c (n + 1)) + Real.sqrt x) :=
      div_nonneg zero_le_one (le_of_lt hden_pos)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using mul_le_mul_of_nonneg_right hgap_le hden_inv_nonneg
  have hden_gt :
      Real.sqrt x < Real.sqrt (c (n + 1)) + Real.sqrt x := by
    have := lt_add_of_pos_right (Real.sqrt x) (Real.sqrt_pos.2 hc_succ_pos)
    simpa [add_comm] using this
  have hfrac_lt_one :
      Real.sqrt x / (Real.sqrt (c (n + 1)) + Real.sqrt x) < 1 := by
    have hden_pos' : 0 < Real.sqrt (c (n + 1)) + Real.sqrt x := hden_pos
    exact (div_lt_one hden_pos').2 hden_gt
  have hright_lt :
      (ε * Real.sqrt x)
            / (Real.sqrt (c (n + 1)) + Real.sqrt x)
        < ε := by
    have hsimp :
        (ε * Real.sqrt x)
            / (Real.sqrt (c (n + 1)) + Real.sqrt x)
        = ε * (Real.sqrt x / (Real.sqrt (c (n + 1)) + Real.sqrt x)) := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have := mul_lt_mul_of_pos_left hfrac_lt_one hε_pos
    simpa [hsimp] using this
  have hratio_lt :
      (c (n + 1) - c n)
            / (Real.sqrt (c (n + 1)) + Real.sqrt x)
        < ε :=
    lt_of_le_of_lt hratio_le hright_lt
  have hx_eq : x = c n := rfl
  have hsqrt_diff :
      Real.sqrt (c (n + 1)) - Real.sqrt (c n) < ε := by
    simpa [x, hx_eq, hsqrt_gap] using hratio_lt
  exact hsqrt_diff

end Visser
end Myproj
