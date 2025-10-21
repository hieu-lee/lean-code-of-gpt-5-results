import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Myproj.ThmKFoldOppermann.ShortIntervals

/-
Final statement for the `k`-fold Oppermann theorem on primes.
-/

noncomputable section

namespace Myproj
namespace ThmKFoldOppermann

open Real

private lemma log_pos_nat {n : ℕ} (hn : 3 ≤ n) :
    0 < Real.log (n : ℝ) := by
  have hgt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hn)
  exact Real.log_pos hgt

private lemma ratio_le_ratio {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) / (300 * Real.log (n : ℝ)) ≤ (n : ℝ) / (200 * Real.log (n : ℝ)) := by
  have hratio_nonneg : 0 ≤ (n : ℝ) / Real.log (n : ℝ) := by
    have hnpos : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hlogpos : 0 < Real.log (n : ℝ) := log_pos_nat hn
    exact div_nonneg hnpos hlogpos.le
  have hcoeff : (1 / (300 : ℝ)) ≤ (1 / (200 : ℝ)) := by norm_num
  have := mul_le_mul_of_nonneg_left hcoeff hratio_nonneg
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

private lemma ratio_bound (n k : ℕ) (hn : 3 ≤ n)
    (h : (n : ℝ) / Real.log (n : ℝ) ≥ ((300 * k : ℕ) : ℝ)) :
    (k : ℝ) ≤ (n : ℝ) / (300 * Real.log (n : ℝ)) := by
  have h' : (300 * (k : ℝ)) ≤ (n : ℝ) / Real.log (n : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_ofNat] using h
  have := mul_le_mul_of_nonneg_right h' (by positivity : 0 ≤ (1 / (300 : ℝ)))
  have hcoeff : (300 : ℝ) ≠ 0 := by norm_num
  have hlogne : Real.log (n : ℝ) ≠ 0 := by exact ne_of_gt (log_pos_nat hn)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hcoeff, hlogne] using this

theorem k_fold_oppermann_for_primes :
    ∀ k : ℕ, ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
      (k : ℝ) ≤ Myproj.primesLeft n ∧ (k : ℝ) ≤ Myproj.primesRight n := by
  classical
  intro k
  obtain ⟨N₁, hleft⟩ := primesLeft_eventually
  obtain ⟨N₂, hright⟩ := primesRight_eventually
  obtain ⟨N₃, hdiv⟩ := eventually_nat_div_log_ge' (300 * k)
  let N := max 3 (max N₁ (max N₂ N₃))
  refine ⟨N, ?_⟩
  intro n hn
  have hn3 : 3 ≤ n :=
    le_trans (le_max_left _ (max N₁ (max N₂ N₃))) hn
  have hrest : max N₁ (max N₂ N₃) ≤ n :=
    le_trans (le_max_right _ _) hn
  have hn₁ : N₁ ≤ n :=
    le_trans (le_max_left _ _) hrest
  have hrest₂ : max N₂ N₃ ≤ n :=
    le_trans (le_max_right _ _) hrest
  have hn₂ : N₂ ≤ n :=
    le_trans (le_max_left _ _) hrest₂
  have hn₃' : N₃ ≤ n :=
    le_trans (le_max_right _ _) hrest₂
  have hL := hleft hn₁
  have hR := hright hn₂
  have hdiv' := hdiv hn₃'
  have hk : (k : ℝ) ≤ (n : ℝ) / (300 * Real.log (n : ℝ)) :=
    ratio_bound n k hn3 hdiv'
  have hk_left :
      (k : ℝ) ≤ (n : ℝ) / (200 * Real.log (n : ℝ)) := by
    calc
      (k : ℝ)
          ≤ (n : ℝ) / (300 * Real.log (n : ℝ)) := hk
      _ ≤ (n : ℝ) / (200 * Real.log (n : ℝ)) := ratio_le_ratio hn3
  refine And.intro ?_ ?_
  · exact le_trans hk_left hL
  · exact le_trans hk hR

end ThmKFoldOppermann
end Myproj
