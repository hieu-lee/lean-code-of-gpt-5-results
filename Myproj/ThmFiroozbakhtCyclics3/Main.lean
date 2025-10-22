import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Myproj.CyclicNumbers.Axioms
import Myproj.ThmFiroozbakhtCyclics3.Axioms

/-
# Summary
Direct Lean translation of `thm_firoozbakht_cyclics_3.tex`. The proof relies on
the axiom `cyclicEnumerator_log_ratio_bound`, which encodes the eventual
inequality on normalised logarithms obtained from Pollack (2022), and converts
it to the desired statement via `Real.rpow`.
-/

noncomputable section

namespace Myproj

open scoped Real
open Real

private noncomputable abbrev c (n : ℕ) : ℝ := Myproj.cyclicEnumerator n

lemma cyclicEnumerator_pos {n : ℕ} (hn : 0 < n) : 0 < c n := by
  have hge : (n : ℝ) ≤ c n := Myproj.cyclicEnumerator_ge_self n
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  exact lt_of_lt_of_le hnpos hge

theorem firoozbakht_cyclics_three (k : ℕ) :
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
      Real.rpow (c n) (1 / ((n + k : ℕ) : ℝ))
        > Real.rpow (c (n + 1)) (1 / (((n + 1) + k : ℕ) : ℝ)) := by
  classical
  obtain ⟨N₀, hratio⟩ := Myproj.cyclicEnumerator_log_ratio_bound k
  let N := Nat.max N₀ 1
  refine ⟨N, ?_⟩
  intro n hn
  have hN₀ : N₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnposNat : 0 < n :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 1) (le_trans (Nat.le_max_right _ _) hn)
  have hpos₁ : 0 < c n := cyclicEnumerator_pos hnposNat
  have hpos₂ : 0 < c (n + 1) := cyclicEnumerator_pos (Nat.succ_pos _)
  have hlog := hratio hN₀
  have hleft :
      Real.exp (Real.log (c n) / (n + k : ℝ))
        = Real.rpow (c n) (1 / (n + k : ℝ)) := by
    simp [Real.rpow_def_of_pos, hpos₁, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc]
  have hright :
      Real.exp (Real.log (c (n + 1)) / (n + k + 1 : ℝ))
        = Real.rpow (c (n + 1)) (1 / (n + k + 1 : ℝ)) := by
    simp [Real.rpow_def_of_pos, hpos₂, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc]
  have hk_cast : ((n + 1) + k : ℕ) = n + k + 1 := by
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hfinal :
      Real.rpow (c (n + 1)) (1 / (n + k + 1 : ℝ))
        < Real.rpow (c n) (1 / (n + k : ℝ)) := by
    have := Real.exp_lt_exp.mpr hlog
    simpa [hleft, hright] using this
  simpa [hk_cast, Nat.cast_add, add_comm, add_left_comm, add_assoc]
    using hfinal

end Myproj
