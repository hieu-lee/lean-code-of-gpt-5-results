import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Myproj.CyclicNumbers.Axioms
import Myproj.Definitions.IteratedLogs
import Myproj.ThmDusartCyclics.Axioms

noncomputable section

namespace Myproj
namespace ThmDusartCyclics

/-- Dusart analog for cyclics (Conj. 53 in Cohen 2025) is false. -/
theorem dusart_analog_cyclics_false :
    ¬ (∀ n : ℕ, 1 < n →
      Myproj.cyclicEnumerator n >
        Real.exp Myproj.eulerMascheroni * (n : ℝ) * (Myproj.L3 n + Myproj.L4 n)) := by
  intro hLower
  rcases eventual_upper_bound_ratio with ⟨K, N1, hKpos, hUpper⟩
  have hL4event : ∀ᶠ n : ℕ in Filter.atTop, K < Myproj.L4 n := by
    have hge := (Filter.tendsto_atTop.1 Myproj.tendsto_L4_atTop_atTop) (K + 1)
    refine hge.mono ?_
    intro n hn
    linarith
  rcases Filter.eventually_atTop.1 hL4event with ⟨N2, hN2⟩
  let n0 : ℕ := max (max N1 N2) 2
  have hn0N1 : N1 ≤ n0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn0N2 : N2 ≤ n0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have h2le : (2 : ℕ) ≤ n0 := le_max_right _ _
  have h1lt : 1 < n0 := Nat.lt_of_lt_of_le (by decide : 1 < 2) h2le
  have hUpper0 : Myproj.cyclicEnumerator n0
      ≤ Real.exp Myproj.eulerMascheroni * (n0 : ℝ) * (Myproj.L3 n0 + K) := by
    set fac : ℝ := Real.exp Myproj.eulerMascheroni * (n0 : ℝ) with hfac
    have hratio : Myproj.cyclicEnumerator n0 / fac ≤ Myproj.L3 n0 + K := by
      simpa [hfac] using hUpper (n := n0) hn0N1
    have hfacPos : 0 < fac := by
      have hn0pos : (0 : ℕ) < n0 := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) h2le
      have : 0 < Real.exp Myproj.eulerMascheroni * (n0 : ℝ) :=
        mul_pos (Real.exp_pos _) (by exact_mod_cast hn0pos)
      simpa [hfac] using this
    have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt hfacPos)
    have hleft : Myproj.cyclicEnumerator n0 / fac * fac = Myproj.cyclicEnumerator n0 := by
      have hfacNe : fac ≠ 0 := ne_of_gt hfacPos
      field_simp [hfacNe]
    have hright :
        (Myproj.L3 n0 + K) * fac
          = Real.exp Myproj.eulerMascheroni * (n0 : ℝ) * (Myproj.L3 n0 + K) := by
      simp [hfac, mul_comm, mul_left_comm, mul_assoc]
    simpa [hleft, hright, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hL4gt : K < Myproj.L4 n0 := hN2 (b := n0) hn0N2
  have hsumlt : Myproj.L3 n0 + K < Myproj.L3 n0 + Myproj.L4 n0 := by linarith
  have hfacPos : 0 < Real.exp Myproj.eulerMascheroni * (n0 : ℝ) := by
    have hn0pos : (0 : ℕ) < n0 := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) h2le
    exact mul_pos (Real.exp_pos _) (by exact_mod_cast hn0pos)
  have hmul :
      Real.exp Myproj.eulerMascheroni * (n0 : ℝ) * (Myproj.L3 n0 + K)
        < Real.exp Myproj.eulerMascheroni * (n0 : ℝ) * (Myproj.L3 n0 + Myproj.L4 n0) :=
    mul_lt_mul_of_pos_left hsumlt hfacPos
  have hfinal :
      Myproj.cyclicEnumerator n0
        < Real.exp Myproj.eulerMascheroni * (n0 : ℝ) * (Myproj.L3 n0 + Myproj.L4 n0) :=
    lt_of_le_of_lt hUpper0 hmul
  exact (not_lt_of_ge (le_of_lt hfinal)) (hLower n0 h1lt)

end ThmDusartCyclics
end Myproj

end
