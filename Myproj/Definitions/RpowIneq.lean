import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! General algebraic helper lemmas for rpow inequalities -/

noncomputable section

-- Silence minor style hints in these generic helper lemmas
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section RpowIneq

open Real

namespace Myproj

lemma rpow_bound_sub_of_mul_bound
    {x a b c L : ℝ} (hxpos : 0 < x)
    (h : x ^ a * L ≤ c * x ^ b) : x ^ (a - b) * L ≤ c := by
  have hxnonneg : 0 ≤ x ^ (-b) := (Real.rpow_pos_of_pos hxpos (-b)).le
  have hmul := mul_le_mul_of_nonneg_left h hxnonneg
  have hxadd_symm : x ^ (-b) * x ^ a = x ^ ((-b) + a) :=
    (Real.rpow_add hxpos (-b) a).symm
  have hxsum : (-b) + a = a - b := by ring
  have hleft : x ^ (-b) * (x ^ a * L) = x ^ (a - b) * L := by
    calc
      x ^ (-b) * (x ^ a * L) = (x ^ (-b) * x ^ a) * L := by ring
      _ = x ^ ((-b) + a) * L := by simpa [hxadd_symm]
      _ = x ^ (a - b) * L := by simpa [hxsum]
  have hright : x ^ (-b) * (c * x ^ b) = c := by
    have hxb : x ^ (-b) * x ^ b = x ^ ((-b) + b) := by
      simpa using (Real.rpow_add hxpos (-b) b).symm
    have : x ^ ((-b) + b) = (1 : ℝ) := by
      have hsum : (-b) + b = (0 : ℝ) := by ring
      simpa [hsum] using (Real.rpow_zero x)
    calc
      x ^ (-b) * (c * x ^ b) = c * (x ^ (-b) * x ^ b) := by ring
      _ = c * x ^ ((-b) + b) := by simpa [hxb]
      _ = c * 1 := by simpa [this]
      _ = c := by ring
  -- Collapse the RHS to `c` and simplify the LHS to `x^(a-b) * L`.
  have htemp : x ^ (-b) * (x ^ a * L) ≤ c := by
    simpa [hright, mul_comm, mul_left_comm, mul_assoc] using hmul
  have htemp2 : x ^ (a - b) * L ≤ c := by
    simpa [hleft] using htemp
  exact htemp2

lemma rpow_scale_bound_of_mul_bound
    {x ε c L : ℝ} (hxpos : 0 < x)
    (h : x ^ (2 * ε) * L ≤ c) : x ^ ε * L ≤ c * x ^ (-ε) := by
  have hxnonneg : 0 ≤ x ^ (-ε) := (Real.rpow_pos_of_pos hxpos (-ε)).le
  have hmul := mul_le_mul_of_nonneg_left h hxnonneg
  have hxsum : (-ε) + 2 * ε = ε := by ring
  have hxprod : x ^ (-ε) * x ^ (2 * ε) = x ^ ε := by
    simpa [hxsum] using (Real.rpow_add hxpos (-ε) (2 * ε)).symm
  have hright : x ^ (-ε) * c = c * x ^ (-ε) := by ring
  -- Move `x^{-ε}` inside, then simplify the left to `x^ε * L` and the right to `c * x^{-ε}`.
  have htemp : x ^ (-ε) * (x ^ (2 * ε) * L) ≤ c * x ^ (-ε) := by
    simpa [hright, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hleft_eq : x ^ (-ε) * (x ^ (2 * ε) * L) = x ^ ε * L := by
    calc
      x ^ (-ε) * (x ^ (2 * ε) * L)
          = (x ^ (-ε) * x ^ (2 * ε)) * L := by ring
      _ = x ^ ε * L := by simpa [hxprod]
  have htemp2 : x ^ ε * L ≤ c * x ^ (-ε) := by
    simpa [hleft_eq] using htemp
  exact htemp2

end Myproj

end RpowIneq

end
