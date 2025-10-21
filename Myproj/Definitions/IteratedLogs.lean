import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/-! Iterated logarithms used in some asymptotic arguments -/

noncomputable section

namespace Myproj

open Filter

/-- Third iterated logarithm on naturals: `L3(n) = log (log (log n))`.
This is used as the slowly varying factor in asymptotics. -/
def L3 (n : ℕ) : ℝ := Real.log (Real.log (Real.log (n : ℝ)))

/-- Fourth iterated logarithm on naturals: `L4(n) = log (log (log (log n)))`. -/
def L4 (n : ℕ) : ℝ := Real.log (Real.log (Real.log (Real.log (n : ℝ))))

/-- `L4(n) → ∞` as `n → ∞`. -/
lemma tendsto_L4_atTop_atTop : Tendsto L4 atTop atTop := by
  -- Compose `natCast → log → log → log → log`.
  have h0 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp h0
  have h2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp h1
  have h3 : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp h2
  have h4 : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (Real.log (n : ℝ))))) atTop atTop :=
    Real.tendsto_log_atTop.comp h3
  simpa [L4] using h4

end Myproj

end
