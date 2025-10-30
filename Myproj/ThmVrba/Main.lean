import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Myproj.ThmVrba.Axioms

/-
From the analytic axioms we deduce the Vrba analog: the ratio `cₙ / Gₙ`
converges to `e`.
-/

noncomputable section

namespace Myproj

open Filter Topology

/-- Vrba analog: `cₙ / Gₙ → e`. -/
theorem vrba_analog :
    Tendsto Myproj.cyclicRatio atTop (𝓝 (Real.exp 1)) := by
  have hlog := Myproj.cyclic_ratio_log_tendsto
  have hpos := Myproj.cyclic_ratio_pos
  have hlimit :
      Tendsto (fun n : ℕ => Real.exp (Real.log (Myproj.cyclicRatio n)))
        atTop (𝓝 (Real.exp 1)) :=
    ((Real.continuous_exp.continuousAt : ContinuousAt Real.exp 1).tendsto).comp hlog
  refine hlimit.congr' ?_
  filter_upwards [Filter.univ_mem] with n _
  have h := hpos n
  simpa [Real.exp_log h] using rfl

end Myproj

end
