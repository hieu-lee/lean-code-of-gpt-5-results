import Mathlib.Data.Finset.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Myproj.Definitions.Cyclics

/-! Real-variable counting and a real iterated logarithm -/

noncomputable section

namespace Myproj

open Real

/-- Real-variable counting function for cyclic numbers: `C(x) = #{m ≤ x : gcd(m, φ(m)) = 1}`. -/
def cyclicCountingReal (x : ℝ) : ℝ :=
  (((Finset.Icc 1 (Nat.floor x)).filter fun m : ℕ => isCyclicNumber m).card : ℕ)
    |> (fun n => (n : ℝ))

/-- Third iterated logarithm on reals: `L(x) = log (log (log x))`. -/
def L3R (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))

end Myproj

end
