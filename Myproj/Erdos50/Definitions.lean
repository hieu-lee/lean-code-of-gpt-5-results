import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.Basic
import Myproj.Erdos50.Axioms

noncomputable section

namespace Myproj
namespace Erdos50

open MeasureTheory
open scoped MeasureTheory

/-- The normalised totient ratio `Φ(n) = φ(n) / n` seen as a real number. -/
def phiRatio (n : ℕ) : ℝ :=
  (Nat.totient n : ℝ) / (n : ℝ)

/--
The limiting Schönberg measure on `(0, 1]` obtained from the distribution of
`phiRatio`. This is introduced as an axiom in `Axioms.lean`.
-/
def schoenbergMeasure : Measure ℝ :=
  phiSchoenbergMeasure

/--
Distribution function `f(c) = μ((0, c])` associated to Schönberg's limiting
measure. We use the right-closed interval in accordance with the original
number-theoretic definition.
-/
def schoenbergF (c : ℝ) : ℝ :=
  (schoenbergMeasure (Set.Ioc (0 : ℝ) c)).toReal

/-- Level set where the totient ratio equals the real constant `c`. -/
def exactValueSet (c : ℝ) : Set ℕ :=
  {n : ℕ | phiRatio n = c}

end Erdos50
end Myproj

end
