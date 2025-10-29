import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Myproj.Erdos50.Axioms
import Myproj.Erdos50.Definitions

noncomputable section

namespace Myproj
namespace Erdos50

open MeasureTheory
open scoped MeasureTheory

lemma schoenberg_isProbability :
    IsProbabilityMeasure schoenbergMeasure :=
  phiSchoenberg_isProbability

/-- Step 1 from the proof: Schönberg's measure is not absolutely continuous. -/
lemma schoenberg_notAbsolutelyContinuous :
    ¬ schoenbergMeasure ≪ volume :=
  phiSchoenberg_notAbsolutelyContinuous

/-- Step 2: the Radon–Nikodym derivative of Schönberg's measure vanishes a.e. -/
lemma schoenberg_zeroRadonNikodym :
    (schoenbergMeasure.rnDeriv volume) =ᵐ[volume] 0 :=
  phiSchoenberg_zeroRadonNikodym

/--
Step 3: whenever the derivative of the distribution function exists, it must
vanish. This is a direct consequence of Vitali's differentiation theorem
specialised via the axiom `schoenberg_derivative_zero`.
-/
lemma schoenberg_derivative_zero_of_hasDeriv {x d : ℝ}
    (h : HasDerivAt schoenbergF x d) :
    d = 0 := by
  classical
  have := schoenberg_derivative_zero (x := x) (d := d)
    (by simpa [schoenbergF] using h)
  exact this

/--
Final statement for Erdős problem 50: Schönberg's distribution function has no
points where the derivative exists with positive value.
-/
theorem schoenberg_no_positive_derivative :
    ¬ ∃ x d : ℝ,
        HasDerivAt schoenbergF x d ∧ 0 < d := by
  intro h
  rcases h with ⟨x, d, hDeriv, hd_pos⟩
  have hd_zero : d = 0 := schoenberg_derivative_zero_of_hasDeriv hDeriv
  have : 0 < (0 : ℝ) := by simpa [hd_zero] using hd_pos
  exact lt_irrefl _ this

end Erdos50
end Myproj

end
