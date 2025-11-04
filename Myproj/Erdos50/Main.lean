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

/-- The Radon–Nikodym derivative of Schönberg's measure vanishes almost everywhere. -/
lemma schoenberg_zeroRadonNikodym :
    (schoenbergMeasure.rnDeriv volume) =ᵐ[volume] 0 :=
  phiSchoenberg_zeroRadonNikodym

/--
Final statement for Erdős problem 50: the set of points where Schönberg's
distribution function admits a positive derivative has Lebesgue measure zero.
-/
theorem schoenberg_no_positive_derivative :
    volume {x : ℝ | ∃ d : ℝ, 0 < d ∧ HasDerivAt schoenbergF d x} = 0 := by
  classical
  have h_zero :
      volume {x : ℝ | ¬ HasDerivAt schoenbergF 0 x} = 0 := by
    simpa [schoenbergF] using
      (ae_iff).1 schoenberg_derivative_zero_ae
  refine measure_mono_null ?_ h_zero
  intro x hx
  rcases hx with ⟨d, hd_pos, hDeriv⟩
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  exact fun hzero =>
    hd_ne <|
      (HasDerivAt.unique
        (by simpa [schoenbergF] using hzero)
        (by simpa [schoenbergF] using hDeriv)).symm

end Erdos50
end Myproj

end
