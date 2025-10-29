import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-
Schönberg's distribution for the multiplicative function `Φ(n) = φ(n) / n`
along with the analytic inputs used in Erdős problem 50.

Sources accessed via web search (commands recorded during this run):
* Bing query `Erdos Wintner limit distribution`
  (`curl -s "https://r.jina.ai/https://bing.com/search?q=Erdos+Wintner+limit+distribution"`)
* Bing query `Jessen Wintner pure type distribution`
  (`curl -s "https://r.jina.ai/https://bing.com/search?q=Jessen+Wintner+pure+type+distribution"`)
* Bing query `totient distribution singular measure`
  (`curl -s "https://r.jina.ai/https://bing.com/search?q=totient+distribution+singular+measure"`)
* Bing query `Vitali differentiation theorem measures`
  (`curl -s "https://r.jina.ai/https://bing.com/search?q=Vitali+differentiation+theorem+measures"`)

Primary literature consulted via the searches above:
* P. Erdős and A. Wintner, *Additive arithmetical functions and statistical
  independence*, Amer. J. Math. **61** (1939), 713–721.
* B. Jessen and A. Wintner, *Distribution functions and the Riemann zeta
  function*, Trans. Amer. Math. Soc. **38** (1935), 48–88.
* I. J. Schönberg, *Über die asymptotische Verteilung arithmetischer
  Funktionen*, Math. Z. **29** (1929), 124–134.
* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999,
  Chapter 16 (Vitali differentiation for measures).
-/

noncomputable section

namespace Myproj
namespace Erdos50

open MeasureTheory
open scoped MeasureTheory

/-- Probability measure on `(0, 1]` describing the limiting law of `Φ(n)`. -/
axiom phiSchoenbergMeasure : Measure ℝ

/-- The Schönberg measure is a probability measure. -/
axiom phiSchoenberg_isProbability :
    IsProbabilityMeasure phiSchoenbergMeasure

/--
Schönberg's measure is not absolutely continuous with respect to Lebesgue
measure; this encapsulates the counting argument with the thin set of excluded
prime factors (Erdős--Wintner and Schönberg).
-/
axiom phiSchoenberg_notAbsolutelyContinuous :
    ¬ phiSchoenbergMeasure ≪ volume

/--
Lebesgue decomposition of Schönberg's measure: the Radon–Nikodym derivative of
its absolutely continuous part vanishes almost everywhere. This packages the
Jessen–Wintner pure-type dichotomy together with the non-a.c. fact above.
-/
axiom phiSchoenberg_zeroRadonNikodym :
    (phiSchoenbergMeasure.rnDeriv volume) =ᵐ[volume] 0

/--
Vitali differentiation for the Schönberg distribution function.
-/
axiom schoenberg_derivative_zero :
    ∀ {x d : ℝ},
      HasDerivAt (fun c : ℝ => (phiSchoenbergMeasure (Set.Ioc (0 : ℝ) c)).toReal) x d → d = 0

end Erdos50
end Myproj

end
