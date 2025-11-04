import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Myproj.Definitions
import Myproj.CyclicNumbers.Axioms

/-
This helper module packages the specialised consequences of Karamata's
integral theorem that we need in the Hassani argument.  We work with real
functions and the `SlowlyVaryingAtTop` predicate from mathlib's asymptotics
library.
-/

noncomputable section

namespace Myproj
namespace Hassani

open Filter
open scoped Topology

variable {L : ℝ → ℝ}

/-- Slowly varying at `+∞` on the reals: for every fixed `a > 0`,
`L(a·x) / L(x) → 1` as `x → +∞`. -/
def SlowlyVaryingAtTop (L : ℝ → ℝ) : Prop :=
  ∀ ⦃a : ℝ⦄, 0 < a → Tendsto (fun x : ℝ => L (a * x) / L x) atTop (𝓝 1)
 
/-! ### Analytic inputs used below, stated as axioms with citations

We record standard facts as axioms to avoid re-developing regular-variation
machinery in this project:

- `karamata_integral_sigma0` and `karamata_integral_sigma1` are the σ = 0 and σ = 1
  cases of Karamata's integral theorem (Bingham–Goldie–Teugels, §1.6).
- `cyclic_over_x_slowly_varying` encodes slow variation of `C(x)/x` from Pollack's
  refined expansion together with the fact that `1/log_3 x` is slowly varying.
-/

/-- Karamata integral theorem, σ = 0. -/
axiom karamata_over_C_over_t
    {C L : ℝ → ℝ}
    (hC : ∀ᶠ x in atTop, C x = x * L x)
    (hL : SlowlyVaryingAtTop L) :
    Tendsto (fun x : ℝ => (∫ t in (1 : ℝ)..x, C t / t) / C x) atTop (𝓝 1)

/-- Karamata integral theorem, σ = 1 (specialised to `C = x·L`). -/
axiom karamata_over_C
    {C L : ℝ → ℝ}
    (hC : ∀ᶠ x in atTop, C x = x * L x)
    (hL : SlowlyVaryingAtTop L) :
    Tendsto (fun x : ℝ => (∫ t in (1 : ℝ)..x, C t) / (x * C x))
      atTop (𝓝 (1 / 2 : ℝ))

/-- Slow variation of `C(x)/x` on reals (Pollack 2022 + closure properties). -/
axiom cyclic_over_x_slowly_varying :
    SlowlyVaryingAtTop (fun x : ℝ => Myproj.cyclicCountingReal x / x)

/-- If `C(x) = x • L(x)` with `L` slowly varying, then the integral
`∫₁ˣ C(t) / t dt` is asymptotic to `C(x)`.  This is a direct restatement of
Karamata's integral theorem (see the Encyclopedia of Mathematics article
*Karamata theory*). -/
theorem integral_over_t_of_regularly_varying
    (hC : ∀ᶠ x in atTop, Myproj.cyclicCountingReal x = x * L x)
    (hL : SlowlyVaryingAtTop L) :
    Tendsto (fun x : ℝ =>
        (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t / t)
          / Myproj.cyclicCountingReal x) atTop (𝓝 1) := by
  classical
  simpa using karamata_over_C_over_t (C := Myproj.cyclicCountingReal) (L := L) hC hL

/-- If `C(x) = x • L(x)` with `L` slowly varying, then the integral
`∫₁ˣ C(t) dt` is asymptotic to `x · C(x) / 2`.  This is the case
`σ = 1` of Karamata's integral theorem. -/
theorem integral_of_regularly_varying_half
    (hC : ∀ᶠ x in atTop, Myproj.cyclicCountingReal x = x * L x)
    (hL : SlowlyVaryingAtTop L) :
    Tendsto (fun x : ℝ =>
        (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t)
          / (x * Myproj.cyclicCountingReal x)) atTop (𝓝 (1 / 2 : ℝ)) := by
  classical
  simpa using karamata_over_C (C := Myproj.cyclicCountingReal) (L := L) hC hL

end Hassani
end Myproj

end
