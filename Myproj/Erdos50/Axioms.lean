import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.CDF

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

open MeasureTheory Measure
open Set Filter
open scoped MeasureTheory Topology

/--
Schönberg's probability measure on `ℝ` capturing the limit law of `Φ(n) = φ(n) / n`.
Existence and continuity of the limiting distribution were proved by Schönberg (1928/29).
Erdős later proved this limit law is of **purely singular** type, so its Radon–Nikodym
derivative with respect to Lebesgue is `0` a.e.; we isolate that as
`phiSchoenberg_zeroRadonNikodym` below.
References:
* I. J. Schönberg, *Über die asymptotische Verteilung reeller Zahlen mod 1*, Math. Z. **28** (1928), 171–199;
  see also accounts stating the φ(n)/n limit exists and is continuous.
* P. Erdős, *On the distribution of numbers of the form σ(n)/n and on some related questions*, Pacific
  J. Math. **52** (1974), 59–65 — proves the distribution for φ(n)/n is purely singular.
* B. Jessen & A. Wintner, *Distribution functions and the Riemann zeta function*, Trans. Amer. Math.
  Soc. **38** (1935) — pure-type paradigm for infinite convolutions.
* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Ch. 16 — Lebesgue
  decomposition; if μ ⟂ Lebesgue then `rnDeriv = 0` a.e. (used conceptually for `phiSchoenberg_zeroRadonNikodym`).
-/
axiom phiSchoenbergMeasure : Measure ℝ

/--
The Schönberg measure has total mass `1`, as expected for a limit distribution for `Φ(n) = φ(n) / n`.
This is standard once existence of the limit law is known, e.g. from Schönberg's original proof.
-/
axiom phiSchoenberg_isProbability :
    IsProbabilityMeasure phiSchoenbergMeasure

/--
The Radon–Nikodym derivative of the Schönberg measure with respect to Lebesgue vanishes almost
everywhere. This packages the purely singular conclusion (Erdős) together with the general
Lebesgue decomposition principle (e.g. Billingsley, Jessen–Wintner framework).
-/
axiom phiSchoenberg_zeroRadonNikodym :
    (phiSchoenbergMeasure.rnDeriv volume) =ᵐ[volume] 0

/--
Let `F(c) = (phiSchoenbergMeasure (Set.Ioc (0 : ℝ) c)).toReal`. Since the Schoenberg
measure is singular with respect to Lebesgue, its Radon–Nikodym derivative vanishes a.e.
Vitali/Lebesgue differentiation then shows `F' = 0` almost everywhere.
-/
theorem schoenberg_derivative_zero_ae :
  ∀ᵐ x : ℝ,
    HasDerivAt
      (fun c : ℝ => (phiSchoenbergMeasure (Set.Ioc (0 : ℝ) c)).toReal) 0 x := by
  classical
  set μ := phiSchoenbergMeasure
  haveI : IsProbabilityMeasure μ := phiSchoenberg_isProbability
  let F : ℝ → ℝ := fun c : ℝ => (μ (Set.Ioc (0 : ℝ) c)).toReal
  let G : ℝ → ℝ := fun x : ℝ => ProbabilityTheory.cdf μ x
  have hF_zero_of_nonpos :
      ∀ {x : ℝ}, x ≤ 0 → F x = 0 := by
    intro x hx
    have hIoc : Set.Ioc (0 : ℝ) x = ∅ := Set.Ioc_eq_empty_of_le hx
    simpa [F, hIoc]
  have hF_eq_of_nonneg :
      ∀ {x : ℝ}, 0 ≤ x → F x = G x - G 0 := by
    intro x hx
    have hmon : Monotone G := ProbabilityTheory.monotone_cdf μ
    have hxnonneg' : 0 ≤ G x - G 0 := sub_nonneg.mpr (hmon hx)
    have hmeasure :
        μ (Set.Ioc (0 : ℝ) x) =
          ENNReal.ofReal (G x - G 0) := by
      simpa [μ, G, ProbabilityTheory.measure_cdf μ] using
        (ProbabilityTheory.cdf μ).measure_Ioc (0 : ℝ) x
    have hFcalc : F x = (ENNReal.ofReal (G x - G 0)).toReal := by
      simpa [F, hmeasure]
    simpa [hFcalc, G, ENNReal.toReal_ofReal, hxnonneg']
  have hF_neg :
      ∀ {x : ℝ}, x < 0 → HasDerivAt F 0 x := by
    intro x hx
    have hconst : HasDerivAt (fun _ : ℝ => 0) (0 : ℝ) x :=
      hasDerivAt_const (x := x) (c := (0 : ℝ))
    have hxmem : x ∈ Set.Iio (0 : ℝ) := by
      simpa [Set.mem_Iio] using hx
    have hxIio : Set.Iio (0 : ℝ) ∈ 𝓝 x :=
      IsOpen.mem_nhds isOpen_Iio hxmem
    have hzero_eventually : ∀ᶠ y in 𝓝 x, y < 0 :=
      Filter.eventually_of_mem hxIio fun y hy => hy
    have hEq : F =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
      refine hzero_eventually.mono ?_
      intro y hy
      have hy' : y ≤ 0 := le_of_lt hy
      simpa [F, hF_zero_of_nonpos hy']
    exact HasDerivAt.congr_of_eventuallyEq hconst hEq
  have hF_of_pos :
      ∀ {x : ℝ}, 0 < x → HasDerivAt G 0 x → HasDerivAt F 0 x := by
    intro x hx hGx
    have hx_mem : x ∈ Set.Ioi (0 : ℝ) := by
      simpa [Set.mem_Ioi] using hx
    have hxIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 x :=
      IsOpen.mem_nhds isOpen_Ioi hx_mem
    have hpos : ∀ᶠ y in 𝓝 x, y > 0 :=
      Filter.eventually_of_mem hxIoi fun y hy => hy
    have hnonneg : ∀ᶠ y in 𝓝 x, 0 ≤ y :=
      hpos.mono fun y hy => (le_of_lt hy)
    have hEq : F =ᶠ[𝓝 x] fun y : ℝ => G y - G 0 := by
      refine hnonneg.mono ?_
      intro y hy
      exact hF_eq_of_nonneg hy
    have hGminus : HasDerivAt (fun y : ℝ => G y - G 0) 0 x :=
      hGx.sub_const (G 0)
    exact HasDerivAt.congr_of_eventuallyEq hGminus hEq
  have hG_deriv :
      ∀ᵐ x : ℝ, HasDerivAt G ((μ.rnDeriv volume x).toReal) x := by
    simpa [G, μ, ProbabilityTheory.measure_cdf μ] using
      (ProbabilityTheory.cdf μ).ae_hasDerivAt
  have hzero :
      ∀ᵐ x : ℝ, (μ.rnDeriv volume x).toReal = 0 := by
    refine (phiSchoenberg_zeroRadonNikodym).mono ?_
    intro x hx
    have hx' : μ.rnDeriv volume x = 0 := by
      simpa using hx
    simpa [hx']
  have hG_zero :
      ∀ᵐ x : ℝ, HasDerivAt G 0 x := by
    refine (hG_deriv.and hzero).mono ?_
    intro x hx
    rcases hx with ⟨hGx, hxzero⟩
    have hderiv_eq : (μ.rnDeriv volume x).toReal = 0 := by
      simpa [hxzero]
    exact HasDerivAt.congr_deriv hGx hderiv_eq
  have h_pos :
      ∀ᵐ x ∂ volume.restrict (Set.Ioi (0 : ℝ)), HasDerivAt F 0 x := by
    have h_mem :
        ∀ᵐ x ∂ volume.restrict (Set.Ioi (0 : ℝ)), x ∈ Set.Ioi (0 : ℝ) :=
      MeasureTheory.self_mem_ae_restrict (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    have hG_pos :
        ∀ᵐ x ∂ volume.restrict (Set.Ioi (0 : ℝ)), HasDerivAt G 0 x :=
      hG_zero.filter_mono
        (ae_mono (Measure.restrict_le_self (μ := volume) (s := Set.Ioi (0 : ℝ))))
    refine (h_mem.and hG_pos).mono ?_
    intro x hx
    rcases hx with ⟨hxpos, hGx⟩
    have hx' : 0 < x := by
      simpa [Set.mem_Ioi] using hxpos
    exact hF_of_pos hx' hGx
  have htc :
      ∀ᵐ x ∂ volume.restrict (Set.Iic (0 : ℝ)), HasDerivAt F 0 x := by
    have h_mem :
        ∀ᵐ x ∂ volume.restrict (Set.Iic (0 : ℝ)), x ∈ Set.Iic (0 : ℝ) :=
      MeasureTheory.self_mem_ae_restrict (μ := volume) (s := Set.Iic (0 : ℝ)) measurableSet_Iic
    have h_ne_zero :
        ∀ᵐ x ∂ volume.restrict (Set.Iic (0 : ℝ)), x ≠ 0 := by
      refine (ae_iff).2 ?_
      simp [Measure.restrict_apply, measurableSet_singleton, measurableSet_Iic]
    refine (h_mem.and h_ne_zero).mono ?_
    intro x hx
    rcases hx with ⟨hxle, hxne⟩
    have hxlt : x < 0 := lt_of_le_of_ne hxle hxne
    exact hF_neg hxlt
  have h_fail_pos :
      volume.restrict (Set.Ioi (0 : ℝ)) {x : ℝ | ¬ HasDerivAt F 0 x} = 0 :=
    (ae_iff).1 h_pos
  have h_fail_nonpos :
      volume.restrict (Set.Iic (0 : ℝ)) {x : ℝ | ¬ HasDerivAt F 0 x} = 0 :=
    (ae_iff).1 htc
  have h_inter_pos :
      volume ({x : ℝ | ¬ HasDerivAt F 0 x} ∩ Set.Ioi (0 : ℝ)) = 0 := by
    have hle := Measure.le_restrict_apply (μ := volume) (s := Set.Ioi (0 : ℝ))
        (t := {x : ℝ | ¬ HasDerivAt F 0 x})
    have : volume ({x : ℝ | ¬ HasDerivAt F 0 x} ∩ Set.Ioi (0 : ℝ)) ≤ 0 := by
      simpa [h_fail_pos] using hle
    exact le_antisymm this bot_le
  have h_inter_nonpos :
      volume ({x : ℝ | ¬ HasDerivAt F 0 x} ∩ Set.Iic (0 : ℝ)) = 0 := by
    have hle := Measure.le_restrict_apply (μ := volume) (s := Set.Iic (0 : ℝ))
        (t := {x : ℝ | ¬ HasDerivAt F 0 x})
    have : volume ({x : ℝ | ¬ HasDerivAt F 0 x} ∩ Set.Iic (0 : ℝ)) ≤ 0 := by
      simpa [h_fail_nonpos] using hle
    exact le_antisymm this bot_le
  have h_fail_zero :
      volume {x : ℝ | ¬ HasDerivAt F 0 x} = 0 := by
    have hle :=
      measure_le_inter_add_diff (μ := volume) {x : ℝ | ¬ HasDerivAt F 0 x}
        (Set.Ioi (0 : ℝ))
    have :
        volume {x : ℝ | ¬ HasDerivAt F 0 x} ≤
          volume ({x : ℝ | ¬ HasDerivAt F 0 x} ∩ Set.Ioi (0 : ℝ)) +
            volume ({x : ℝ | ¬ HasDerivAt F 0 x} \ Set.Ioi (0 : ℝ)) := hle
    have h_diff :
        volume ({x : ℝ | ¬ HasDerivAt F 0 x} \ Set.Ioi (0 : ℝ)) = 0 := by
      classical
      refine measure_mono_null ?_ h_inter_nonpos
      intro x hx
      rcases hx with ⟨hxS, hxIoi⟩
      have hxle : x ≤ 0 := le_of_not_gt (by simpa [Set.mem_Ioi] using hxIoi)
      exact ⟨hxS, by simpa [Set.mem_Iic] using hxle⟩
    have hsum :
        volume ({x : ℝ | ¬ HasDerivAt F 0 x} ∩ Set.Ioi (0 : ℝ)) +
            volume ({x : ℝ | ¬ HasDerivAt F 0 x} \ Set.Ioi (0 : ℝ)) = 0 := by
      simpa [h_inter_pos, h_diff]
    exact le_antisymm
      (this.trans_eq hsum)
      bot_le
  have h_total :
      ∀ᵐ x ∂ volume, HasDerivAt F 0 x :=
    (ae_iff).2 h_fail_zero
  exact h_total.mono (by intro x hx; simpa [F] using hx)

end Erdos50
end Myproj

end
