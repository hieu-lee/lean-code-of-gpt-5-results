import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Myproj.Definitions
import Myproj.CyclicNumbers.Axioms
import Myproj.ThmFiroozbakhtCyclics3.Axioms

/-
Axioms encapsulating the analytic number theory inputs that drive the
Visser analog for cyclic integers. Each axiom records a classical result
with an explicit literature citation and the search command used to
locate the source during this run.
-/

noncomputable section

namespace Myproj
namespace Visser

open Filter
open scoped Topology

/-- Euler product over primes up to `z`: `V(z) = ∏_{p ≤ z} (1 - 1/p)`. -/
axiom eulerProduct : ℝ → ℝ

/-- Count of integers `n ∈ (x, x + h]` whose least prime factor exceeds `z`. -/
axiom roughIntervalCount : ℝ → ℝ → ℝ → ℝ

/-- Count of non-squarefree integers among `n ∈ (x, x + h]`. -/
axiom nonSquarefreeIntervalCount : ℝ → ℝ → ℝ → ℝ

/-
Count of integers `n ∈ (x, x + h]` possessing primes `p, q` with
`p ∣ n`, `q ∣ n`, and `q ≡ 1 (mod p)`.
-/
axiom congruenceIntervalCount : ℝ → ℝ → ℝ → ℝ

/-!
### Linear sieve lower bound

Iwaniec & Kowalski (2004, Thm. 11.13) and Halberstam & Richert (1974,
Ch. 6) provide a uniform linear-sieve lower bound for rough numbers in
short intervals.

Search commands recorded during this run:
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Iwaniec+Kowalski+linear+sieve+short+interval"`
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Halberstam+Richert+linear+sieve+cyclic"`
-/
axiom linear_sieve_short_interval :
  ∃ (R₁ : ℝ → ℝ) (X₁ : ℝ),
    0 < X₁ ∧ Tendsto R₁ atTop (𝓝 0) ∧
    ∀ ⦃x h z : ℝ⦄, X₁ ≤ x → 0 < h → 1 < z → z ≤ x →
      roughIntervalCount x h z ≥ h * eulerProduct z * (1 + R₁ x)

/-!
### Removing non-squarefree integers

Divisor-sum bounds show that the discarded set of non-squarefree
integers contributes `o(h / log z)` elements. References include
Montgomery & Vaughan (2007, §7) together with classical Brun–Titchmarsh
estimates.

Search command recorded during this run:
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Montgomery+Vaughan+Brun+Titchmarsh+squarefree"`
-/
axiom non_squarefree_removal :
  ∃ (R₂ : ℝ → ℝ) (X₂ : ℝ),
    0 < X₂ ∧ Tendsto R₂ atTop (𝓝 0) ∧
    ∀ ⦃x h z : ℝ⦄, X₂ ≤ x → 0 < h → 1 < z →
      nonSquarefreeIntervalCount x h z ≤ R₂ x * h / Real.log z

/-!
### Removing congruence obstructions

Brun–Titchmarsh bounds (see Montgomery & Vaughan 2007, Thm. 7.3) ensure
that integers with two prime factors `p, q` and `q ≡ 1 (mod p)` inside
the interval contribute `o(h / log z)` elements.

Search command recorded during this run:
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Montgomery+Vaughan+Brun+Titchmarsh+squarefree"`
-/
axiom congruence_removal :
  ∃ (R₃ : ℝ → ℝ) (X₃ : ℝ),
    0 < X₃ ∧ Tendsto R₃ atTop (𝓝 0) ∧
    ∀ ⦃x h z : ℝ⦄, X₃ ≤ x → 0 < h → 1 < z →
      congruenceIntervalCount x h z ≤ R₃ x * h / Real.log z

/-!
### Bookkeeping from sieve to cyclic integers

Combining the sieve lower bound with the exclusions yields a lower
bound for the cyclic counting function itself.

Search command recorded during this run:
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+linear+sieve"`
-/
axiom cyclic_counting_from_sieve ⦃x h z : ℝ⦄ :
    Myproj.cyclicCountingReal (x + h) - Myproj.cyclicCountingReal x
      ≥ roughIntervalCount x h z
        - nonSquarefreeIntervalCount x h z
        - congruenceIntervalCount x h z

/-!
### Enumerator capture from counting data

If the cyclic counting function exceeds `n`, then the `(n+1)`-st cyclic
number lies below that point.

Search command recorded during this run:
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+linear+sieve"`
-/
axiom enumerator_le_of_count_succ {n : ℕ} {x : ℝ} :
    (n : ℝ) < Myproj.cyclicCountingReal x →
      Myproj.cyclicEnumerator (n + 1) ≤ x

/-!
### Mertens’ product asymptotic

The Euler product satisfies `V(z) = e^{−γ} / log z · (1 + o(1))` as
`z → ∞`. See Apostol (1976, §5.8) or Montgomery & Vaughan (2007, Ch. 1).

Search command recorded during this run:
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Apostol+Mertens+product+euler+gamma"`
-/
axiom mertens_euler_product :
  ∃ (R₀ : ℝ → ℝ) (Z₀ : ℝ),
    1 < Z₀ ∧ Tendsto R₀ atTop (𝓝 0) ∧
    ∀ ⦃z : ℝ⦄, Z₀ ≤ z →
      eulerProduct z =
        Real.exp (-Myproj.eulerMascheroni) / Real.log z * (1 + R₀ z)

/-!
### Short-interval bound (Statement (A) in the proof)

Combining the sieve data yields the explicit lower bound (A):
for large `x` and `h = ε √x`, the difference
`C(x + h) - C(x)` is bounded below by
`(e^{−γ} + o(1)) h / √(log x)`.

Search command recorded during this run:
* `curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+linear+sieve"`
-/
private lemma sqrt_log_tendsto_atTop :
    Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  refine (eventually_ge_atTop (Real.exp ((max B 0) ^ 2))).mono ?_
  intro x hx
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx_exp_pos : 0 < Real.exp ((max B 0) ^ 2) := Real.exp_pos _
  have hx_log_ge :
      (max B 0) ^ 2 ≤ Real.log x := by
    have hlog_le :
        Real.log (Real.exp ((max B 0) ^ 2)) ≤ Real.log x :=
      (Real.log_le_log_iff hx_exp_pos hx_pos).2 hx
    simpa [Real.log_exp, sq] using hlog_le
  have htarget :
      max B 0 ≤ Real.sqrt (Real.log x) :=
    Real.le_sqrt_of_sq_le (by simpa [sq] using hx_log_ge)
  exact (le_max_left _ _).trans htarget

private lemma sqrt_log_le_log {x : ℝ} (hx_exp1 : Real.exp 1 ≤ x) :
    Real.sqrt (Real.log x) ≤ Real.log x := by
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx_exp1
  have hx_log_ge_one :
      1 ≤ Real.log x := by
    simpa [Real.log_exp] using
      (Real.le_log_iff_exp_le hx_pos).2 hx_exp1
  have hx_log_nonneg : 0 ≤ Real.log x :=
    (zero_le_one : (0 : ℝ) ≤ 1).trans hx_log_ge_one
  have hx_log_sq :
      Real.log x ≤ (Real.log x) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hx_log_ge_one hx_log_nonneg
    simpa [sq, mul_comm] using this
  have := Real.sqrt_le_sqrt hx_log_sq
  have hsq :
      Real.sqrt ((Real.log x) ^ 2) = Real.log x := by
    simpa [sq, abs_of_nonneg hx_log_nonneg] using Real.sqrt_sq hx_log_nonneg
  simpa [hsq] using this

private lemma expand_mertens_factor (a r₀ r₁ : ℝ) :
    a * (1 + r₀) * (1 + r₁) = a + a * (r₀ + r₁ + r₀ * r₁) := by
  ring

theorem cyclic_short_interval_bound :
  ∃ (R : ℝ → ℝ) (X : ℝ),
    1 < X ∧ Tendsto R atTop (𝓝 0) ∧
    ∀ ⦃x ε : ℝ⦄, X ≤ x → 0 < ε → ε < 1 →
      Myproj.cyclicCountingReal (x + ε * Real.sqrt x) - Myproj.cyclicCountingReal x
        ≥ (Real.exp (-Myproj.eulerMascheroni) + R x)
            * (ε * Real.sqrt x) / Real.sqrt (Real.log x) := by
  classical
  obtain ⟨R₁, X₁, hX₁, hR₁, hLinear⟩ := linear_sieve_short_interval
  obtain ⟨R₂, X₂, hX₂, hR₂, hSqfree⟩ := non_squarefree_removal
  obtain ⟨R₃, X₃, hX₃, hR₃, hCong⟩ := congruence_removal
  obtain ⟨R₀, Z₀, hZ₀, hR₀, hMertens⟩ := mertens_euler_product
  let zfun : ℝ → ℝ := fun x => Real.exp (Real.sqrt (Real.log x))
  have hz_tendsto :
      Tendsto zfun atTop atTop :=
    Real.tendsto_exp_atTop.comp sqrt_log_tendsto_atTop
  let g : ℝ → ℝ :=
    fun x => R₀ (zfun x) + R₁ x + R₀ (zfun x) * R₁ x
  have hg_tendsto : Tendsto g atTop (𝓝 0) := by
    have hR₀_comp := hR₀.comp hz_tendsto
    have hsum := hR₀_comp.add hR₁
    have hprod := hR₀_comp.mul hR₁
    have htotal := hsum.add hprod
    simpa [g, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using htotal
  let R : ℝ → ℝ :=
    fun x =>
      Real.exp (-Myproj.eulerMascheroni) * g x - (R₂ x + R₃ x)
  have hR_tendsto : Tendsto R atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℝ => Real.exp (-Myproj.eulerMascheroni))
          atTop (𝓝 (Real.exp (-Myproj.eulerMascheroni))) :=
      tendsto_const_nhds
    have hscale := hconst.mul hg_tendsto
    have hsumR₂₃ := hR₂.add hR₃
    have hsub := hscale.sub hsumR₂₃
    simpa [R, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hsub
  let Xz : ℝ := Real.exp ((Real.log Z₀) ^ 2)
  let X₀ : ℝ :=
    max X₁ (max X₂ (max X₃ (max (Real.exp 1) (max Z₀ Xz))))
  have hX₀_ge_exp :
      Real.exp 1 ≤ X₀ := by
    have h₁ : Real.exp 1 ≤ max (Real.exp 1) (max Z₀ Xz) := le_max_left _ _
    have h₂ :
        max (Real.exp 1) (max Z₀ Xz)
          ≤ max X₃ (max (Real.exp 1) (max Z₀ Xz)) := le_max_right _ _
    have h₃ :
        max X₃ (max (Real.exp 1) (max Z₀ Xz))
          ≤ max X₂ (max X₃ (max (Real.exp 1) (max Z₀ Xz))) := le_max_right _ _
    have h₄ :
        max X₂ (max X₃ (max (Real.exp 1) (max Z₀ Xz))) ≤ X₀ := le_max_right _ _
    exact h₁.trans (h₂.trans (h₃.trans h₄))
  have hX₀_gt : 1 < X₀ :=
    lt_of_lt_of_le ((Real.one_lt_exp_iff).2 zero_lt_one) hX₀_ge_exp
  refine ⟨R, X₀, hX₀_gt, hR_tendsto, ?_⟩
  intro x ε hxX hε_pos hε_lt
  let h : ℝ := ε * Real.sqrt x
  let z := zfun x
  have hx_ge_X2 :
      max X₂ (max X₃ (max (Real.exp 1) (max Z₀ Xz))) ≤ x :=
    (le_max_right _ _).trans hxX
  have hx_ge_X3 :
      max X₃ (max (Real.exp 1) (max Z₀ Xz)) ≤ x :=
    (le_max_right _ _).trans hx_ge_X2
  have hx_ge_exp :
      max (Real.exp 1) (max Z₀ Xz) ≤ x :=
    (le_max_right _ _).trans hx_ge_X3
  have hx_X₁ : X₁ ≤ x := (le_max_left _ _).trans hxX
  have hx_X₂ : X₂ ≤ x := (le_max_left _ _).trans hx_ge_X2
  have hx_X₃ : X₃ ≤ x := (le_max_left _ _).trans hx_ge_X3
  have hx_exp1 : Real.exp 1 ≤ x := (le_max_left _ _).trans hx_ge_exp
  have hx_Z₀ : Z₀ ≤ x := by
    have : Z₀ ≤ max Z₀ Xz := le_max_left _ _
    exact this.trans ((le_max_right _ _).trans hx_ge_exp)
  have hx_Xz : Xz ≤ x := by
    have : Xz ≤ max Z₀ Xz := le_max_right _ _
    exact this.trans ((le_max_right _ _).trans hx_ge_exp)
  have hx_gt_one : 1 < x :=
    lt_of_lt_of_le ((Real.one_lt_exp_iff).2 zero_lt_one) hx_exp1
  have hx_pos : 0 < x := lt_trans zero_lt_one hx_gt_one
  have hx_log_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hx_log_nonneg : 0 ≤ Real.log x := le_of_lt hx_log_pos
  have hz_def : z = Real.exp (Real.sqrt (Real.log x)) := rfl
  have hz_gt_one : 1 < z := by
    have : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hx_log_pos
    simpa [z, hz_def] using (Real.one_lt_exp_iff).2 this
  have hz_log_pos : 0 < Real.log z := by
    simpa [z, hz_def] using Real.sqrt_pos.2 hx_log_pos
  have hz_log_nonneg : 0 ≤ Real.log z := le_of_lt hz_log_pos
  have hz_le_x : z ≤ x := by
    have hsqrt_le := sqrt_log_le_log hx_exp1
    have := Real.exp_le_exp.mpr hsqrt_le
    simpa [z, hz_def, Real.exp_log hx_pos] using this
  have hz_ge_Z₀ : Z₀ ≤ z := by
    have hxz_pos : 0 < Xz := Real.exp_pos _
    have hx_log_sq :
        (Real.log Z₀) ^ 2 ≤ Real.log x := by
      have := (Real.log_le_log_iff hxz_pos hx_pos).2 hx_Xz
      simpa [Xz, sq, Real.log_exp] using this
    have hlog_le :
        Real.log Z₀ ≤ Real.sqrt (Real.log x) :=
      Real.le_sqrt_of_sq_le (by simpa [sq] using hx_log_sq)
    have := Real.exp_le_exp.mpr hlog_le
    simpa [z, hz_def, Real.exp_log (lt_trans zero_lt_one hZ₀)] using this
  have hz_log_eq :
      Real.log z = Real.sqrt (Real.log x) := by
    simp [z, hz_def]
  have h_pos : 0 < h := by
    have hx_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx_pos
    simpa [h] using mul_pos hε_pos hx_sqrt_pos
  have hrough :=
    hLinear hx_X₁ h_pos hz_gt_one hz_le_x
  have hsq :=
    hSqfree hx_X₂ h_pos hz_gt_one
  have hcong :=
    hCong hx_X₃ h_pos hz_gt_one
  have hcount :=
    cyclic_counting_from_sieve (x := x) (h := h) (z := z)
  have hcount' :
      Myproj.cyclicCountingReal (x + h) - Myproj.cyclicCountingReal x ≥
        roughIntervalCount x h z
          - (nonSquarefreeIntervalCount x h z + congruenceIntervalCount x h z) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcount
  have hsum_le :
      nonSquarefreeIntervalCount x h z + congruenceIntervalCount x h z
        ≤ (R₂ x + R₃ x) * (h / Real.log z) := by
    have := add_le_add hsq hcong
    simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc,
      add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc] using this
  have hthrough_bound :
      h * eulerProduct z * (1 + R₁ x) - (R₂ x + R₃ x) * (h / Real.log z)
        ≤ roughIntervalCount x h z
          - (nonSquarefreeIntervalCount x h z + congruenceIntervalCount x h z) := by
    have := (sub_le_sub_left hsum_le _).trans (sub_le_sub_right hrough _)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hmain :
      Myproj.cyclicCountingReal (x + h) - Myproj.cyclicCountingReal x ≥
        h * eulerProduct z * (1 + R₁ x)
          - (R₂ x + R₃ x) * (h / Real.log z) :=
    (hthrough_bound.trans hcount'.le)
  have hEuler_z :
      eulerProduct z =
        Real.exp (-Myproj.eulerMascheroni) / Real.log z * (1 + R₀ z) :=
    hMertens hz_ge_Z₀
  have hlog_ne : Real.log z ≠ 0 := ne_of_gt hz_log_pos
  have hproduct_core :
      h * eulerProduct z
        = (h / Real.log z) *
            (Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z)) := by
    have hlog_ne' : Real.log z ≠ 0 := hlog_ne
    simp [hEuler_z, hlog_ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hproduct :
      h * eulerProduct z * (1 + R₁ x)
        = (h / Real.log z) *
            (Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x)) := by
    calc
      h * eulerProduct z * (1 + R₁ x)
          = ((h / Real.log z) *
              (Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z))) * (1 + R₁ x) := by
            simpa [hproduct_core]
      _ = (h / Real.log z) *
            ((Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z)) * (1 + R₁ x)) := by
        simp [mul_assoc]
      _ = (h / Real.log z) *
            (Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x)) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
  have hmain_factored :
      Myproj.cyclicCountingReal (x + h) - Myproj.cyclicCountingReal x ≥
        (h / Real.log z) *
            (Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x)
              - (R₂ x + R₃ x)) := by
    have hcomm :
        (R₂ x + R₃ x) * (h / Real.log z)
          = (h / Real.log z) * (R₂ x + R₃ x) := by
      simp [mul_comm]
    have hrewrite :
        h * eulerProduct z * (1 + R₁ x)
              - (R₂ x + R₃ x) * (h / Real.log z)
          = (h / Real.log z) *
              (Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x)
                - (R₂ x + R₃ x)) := by
      calc
        h * eulerProduct z * (1 + R₁ x)
              - (R₂ x + R₃ x) * (h / Real.log z)
            = (h / Real.log z) *
                (Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x))
                - (h / Real.log z) * (R₂ x + R₃ x) := by
              simpa [hproduct, hcomm]
        _ = (h / Real.log z) *
              ((Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x))
                - (R₂ x + R₃ x)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (mul_sub (h / Real.log z)
              (Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x))
              (R₂ x + R₃ x)).symm
    simpa [hrewrite] using hmain
  have hfactor :
      Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x)
        = Real.exp (-Myproj.eulerMascheroni)
          + Real.exp (-Myproj.eulerMascheroni) * g x := by
    have := expand_mertens_factor (Real.exp (-Myproj.eulerMascheroni)) (R₀ z) (R₁ x)
    simpa [g, z, hz_def, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]
      using this
  have hcoeff_core :
      Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x)
        - (R₂ x + R₃ x)
        = Real.exp (-Myproj.eulerMascheroni) + R x := by
    calc
      Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x)
            - (R₂ x + R₃ x)
          = (Real.exp (-Myproj.eulerMascheroni)
              + Real.exp (-Myproj.eulerMascheroni) * g x)
                - (R₂ x + R₃ x) := by
            simp [hfactor]
      _ = Real.exp (-Myproj.eulerMascheroni)
            + (Real.exp (-Myproj.eulerMascheroni) * g x
                - (R₂ x + R₃ x)) := by
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = Real.exp (-Myproj.eulerMascheroni) + R x := by
        simp [R, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hmain_coeff :
      Myproj.cyclicCountingReal (x + h) - Myproj.cyclicCountingReal x ≥
        (h / Real.log z) *
            (Real.exp (-Myproj.eulerMascheroni) + R x) := by
    have hrew :
        (h / Real.log z) *
            (Real.exp (-Myproj.eulerMascheroni) * (1 + R₀ z) * (1 + R₁ x)
              - (R₂ x + R₃ x))
          = (h / Real.log z) * (Real.exp (-Myproj.eulerMascheroni) + R x) := by
      simp [hcoeff_core]
    have := hmain_factored
    simpa [hrew] using this
  have hmain_coeff' :
      Myproj.cyclicCountingReal (x + h) - Myproj.cyclicCountingReal x ≥
        (Real.exp (-Myproj.eulerMascheroni) + R x) * (h / Real.log z) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain_coeff
  have hscale :
      h / Real.log z = (ε * Real.sqrt x) / Real.sqrt (Real.log x) := by
    simp [h, hz_log_eq]
  have hmain_coeff'' :
      Myproj.cyclicCountingReal (x + h) - Myproj.cyclicCountingReal x ≥
        (Real.exp (-Myproj.eulerMascheroni) + R x)
            * ((ε * Real.sqrt x) / Real.sqrt (Real.log x)) := by
    simpa [hscale, mul_comm, mul_left_comm, mul_assoc] using hmain_coeff'
  have hgoal :
      Myproj.cyclicCountingReal (x + h) - Myproj.cyclicCountingReal x ≥
        (Real.exp (-Myproj.eulerMascheroni) + R x)
            * (ε * Real.sqrt x) / Real.sqrt (Real.log x) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmain_coeff''
  simpa [h] using hgoal

end Visser
end Myproj
