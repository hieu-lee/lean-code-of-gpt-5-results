import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Myproj.Definitions
import Mathlib.Tactic
import Myproj.CyclicNumbers.Axioms
import Myproj.ThmFiroozbakhtCyclics4.Axioms
import Myproj.ThmIshikawaCyclics.Axioms
import Myproj.ThmVrba.Axioms
import Myproj.ThmHassani.RegularVariation

/-!
This module collects the analytic inputs used in
`theorems/thm_hassani.tex`.  We prove that the real-variable sums
`S(x) = ∑_{c ≤ x} c` and `J(x) = ∑_{c ≤ x} log c` agree with the discrete
enumerator, and record the Karamata- and Abel-type asymptotics required in the
Hassani argument.  References:

* E. Pollack, *Numbers which are orders only of cyclic groups*, Proc. Amer.
  Math. Soc. **150** (2022), 515–524.
* J. Karamata, *Sur un mode de croissance régulière des fonctions*, Mathematica
  (Cluj) **4** (1930), 38–53.  See also the Encyclopedia of Mathematics entry
  “Karamata theory” for the integral asymptotics used below.
* `Mathlib/NumberTheory/AbelSummation` for Abel summation identities.
-/

noncomputable section

namespace Myproj
namespace Hassani

open scoped BigOperators Topology
open Filter Real

/-! ### Real-variable sums S and J

We work with the real-variable sums over cyclic numbers up to `x`:
`S(x) = ∑_{c ≤ x} c` and `J(x) = ∑_{c ≤ x} log c`.
-/

/-- Sum of cyclic numbers up to `x`. -/
def S (x : ℝ) : ℝ :=
  ((Finset.Icc 1 (Nat.floor x)).filter (fun m : ℕ => Myproj.isCyclicNumber m)).sum
    (fun m => (m : ℝ))

/-- Sum of logarithms of cyclic numbers up to `x`. -/
def J (x : ℝ) : ℝ :=
  ((Finset.Icc 1 (Nat.floor x)).filter (fun m : ℕ => Myproj.isCyclicNumber m)).sum
    (fun m => Real.log (m : ℝ))

/-! ### Abel summation inputs (recorded as axioms)

We use standard Abel (partial) summation identities in ratio form with vanishing
errors; these follow from the Riemann–Stieltjes integration-by-parts formula and
boundedness of the boundary terms for monotone `C`.
-/

/-- Ratio-level Abel identity for `S(x)` with vanishing error. -/
axiom abel_S_ratio_error_tendsto_zero :
  Tendsto (fun x : ℝ =>
    S x / (x * Myproj.cyclicCountingReal x)
      - (1 - (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t)
              / (x * Myproj.cyclicCountingReal x))) atTop (𝓝 0)

/-- Ratio-level Abel identity for `J(x)` with vanishing error. -/
axiom abel_J_ratio_error_tendsto_zero :
  Tendsto (fun x : ℝ =>
    J x / Myproj.cyclicCountingReal x
      - (Real.log x
          - (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t / t)
              / Myproj.cyclicCountingReal x)) atTop (𝓝 0)

/-- Natural number underlying the `n`-th cyclic enumerator value. -/
private noncomputable def cNat (n : ℕ) : ℕ :=
  Classical.choose (Myproj.Ishikawa.cyclicEnumerator_spec n)

lemma c_cast (n : ℕ) : Myproj.cyclicEnumerator n = (cNat n : ℝ) :=
  (Classical.choose_spec (Myproj.Ishikawa.cyclicEnumerator_spec n)).1

lemma cNat_isCyclic (n : ℕ) : Myproj.isCyclicNumber (cNat n) :=
  (Classical.choose_spec (Myproj.Ishikawa.cyclicEnumerator_spec n)).2

lemma cNat_strictMono : StrictMono cNat := by
  classical
  intro m n hmn
  have h := Myproj.Ishikawa.cyclicEnumerator_strictMono hmn
  have : (cNat m : ℝ) < (cNat n : ℝ) := by simpa [c_cast] using h
  exact_mod_cast this

lemma cNat_monotone : Monotone cNat :=
  cNat_strictMono.monotone

lemma cNat_one : cNat 1 = 1 := by
  simpa [c_cast] using Myproj.cyclicEnumerator_one

lemma cNat_zero : cNat 0 = 0 := by
  classical
  have hlt :
      (cNat 0 : ℝ) < (cNat 1 : ℝ) := by
    have h := Myproj.Ishikawa.cyclicEnumerator_strictMono (show 0 < 1 by decide)
    simpa [c_cast] using h
  have hlt_nat : cNat 0 < cNat 1 := by exact_mod_cast hlt
  have h1 : cNat 1 = 1 := cNat_one
  have hbound : cNat 0 < 1 := by simpa [h1] using hlt_nat
  have hle : cNat 0 ≤ 0 := by
    have : cNat 0 < 0 + 1 := by simpa using hbound
    exact Nat.lt_succ_iff.mp this
  exact le_antisymm hle (Nat.zero_le _)

lemma succ_le_cNat_succ (k : ℕ) : k.succ ≤ cNat k.succ := by
  have hR : (k.succ : ℝ) ≤ Myproj.cyclicEnumerator k.succ :=
    Myproj.cyclicEnumerator_ge_self k.succ
  have : (k.succ : ℝ) ≤ (cNat k.succ : ℝ) := by simpa [c_cast] using hR
  exact_mod_cast this

lemma floor_cyclicEnumerator (n : ℕ) :
    Nat.floor (Myproj.cyclicEnumerator n) = cNat n := by
  simpa [c_cast] using (Nat.floor_natCast (cNat n))

/-- The cyclic numbers up to `c_n` coincide with the first `n` enumerator values. -/
lemma cyclic_filter_eq_range_image {n : ℕ} (hn : 1 ≤ n) :
    ((Finset.Icc 1 (Nat.floor (Myproj.cyclicEnumerator n))).filter
        (fun m : ℕ => Myproj.isCyclicNumber m))
      = (Finset.range n).image (fun k => cNat k.succ) := by
  classical
  set C :=
      ((Finset.Icc 1 (Nat.floor (Myproj.cyclicEnumerator n))).filter
        (fun m : ℕ => Myproj.isCyclicNumber m)) with hC
  set E := (Finset.range n).image (fun k => cNat k.succ) with hE
  have hfloor := floor_cyclicEnumerator n
  have hsubset₁ : E ⊆ C := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
    have hk_lt : k < n := Finset.mem_range.mp hk
    have hk_succ_le : k.succ ≤ n := Nat.succ_le_of_lt hk_lt
    have hk_bot : 1 ≤ cNat k.succ := by
      have hkpos : 1 ≤ k.succ := Nat.succ_le_of_lt (Nat.zero_lt_succ k)
      exact le_trans hkpos (succ_le_cNat_succ k)
    have hk_top : cNat k.succ ≤ cNat n := cNat_monotone hk_succ_le
    have hk_cyc : Myproj.isCyclicNumber (cNat k.succ) := cNat_isCyclic _
    refine Finset.mem_filter.mpr ?_
    constructor
    · have : cNat k.succ ∈ Finset.Icc 1 (cNat n) := by
        simpa [Finset.mem_Icc, hk_bot, hk_top]
      simpa [C, hfloor] using this
    · simpa [C] using hk_cyc
  have hsubset₂ : C ⊆ E := by
    intro m hm
    have hmem := Finset.mem_filter.mp hm
    have hm_Icc :
        m ∈ Finset.Icc 1 (cNat n) := by
      simpa [C, hfloor] using hmem.1
    have hm_cyc : Myproj.isCyclicNumber m := by
      simpa [C] using hmem.2
    obtain ⟨ℓ, hℓ⟩ := Myproj.Ishikawa.cyclicEnumerator_surjective hm_cyc
    have hℓ_nat : cNat ℓ = m := by
      have := c_cast ℓ
      exact_mod_cast by simpa [hℓ] using this.symm
    have hℓ_le : ℓ ≤ n := by
      by_contra hlt
      have hlt' : n < ℓ := Nat.lt_of_not_ge hlt
      have hstrict := cNat_strictMono hlt'
      have hm_top : m ≤ cNat n := (Finset.mem_Icc.mp hm_Icc).2
      have hℓ_top : cNat ℓ ≤ cNat n := by
        simpa [hℓ_nat] using hm_top
      exact lt_irrefl _ (lt_of_le_of_lt hℓ_top hstrict)
    have hℓ_ne : ℓ ≠ 0 := by
      intro hzero
      have hm_pos : 0 < m := Nat.succ_le_iff.mp (Finset.mem_Icc.mp hm_Icc).1
      have hm_zero : m = 0 := by
        have h : cNat ℓ = m := hℓ_nat
        have h' : cNat 0 = m := by simpa [hzero] using h
        simpa [cNat_zero] using h'.symm
      exact (ne_of_gt hm_pos) hm_zero
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hℓ_ne
    subst hk
    have hk_lt : k < n := Nat.lt_of_succ_le hℓ_le
    have hk_mem : k ∈ Finset.range n := Finset.mem_range.mpr hk_lt
    have hk_val : (fun j : ℕ => cNat j.succ) k = m := by
      simpa [hℓ_nat]
    refine Finset.mem_image.mpr ?_
    exact ⟨k, hk_mem, hk_val⟩
  have hCE : C = E := Finset.Subset.antisymm hsubset₂ hsubset₁
  simpa [C, E]
/-- Arithmetic mean of the first `n` cyclic numbers (set to `0` when `n = 0`). -/
def A (n : ℕ) : ℝ :=
  if hn : n = 0 then 0 else
    (1 / (n : ℝ)) *
      (Finset.range n).sum (fun k => Myproj.cyclicEnumerator k.succ)

/-- Geometric mean of the first `n` cyclic numbers (already set to `1` at `0`). -/
@[simp] def G (n : ℕ) : ℝ := Myproj.cyclicGeomMean n

/--
Compatibility between the real sum `S` and the discrete enumerator.  The proof
is a finite combinatorial argument showing that the filter describing `S` agrees
with the first `n` cyclic numbers.
-/
lemma S_eval_enumerator {n : ℕ} (hn : 1 ≤ n) :
    S (Myproj.cyclicEnumerator n)
      = (Finset.range n).sum (fun k => Myproj.cyclicEnumerator k.succ) := by
  classical
  have hfilter :=
    cyclic_filter_eq_range_image (n := n) hn
  have hsum_image :
      ((Finset.range n).image (fun k => cNat k.succ)).sum
          (fun m : ℕ => (m : ℝ))
        = (Finset.range n).sum (fun k => (cNat k.succ : ℝ)) := by
    refine Finset.sum_image ?_
    intro x hx y hy hxy
    have hsucc := cNat_strictMono.injective hxy
    exact Nat.succ.inj hsucc
  have hS :
      S (Myproj.cyclicEnumerator n)
        = ((Finset.range n).image (fun k => cNat k.succ)).sum
            (fun m : ℕ => (m : ℝ)) := by
    simpa [S, hfilter]
  have hcast :
      (Finset.range n).sum (fun k => (cNat k.succ : ℝ))
        = (Finset.range n).sum (fun k => Myproj.cyclicEnumerator k.succ) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [c_cast]
  simpa [hS, hsum_image, hcast]

/--
Logarithmic compatibility between `J` and the enumerator.  This follows from
`S_eval_enumerator` applied to the logarithmic weights.
-/
lemma J_eval_enumerator {n : ℕ} (hn : 1 ≤ n) :
    J (Myproj.cyclicEnumerator n)
      = (Finset.range n).sum
          (fun k => Real.log (Myproj.cyclicEnumerator k.succ)) := by
  classical
  have hfilter :=
    cyclic_filter_eq_range_image (n := n) hn
  have hsum_image :
      ((Finset.range n).image (fun k => cNat k.succ)).sum
          (fun m : ℕ => Real.log (m : ℝ))
        = (Finset.range n).sum (fun k => Real.log (cNat k.succ : ℝ)) := by
    refine Finset.sum_image ?_
    intro x hx y hy hxy
    have hsucc := cNat_strictMono.injective hxy
    exact Nat.succ.inj hsucc
  have hJ :
      J (Myproj.cyclicEnumerator n)
        = ((Finset.range n).image (fun k => cNat k.succ)).sum
            (fun m : ℕ => Real.log (m : ℝ)) := by
    simpa [J, hfilter]
  have hcast :
      (Finset.range n).sum (fun k => Real.log (cNat k.succ : ℝ))
        = (Finset.range n).sum
            (fun k => Real.log (Myproj.cyclicEnumerator k.succ)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [c_cast]
  simpa [hJ, hsum_image, hcast]

/-- Arithmetic mean along the enumerator: `A_n = S(c_n) / n`. -/
lemma A_eval_enumerator {n : ℕ} (hn : 1 ≤ n) :
    A n = S (Myproj.cyclicEnumerator n) / (n : ℝ) := by
  classical
  have hnpos : 0 < n := Nat.succ_le_iff.mp (by simpa using hn)
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  simp [A, hn0, S_eval_enumerator hn, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Logarithm of the geometric mean along the enumerator. -/
lemma log_G_eval_enumerator {n : ℕ} (hn : 1 ≤ n) :
    Real.log (G n) = J (Myproj.cyclicEnumerator n) / (n : ℝ) := by
  classical
  have hnpos : 0 < n := Nat.succ_le_iff.mp (by simpa using hn)
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnpos
  simp [G, Myproj.cyclicGeomMean, hn0, J_eval_enumerator hn,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hn0', hnpos',
    Myproj.cyclicLogSum]

/-!
### Asymptotic inputs via Abel summation and Karamata's integral theorem
-/

/--
Karamata integral theorem applied to Pollack's asymptotic: the Abel integral of
the counting function satisfies
`(∫₁ˣ C(t) / t dt) / C(x) ⟶ 1`.  See Pollack (2022) together with the
Karamata integral asymptotics for slowly varying functions.
-/
theorem integral_cyclic_over_t_tendsto_one :
    Tendsto (fun x : ℝ =>
        (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t / t)
          / Myproj.cyclicCountingReal x) atTop (𝓝 1) := by
  classical
  have hC :
      (∀ᶠ x in atTop,
        Myproj.cyclicCountingReal x
          = x * (fun y : ℝ => Myproj.cyclicCountingReal y / y) x) :=
    (Filter.eventually_gt_atTop (0 : ℝ)).mono (by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      simp [hx0, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc])
  have hL :
      SlowlyVaryingAtTop (fun x : ℝ => Myproj.cyclicCountingReal x / x) := by
    simpa using Myproj.Hassani.cyclic_over_x_slowly_varying
  simpa using
    integral_over_t_of_regularly_varying
      (L := fun x : ℝ => Myproj.cyclicCountingReal x / x) hC hL

/--
Second Karamata consequence: the integral `∫₁ˣ C(t) dt` is asymptotic to
`x · C(x) / 2`.  Again this is a direct application of Karamata to the Pollack
expansion.
-/
theorem integral_cyclic_tendsto_half :
    Tendsto (fun x : ℝ =>
        (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t)
          / (x * Myproj.cyclicCountingReal x)) atTop (𝓝 (1 / 2 : ℝ)) := by
  classical
  have hC :
      (∀ᶠ x in atTop,
        Myproj.cyclicCountingReal x
          = x * (fun y : ℝ => Myproj.cyclicCountingReal y / y) x) :=
    (Filter.eventually_gt_atTop (0 : ℝ)).mono (by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      simp [hx0, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc])
  have hL :
      SlowlyVaryingAtTop (fun x : ℝ => Myproj.cyclicCountingReal x / x) := by
    simpa using Myproj.Hassani.cyclic_over_x_slowly_varying
  simpa using
    integral_of_regularly_varying_half
      (L := fun x : ℝ => Myproj.cyclicCountingReal x / x) hC hL

/--
Partial summation normalised: `S(x) / (x · C(x)) → 1/2` as `x → ∞`.  This comes
from Abel summation combined with `integral_cyclic_tendsto_half`.
-/
theorem S_over_xC_tendsto_half :
    Tendsto (fun x : ℝ => S x / (x * Myproj.cyclicCountingReal x))
      atTop (𝓝 ((2 : ℝ)⁻¹)) := by
  classical
  -- Abel summation identity with vanishing ratio error (analytic input).
  have abel_S_ratio_error := abel_S_ratio_error_tendsto_zero
  have hint := integral_cyclic_tendsto_half
  -- Set `I(x) := (∫ C(t) dt) / (x · C(x))`.
  have : Tendsto (fun x : ℝ =>
      1 - (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t)
            / (x * Myproj.cyclicCountingReal x)) atTop (𝓝 (1 - (1/2 : ℝ))) := by
    simpa using (tendsto_const_nhds.sub hint)
  -- Combine with the vanishing Abel error.
  have hsum := this.add abel_S_ratio_error
  -- First simplify the left-hand side to `S(x) / (x · C(x))`, keeping the limit value as `1 − 1/2`.
  have hsum' :
      Tendsto (fun x : ℝ => S x / (x * Myproj.cyclicCountingReal x))
        atTop (𝓝 ((1 : ℝ) - (1 / 2 : ℝ))) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  -- Convert the limit value `(1 - 1/2)` to `2⁻¹`.
  have h₂ : (1 : ℝ) - (1 / 2 : ℝ) = ((2 : ℝ)⁻¹) := by
    have : (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) := by norm_num
    simpa [one_div] using this
  simpa only [h₂] using hsum'

/--
Logarithmic partial summation: `J(x) / C(x) - (log x - 1) → 0` as `x → ∞`.
-/
theorem J_over_C_sub_log_tendsto_zero :
    Tendsto (fun x : ℝ =>
        J x / Myproj.cyclicCountingReal x - (Real.log x - 1)) atTop (𝓝 0) := by
  classical
  -- Abel summation identity with vanishing ratio error (analytic input).
  have abel_J_ratio_error := abel_J_ratio_error_tendsto_zero
  have hint := integral_cyclic_over_t_tendsto_one
  -- The difference `(log x - I₀(x)) - (log x - 1)` tends to `0` since `I₀(x) → 1`.
  have hdiff : Tendsto (fun x : ℝ =>
      (Real.log x - (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t / t)
          / Myproj.cyclicCountingReal x)
        - (Real.log x - 1)) atTop (𝓝 0) := by
    -- `I₀(x) := (∫ C(t)/t) / C(x) → 1`, so `1 - I₀(x) → 0`.
    have hI0' : Tendsto (fun x : ℝ =>
        (1 : ℝ) - (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t / t)
          / Myproj.cyclicCountingReal x) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _x : ℝ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
        tendsto_const_nhds
      have hsub := hconst.sub hint
      simpa using hsub
    -- The difference of interest equals `1 - I₀(x)` pointwise.
    have : (fun x : ℝ =>
        (Real.log x - (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t / t)
            / Myproj.cyclicCountingReal x)
          - (Real.log x - 1))
        = (fun x : ℝ =>
            (1 : ℝ) - (∫ t in (1 : ℝ)..x, Myproj.cyclicCountingReal t / t)
              / Myproj.cyclicCountingReal x) := by
      funext x; ring
    simpa [this]
  -- Add the vanishing Abel error.
  have hsum := hdiff.add abel_J_ratio_error
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum

end Hassani
end Myproj
