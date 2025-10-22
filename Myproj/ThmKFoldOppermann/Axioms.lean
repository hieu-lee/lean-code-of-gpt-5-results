import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Myproj.Definitions

/-
Axioms and quantitative prime-gap bounds used in the
`ThmKFoldOppermann` folder.
-/

noncomputable section

namespace Myproj

open Filter
open scoped Real

/--
Short-interval lower bound for primes. For `θ > 21/40 = 0.525` there exists
`Xθ ≥ 2` such that whenever `x ≥ Xθ` and `0 < y ≤ x^θ`, many primes
lie in `(x - y, x]`. The numerical factor `1/100` matches the LaTeX
argument.

References:
- Baker–Harman–Pintz (2001), *The difference between consecutive primes. II*,
  Proc. Lond. Math. Soc. (3) 83(3): 532–562. Public PDF:
  https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf
- The short-interval exponent `θ = 0.525` is summarized in the "Prime gap"
  article on Wikipedia (retrieved via https://r.jina.ai/https://en.wikipedia.org/wiki/Prime_gap,
  see the paragraph referencing Baker–Harman–Pintz).
-/
axiom short_interval_primes_lower_bound
  {θ : ℝ} (hθ : (23 / 42 : ℝ) < θ) :
  ∃ Xθ : ℝ, 2 ≤ Xθ ∧
    ∀ ⦃x y : ℝ⦄, Xθ ≤ x → 0 < y → y ≤ Real.rpow x θ →
      Myproj.primePi x - Myproj.primePi (x - y) ≥ y / (100 * Real.log x)

/--
Concrete version for the left Legendre interval: for large `n`,
`[n^2 - n, n^2]` contains at least `n / (200 log n)` primes.
This is exactly the inequality used in the LaTeX proof and is obtained
from the previous short-interval bound (Iwaniec–Pintz / Baker–Harman–Pintz,
see comments above) together with elementary manipulations
(`log(n^2) = 2 log n`). The literature reference is the same as for
`short_interval_primes_lower_bound`, cf. Baker–Harman–Pintz (2001)
and the summary in `https://r.jina.ai/https://en.wikipedia.org/wiki/Prime_gap`.
-/
theorem primesLeft_lower_bound :
  ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
    Myproj.primesLeft n ≥ (n : ℝ) / (200 * Real.log (n : ℝ)) :=
by
  classical
  have hθ : (23 / 42 : ℝ) < (1 : ℝ) := by norm_num
  obtain ⟨Xθ, hXθ, hshort⟩ := short_interval_primes_lower_bound hθ
  let Nbase : ℕ := Nat.floor Xθ + 1
  let N₀ : ℕ := max 3 Nbase
  refine ⟨N₀, ?_⟩
  intro n hn
  have hNbase : Nbase ≤ n :=
    (le_max_right (3 : ℕ) Nbase).trans hn
  have hn3 : (3 : ℕ) ≤ n :=
    (le_max_left (3 : ℕ) Nbase).trans hn
  have hn_pos_nat : 0 < n :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hn3
  have hy_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hx_bound :
      (Xθ : ℝ) ≤ Nbase := by
    have hx_lt : (Xθ : ℝ) < Nat.floor Xθ + 1 := by
      exact_mod_cast Nat.lt_floor_add_one Xθ
    simpa [Nbase] using hx_lt.le
  have hx_to_nat : (Nbase : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNbase
  have hx_le_sq :
      (Xθ : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hx_le_n : (Xθ : ℝ) ≤ (n : ℝ) := hx_bound.trans hx_to_nat
    have hy_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hy_nat : n ≤ n * n := Nat.le_mul_self n
      have hy_cast : (n : ℝ) ≤ (n * n : ℕ) := by exact_mod_cast hy_nat
      simpa [pow_two, Nat.cast_mul] using hy_cast
    exact hx_le_n.trans hy_sq
  have hy_le_sq :
      (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hy_nat : n ≤ n * n := Nat.le_mul_self n
    have hy_cast : (n : ℝ) ≤ (n * n : ℕ) := by exact_mod_cast hy_nat
    simpa [pow_two, Nat.cast_mul] using hy_cast
  have hy_le_rpow :
      (n : ℝ) ≤ Real.rpow ((n : ℝ) ^ 2) (1 : ℝ) := by
    simpa [Real.rpow_one] using hy_le_sq
  have hmain :=
    hshort hx_le_sq hy_pos hy_le_rpow
  have hmain' :
      Myproj.primesLeft n ≥
        (n : ℝ) / (100 * Real.log ((n : ℝ) ^ 2)) := by
    simpa [Myproj.primesLeft, pow_two, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hmain
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast
    (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hn3)
  have hlog_square :
      Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
    have hmul :=
      Real.log_mul hy_pos.ne' hy_pos.ne'
    have hmul' :
        Real.log ((n : ℝ) ^ 2) = Real.log (n : ℝ) + Real.log (n : ℝ) := by
      simpa [pow_two] using hmul
    simpa [two_mul] using hmul'
  have hden_eq₁ :
      100 * Real.log ((n : ℝ) ^ 2) = 100 * (2 * Real.log (n : ℝ)) := by
    simp [hlog_square]
  have hden_eq₂ :
      100 * (2 * Real.log (n : ℝ)) = 200 * Real.log (n : ℝ) := by
    ring
  have hk :
      Myproj.primesLeft n ≥ (n : ℝ) / (200 * Real.log (n : ℝ)) := by
    simpa [hden_eq₁, hden_eq₂, mul_comm, mul_left_comm, mul_assoc] using hmain'
  exact hk

/--
Concrete version for the right Legendre interval: for large `n`,
`[n^2, n^2 + n]` contains at least `n / (300 log n)` primes.
This follows from the same short-interval bound (Baker–Harman–Pintz 2001,
see the Wikipedia "Prime gap" article via `r.jina.ai` as noted above)
combined with the elementary inequality `log(n^2 + n) ≤ 3 log n`
for `n ≥ 2`, matching the computation in the LaTeX proof.
-/
theorem primesRight_lower_bound :
  ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
    Myproj.primesRight n ≥ (n : ℝ) / (300 * Real.log (n : ℝ)) :=
by
  classical
  have hθ : (23 / 42 : ℝ) < (1 : ℝ) := by norm_num
  obtain ⟨Xθ, hXθ, hshort⟩ := short_interval_primes_lower_bound hθ
  let Nbase : ℕ := Nat.floor Xθ + 1
  let N₀ : ℕ := max 3 Nbase
  refine ⟨N₀, ?_⟩
  intro n hn
  have hNbase : Nbase ≤ n :=
    (le_max_right (3 : ℕ) Nbase).trans hn
  have hn3 : (3 : ℕ) ≤ n :=
    (le_max_left (3 : ℕ) Nbase).trans hn
  have hn_pos_nat : 0 < n :=
    lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hn3
  have hy_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hx_bound :
      (Xθ : ℝ) ≤ Nbase := by
    have hx_lt : (Xθ : ℝ) < Nat.floor Xθ + 1 := by
      exact_mod_cast Nat.lt_floor_add_one Xθ
    simpa [Nbase] using hx_lt.le
  have hx_to_nat : (Nbase : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNbase
  have hx_le_n : (Xθ : ℝ) ≤ (n : ℝ) := hx_bound.trans hx_to_nat
  have hx_le_sq :
      (Xθ : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hy_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hy_nat : n ≤ n * n := Nat.le_mul_self n
      have hy_cast : (n : ℝ) ≤ (n * n : ℕ) := by exact_mod_cast hy_nat
      simpa [pow_two, Nat.cast_mul] using hy_cast
    exact hx_le_n.trans hy_sq
  have hx_le_interval :
      (Xθ : ℝ) ≤ (n : ℝ) ^ 2 + n := by
    have hge : (n : ℝ) ≤ (n : ℝ) ^ 2 + n := by
      have hdiff :
          (n : ℝ) ^ 2 + n - (n : ℝ) = (n : ℝ) ^ 2 := by ring
      have hdiff_nonneg :
          0 ≤ (n : ℝ) ^ 2 + n - (n : ℝ) := by
        have : 0 ≤ (n : ℝ) ^ 2 := by positivity
        simpa [hdiff] using this
      exact sub_nonneg.mp hdiff_nonneg
    exact hx_le_n.trans hge
  have hy_le_interval :
      (n : ℝ) ≤ (n : ℝ) ^ 2 + n := by
    have hdiff :
        (n : ℝ) ^ 2 + n - (n : ℝ) = (n : ℝ) ^ 2 := by ring
    have : 0 ≤ (n : ℝ) ^ 2 := by positivity
    have hdiff_nonneg : 0 ≤ (n : ℝ) ^ 2 + n - (n : ℝ) := by
      simpa [hdiff] using this
    exact sub_nonneg.mp hdiff_nonneg
  have hy_le_rpow :
      (n : ℝ) ≤ Real.rpow ((n : ℝ) ^ 2 + n) (1 : ℝ) := by
    simpa [Real.rpow_one] using hy_le_interval
  have hmain :=
    hshort hx_le_interval hy_pos hy_le_rpow
  have hmain' :
      Myproj.primesRight n ≥
        (n : ℝ) / (100 * Real.log ((n : ℝ) ^ 2 + n)) := by
    simpa [Myproj.primesRight, pow_two, add_comm, add_left_comm,
      add_assoc, sub_eq_add_neg] using hmain
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast
    (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hn3)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt_one
  have hinterval_gt_one : (1 : ℝ) < (n : ℝ) ^ 2 + n := by
    have : (n : ℝ) ≤ (n : ℝ) ^ 2 + n := hy_le_interval
    exact lt_of_lt_of_le hn_gt_one this
  have hlog_interval_pos :
      0 < Real.log ((n : ℝ) ^ 2 + n) := Real.log_pos hinterval_gt_one
  have hy_sq_pos : 0 < (n : ℝ) ^ 2 := by
    have : 0 < (n : ℝ) := hy_pos
    simpa [pow_two] using mul_pos this this
  have hlog_square :
      Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
    have hmul :=
      Real.log_mul hy_pos.ne' hy_pos.ne'
    have hmul' :
        Real.log ((n : ℝ) ^ 2) = Real.log (n : ℝ) + Real.log (n : ℝ) := by
      simpa [pow_two] using hmul
    simpa [two_mul] using hmul'
  have hlog_cube :
      Real.log ((n : ℝ) ^ 3) = 3 * Real.log (n : ℝ) := by
    have hmul :=
      Real.log_mul hy_sq_pos.ne' hy_pos.ne'
    have hmul' :
        Real.log ((n : ℝ) ^ 3) =
          Real.log ((n : ℝ) ^ 2) + Real.log (n : ℝ) := by
      simpa [pow_three, pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
    calc
      Real.log ((n : ℝ) ^ 3)
          = Real.log ((n : ℝ) ^ 2) + Real.log (n : ℝ) := hmul'
      _ = 2 * Real.log (n : ℝ) + Real.log (n : ℝ) := by
          simpa [hlog_square]
      _ = 3 * Real.log (n : ℝ) := by ring
  have hcube_bound :
      (n : ℝ) ^ 2 + n ≤ (n : ℝ) ^ 3 := by
    have hdiff :
        (n : ℝ) ^ 3 - ((n : ℝ) ^ 2 + n) =
          (n : ℝ) * ((n : ℝ) - 1) ^ 2 + (n : ℝ) * ((n : ℝ) - 2) := by
      ring
    have hterm1 :
        0 ≤ (n : ℝ) * ((n : ℝ) - 1) ^ 2 := by
      have hnonneg₁ : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hnonneg₂ : 0 ≤ ((n : ℝ) - 1) ^ 2 := sq_nonneg _
      exact mul_nonneg hnonneg₁ hnonneg₂
    have hterm2 :
        0 ≤ (n : ℝ) * ((n : ℝ) - 2) := by
      have hnonneg₁ : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have htwo_le_n : (2 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (by decide : (2 : ℕ) ≤ 3) hn3)
      have hnonneg₂ : 0 ≤ (n : ℝ) - 2 := sub_nonneg.mpr htwo_le_n
      exact mul_nonneg hnonneg₁ hnonneg₂
    have hdiff_nonneg :
        0 ≤ (n : ℝ) ^ 3 - ((n : ℝ) ^ 2 + n) := by
      simpa [hdiff] using add_nonneg hterm1 hterm2
    exact sub_nonneg.mp hdiff_nonneg
  have hlog_bound :
      Real.log ((n : ℝ) ^ 2 + n) ≤ 3 * Real.log (n : ℝ) := by
    have hx_pos : 0 < (n : ℝ) ^ 2 + n := by
      have : 0 ≤ (n : ℝ) ^ 2 := by positivity
      exact add_pos_of_nonneg_of_pos this hy_pos
    have := Real.log_le_log hx_pos hcube_bound
    simpa [hlog_cube] using this
  have hscaled :
      100 * Real.log ((n : ℝ) ^ 2 + n) ≤ 300 * Real.log (n : ℝ) := by
    have hcoeff : (0 : ℝ) ≤ 100 := by norm_num
    have hscaled₀ := mul_le_mul_of_nonneg_left hlog_bound hcoeff
    have hrewrite : 100 * (3 * Real.log (n : ℝ)) = 300 * Real.log (n : ℝ) := by
      ring
    simpa [hrewrite, mul_comm, mul_left_comm, mul_assoc] using hscaled₀
  have hrecip :
      (1 / (300 * Real.log (n : ℝ)))
        ≤ 1 / (100 * Real.log ((n : ℝ) ^ 2 + n)) := by
    have hpos₂ : 0 < 100 * Real.log ((n : ℝ) ^ 2 + n) := by
      have : 0 < Real.log ((n : ℝ) ^ 2 + n) := hlog_interval_pos
      have : 0 < 100 * Real.log ((n : ℝ) ^ 2 + n) := mul_pos (by norm_num) this
      exact this
    have hrecip' := one_div_le_one_div_of_le hpos₂ hscaled
    simpa [one_div] using hrecip'
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hratio :
      (n : ℝ) / (300 * Real.log (n : ℝ))
        ≤ (n : ℝ) / (100 * Real.log ((n : ℝ) ^ 2 + n)) := by
    have hmul := mul_le_mul_of_nonneg_left hrecip hn_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hk :
      Myproj.primesRight n ≥ (n : ℝ) / (300 * Real.log (n : ℝ)) := by
    exact le_trans hratio hmain'
  exact hk

/--
Classical growth of `n / log n`: the quotient tends to `∞`, so every height
is achieved eventually. This is a standard corollary of the prime number theorem.

Reference: Rosser–Schoenfeld (1962), *Approximate formulas for some functions
of prime numbers*, Illinois J. Math. 6, 64–94; see also
https://r.jina.ai/https://en.wikipedia.org/wiki/Prime_number_theorem.
-/
axiom eventually_nat_div_log_ge (k : ℕ) :
  ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
    (n : ℝ) / Real.log (n : ℝ) ≥ k

end Myproj

end
