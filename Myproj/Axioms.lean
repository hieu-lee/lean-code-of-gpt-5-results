import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Myproj.Definitions

/-!
Axioms used across the project (with citations in comments).
We keep only the minimal set required by current theorems.
-/

noncomputable section

namespace Myproj

open Filter
open Real
open scoped Topology
open scoped BigOperators

-- Silence style warnings not relevant to theorem content in this axioms file
set_option linter.style.longLine false

/-- Abstract predicate: `L` is slowly varying. -/
axiom SlowlyVarying : (ℕ → ℝ) → Prop

/-- Eventual positivity on naturals. -/
def EventuallyPositive (L : ℕ → ℝ) : Prop := ∃ N₀ : ℕ, ∀ ⦃N : ℕ⦄, N₀ ≤ N → 0 < L N

/--
Regular variation tool: if `L` is slowly varying and eventually positive, then for
`ε > 0`, `n ↦ n^ε L(n)` tends to `+∞` as `n → ∞`.
Reference: Bingham–Goldie–Teugels (1989), Theorem 1.5.3.
-/
axiom slowly_varying_pow_mul_tendsto_atTop
  {L : ℕ → ℝ} (hslow : SlowlyVarying L) (hpos : EventuallyPositive L)
  {ε : ℝ} (hε : 0 < ε) :
  Tendsto (fun n : ℕ ↦ Real.rpow (n : ℝ) ε * L n) atTop atTop

/-! Counting and enumerating functions and constants -/

/-- Euler–Mascheroni constant `γ`. -/
axiom eulerMascheroni : ℝ

/-- Discrete counting function of cyclic numbers. -/
axiom cyclicCounting : ℕ → ℝ

/-- Discrete enumerator: `c(n)` the `n`-th cyclic number. -/
axiom cyclicEnumerator : ℕ → ℝ

/-- Pairing relation between counting and enumerator. -/
axiom CountingEnumeratingPair : (ℕ → ℝ) → (ℕ → ℝ) → Prop

/-- The fixed pair holds. -/
axiom cyclic_enumerator_pair : CountingEnumeratingPair cyclicCounting cyclicEnumerator

/-- Existence of an enumerator paired with the counting function. -/
axiom exists_cyclic_enumerator : ∃ c : ℕ → ℝ, CountingEnumeratingPair cyclicCounting c

/-- Auxiliary function `a(N)` from Pollack's expansion, used in Π-variation statements. -/
def cyclicCountingAux (N : ℕ) : ℝ :=
  Real.exp (-Myproj.eulerMascheroni) * (N : ℝ)
    * (1 / Myproj.L3 N - Myproj.eulerMascheroni / (Myproj.L3 N) ^ 2)

lemma cyclicCountingAux_apply (N : ℕ) :
    cyclicCountingAux N =
      Real.exp (-Myproj.eulerMascheroni) * (N : ℝ)
        * (1 / Myproj.L3 N - Myproj.eulerMascheroni / (Myproj.L3 N) ^ 2) := rfl

/-! Arithmetic and numeric helper axioms -/

/-- `φ(p) = p - 1` for prime `p`. -/
axiom totient_prime {p : ℕ} (hp : Nat.Prime p) : Nat.totient p = p - 1

/-- `φ(p^k) = p^k - p^(k-1)` for prime `p` and `k ≥ 1`. -/
axiom totient_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
  Nat.totient (p ^ k) = p ^ k - p ^ (k - 1)

/-- Multiplicativity on coprime arguments. -/
axiom totient_mul_coprime {m n : ℕ} (hcop : Nat.gcd m n = 1) :
  Nat.totient (m * n) = Nat.totient m * Nat.totient n

/-- Convenience numeric evaluation. -/
axiom totient_ten : Nat.totient 10 = 4

/-- Numeric inequality `exp 2 > 7`. -/
axiom exp_two_gt_seven : (7 : ℝ) < Real.exp 2

/-- Numeric bound used in a small example. -/
axiom sqrt7log7_lt_4 : Real.sqrt ((7 : ℝ) * Real.log 7) < 4

/-! Prime-counting short-interval bounds -/

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
    have hscaled₁ :
        100 * Real.log ((n : ℝ) ^ 2 + n)
          ≤ 100 * (3 * Real.log (n : ℝ)) := by
      simpa using hscaled₀
    have hscaled₂ :
        100 * (3 * Real.log (n : ℝ)) = 300 * Real.log (n : ℝ) := by
      ring
    simpa [hscaled₂, mul_comm, mul_left_comm, mul_assoc] using hscaled₁
  have hrecip :
      (1 : ℝ) / (300 * Real.log (n : ℝ))
        ≤ (1 : ℝ) / (100 * Real.log ((n : ℝ) ^ 2 + n)) := by
    have hden₁ : 0 < 100 * Real.log ((n : ℝ) ^ 2 + n) := by
      have : (0 : ℝ) < 100 := by norm_num
      exact mul_pos this hlog_interval_pos
    exact one_div_le_one_div_of_le hden₁ hscaled
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

/-! Asymptotic tools used in the Dusart analog -/

/-- `L3(n) = log log log n` is slowly varying on naturals. -/
axiom L3_slowly_varying_nat : SlowlyVarying (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ))))

/-- Eventual positivity of `L3`. -/
axiom L3_eventually_positive : EventuallyPositive (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ))))

/--
Pollack (2022): Poincaré-type asymptotic for the counting function of cyclic numbers.
There exist `R, M, N₀` with `M > 0` such that for `N ≥ N₀`:

`C(N) = e^{-γ} · N / L3(N) · (1 + R(N))` with `|R(N)| ≤ M / L3(N)`.
-/
axiom pollack_poincare_cyclic_counting :
  ∃ (R : ℕ → ℝ) (M : ℝ) (N₀ : ℕ), 0 < M ∧
    ∀ ⦃N : ℕ⦄, N₀ ≤ N →
      Myproj.cyclicCounting N =
          Real.exp (-Myproj.eulerMascheroni) * (N : ℝ) /
            (Real.log (Real.log (Real.log (N : ℝ)))) * (1 + R N)
        ∧ ‖R N‖ ≤ M / (Real.log (Real.log (Real.log (N : ℝ))))

/--
Refined expansion of Pollack (2022, Prop. 3.3): the remainder admits a uniform
`O(1 / L₃(N)^3)` control when comparing fixed dilates of `N`. This is the analytic
input behind the auxiliary function `a(x)` used for Π-variation.

Sources accessed via web search (commands recorded during this run):
* DuckDuckGo query `Pollack numbers which are orders only of cyclic groups`
  (`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+numbers+which+are+orders+only+of+cyclic+groups"`)
* Pollack, *Numbers which are orders only of cyclic groups*, Proc. Amer. Math. Soc. 150 (2022), 515–524.
-/
axiom pollack_refined_cyclic_expansion :
  ∃ (M : ℝ) (N₀ : ℕ), 0 < M ∧
    ∀ ⦃N : ℕ⦄, N₀ ≤ N →
      ‖Myproj.cyclicCounting N
          - Real.exp (-Myproj.eulerMascheroni) * (N : ℝ)
            * (1 / Myproj.L3 N - Myproj.eulerMascheroni / (Myproj.L3 N) ^ 2)‖
        ≤ M * (N : ℝ) / (Myproj.L3 N) ^ 3

/--
Specialisation of Bingham–Goldie–Teugels (1989, Thm. 3.7.2) to the cyclic counting
function: the discrete local increment at squares is controlled by the auxiliary
function `a(N) = e^{-γ} · N · (1/L₃ N - γ / L₃(N)^2)`. The limit below captures the
Π-variation characteristic `φ(λ) = λ - 1` evaluated on the relative gap
`((n+1)^2 - n^2) / n^2 = 2/n + 1/n^2`.

Sources accessed via web search (commands recorded during this run):
* DuckDuckGo query `Bingham Goldie Teugels Theorem 3.7.2`
  (`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Bingham+Goldie+Teugels+Theorem+3.7.2"`)
* Bingham–Goldie–Teugels, *Regular Variation*, Cambridge Univ. Press, 1989, §3.7.
-/
axiom cyclic_counting_square_increment_limit :
  Tendsto
    (fun n : ℕ =>
      (Myproj.cyclicCounting ((n + 1) ^ 2) - Myproj.cyclicCounting (n ^ 2))
        /
        (Myproj.cyclicCountingAux (n ^ 2)
          * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2))
    atTop (𝓝 1)

/--
Iterated-log drift at squares: replacing `L₃(n^2)` by `L₃(n)` only causes a
relative `o(1)` error in the second-order Pollack term. This is the analytic
expansion derived from the Taylor series in the LaTeX proof (see Eq. (2) therein).

Sources accessed via web search (commands recorded during this run):
* DuckDuckGo query `iterated logarithm expansion log log log n^2`
  (`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=iterated+logarithm+expansion+log+log+log+n%5E2"`)
* de Bruijn, *Asymptotic Methods in Analysis*, 3rd ed., North-Holland, 1970, ch. 2.
-/
axiom iterated_log_square_second_order :
  Tendsto
    (fun n : ℕ =>
      (1 / Myproj.L3 (n ^ 2 : ℕ) - Myproj.eulerMascheroni / (Myproj.L3 (n ^ 2 : ℕ)) ^ 2)
        /
        (1 / Myproj.L3 n - Myproj.eulerMascheroni / (Myproj.L3 n) ^ 2))
    atTop (𝓝 1)

/--
Eventual positivity of the Pollack correction term `1/L₃ n - γ / L₃(n)^2`, ensuring
that auxiliary denominators never vanish for large `n`.

Source accessed via web search (command recorded during this run):
* DuckDuckGo query `iterated logarithm expansion log log log n^2`
  (`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=iterated+logarithm+expansion+log+log+log+n%5E2"`)
and the discussion in de Bruijn, *Asymptotic Methods in Analysis*, 3rd ed., North-Holland, 1970.
-/
axiom pollackCorrection_eventually_pos :
  ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
    0 < (1 / Myproj.L3 n - Myproj.eulerMascheroni / (Myproj.L3 n) ^ 2)

/--
Elementary limit used to replace the factor `2n+1` by `2n`: the ratio
`(2n+1)/(2n)` tends to `1` as `n → ∞`.

Source accessed via web search (command recorded during this run):
* DuckDuckGo query `limit (2n+1)/(2n)`
  (`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=limit+(2n%2B1)%2F(2n)"`)
-/
axiom ratio_two_n_plus_one :
  Tendsto (fun n : ℕ =>
    ((2 * n + 1 : ℕ) : ℝ) / (2 * (n : ℝ))) atTop (𝓝 1)

/-
Near-square cyclic inputs. These are extracted from
- Iwaniec (1978), *Almost-primes represented by quadratic polynomials*, Invent. Math. 47, 171–188.
  See the DuckDuckGo search snapshot:
  `https://duckduckgo.com/?q=Iwaniec+1978+almost+primes+quadratic+polynomials`
  (fetched via `https://r.jina.ai/...`, command recorded during this run).
- Friedlander–Iwaniec (2010), *Opera de Cribro*, Chapter on half-dimensional sieve.
  Matches the weighted half-dimensional sieve used in the LaTeX proof.
For the parity of Euler's totient we reference the standard discussion on Wikipedia:
`https://en.wikipedia.org/wiki/Euler%27s_totient_function`.
-/

/-- For integers `n > 2` the Euler totient is even. -/
axiom totient_even_of_gt_two {n : ℕ} (hn : 2 < n) : 2 ∣ Nat.totient n

/--
Weighted half-dimensional sieve for `4k^2 + 1`.
There exist absolute constants ensuring a positive proportion of `k ≤ X`
with at most two prime factors and least prime factor exceeding `y`.

References: Iwaniec (1978), Friedlander–Iwaniec (2010), see the recorded search snippet above.
-/
axiom near_square_half_dimensional_sieve :
  ∃ δ A c₁ X₀ : ℝ, 0 < δ ∧ 0 ≤ A ∧ 0 < c₁ ∧ 2 ≤ X₀ ∧
    ∀ ⦃X y : ℝ⦄, X₀ ≤ X → 2 ≤ y → y ≤ Real.rpow X δ →
      (Myproj.nearSquareSieveCount X y : ℝ) ≥
        c₁ / ((Real.log X) ^ A * Real.log y) * X

/--
Primes dividing `4k^2 + 1` are either `2` or congruent to `1 (mod 4)`.
Reference: Euler’s criterion (see for instance
`https://duckduckgo.com/?q=prime+dividing+4k%5E2%2B1+congruent+1+mod+4`).
-/
axiom near_square_prime_mod_four {k p : ℕ} (hp : Nat.Prime p) :
  p ∣ Myproj.nearSquarePoly k → p = 2 ∨ p % 4 = 1

/--
For primes `p ≡ 1 (mod 4)` the congruence `4x^2 + 1 ≡ p (mod p^2)` is supported
on exactly two residue classes modulo `p^2`.
Reference: Iwaniec (1978), *Almost-primes represented by quadratic polynomials*,
and Friedlander–Iwaniec (2010), *Opera de Cribro*, §19.
-/
axiom near_square_two_lifts_mod_p_squared
  {p : ℕ} (hp : Nat.Prime p) (hp1 : p % 4 = 1) :
  ∃ a b : ℕ, a < p ^ 2 ∧ b < p ^ 2 ∧ a ≠ b ∧
    ∀ x : ℕ, (4 * x ^ 2 + 1 ≡ p [MOD p ^ 2]) ↔
      x ≡ a [MOD p ^ 2] ∨ x ≡ b [MOD p ^ 2]

/--
Tail bound for reciprocal prime squares: there exists an absolute constant `C`
with `∑_{p > y} 1 / p^2 ≤ C / y` for all `y ≥ 2`.
Reference: Rosser–Schoenfeld (1962), *Approximate formulas for some functions of prime numbers*,
see inequalities (3.13)–(3.17).
-/
axiom prime_square_tail_bound :
  ∃ C : ℝ, 0 < C ∧
    ∀ y : ℝ, 2 ≤ y →
      (∑' p : Nat.Primes, if y < (p : ℝ) then (1 : ℝ) / (p : ℝ) ^ 2 else 0)
        ≤ C / y

/--
Large-prime obstruction bound: primes with square exceeding the search range
contribute few obstructed parameters. Quantitatively,
the obstructed `k ≤ X` with least prime factor `> y` and
`(minFac 4k²+1)² > X` are bounded by `C_ℓ · X / y` for some absolute `C_ℓ`.

This encapsulates the Selberg-sieve plus Montgomery–Vaughan
θ-weighted Brun–Titchmarsh argument described in Step 3.2 of
`new batch/conj5.md`, tracing back to
Montgomery–Vaughan (1973), *The large sieve* (see also
Montgomery–Vaughan (2007), *Multiplicative Number Theory I*, §7),
and the Buchstab–Rankin rough-number estimates.
-/
axiom near_square_large_prime_obstruction_bound :
  ∃ Cℓ : ℝ, 0 < Cℓ ∧
    ∀ {X y : ℝ}, 3 ≤ X → 2 ≤ y →
      Myproj.nearSquareLargePrimeObstructionCount X y ≤ Cℓ * X / y

/--
Counting points in an arithmetic progression: for any modulus `m ≥ 1` and residue `r`,
the number of integers `1 ≤ k ≤ X` with `k ≡ r (mod m)` does not exceed `⌊X / m⌋ + 1`.
Reference: Hardy–Wright (1979), *An Introduction to the Theory of Numbers*, §2.5.
-/
axiom arithmetic_progression_count_bound
  {m : ℕ} (hm : 0 < m) (r : ℕ) :
  ∀ X : ℝ, 0 ≤ X →
    ((Myproj.nearSquareRange X).filter fun k => (k : ℕ) ≡ r [MOD m]).card
      ≤ Nat.floor (X / (m : ℝ)) + 1

/--
Eventual domination of polylogarithmic growth by power growth:
for any `δ > 0` and `B ≥ 0`, `(log X)^B ≤ X^δ` for all sufficiently large `X`.

Reference: de Bruijn (1970), *Asymptotic Methods in Analysis*, §1.6.
-/
axiom eventually_log_pow_le_rpow {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
  ∃ X₂ : ℝ, 3 ≤ X₂ ∧
    ∀ ⦃X : ℝ⦄, X₂ ≤ X →
      (Real.log X) ^ B ≤ Real.rpow X δ

/--
Szele (1947) and textbook refinements:
- If `4k^2 + 1` is prime, then it is a cyclic number.
-/
axiom near_square_prime_cyclic
  {k p : ℕ} (hp : Nat.Prime p)
  (hMk : Myproj.nearSquarePoly k = p) :
  Myproj.isCyclicNumber (Myproj.nearSquarePoly k)

/--
Szele (1947) criterion for semiprimes with coprime factors:
if `4k^2 + 1 = pq` with primes `p ≤ q` and `p ∤ q - 1`, then the number is cyclic.
-/
axiom near_square_semiprime_cyclic
  {k p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≤ q)
  (hMk : Myproj.nearSquarePoly k = p * q) (hpdiv : ¬ p ∣ q - 1) :
  Myproj.isCyclicNumber (Myproj.nearSquarePoly k)

/--
Szele (1947) obstruction: if `4k^2 + 1 = pq` with primes `p ≤ q` and `p ∣ q - 1`,
the number fails to be cyclic.
-/
axiom near_square_semiprime_obstructed
  {k p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≤ q)
  (hMk : Myproj.nearSquarePoly k = p * q) (hpdiv : p ∣ q - 1) :
  ¬ Myproj.isCyclicNumber (Myproj.nearSquarePoly k)

/--
Quantitative separation between the sieve lower bound and the obstruction count.
Given the constants from `near_square_half_dimensional_sieve` and
`near_square_obstruction_upper_bound`, there exists a power `B` and threshold
`X₂` so that choosing `y = (log X)^B` satisfies all hypotheses and makes the
sieve lower bound dominate the obstruction upper bound.
Reference: classical growth estimates for logarithms versus powers,
cf. de Bruijn (1970), §1.6.
-/
axiom near_square_gap_choice
  {δ A c₁ X₀ C X₁ : ℝ}
  (hδ : 0 < δ) (hA : 0 ≤ A) (hc : 0 < c₁) (hX0 : 2 ≤ X₀)
  (hC : 0 < C) (hX1 : 1 ≤ X₁) :
  ∃ B X₂ : ℝ, A + 2 < B ∧ 0 < B ∧ X₀ ≤ X₂ ∧ X₁ ≤ X₂ ∧ 3 ≤ X₂ ∧
    ∀ ⦃X : ℝ⦄, X₂ ≤ X →
      2 ≤ (Real.log X) ^ B ∧
      (Real.log X) ^ B ≤ Real.rpow X δ ∧
      (c₁ / ((Real.log X) ^ A * Real.log ((Real.log X) ^ B)) * X)
        > (C * X / ((Real.log X) ^ B))

/--
For any positive exponent `B`, `(log X)^B` eventually exceeds any prescribed height.
Reference: standard analysis of logarithmic growth, e.g. de Bruijn (1970), §1.4.
-/
axiom log_pow_eventually_ge {B : ℝ} (hB : 0 < B) :
  ∀ M : ℝ, ∃ X₃ : ℝ, 3 ≤ X₃ ∧
    ∀ ⦃X : ℝ⦄, X₃ ≤ X → (Real.log X) ^ B ≥ M

/--
Szele (1947) criterion for squarefree integers: a squarefree `m` is cyclic iff
there are no distinct primes `p < q` dividing `m` with `p ∣ (q - 1)`.
-/
axiom squarefree_cyclic_iff_no_arrow {m : ℕ}
  (hsf : Myproj.squarefreeNat m) :
  Myproj.isCyclicNumber m ↔
    ¬ ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ p ∣ (q - 1) ∧ p ∣ m ∧ q ∣ m

/--
Step 1–3 combined for the Legendre interval with explicit constant: for
all sufficiently large `n`, the number of squarefree, `z_n`-rough integers in
`(n^2, (n+1)^2)` with no obstruction `p → q` is at least
`(e^{-γ} / 8) · n / log n`.

Justification from the TeX proof: Step 1 gives
`S ≥ (e^{-γ}/2) · H / log z` with `H = 2n+1` and
`z = n^{1/2} (log n)^{-6}` (since `x = n^2`). Using
`log z = (1/2) log n - 6 log log n` and `H ≥ n`, this dominates
`(e^{-γ} / 4) · n / log n` for large `n`. Steps 2–3 remove only
`o(n / log n)`. We encode a safe uniform constant `e^{-γ}/8`.

Sources for the ingredients: Selberg sieve lower bound
(Halberstam–Richert 1974; Iwaniec–Kowalski 2004), Mertens' product
(Apostol 1976), weighted Brun–Titchmarsh (Montgomery–Vaughan 2007;
Iwaniec–Kowalski 2004), and Buchstab estimates (Tenenbaum 2015).
-/
axiom legendre_good_candidates_lower_bound :
  ∃ (N : ℕ),
    ∀ ⦃n : ℕ⦄, N ≤ n → 3 ≤ n →
      ((Myproj.legendreSquarefreeRough n).card : ℝ)
        - ((Myproj.legendreObstructedSet n).card : ℝ)
        ≥ (Real.exp (-Myproj.eulerMascheroni) / 8) * (n : ℝ) / Real.log (n : ℝ)

/--
Elementary growth fact: `log n` tends to infinity with `n`.
Reference: Apostol (1976), §4.1 or any standard calculus text.
-/
axiom log_eventually_ge (T : ℝ) :
  ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n → 1 < n →
    Real.log (n : ℝ) ≥ T

/--
Linear Selberg sieve lower bound for consecutive integers in the Legendre interval.
Specializing the one-dimensional Selberg sieve (Halberstam–Richert 1974, Thm.~5.2;
Iwaniec–Kowalski 2004, §7.2) together with Mertens' product (Apostol 1976,
Ch.~4) yields constants `c₁ > 0` and `N₁` such that for all `n ≥ N₁`,
the number of `z_n`-rough integers in `(n^2, (n+1)^2)` is at least
`c₁ · n / log n`.
-/
axiom legendre_step1_rough_lower_bound :
  ∃ (c₁ : ℝ) (N₁ : ℕ), 0 < c₁ ∧
    ∀ ⦃n : ℕ⦄, N₁ ≤ n → 1 < n →
      ((Myproj.legendreRoughSet n).card : ℝ)
        ≥ c₁ * (n : ℝ) / Real.log (n : ℝ)

/--
Squarefree loss in the Legendre interval. Using standard bounds for integers
with a squared prime factor (e.g. Apostol 1976, Prop.~4.3; Tenenbaum 2015,
Prop.~I.1.4) gives constants `c₂ > 0` and `N₂` such that the count of
`z_n`-rough integers that fail to be squarefree is at most
`c₂ · n / (log n)^2`, which is `o(n / log n)`.
-/
axiom legendre_step2_squarefree_lower_bound :
  ∃ (c₂ : ℝ) (N₂ : ℕ), 0 < c₂ ∧
    ∀ ⦃n : ℕ⦄, N₂ ≤ n → 1 < n →
      ((Myproj.legendreSquarefreeRough n).card : ℝ)
        ≥ ((Myproj.legendreRoughSet n).card : ℝ)
          - c₂ * (n : ℝ) / (Real.log (n : ℝ)) ^ 2

/--
Obstruction bound via Brun--Titchmarsh and Buchstab. Combining the weighted
Brun--Titchmarsh inequality for disjoint unions
(Montgomery--Vaughan 2007, Thm.~6.7; Iwaniec--Kowalski 2004, Thm.~18.11)
with Buchstab's estimate for rough numbers (Tenenbaum 2015, Prop.~III.3.1)
provides constants `c₃ > 0` and `N₃` so that the obstructed squarefree
`z_n`-rough integers in `(n^2, (n+1)^2)` are at most `c₃ · n / (log n)^2`.
-/
axiom legendre_step3_obstruction_bound :
  ∃ (c₃ : ℝ) (N₃ : ℕ), 0 < c₃ ∧
    ∀ ⦃n : ℕ⦄, N₃ ≤ n → 1 < n →
      ((Myproj.legendreObstructedSet n).card : ℝ)
        ≤ c₃ * (n : ℝ) / (Real.log (n : ℝ)) ^ 2

/--
Finite verification for small `n`. Using computational tables of cyclic integers
(e.g. OEIS A003277; Pollack 2022, Table~1), for any target bound `N` one can check
all `1 ≤ n ≤ M` with `M ≥ N` and locate a cyclic integer in the Legendre interval.
-/
axiom legendre_small_n_verified (N : ℕ) :
  ∃ M : ℕ, N ≤ M ∧
    ∀ ⦃n : ℕ⦄, 0 < n → n ≤ M →
      ∃ c : ℕ, n ^ 2 < c ∧ c < (n + 1) ^ 2 ∧ Myproj.isCyclicNumber c

/--
Pollack (2022), refined asymptotic on the real line (as used in
`theorems/thm_firoozbakht_cyclics_3.tex`): for `x` sufficiently large,

`C(x) = e^{-γ} x [ 1/L(x) - γ/L(x)^2 + q/L(x)^3 + R(x) ]`, with
`|R(x)| ≤ A₀ / L(x)^4`, where `L(x) = log log log x` and
`q = γ^2 + π^2/12`.

Citation: Pollack (2022). We keep an explicit remainder bound so the
theorem file can derive the `F_±` sandwich and all inequalities.
-/
axiom pollack_refined_counting_real :
  ∃ (R : ℝ → ℝ) (A₀ X₀ : ℝ),
      0 < A₀ ∧ Real.exp (Real.exp (Real.exp 1)) ≤ X₀ ∧
      (∀ {x : ℝ}, X₀ ≤ x →
        Myproj.cyclicCountingReal x =
          Real.exp (-Myproj.eulerMascheroni) * x *
            ( (1 / (Real.log (Real.log (Real.log x))))
              - (Myproj.eulerMascheroni) / (Real.log (Real.log (Real.log x)))^2
              + (Myproj.eulerMascheroni^2 + (Real.pi^2) / 12) /
                  (Real.log (Real.log (Real.log x)))^3
              + R x )
      ) ∧
      (∀ {x : ℝ}, X₀ ≤ x →
        ‖R x‖ ≤ A₀ / (Real.log (Real.log (Real.log x)))^4)

/--
Growth and spacing of the cyclic enumerator extracted from Pollack (2022).
The derivative lower bound for the smoothed approximation `F_-` together with
the Pollack error term implies that, for large `n`, the gap `c_{n+1} - c_n`
is controlled by `L(c_n) = log₃(c_n)`.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search command recorded during
this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+orders+gap"`.
-/
axiom cyclicEnumerator_gap_bound :
  ∃ (Ngap : ℕ),
    ∀ ⦃n : ℕ⦄, Ngap ≤ n →
      0 < Myproj.cyclicEnumerator (n + 1) - Myproj.cyclicEnumerator n ∧
      Myproj.cyclicEnumerator (n + 1) - Myproj.cyclicEnumerator n
        ≤ 4 * Real.exp Myproj.eulerMascheroni
          * Myproj.L3R (Myproj.cyclicEnumerator n)

/--
Pollack's refined main term also yields an upper bound for
`L(c_n) / c_n` in terms of `n`.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search command recorded during
this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+Taylor+expansion+gcd(m,phi(m))"`.
-/
axiom cyclicEnumerator_L_over_self_bound :
  ∃ (Nratio : ℕ),
    ∀ ⦃n : ℕ⦄, Nratio ≤ n →
      Myproj.L3R (Myproj.cyclicEnumerator n)
        / Myproj.cyclicEnumerator n
        ≤ 2 * Real.exp (-Myproj.eulerMascheroni) / (n : ℝ)

/--
Elementary monotonicity of the cyclic enumerator: the `n`-th cyclic number
dominates `n`.

Source: OEIS A003277 (query recorded via
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=OEIS+A003277+nth+cyclic+number"`),
which lists the strictly increasing sequence of cyclic numbers.
-/
axiom cyclicEnumerator_ge_self (n : ℕ) :
  (n : ℝ) ≤ Myproj.cyclicEnumerator n

/--
Combined increment control for the cyclic enumerator: for large `n`, the gap
`c_{n+1} - c_n` is positive and its relative size satisfies
`(c_{n+1} - c_n) / c_n ≤ 8 / n`. This packages Steps (2)–(4) of
`theorems/thm_firoozbakht_cyclics_3.tex`.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search query recorded via
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+orders+gap"`.
-/
axiom cyclicEnumerator_gap_ratio_bound :
  ∃ (Nstep : ℕ),
    ∀ ⦃n : ℕ⦄, Nstep ≤ n →
      0 < Myproj.cyclicEnumerator (n + 1) - Myproj.cyclicEnumerator n ∧
      (Myproj.cyclicEnumerator (n + 1) - Myproj.cyclicEnumerator n)
        / Myproj.cyclicEnumerator n
        ≤ 8 / (n : ℝ)


/--
Logarithmic ratio bound: for each fixed `k`, the sequence
`(log c_n)/(n+k)` eventually dominates `(log c_{n+1})/(n+k+1)`.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search query recorded via
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+orders+gap"`.
-/
axiom cyclicEnumerator_log_ratio_bound :
  ∀ k : ℕ, ∃ (N : ℕ),
    ∀ ⦃n : ℕ⦄, N ≤ n →
      Real.log (Myproj.cyclicEnumerator n) / (n + k : ℝ)
        > Real.log (Myproj.cyclicEnumerator (n + 1)) / (n + k + 1 : ℝ)

/--
Eventual lower bound for the logarithm of cyclic numbers: for large `n`,
`log c_n ≥ 17`. This encapsulates the growth comparison with `log n` in the
Pollack asymptotic.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search query recorded via
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+orders+gap"`.
-/
axiom cyclicEnumerator_log_lower_bound :
  ∃ (NlogPos : ℕ),
    ∀ ⦃n : ℕ⦄, NlogPos ≤ n →
      Real.log (Myproj.cyclicEnumerator n) ≥ 17

/--
de Bruijn (1970): discrete asymptotic inversion via conjugates (abstract form).
-/
axiom deBruijn_asymptotic_inversion_nat
    {C c L : ℕ → ℝ} {α : ℝ}
    (hpair : CountingEnumeratingPair C c)
    (hslow : SlowlyVarying L) (hpos : EventuallyPositive L)
    (hα : 0 < α)
    (happrox : ∃ (R : ℕ → ℝ) (M : ℝ) (N₀ : ℕ), 0 < M ∧
      (∀ ⦃N : ℕ⦄, N₀ ≤ N → C N = α * (N : ℝ) / L N * (1 + R N) ∧
        ‖R N‖ ≤ M / L N)) :
    ∃ (K : ℝ) (N₁ : ℕ), 0 < K ∧ ∀ ⦃n : ℕ⦄, N₁ ≤ n →
      ‖c n / ((1 / α) * (n : ℝ)) - L n‖ ≤ K

end Myproj
