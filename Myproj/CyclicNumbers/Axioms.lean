import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Myproj.Definitions

/-
Global axioms and constants for cyclic-number proofs across the project.
-/

noncomputable section

namespace Myproj

open Filter
open scoped Topology

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

/-- For integers `n > 2` the Euler totient is even. -/
axiom totient_even_of_gt_two {n : ℕ} (hn : 2 < n) : 2 ∣ Nat.totient n

/-! Asymptotic tools used throughout the cyclic-number proofs -/

/-- `L3(n) = log log log n` is slowly varying on naturals. -/
axiom L3_slowly_varying_nat :
  SlowlyVarying (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ))))

/-- Eventual positivity of `L3`. -/
axiom L3_eventually_positive :
  EventuallyPositive (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ))))

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

end
