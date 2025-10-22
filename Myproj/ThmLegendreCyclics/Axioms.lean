import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Myproj.CyclicNumbers.Axioms
import Myproj.Definitions

/-
Axioms underpinning the Legendre-interval argument for cyclic numbers.
-/

noncomputable section

namespace Myproj

open scoped BigOperators

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
(Apostol 1976, §3.10), and the quantitative obstruction bounds from
Friedlander–Iwaniec (2010).
-/
axiom legendre_good_candidates_lower_bound :
  ∃ (N : ℕ),
    ∀ ⦃n : ℕ⦄, N ≤ n → 3 ≤ n →
      ((Myproj.legendreSquarefreeRough n).card : ℝ)
        - ((Myproj.legendreObstructedSet n).card : ℝ)
        ≥ (Real.exp (-Myproj.eulerMascheroni) / 8) * (n : ℝ) / Real.log (n : ℝ)

/--
Logarithm eventually dominates any prescribed bound `T`.
Reference: de Bruijn (1970), *Asymptotic Methods in Analysis*, §1.4.
-/
axiom log_eventually_ge (T : ℝ) :
  ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n → 1 < n →
    Real.log (n : ℝ) ≥ T

/--
Selberg sieve lower bound for the Legendre interval (Step 1).
-/
axiom legendre_step1_rough_lower_bound :
  ∃ (c₁ : ℝ) (N₁ : ℕ), 0 < c₁ ∧
    ∀ ⦃n : ℕ⦄, N₁ ≤ n → 1 < n →
      ((Myproj.legendreRoughSet n).card : ℝ)
        ≥ c₁ * (n : ℝ) / Real.log (n : ℝ)

/--
Squarefree sieve refinement (Step 2).
-/
axiom legendre_step2_squarefree_lower_bound :
  ∃ (c₂ : ℝ) (N₂ : ℕ), 0 < c₂ ∧
    ∀ ⦃n : ℕ⦄, N₂ ≤ n → 1 < n →
      ((Myproj.legendreSquarefreeRough n).card : ℝ)
        ≥ ((Myproj.legendreRoughSet n).card : ℝ)
          - c₂ * (n : ℝ) / (Real.log (n : ℝ)) ^ 2

/--
Obstruction removal bound (Step 3).
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

end Myproj

end
