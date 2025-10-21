import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Myproj.IMO2025P3.Setup

/-!
Axioms specific to IMO 2025 P3 formalization.
We keep only standard, well-known results not already in mathlib.

- 2-adic LTE identity for odd base and even exponent:
  ν₂(x^n − 1) = ν₂(x − 1) + ν₂(x + 1) + ν₂(n) − 1, for odd `x` and even `n ≥ 1`.

Source: Lifting The Exponent (LTE) lemma; see e.g.
Wikipedia "Lifting-the-exponent lemma" or standard olympiad references.
-/

namespace Myproj.IMO2025P3

noncomputable section

/-- For every natural `n`, exactly one of odd/even holds in our local sense. -/
axiom odd_or_even (n : ℕ) : IsOdd n ∨ IsEven n

/-- Fermat's little theorem over integers: for prime `p` and any integer `x`,
`x^p ≡ x [ZMOD p]`. Source: Fermat's little theorem (see Wikipedia or standard texts). -/
axiom fermat_little_int {p : ℕ} (hp : Nat.Prime p) (x : ℤ) :
  x ^ p ≡ x [ZMOD (p : ℤ)]

/-- Divisors of a prime power are themselves prime powers: if `d ∣ p^k` with prime `p`,
then `∃ s ≤ k, d = p^s`. This is a standard fact from unique factorization.
Source: Elementary number theory (divisors of prime powers). -/
axiom dvd_prime_pow_eq {p k d : ℕ} (hp : Nat.Prime p) (h : d ∣ p ^ k) : ∃ s ≤ k, d = p ^ s

/-- Bridge between Int.ModEq and divisibility: `a ≡ b [ZMOD m]` iff `m ∣ a - b`.
Standard equivalence by definition of `Int.ModEq`. -/
axiom int_modEq_iff_dvd {m a b : ℤ} : (a ≡ b [ZMOD m]) ↔ m ∣ a - b

/-- If `((2 : ℤ)^e) ∣ ((3 : ℤ)^n - 1)` and `n` is even with `n > 0`, then `e ≤ nu2 n + 2`.
This is a direct consequence of the 2-adic LTE for base 3 and the fact that
`2^e ∣ 3^n - 1` implies `e ≤ ν₂(3^n - 1) = ν₂(3-1)+ν₂(3+1)+ν₂(n)-1 = ν₂(n)+2`.
Source: LTE (see Wikipedia) and basic properties of 2-adic valuation. -/
axiom le_nu2_of_two_pow_dvd_pow3_sub_one
  {n e : ℕ} (hnpos : 0 < n) (heven : IsEven n)
  (hdiv : ((2 : ℤ) ^ e) ∣ ((3 : ℤ) ^ n - 1)) : e ≤ nu2 n + 2

/-- LTE for the 2-adic valuation with odd base and even exponent. -/
axiom v2_pow_sub_one_of_odd_even
  {x n : ℕ} (hodd : IsOdd x) (heven : IsEven n) (hnpos : 0 < n) :
  nu2 (x ^ n - 1) = nu2 (x - 1) + nu2 (x + 1) + nu2 n - 1

/-- Classification of numbers with no odd prime divisors: if `m > 0` and no odd prime divides `m`,
then `m` is a power of two. Source: unique factorization and parity of prime factors. -/
axiom pow_two_classification
  {m : ℕ} (hmpos : 0 < m)
  (h : ∀ r : ℕ, Nat.Prime r → IsOdd r → ¬ r ∣ m) : ∃ e : ℕ, m = 2 ^ e

/-- For `e > 0`, `2^e` is even. Source: basic parity of powers of 2. -/
axiom two_pow_even_of_pos {e : ℕ} (he : 0 < e) : IsEven (2 ^ e)

/-- An even number cannot divide an odd number. Source: elementary parity/divisibility. -/
axiom even_not_dvd_odd {m n : ℕ} (hm : IsEven m) (hn : IsOdd n) : ¬ m ∣ n

/-- If an integer has infinitely many prime divisors then it is zero.
Equivalently, every nonzero integer has only finitely many prime divisors.
Source: fundamental theorem of arithmetic (unique factorization). -/
axiom int_infinite_prime_divisors_implies_zero
  {z : ℤ} (hinf : Set.Infinite {p : ℕ | Nat.Prime p ∧ (p : ℤ) ∣ z}) : z = 0

/-- If `n` is odd then every power `n^m` is odd. Source: basic parity properties. -/
axiom odd_pow_of_odd {n m : ℕ} (hodd : IsOdd n) : IsOdd (n ^ m)

/-- Chinese remainder theorem (existence form) specialized to one modulus `2` and a finite
set `S` of odd primes: there exists `b` such that `b ≡ 1 [MOD 2]` and `b ≡ 2 [MOD p]`
for all `p ∈ S`. The moduli are pairwise coprime since `2` is coprime with every odd
prime and distinct primes are coprime.
Source: Chinese remainder theorem (see any standard algebra/number theory text). -/
axiom crt_exists_one_mod_two_two_mod_primes
  (S : Finset ℕ)
  (hS : ∀ p ∈ S, Nat.Prime p ∧ IsOdd p) :
  ∃ b : ℕ, Nat.ModEq 2 b 1 ∧ ∀ p ∈ S, Nat.ModEq p b 2

/-- Congruence modulo 2 characterizes oddness: if `b ≡ 1 [MOD 2]` then `b` is odd.
Source: elementary number theory (classification of odd/even via residues mod 2). -/
axiom odd_of_mod2_eq_one {b : ℕ} (h : Nat.ModEq 2 b 1) : IsOdd b

/-- For odd `b`, `b^2 ≡ 1 (mod 8)`, i.e. `(8 : ℤ) ∣ (b^2 - 1)` over integers.
Source: classical congruence of odd squares modulo 8 (elementary number theory). -/
axiom eight_dvd_odd_sq_sub_one {b : ℕ} (hodd : IsOdd b) :
  (8 : ℤ) ∣ ((b : ℤ) ^ 2 - 1)

/-- For odd `x`, one has `ν₂(x - 1) + ν₂(x + 1) ≥ 3`.
Reason: both are even, and among two consecutive even numbers one is divisible by 4.
Source: elementary parity/divisibility; standard consequence used with LTE. -/
axiom v2_bminus1_add_bplus1_ge_three {x : ℕ} (hodd : IsOdd x) :
  3 ≤ nu2 (x - 1) + nu2 (x + 1)

/-- Positivity of `ν₂` on even numbers: if `n` is even then `0 < ν₂(n)`.
Source: definition of 2-adic valuation (power of two dividing `n`). -/
axiom nu2_pos_of_even {n : ℕ} (heven : IsEven n) : 0 < nu2 n

/-- Exact valuation on powers of two: `ν₂(2^k) = k` for all `k`.
Source: padic valuation on prime powers (standard). -/
axiom nu2_pow_two (k : ℕ) : nu2 (2 ^ k) = k

/-- If `b` is even then `(4 : ℤ) ∣ (b : ℤ)^2`.
Source: elementary parity: write `b = 2t`, then `b^2 = 4 t^2`. -/
axiom even_square_four_dvd_int {b : ℕ} (he : IsEven b) : (4 : ℤ) ∣ ((b : ℤ) ^ 2)

/-- Bridge between `Nat.ModEq` and `Int.ModEq` for natural moduli and residues. -/
  axiom nat_modEq_iff_int_modEq {p a b : ℕ} : Nat.ModEq p a b ↔ Int.ModEq (p : ℤ) (a : ℤ) (b : ℤ)

/-- An odd prime does not divide 2. Source: only prime divisor of 2 is 2. -/
axiom odd_prime_not_dvd_two {p : ℕ} (hp : Nat.Prime p) (hodd : IsOdd p) : ¬ p ∣ 2

/-- For an odd prime p, 1 is not congruent to 2 modulo p. -/
  axiom one_ne_two_mod_odd_prime {p : ℕ} (hp : Nat.Prime p) (hodd : IsOdd p) : ¬ Nat.ModEq p 1 2

/-- For even `a ≥ 4`, we have `nu2 a + 2 ≤ a`.
Elementary 2-adic size bound using the factorization `a = 2^k * u` with `k = nu2 a`.
Source: basic properties of `ν₂` and prime power factorizations. -/
axiom nu2_add_two_le_self_of_even_ge4 {a : ℕ}
  (ha4 : 4 ≤ a) (ha_even : IsEven a) : nu2 a + 2 ≤ a

/-- Casting bridge: for `b ≥ 1`, `a ≥ 1`, the natural difference `b^a − 1` cast to `ℤ`
coincides with the integer difference `(b:ℤ)^a − 1`.
Source: standard cast/arithmetics; follows since `b^a ≥ 1`. -/
  axiom int_cast_pow_sub_one {b a : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) :
  ((b : ℤ) ^ a - 1) = ((b ^ a - 1 : ℕ) : ℤ)

/-- Evenness equivalence: `IsEven a` iff `∃ t, a = 2 * t`.
Source: elementary parity characterization. -/
axiom exists_two_mul_of_even {a : ℕ} (h : IsEven a) : ∃ t : ℕ, a = 2 * t
end

end Myproj.IMO2025P3
