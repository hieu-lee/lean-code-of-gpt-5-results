import Mathlib.Data.Real.Basic

/-
Basic wrappers for the prime-counting function and the short intervals used
in the $k$-fold Oppermann argument. We keep `primePi` abstract, but spell out
its derived interval-counting helpers so that subsequent lemmas can reason
purely algebraically.
-/

noncomputable section

namespace Myproj

open Real

/-- Prime-counting function `π(x)` (left unspecified in this project). -/
axiom primePi : ℝ → ℝ

/-- Number of primes in the half-open real interval `(a, b]`. -/
def primesInInterval (a b : ℝ) : ℝ :=
  primePi b - primePi a

/--
Primes in the left Legendre-type interval `[n^2 - n, n^2]`. The expression is
kept explicit so that short-interval lower bounds can specialise to it.
-/
def primesLeft (n : ℕ) : ℝ :=
  primePi ((n : ℝ) ^ 2) - primePi ((n : ℝ) ^ 2 - n)

/--
Primes in the right Legendre-type interval `[n^2, n^2 + n]`.
-/
def primesRight (n : ℕ) : ℝ :=
  primePi ((n : ℝ) ^ 2 + n) - primePi ((n : ℝ) ^ 2)

end Myproj

end
