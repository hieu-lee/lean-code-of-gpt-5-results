import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Definitions specific to the Legendre analog for cyclic integers.
These provide the combinatorial sets appearing in the analytic proof,
while the heavy quantitative bounds are supplied separately via axioms.
-/

noncomputable section

namespace Myproj

open scoped Classical

/-- Predicate: `n` is squarefree if no square of a prime divides it. -/
def squarefreeNat (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ n

/-- `x_n = n^2`, the left endpoint in the Legendre interval. -/
def legendreX (n : ℕ) : ℕ :=
  n ^ 2

/-- `H_n = 2n + 1`, the length of the Legendre interval. -/
def legendreH (n : ℕ) : ℕ :=
  2 * n + 1

/-- Real-valued version `x_n = (n : ℝ)^2`. -/
def legendreXReal (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2

/-- The open integer interval `(n^2, (n+1)^2)` as a finset. -/
def legendreInterval (n : ℕ) : Finset ℕ :=
  Finset.Icc (n ^ 2 + 1) ((n + 1) ^ 2 - 1)

/-- Auxiliary quantity `z_n = ⌈x^{1/4} / (log x)^6⌉` used in the sieve argument.
For small `n` (when `log x` would be problematic) we clamp the value to `2`. -/
def legendreZ (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 2
  else
    let x : ℝ := (n : ℝ) ^ 2
    Nat.ceil (Real.rpow x (1 / 4 : ℝ) / (Real.log x) ^ 6)

/-- Predicate: `m` is `z_n`-rough, i.e. every prime factor is at least `z_n`
   (with `m = 1` treated as rough, matching the LaTeX convention `P^-(1)=∞`). -/
def legendreZRough (n m : ℕ) : Prop :=
  m = 1 ∨ legendreZ n ≤ Nat.minFac m

/-- Predicate: `m` is obstructed by a pair of primes `p < q` with `p ∣ (q - 1)`
    and both dividing `m`, which forces `m` to fail cyclicity. -/
def legendreObstructed (m : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ p ∣ (q - 1) ∧ p ∣ m ∧ q ∣ m

/-- `z_n`-rough integers inside the Legendre interval. -/
def legendreRoughSet (n : ℕ) : Finset ℕ :=
  (legendreInterval n).filter fun m =>
    legendreZRough n m

/-- Squarefree `z_n`-rough integers inside the Legendre interval. -/
def legendreSquarefreeRough (n : ℕ) : Finset ℕ :=
  (legendreInterval n).filter fun m =>
    legendreZRough n m ∧ squarefreeNat m

/-- Squarefree `z_n`-rough integers in the interval that suffer an obstruction `p → q`. -/
def legendreObstructedSet (n : ℕ) : Finset ℕ :=
  (legendreSquarefreeRough n).filter fun m => legendreObstructed m

end Myproj

end

/-!
Auxiliary arithmetic lemma (Step 2): there is no perfect square between
consecutive squares `n^2` and `(n+1)^2`.
-/

namespace Myproj

lemma no_square_between_consecutive_squares (n t : ℕ) :
    ¬ (n ^ 2 < t ^ 2 ∧ t ^ 2 < (n + 1) ^ 2) := by
  intro h
  rcases h with ⟨h1, h2⟩
  by_cases ht : t ≤ n
  · have hle : t ^ 2 ≤ n ^ 2 := by
      have hmul : t * t ≤ n * n := Nat.mul_le_mul ht ht
      simpa [pow_two] using hmul
    exact (not_lt_of_ge hle) h1
  · have hnt : n < t := lt_of_not_ge ht
    have hsqr : (n + 1) ^ 2 ≤ t ^ 2 := by
      have : n.succ ≤ t := Nat.succ_le_of_lt hnt
      have hmul : (n + 1) * (n + 1) ≤ t * t := Nat.mul_le_mul this this
      simpa [pow_two, Nat.succ_eq_add_one] using hmul
    exact (not_lt_of_ge hsqr) h2

end Myproj
