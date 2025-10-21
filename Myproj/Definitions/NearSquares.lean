import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

noncomputable section

open scoped Classical

namespace Myproj

/-- Auxiliary polynomial `4k^2 + 1` appearing in near-square cyclic arguments. -/
def nearSquarePoly (k : ℕ) : ℕ :=
  4 * k ^ 2 + 1

/-- Numbers with at most two prime factors (counted with multiplicity). -/
def primeOrSemiprime (n : ℕ) : Prop :=
  Nat.Prime n ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ n = p * q

/-- The sieve condition used in the near-square argument. -/
def nearSquareSieveEligibleNat (y k : ℕ) : Prop :=
  primeOrSemiprime (nearSquarePoly k) ∧ (y < Nat.minFac (nearSquarePoly k))

/-- Real-valued variant of the sieve condition. -/
def nearSquareSieveEligible (y : ℝ) (k : ℕ) : Prop :=
  primeOrSemiprime (nearSquarePoly k) ∧ (y < (Nat.minFac (nearSquarePoly k) : ℝ))

/-- Congruence obstruction to cyclicity via a pair of primes. -/
def nearSquareObstructed (k : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧
      nearSquarePoly k = p * q ∧ p ∣ (q - 1)

/-- `k` in `[1, ⌊X⌋]`. -/
def nearSquareRange (X : ℝ) : Finset ℕ :=
  Finset.Icc 1 (Nat.floor X)

/-- Count of `k ≤ X` passing the sieve condition at threshold `y`. -/
def nearSquareSieveCount (X y : ℝ) : ℕ :=
  ((nearSquareRange X).filter fun k => nearSquareSieveEligible y k).card

/-- Count of obstructed `k ≤ X` at threshold `y`. -/
def nearSquareObstructionCount (X y : ℝ) : ℕ :=
  ((nearSquareRange X).filter fun k => nearSquareObstructed k ∧
      (y < (Nat.minFac (nearSquarePoly k) : ℝ))).card

/--
Noncomputable count used in Step 3.2 (large prime obstruction): number of
parameters `k ≤ X` with an obstruction and with `minFac(4k^2+1)^2 > X`.
We wrap the filter in a `by classical` block to avoid decidability hassles.
-/
noncomputable def nearSquareLargePrimeObstructionCount (X y : ℝ) : ℝ := by
  classical
  exact
    (((nearSquareRange X).filter
      (fun k => nearSquareObstructed k ∧
        y < (Nat.minFac (nearSquarePoly k) : ℝ) ∧
        X < (Nat.minFac (nearSquarePoly k) : ℝ) ^ 2)).card : ℝ)

end Myproj
