import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Myproj.Definitions

/-!
Definitions for `theorems/thm_infinitely_many_sg_cyclics.tex`.

We work with a large natural parameter `x` (standing for the TeX real parameter),
and define `y(x) = exp(√(log log x))` as in the proof.

The finsets `S0`, `S1`, `Bn`, `B2n1`, `G` are the formal counterparts of the
sets in Steps 1–5 of the TeX argument.
-/

noncomputable section

namespace Myproj

open scoped Classical

/-- The TeX parameter `y := exp((log log x)^{1/2})`. -/
def sgY (x : ℕ) : ℝ :=
  Real.exp (Real.sqrt (Real.log (Real.log (x : ℝ))))

/--
`Rough y n` means `P⁻(n) > y` with the convention `P⁻(1)=∞`:
either `n=1` or every prime divisor of `n` is larger than `y`.
-/
def Rough (y : ℝ) (n : ℕ) : Prop :=
  n = 1 ∨ ∀ p : ℕ, Nat.Prime p → p ∣ n → y < (p : ℝ)

/-- Step 1 set: simultaneous roughness for `n` and `2n+1` up to `x`. -/
def sgS0 (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n => Rough (sgY x) n ∧ Rough (sgY x) (2 * n + 1)

/-- Step 2 exceptional set: a prime-square divides `n` or `2n+1`. -/
def sgS1 (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n =>
    ∃ p : ℕ, Nat.Prime p ∧ sgY x < (p : ℝ) ∧ (p ^ 2 ∣ n ∨ p ^ 2 ∣ (2 * n + 1))

/-- Step 3 exceptional set: internal Szele obstruction for `n`. -/
def sgBn (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n =>
    ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ sgY x < (p : ℝ) ∧ sgY x < (q : ℝ) ∧
        p ∣ (q - 1) ∧ p * q ∣ n

/-- Step 4 exceptional set: internal Szele obstruction for `2n+1`. -/
def sgB2n1 (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n =>
    ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ sgY x < (p : ℝ) ∧ sgY x < (q : ℝ) ∧
        p ∣ (q - 1) ∧ p * q ∣ (2 * n + 1)

/-- Step 5 good set. -/
def sgG (x : ℕ) : Finset ℕ :=
  sgS0 x \ (sgS1 x ∪ sgBn x ∪ sgB2n1 x)

end Myproj

end

