import Mathlib.Data.Finset.Interval
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

-- Silence unrelated linter noise in this utility file
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.missingEnd false

noncomputable section

namespace Myproj

open scoped BigOperators
open Filter

/-- A natural number `n` is a cyclic order iff `gcd(n, φ(n)) = 1`.
This matches Szele's criterion (1947), used as the working definition
throughout these proofs. -/
def isCyclicNumber (n : ℕ) : Prop :=
  Nat.gcd n (Nat.totient n) = 1

/-- Two numbers `a < b` are consecutive cyclic numbers if both are cyclic
and no cyclic number lies strictly between them. -/
def consecutiveCyclic (a b : ℕ) : Prop :=
  a < b ∧ isCyclicNumber a ∧ isCyclicNumber b ∧
    ∀ m : ℕ, a < m → m < b → ¬ isCyclicNumber m

/-- `n` is an "SG cyclic" if `n` and `2n+1` are cyclic. -/
def isSGCyclicNumber (n : ℕ) : Prop :=
  isCyclicNumber n ∧ isCyclicNumber (2 * n + 1)

/-- Two numbers `a < b` are consecutive SG cyclic numbers if both are SG cyclic
and no SG cyclic number lies strictly between them. -/
def consecutiveSGCyclic (a b : ℕ) : Prop :=
  a < b ∧ isSGCyclicNumber a ∧ isSGCyclicNumber b ∧
    ∀ m : ℕ, a < m → m < b → ¬ isSGCyclicNumber m

/-- The interval `I_N := (N^3, (N+1)^3]` viewed as a finset of natural numbers. -/
@[simp] def cubeInterval (N : ℕ) : Finset ℕ :=
  Finset.Icc (N ^ 3 + 1) ((N + 1) ^ 3)

/-- An integer `n` is a witness for offset `h` when both `n` and `n + h` are cyclic orders. -/
def cyclicWitness (h n : ℕ) : Prop :=
  isCyclicNumber n ∧ isCyclicNumber (n + h)

instance (h : ℕ) : DecidablePred (cyclicWitness h) := by
  classical
  intro n
  unfold cyclicWitness
  infer_instance

-- Decidability for the predicate `isCyclicNumber` (needed for finset filters).
instance : DecidablePred isCyclicNumber := by
  classical
  intro n
  unfold isCyclicNumber
  infer_instance

/-- The counting function `A_h(N)` appearing in the statement. -/
def cyclicCount (h N : ℕ) : ℕ :=
  ((cubeInterval N).filter fun n => cyclicWitness h n).card

lemma cyclicCount_le_card (h N : ℕ) : cyclicCount h N ≤ (cubeInterval N).card := by
  classical
  simpa [cyclicCount] using
    Finset.card_filter_le (s := cubeInterval N) (p := fun n => cyclicWitness h n)

lemma cubeInterval_card (N : ℕ) :
    (cubeInterval N).card = (N + 1) ^ 3 - N ^ 3 := by
  classical
  have h := Nat.card_Icc (N ^ 3 + 1) ((N + 1) ^ 3)
  have hdiff1 : 1 + (N + 1) ^ 3 - (1 + N ^ 3)
      = (N + 1) ^ 3 + 1 - (N ^ 3 + 1) := by
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hdiff2 : (N + 1) ^ 3 + 1 - (N ^ 3 + 1) = (N + 1) ^ 3 - N ^ 3 := by
    simpa using Nat.add_sub_add_right ((N + 1) ^ 3) (N ^ 3) 1
  have hdiff := hdiff1.trans hdiff2
  simpa [cubeInterval, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, hdiff]
    using h

lemma cubeInterval_card_real (N : ℕ) :
    ((cubeInterval N).card : ℝ) = ((N : ℝ) + 1) ^ 3 - (N : ℝ) ^ 3 := by
  classical
  have h := cubeInterval_card N
  have h' : ((cubeInterval N).card : ℝ) = (( (N + 1) ^ 3 - N ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hle : N ^ 3 ≤ (N + 1) ^ 3 := by
    simpa using Nat.pow_le_pow_left (Nat.le_succ N) (3 : ℕ)
  have hsub : (( (N + 1) ^ 3 - N ^ 3 : ℕ) : ℝ)
      = (( (N + 1) ^ 3 : ℕ) : ℝ) - ((N ^ 3 : ℕ) : ℝ) := by
    simpa [Nat.cast_pow] using
      (Nat.cast_sub hle :
        (( (N + 1) ^ 3 - N ^ 3 : ℕ) : ℝ)
          = (( (N + 1) ^ 3 : ℕ) : ℝ) - ((N ^ 3 : ℕ) : ℝ))
  have hpow1 : (( (N + 1) ^ 3 : ℕ) : ℝ) = ((N : ℝ) + 1) ^ 3 := by
    simp [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hpow2 : ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ 3 := by
    simp [Nat.cast_pow]
  simpa [hsub, hpow1, hpow2] using h'

lemma cubeInterval_card_poly (N : ℕ) :
    ((cubeInterval N).card : ℝ) = 3 * (N : ℝ) ^ 2 + 3 * (N : ℝ) + 1 := by
  have h := cubeInterval_card_real N
  have hbinom : ((N : ℝ) + 1) ^ 3 - (N : ℝ) ^ 3
      = 3 * (N : ℝ) ^ 2 + 3 * (N : ℝ) + 1 := by
    ring
  simpa [cubeInterval_card_real, hbinom] using h

lemma cubeInterval_card_le_four_mul_sq {N : ℕ} (hN : 4 ≤ N) :
    ((cubeInterval N).card : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
  have hN' : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hineq : 3 * (N : ℝ) ^ 2 + 3 * (N : ℝ) + 1 ≤ 4 * (N : ℝ) ^ 2 := by
    nlinarith [hN']
  have hexpr : ((N : ℝ) + 1) ^ 3 - (N : ℝ) ^ 3 = 3 * (N : ℝ) ^ 2 + 3 * (N : ℝ) + 1 := by
    ring
  have hineq' : ((N : ℝ) + 1) ^ 3 - (N : ℝ) ^ 3 ≤ 4 * (N : ℝ) ^ 2 := by
    simpa [hexpr] using hineq
  calc
    ((cubeInterval N).card : ℝ)
        = ((N : ℝ) + 1) ^ 3 - (N : ℝ) ^ 3 := cubeInterval_card_real N
    _ ≤ 4 * (N : ℝ) ^ 2 := hineq'

end Myproj

-- close the noncomputable section opened above
end

