import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
Setup for IMO 2025 P3 formalization.
-/

namespace Myproj.IMO2025P3

noncomputable section

open Int

/-- Local aliases for parity to avoid depending on external modules. -/
def IsOdd (n : ℕ) : Prop := n % 2 = 1
def IsEven (n : ℕ) : Prop := n % 2 = 0

/-- Bonza predicate: for all positive `a, b`,
`f a` divides `b^a - f(b)^(f a)` (as an integer divisibility). -/
def Bonza (f : ℕ → ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, 1 ≤ a → 1 ≤ b → (f a : ℤ) ∣ ((b : ℤ) ^ a - (f b : ℤ) ^ (f a))

/-! Some small helpers -/

@[simp] lemma pow_nat_cast_int (n k : ℕ) : ((n : ℤ) ^ k) = (n : ℤ) ^ k := rfl

/-- 2-adic valuation on naturals. -/
def nu2 (n : ℕ) : ℕ := padicValNat 2 n

lemma pow_nu2_dvd (n : ℕ) : 2 ^ nu2 n ∣ n := by
  simpa [nu2] using (pow_padicValNat_dvd (p := 2) (n := n))

/-! Set of odd primes dividing their own image under `f`. -/
def Podd (f : ℕ → ℕ) : Set ℕ := {p | Nat.Prime p ∧ IsOdd p ∧ p ∣ f p}

end

end Myproj.IMO2025P3
