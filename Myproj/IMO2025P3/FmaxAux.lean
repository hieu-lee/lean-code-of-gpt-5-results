import Myproj.IMO2025P3.Setup
import Myproj.IMO2025P3.Axioms

/-!
Auxiliary lemmas (independent of `fmax`) used in the sharpness proof.
-/

namespace Myproj.IMO2025P3

noncomputable section

open Int

-- If 2 ∣ x then (2^m) ∣ x^m over ℤ
lemma twoPowInt_dvd_pow_of_two_dvd {x : ℤ} {m : ℕ} (h2x : (2 : ℤ) ∣ x) :
  (2 : ℤ) ^ m ∣ x ^ m := by
  rcases h2x with ⟨t, rfl⟩
  refine ⟨t ^ m, ?_⟩
  simp [mul_pow, mul_comm, mul_left_comm, mul_assoc]

-- If 2 ∣ z, then 4 ∣ z^4 (over ℤ)
lemma four_dvd_pow_four_of_two_dvd {z : ℤ} (hz : (2 : ℤ) ∣ z) :
  (4 : ℤ) ∣ z ^ 4 := by
  have h16 : (2 : ℤ) ^ 4 ∣ z ^ 4 := twoPowInt_dvd_pow_of_two_dvd (x := z) (m := 4) hz
  have h4_16 : (4 : ℤ) ∣ (2 : ℤ) ^ 4 := by exact ⟨4, by decide⟩
  exact Int.dvd_trans h4_16 h16

-- Monotonicity: if e ≤ e' then (2^e) ∣ (2^e') over ℤ
lemma twoPowInt_dvd_twoPowInt_of_le {e e' : ℕ} (hle : e ≤ e') :
  (2 : ℤ) ^ e ∣ (2 : ℤ) ^ e' := by
  rcases Nat.exists_eq_add_of_le hle with ⟨k, hk⟩
  refine ⟨(2 : ℤ) ^ k, ?_⟩
  simp [hk, pow_add, mul_comm, mul_left_comm, mul_assoc]

-- Nat version: if e ≤ e' then 2^e ∣ 2^e'
lemma two_pow_dvd_mono {e e' : ℕ} (hle : e ≤ e') : 2 ^ e ∣ 2 ^ e' := by
  rcases Nat.exists_eq_add_of_le hle with ⟨k, hk⟩
  refine ⟨2 ^ k, ?_⟩
  simp [hk, Nat.pow_add, Nat.mul_comm]

-- Simple growth: s ≤ 2^s for all natural s
lemma le_pow_two_pow : ∀ s : ℕ, s ≤ 2 ^ s
  | 0 => by simp
  | s + 1 => by
      have ih : s ≤ 2 ^ s := le_pow_two_pow s
      have h1 : 1 ≤ 2 ^ s := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) s)
      have : s + 1 ≤ 2 ^ s + 2 ^ s :=
        le_trans (Nat.add_le_add_right ih 1) (by simpa [two_mul] using Nat.add_le_add_left h1 (2 ^ s))
      simpa [Nat.pow_succ, Nat.mul_comm, two_mul] using this

end

end Myproj.IMO2025P3

