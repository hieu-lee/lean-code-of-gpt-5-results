import Myproj.IMO2025P3.Setup
import Myproj.IMO2025P3.Axioms
import Myproj.IMO2025P3.FmaxDef
import Myproj.IMO2025P3.FmaxAux

/-!
Extremal function `fmax` and sharpness: `fmax` is bonza and achieves ratio 4.
-/

namespace Myproj.IMO2025P3

noncomputable section

open Int
open Classical

/-- `fmax` is bonza. -/
theorem fmax_bonza : Bonza fmax := by
  intro a b ha hb
  classical
  -- Cases on a
  by_cases h1 : a = 1
  · -- fmax a = 1
    simp [fmax, h1]
  by_cases haodd : IsOdd a
  · -- fmax a = 1 when a is odd and a ≠ 1
    simp [fmax, h1, haodd]
  -- a is even
  have ha_even : IsEven a := by
    rcases odd_or_even a with h | h
    · exact (False.elim (by simpa [haodd] using h))
    · exact h
  by_cases ha2 : a = 2
  · -- a = 2
    have hf2 : fmax a = 4 := by simpa [fmax_two] using congrArg fmax ha2
    have hf2Z : (fmax a : ℤ) = 4 := by simpa [hf2]
    rcases odd_or_even b with hbodd | hbeven
    · -- b odd: fmax b = 1 and 4 ∣ b^2 - 1
      have hf1 : fmax b = 1 := fmax_odd b hbodd
      have h8 : (8 : ℤ) ∣ ((b : ℤ) ^ 2 - 1) := eight_dvd_odd_sq_sub_one hbodd
      have h4 : (4 : ℤ) ∣ ((b : ℤ) ^ 2 - 1) := Int.dvd_trans ⟨2, by decide⟩ h8
      -- rewrite target with fmax 2 = 4 and fmax b = 1
      have hx : (fmax b : ℤ) ^ (fmax a) = 1 := by simp [hf1, hf2]
      have : (fmax a : ℤ) ∣ ((b : ℤ) ^ 2 - (fmax b : ℤ) ^ (fmax a)) := by
        -- rewrite using fmax a = 4 and fmax b = 1
        simpa [hf2Z, hx] using h4
      simpa [ha2] using this
    · -- b even: show 4 ∣ b^2 and 4 ∣ fmax(b)^4
      have hb2 : (4 : ℤ) ∣ ((b : ℤ) ^ 2) := even_square_four_dvd_int hbeven
      -- Show 2 ∣ fmax b, hence 4 ∣ (fmax b)^2 and thus 4 ∣ (fmax b)^4
      have h2f : (2 : ℤ) ∣ (fmax b : ℤ) := by
        by_cases hb2eq : b = 2
        · have : fmax b = 4 := by simpa [fmax_two] using congrArg fmax hb2eq
          exact ⟨2, by simpa [this] using (by decide : (4 : ℤ) = 2 * 2)⟩
        ·
          -- b is even and not 2, hence fmax b is a power of two ≥ 4
          have hfbeq : fmax b = 2 ^ (nu2 b + 2) := by
            -- b ≠ 1 since b is even
            have hbne1 : b ≠ 1 := by
              intro h
              have even1 : IsEven 1 := by simpa [h] using hbeven
              have hmod0 : 1 % 2 = 0 := by simpa [IsEven] using even1
              have hmod1 : 1 % 2 = 1 := Nat.mod_eq_of_lt (by decide : 1 < 2)
              have : 1 = 0 := by simpa [hmod1] using hmod0
              exact Nat.one_ne_zero this
            -- not odd since b is even
            have notOdd : ¬ IsOdd b := by
              intro hbodd
              have hb0 : b % 2 = 0 := by simpa [IsEven] using hbeven
              have hb1 : b % 2 = 1 := by simpa [IsOdd] using hbodd
              have : (0 : Nat) = 1 := by simpa [hb0] using hb1
              exact Nat.zero_ne_one this
            simpa [fmax, hbne1, notOdd, hb2eq]
          exact ⟨(2 ^ (nu2 b + 1) : ℤ), by simpa [hfbeq, pow_succ, mul_comm]⟩
      have h4f_sq : (4 : ℤ) ∣ ((fmax b : ℤ) ^ 2) := by
        have : (2 : ℤ) ^ 2 ∣ (fmax b : ℤ) ^ 2 :=
          twoPowInt_dvd_pow_of_two_dvd (x := (fmax b : ℤ)) (m := 2) h2f
        simpa using this
      have h4f : (4 : ℤ) ∣ ((fmax b : ℤ) ^ 4) :=
        four_dvd_pow_four_of_two_dvd (z := (fmax b : ℤ)) h2f
      have hdiff : (4 : ℤ) ∣ ((b : ℤ) ^ 2 - (fmax b : ℤ) ^ 4) := dvd_sub hb2 h4f
      have hf2N : fmax a = 4 := by simpa [fmax_two] using congrArg fmax ha2
      have : (fmax a : ℤ) ∣ ((b : ℤ) ^ 2 - (fmax b : ℤ) ^ (fmax a)) := by
        simpa [hf2Z, hf2N] using hdiff
      simpa [ha2] using this
  · -- a ≥ 4 and even: set s = ν₂(a)+2 so fmax a = 2^s
    have ha4 : 4 ≤ a := by
      -- From even `a` and `a ≠ 2`, write `a = 2*t` with `t ≥ 2`.
      rcases exists_two_mul_of_even ha_even with ⟨t, ht⟩
      -- t cannot be 0, else a = 0 contradicts ha
      have ht_ne0 : t ≠ 0 := by
        intro h0
        have : a = 0 := by simpa [h0, Nat.mul_zero] using ht
        have : 1 ≤ (0 : ℕ) := by simpa [this] using ha
        exact (Nat.not_succ_le_self 0 this).elim
      -- t cannot be 1, else a = 2 contradicts ha2
      have ht_ne1 : t ≠ 1 := by
        intro h1
        have h2 : 2 * t = 2 := by simpa [h1, Nat.mul_comm]
        have : a = 2 := by simpa [ht] using h2
        exact (ha2 this).elim
      -- hence t ≥ 2
      have ht_ge2 : 2 ≤ t := by
        have : 1 < t := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht_ne0)) ht_ne1.symm
        exact Nat.succ_le_of_lt this
      have : 2 * 2 ≤ 2 * t := Nat.mul_le_mul_left 2 ht_ge2
      simpa [ht, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    let s := nu2 a + 2
    have hfA : fmax a = 2 ^ s := by
      have := fmax_even_ge4_eval (a := a) ha_even (by exact h1) ha2
      simpa [s] using this
    rcases odd_or_even b with hbodd | hbeven
    · -- b odd: show 2^s ∣ b^a − 1 using ν₂ identity
      have hbpos : 1 ≤ b := hb
      have hnu : nu2 (b ^ a - 1) = nu2 (b - 1) + nu2 (b + 1) + nu2 a - 1 :=
        v2_pow_sub_one_of_odd_even (x := b) (n := a) hbodd ha_even (Nat.succ_le_iff.mp ha)
      have hb3 : 3 ≤ nu2 (b - 1) + nu2 (b + 1) := v2_bminus1_add_bplus1_ge_three hbodd
      have hle : nu2 a + 2 ≤ nu2 (b ^ a - 1) := by
        -- From hb3: 3 ≤ ν₂(b−1)+ν₂(b+1)
        have htmp : nu2 a + 3 ≤ (nu2 (b - 1) + nu2 (b + 1)) + nu2 a := by
          have hx := Nat.add_le_add_left hb3 (nu2 a)
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx
        have hpred : nu2 a + 2 ≤ (nu2 (b - 1) + nu2 (b + 1)) + nu2 a - 1 :=
          Nat.le_pred_of_lt (Nat.lt_of_succ_le (by simpa [Nat.succ_eq_add_one] using htmp))
        -- Rewrite using the ν₂ identity
        simpa [hnu, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hpred
      have hdiv_nat : 2 ^ (nu2 a + 2) ∣ b ^ a - 1 := by
        have hmax : 2 ^ nu2 (b ^ a - 1) ∣ b ^ a - 1 := pow_nu2_dvd (b ^ a - 1)
        exact Nat.dvd_trans (two_pow_dvd_mono hle) hmax
      have hf_bodd : fmax b = 1 := fmax_odd b hbodd
      have hdiv_int : ((2 ^ (nu2 a + 2) : ℕ) : ℤ) ∣ ((b : ℤ) ^ a - 1) := by
        have := Int.ofNat_dvd.mpr hdiv_nat
        simpa [int_cast_pow_sub_one hb (Nat.succ_le_iff.mp ha)] using this
      -- interpret as divisibility of the target difference using fmax b = 1 and fmax a = 2^s
      simpa [hfA, hf_bodd] using hdiv_int
    · -- b even: show 2^s ∣ both terms and subtract
      -- (2^a) ∣ b^a
      have hb2Z : (2 : ℤ) ∣ (b : ℤ) := by
        rcases exists_two_mul_of_even hbeven with ⟨t, ht⟩
        refine ⟨(t : ℤ), ?_⟩
        simp [ht, Int.ofNat_mul, mul_comm]
      have hpow1 : (2 : ℤ) ^ a ∣ (b : ℤ) ^ a := twoPowInt_dvd_pow_of_two_dvd (x := (b : ℤ)) (m := a) hb2Z
      -- s ≤ a (since a ≥ 4 and even), hence (2^s) ∣ (2^a)
      have hs_le_a : nu2 a + 2 ≤ a := nu2_add_two_le_self_of_even_ge4 ha4 ha_even
      have hstep : (2 : ℤ) ^ (nu2 a + 2) ∣ (2 : ℤ) ^ a := twoPowInt_dvd_twoPowInt_of_le hs_le_a
      have hdiv1 : (2 : ℤ) ^ (nu2 a + 2) ∣ (b : ℤ) ^ a := Int.dvd_trans hstep hpow1
      -- 2 ∣ fmax b
      have h2f : (2 : ℤ) ∣ (fmax b : ℤ) := by
        by_cases hb2eq : b = 2
        · have : fmax b = 4 := by simpa [fmax_two] using congrArg fmax hb2eq
          exact ⟨2, by simpa [this] using (by decide : (4 : ℤ) = 2 * 2)⟩
        · have notOdd : ¬ IsOdd b := by
            intro hbodd
            have hb0 : b % 2 = 0 := by simpa [IsEven] using hbeven
            have hb1 : b % 2 = 1 := by simpa [IsOdd] using hbodd
            have : (0 : Nat) = 1 := by simpa [hb0] using hb1
            exact Nat.zero_ne_one this
          -- Since b is even and b ≠ 2, b ≠ 1 and we are in the last branch of fmax.
          have hbne1 : b ≠ 1 := by
            intro h
            have hb0 : 1 % 2 = 0 := by simpa [h, IsEven] using hbeven
            have hb1 : 1 % 2 = 1 := Nat.mod_eq_of_lt (by decide : 1 < 2)
            have : (0 : Nat) = 1 := by simpa [hb0] using hb1
            exact Nat.zero_ne_one this
          have hfbeq : fmax b = 2 ^ (nu2 b + 2) := by simpa [fmax, hbne1, notOdd, hb2eq]
          exact ⟨(2 ^ (nu2 b + 1) : ℤ), by simpa [hfbeq, pow_succ, mul_comm]⟩
      have hpow2 : (2 : ℤ) ^ (2 ^ (nu2 a + 2)) ∣ (fmax b : ℤ) ^ (2 ^ (nu2 a + 2)) :=
        twoPowInt_dvd_pow_of_two_dvd (x := (fmax b : ℤ)) (m := 2 ^ (nu2 a + 2)) h2f
      -- Since (nu2 a + 2) ≤ 2^(nu2 a + 2), (2^(nu2 a + 2)) ∣ (2^(2^(nu2 a + 2)))
      have hmon : (2 : ℤ) ^ (nu2 a + 2) ∣ (2 : ℤ) ^ (2 ^ (nu2 a + 2)) :=
        twoPowInt_dvd_twoPowInt_of_le (by simpa using le_pow_two_pow (nu2 a + 2))
      have hdiv2 : (2 : ℤ) ^ (nu2 a + 2) ∣ (fmax b : ℤ) ^ (2 ^ (nu2 a + 2)) := Int.dvd_trans hmon hpow2
      have hdiv : (2 : ℤ) ^ (nu2 a + 2) ∣ ((b : ℤ) ^ a - (fmax b : ℤ) ^ (2 ^ (nu2 a + 2))) :=
        dvd_sub hdiv1 hdiv2
      simpa [hfA] using hdiv

/-- Exact values of `fmax` on powers of two (for `k ≥ 2`). -/
theorem fmax_pow_two {k : ℕ} (hk : 2 ≤ k) : fmax (2 ^ k) = 4 * 2 ^ k := by
  classical
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have heven_pow : IsEven (2 ^ k) := two_pow_even_of_pos hkpos
  have notOdd : ¬ IsOdd (2 ^ k) := by
    intro h
    -- IsEven and IsOdd are incompatible
    have h0 : (2 ^ k) % 2 = 0 := by simpa [IsEven] using heven_pow
    have h1 : (2 ^ k) % 2 = 1 := by simpa [IsOdd] using h
    exact Nat.zero_ne_one (by simpa [h0] using h1)
  -- 2^k ≥ 4
  have hge4 : 4 ≤ 2 ^ k := by
    rcases Nat.exists_eq_add_of_le hk with ⟨t, ht⟩
    have : 1 ≤ 2 ^ t := by
      cases t with
      | zero => simp
      | succ t =>
          have : 0 < 2 ^ (Nat.succ t) := pow_pos (by decide : 0 < 2) _
          exact Nat.succ_le_of_lt this
    simpa [ht, Nat.pow_add, Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using (Nat.mul_le_mul_left 4 this)
  have hne1 : (2 ^ k) ≠ 1 := by
    -- Since 1 < 4 ≤ 2^k, we have 1 < 2^k
    exact ne_of_gt (lt_of_lt_of_le (by decide : 1 < 4) hge4)
  have hne2 : (2 ^ k) ≠ 2 := by
    -- Since 2 < 4 ≤ 2^k, we have 2 < 2^k
    exact ne_of_gt (lt_of_lt_of_le (by decide : 2 < 4) hge4)
  have hf : fmax (2 ^ k) = 2 ^ (nu2 (2 ^ k) + 2) := by
    simp [fmax, hne1, notOdd, hne2]
  have : 2 ^ (nu2 (2 ^ k) + 2) = 2 ^ k * 4 := by
    simp [nu2_pow_two, Nat.pow_add, Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hcomm : 2 ^ k * 4 = 4 * 2 ^ k := by simpa [Nat.mul_comm]
  simpa [hf, this, hcomm]

/-- Bundle sharpness: `fmax` is bonza and achieves ratio `4` on `2^k` for `k ≥ 2`. -/
theorem fmax_sharpness : Bonza fmax ∧ ∀ k ≥ 2, fmax (2 ^ k) = 4 * 2 ^ k := by
  refine ⟨fmax_bonza, ?_⟩
  intro k hk; exact fmax_pow_two hk

end

end Myproj.IMO2025P3
