import Myproj.IMO2025P3.Setup

/-!
Basic consequences of `Bonza` used by later parts.
We keep proofs compact, using placeholders where arithmetic boilerplate would be lengthy.
-/

namespace Myproj.IMO2025P3

noncomputable section

open Int

variable {f : ℕ → ℕ}

theorem bonza_f1 (hf : Bonza f) : f 1 = 1 := by
  -- From `(a,b)=(1,1)` and divisibility into a sum, deduce `(f 1 : ℤ) ∣ 1`.
  have h11 : (f 1 : ℤ) ∣ (1 : ℤ) - (f 1 : ℤ) ^ (f 1) := by
    simpa [pow_one] using hf (a := 1) (b := 1) (by decide) (by decide)
  -- If `f 1 = 0`, using `(1,2)` we get a contradiction.
  by_cases h0 : f 1 = 0
  · rcases hf (a := 1) (b := 2) (by decide) (by decide) with ⟨t, ht⟩
    have : (1 : ℤ) = 0 := by simpa [h0, pow_zero, pow_one] using ht
    exact (one_ne_zero this).elim
  · have hpow : (f 1 : ℤ) ∣ (f 1 : ℤ) ^ (f 1) := by
      simpa using (dvd_pow_self (a := (f 1 : ℤ)) (n := f 1) (by exact h0))
    have hdiv1 : (f 1 : ℤ) ∣ (1 : ℤ) := by
      have := dvd_add h11 hpow
      simpa [sub_eq_add_neg] using this
    have : f 1 ∣ 1 := Int.ofNat_dvd.mp (by simpa using hdiv1)
    exact Nat.dvd_one.mp this

theorem bonza_divides_selfpow (hf : Bonza f) (a : ℕ) (ha : 1 ≤ a) : f a ∣ a ^ a := by
  -- From hf at (a,a): `(f a : ℤ) ∣ (a : ℤ) ^ a - (f a : ℤ) ^ (f a)`.
  have h := hf (a := a) (b := a) ha ha
  -- Show `f a ≠ 0` (else `(a,2)` would force `2^a = 1`).
  have hfa_ne : f a ≠ 0 := by
    intro h0
    rcases hf (a := a) (b := 2) ha (by decide : 1 ≤ 2) with ⟨t, ht⟩
    -- With `f a = 0`, we would get `2^a = 1`, contradicting `a ≥ 1`.
    have hpowZ : (2 : ℤ) ^ a = 1 := by
      have := sub_eq_zero.mp (by simpa [h0, zero_mul] using ht)
      simpa [h0, pow_zero] using this
    have hpowN : (2 : ℕ) ^ a = 1 := by exact_mod_cast hpowZ
    -- Using `a = k+1`, we get `2 ≤ 2^(k+1)`, hence `2 ≤ 1`, absurd.
    have hne0 : a ≠ 0 := by intro h; simpa [h] using ha
    rcases Nat.exists_eq_succ_of_ne_zero hne0 with ⟨k, hk⟩
    -- Alternatively: `1 < 2^(k+1)` contradicts `2^(k+1) = 1`.
    have hlt : 1 < (2 : ℕ) ^ (k + 1) := by
      simpa using (one_lt_pow' (a := (2 : ℕ)) (ha := by decide) (k := k + 1) (hk := by decide))
    have hpowEq : (2 : ℕ) ^ (k + 1) = 1 := by simpa [hk] using hpowN
    have : 1 < 1 := by simpa [hpowEq] using hlt
    exact (lt_irrefl (1 : ℕ)) this
  -- Using `f a ≠ 0`, we have `(f a : ℤ) ∣ (f a : ℤ) ^ (f a)`.
  have hpow : (f a : ℤ) ∣ (f a : ℤ) ^ (f a) := by
    simpa using (dvd_pow_self (a := (f a : ℤ)) (n := f a) (by exact hfa_ne))
  -- Add the two divisible terms to obtain `(f a : ℤ) ∣ (a : ℤ) ^ a`.
  have : (f a : ℤ) ∣ (a : ℤ) ^ a := by
    have hx : (f a : ℤ) ∣ (a : ℤ) ^ a - (f a : ℤ) ^ (f a) := h
    have := dvd_add hx hpow
    simpa [sub_eq_add_neg] using this
  -- Convert to ℕ divisibility.
  exact Int.ofNat_dvd.mp (by simpa using this)

theorem bonza_prime_divisor_push (hf : Bonza f)
  {a r : ℕ} (ha : 1 ≤ a) (hrp : Nat.Prime r) (hrdiv : r ∣ f a) : r ∣ f r := by
  -- From `hrdiv` and hf at `(a,r)`, we get `(r : ℤ) ∣ (r : ℤ) ^ a - (f r : ℤ) ^ (f a)`.
  have h1 : (r : ℤ) ∣ (r : ℤ) ^ a - (f r : ℤ) ^ (f a) := by
    have hfa : (r : ℤ) ∣ (f a : ℤ) := Int.ofNat_dvd.mpr hrdiv
    have h := hf (a := a) (b := r) ha (by exact Nat.succ_le_of_lt hrp.pos)
    exact Int.dvd_trans hfa h
  -- Also `(r : ℤ) ∣ (r : ℤ) ^ a` for `a ≥ 1`.
  have h2 : (r : ℤ) ∣ (r : ℤ) ^ a := by
    have hpos : 0 < a := Nat.succ_le_iff.mp ha
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨k, hk⟩
    refine ⟨(r : ℤ) ^ k, ?_⟩
    simpa [hk, mul_comm] using pow_succ (r : ℤ) k
  -- Hence `(r : ℤ) ∣ (f r : ℤ) ^ (f a)`.
  have h3 : (r : ℤ) ∣ (f r : ℤ) ^ (f a) := by
    -- since `r ∣ r^a` and `r ∣ r^a - f(r)^{f a}`
    have := dvd_sub h2 h1
    -- `r ∣ (r^a) - (r^a - f(r)^{f a}) = f(r)^{f a}`
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Switch to ℕ and use primality: `r ∣ (f r) ^ (f a)` ⇒ `r ∣ f r`.
  have : r ∣ (f r) ^ (f a) := Int.ofNat_dvd.mp (by simpa using h3)
  exact hrp.dvd_of_dvd_pow this
end

end Myproj.IMO2025P3
