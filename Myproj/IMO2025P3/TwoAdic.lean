import Myproj.IMO2025P3.Setup
import Myproj.IMO2025P3.Axioms
import Myproj.IMO2025P3.Bonza

/-!
2-adic bound for bonza functions when `Podd f` is empty.
-/

namespace Myproj.IMO2025P3

noncomputable section

variable {f : ℕ → ℕ}

open Int

-- Step 5 helper (kept for future use): for odd prime p, f p = 1 under `Podd f = ∅`.
lemma f_odd_prime_eq_one
  (hf : Bonza f) (hP0 : Podd f = ∅)
  {p : ℕ} (hp : Nat.Prime p) (hpodd : IsOdd p) : f p = 1 := by
  -- From Podd empty, `p ∣ f p` is impossible for odd primes `p`.
  have hnot : ¬ p ∣ f p := by
    intro hdiv
    have : p ∈ Podd f := And.intro hp (And.intro hpodd hdiv)
    have : False := by simpa [hP0] using this
    exact this.elim
  -- From `f p ∣ p^p`, deduce `f p = p^s` and use `¬ p ∣ f p` to get `s = 0`.
  have hfp_dvd : f p ∣ p ^ p :=
    bonza_divides_selfpow (f := f) (hf := hf) (a := p) (ha := by exact Nat.succ_le_of_lt hp.pos)
  obtain ⟨s, hsle, hfp⟩ := dvd_prime_pow_eq (p := p) (k := p) (d := f p) hp hfp_dvd
  -- Show `s = 0` (else `p ∣ f p`).
  have hs0 : s = 0 := by
    by_contra hspos
    have hpos : 0 < s := Nat.pos_of_ne_zero hspos
    -- Then `p ∣ f p = p^s`.
    have : p ∣ f p := by
      -- Write `s = t+1` and use `p ∣ p^(t+1)`.
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨t, ht⟩
      refine ⟨p ^ t, ?_⟩
      simpa [hfp, ht, Nat.pow_succ, Nat.mul_comm]
    exact (hnot this).elim
  simpa [hfp, hs0]

-- Global bound (step 7) will be finalized in a later step; kept admitted for now.
private lemma two_pow_dvd_mono {e e' : ℕ} (hle : e ≤ e') : 2 ^ e ∣ 2 ^ e' := by
  rcases Nat.exists_eq_add_of_le hle with ⟨k, hk⟩
  refine ⟨2 ^ k, ?_⟩
  simp [hk, Nat.pow_add, Nat.mul_comm]

private lemma two_pow_pos (e : ℕ) : 0 < 2 ^ e := by
  exact pow_pos (by decide : 0 < 2) e

private lemma fn_pos_of_divides_selfpow (hf : Bonza f) {n : ℕ} (hn : 1 ≤ n) : 0 < f n := by
  -- From `f n ∣ n^n`, we cannot have `f n = 0` since `n^n > 0`.
  have hdiv : f n ∣ n ^ n := bonza_divides_selfpow (f := f) (hf := hf) (a := n) (ha := hn)
  by_cases h0 : f n = 0
  · rcases hdiv with ⟨k, hk⟩
    have hzero : n ^ n = 0 := by simpa [h0] using hk
    have hpos : 0 < n ^ n := by
      have : 0 < n := Nat.succ_le_iff.mp hn
      exact pow_pos this n
    exact (ne_of_gt hpos hzero).elim
  · exact Nat.pos_of_ne_zero h0

private lemma no_odd_prime_divides_fn
  (hf : Bonza f) (hP0 : Podd f = ∅) {n : ℕ} (hn : 1 ≤ n) :
  ∀ r : ℕ, Nat.Prime r → IsOdd r → ¬ r ∣ f n := by
  intro r hr hro hdiv
  -- From the push lemma, `r ∣ f r`, contradicting `Podd f = ∅`.
  have : r ∣ f r := bonza_prime_divisor_push (f := f) (hf := hf)
      (a := n) (r := r) (ha := hn) (hrp := hr) (hrdiv := hdiv)
  have : r ∈ Podd f := And.intro hr (And.intro hro this)
  simpa [hP0] using this

private lemma le_of_dvd_pos {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : a ≤ b := by
  rcases h with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_cases hk0 : k = 0
    · simp [hk, hk0] at hb
    · exact Nat.pos_of_ne_zero hk0
  have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkpos
  have : a ≤ a * k := by
    simpa [Nat.mul_one] using (Nat.mul_le_mul_left a hk1)
  simpa [hk] using this

lemma bound_four_when_Podd_empty (hf : Bonza f) (hP0 : Podd f = ∅) :
  ∀ n, 1 ≤ n → f n ≤ 4 * n := by
  intro n hn
  -- First, classify `f n` as a power of two using absence of odd prime divisors.
  have hpos_fn : 0 < f n := fn_pos_of_divides_selfpow (f := f) (hf := hf) (n := n) hn
  obtain ⟨e, hfe⟩ : ∃ e : ℕ, f n = 2 ^ e :=
    pow_two_classification (m := f n) (hmpos := hpos_fn)
      (h := by
        intro r hr hro
        exact no_odd_prime_divides_fn (f := f) (hf := hf) (hP0 := hP0) (n := n) hn r hr hro)
  -- Split on parity of n.
  have hpar := odd_or_even n
  rcases hpar with hodd | heven
  · -- If n is odd, then f n = 1 from divisibility into an odd number.
    have hoddpow : IsOdd (n ^ n) := odd_pow_of_odd (n := n) (m := n) hodd
    -- Show the exponent must be zero, else even divides odd.
    cases e with
    | zero =>
        -- f n = 1
        -- hence trivially ≤ 4n
        have hf1 : f n = 1 := by simpa using hfe
        have hpos4n : 0 < 4 * n := Nat.mul_pos (by decide : 0 < 4) (Nat.succ_le_iff.mp hn)
        have : 1 ≤ 4 * n := Nat.succ_le_of_lt hpos4n
        simpa [hf1] using this
    | succ e' =>
        have heav : IsEven (2 ^ (Nat.succ e')) := two_pow_even_of_pos (Nat.succ_pos _)
        have hdiv' : 2 ^ (Nat.succ e') ∣ n ^ n := by
          -- from `f n ∣ n^n` and `f n = 2^(e'+1)`
          have : f n ∣ n ^ n := bonza_divides_selfpow (f := f) (hf := hf) (a := n) (ha := hn)
          -- rewrite by `hfe`
          simpa [hfe] using this
        -- Contradiction: an even number cannot divide an odd number.
        have : False := (even_not_dvd_odd (m := 2 ^ (Nat.succ e')) (n := n ^ n) heav hoddpow) hdiv'
        exact this.elim
  · -- n is even: use the 2-adic LTE consequence with b = 3 and f(3) = 1.
    -- First, `f 3 = 1` since 3 is an odd prime and Podd f = ∅.
    have h3p : Nat.Prime 3 := by decide
    have h3odd : IsOdd 3 := by
      unfold IsOdd; decide
    have hf3 : f 3 = 1 := f_odd_prime_eq_one (f := f) (hf := hf) (hP0 := hP0) h3p h3odd
    -- From bonza at (a,b) = (n,3): `(f n : ℤ) ∣ 3^n - 1`.
    have hdivZ : (f n : ℤ) ∣ ((3 : ℤ) ^ n - 1) := by
      have := hf (a := n) (b := 3) hn (by decide : 1 ≤ 3)
      simpa [hf3] using this
    -- Since f n = 2^e, rewrite the divisibility and apply the LTE corollary.
    have hle : e ≤ nu2 n + 2 :=
      le_nu2_of_two_pow_dvd_pow3_sub_one (n := n) (e := e)
        (hnpos := Nat.succ_le_iff.mp hn) (heven := heven)
        (hdiv := by simpa [hfe] using hdivZ)
    -- Bound `f n = 2^e ≤ 2^(nu2 n + 2) ≤ 4 n`.
    have hle2 : 2 ^ e ≤ 2 ^ (nu2 n + 2) := by
      -- use divisibility monotonicity then `le_of_dvd_pos` with positivity
      have hdiv' : 2 ^ e ∣ 2 ^ (nu2 n + 2) := two_pow_dvd_mono hle
      exact le_of_dvd_pos (two_pow_pos (nu2 n + 2)) hdiv'
    have hdiv4n : 2 ^ (nu2 n + 2) ∣ 4 * n := by
      -- From `2^(nu2 n) ∣ n`, scale by 4.
      have : 2 ^ (nu2 n) ∣ n := pow_nu2_dvd n
      simpa [Nat.pow_add, Nat.pow_two, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using Nat.mul_dvd_mul_left 4 this
    have hle4n : 2 ^ (nu2 n + 2) ≤ 4 * n := by
      have hpos4n : 0 < 4 * n := Nat.mul_pos (by decide : 0 < 4) (Nat.succ_le_iff.mp hn)
      exact le_of_dvd_pos hpos4n hdiv4n
    -- Reinsert `f n` via `hfe` for the first inequality.
    have hle2' : f n ≤ 2 ^ (nu2 n + 2) := by simpa [hfe] using hle2
    exact le_trans hle2' hle4n

end

end Myproj.IMO2025P3
