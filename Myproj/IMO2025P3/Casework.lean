import Myproj.IMO2025P3.Setup
import Myproj.IMO2025P3.Bonza
import Myproj.IMO2025P3.Axioms
import Myproj.IMO2025P3.Congruences
import Myproj.IMO2025P3.CaseworkInfinite
import Mathlib.Data.Int.Basic
import Myproj.IMO2025P3.TwoAdic

namespace Myproj.IMO2025P3

noncomputable section

open Int
open Classical
open Set

attribute [local instance] Classical.decEq

variable {f : ℕ → ℕ}

/-- Positivity of `f n` from `f n ∣ n^n` and `n ≥ 1`. -/
private lemma fn_pos_of_divides_selfpow (hf : Bonza f) {n : ℕ} (hn : 1 ≤ n) : 0 < f n := by
  have hdiv : f n ∣ n ^ n := bonza_divides_selfpow (f := f) (hf := hf) (a := n) (ha := hn)
  by_cases h0 : f n = 0
  · rcases hdiv with ⟨k, hk⟩
    have : n ^ n = 0 := by simpa [h0, Nat.zero_mul] using hk
    have : 0 < n ^ n := by exact pow_pos (Nat.succ_le_iff.mp hn) n
    exact (ne_of_gt this ‹_›).elim
  · exact Nat.pos_of_ne_zero h0

/-- Finite nonempty case forces a contradiction; hence if `Podd f` is finite,
it must be empty. This matches Case II in the markdown proof (CRT + parity). -/
private lemma Podd_empty_of_finite (hf : Bonza f)
  (hfin : (Podd f).Finite) : Podd f = ∅ := by
  classical
  by_contra hne
  have hne' : (Podd f).Nonempty := by simpa [Set.eq_empty_iff_forall_notMem] using hne
  -- Enumerate Podd f as a finite set S of odd primes p with p ∣ f p
  let S : Finset ℕ := hfin.toFinset
  have hmemS : ∀ x, x ∈ S ↔ x ∈ Podd f := by simpa [S] using hfin.mem_toFinset
  have hSnonempty : S.Nonempty := by rcases hne' with ⟨p, hp⟩; exact ⟨p, (hmemS p).2 hp⟩
  have hSprop : ∀ p ∈ S, Nat.Prime p ∧ IsOdd p ∧ p ∣ f p := by
    intro p hpS; have : p ∈ Podd f := (hmemS p).1 hpS; rcases this with ⟨hp, ho, hd⟩; exact ⟨hp, ho, hd⟩
  -- Use CRT axiom to pick b with b ≡ 1 (mod 2) and b ≡ 2 (mod p) for all p ∈ S
  have hSodd : ∀ p ∈ S, Nat.Prime p ∧ IsOdd p := fun p hp => ⟨(hSprop p hp).1, (hSprop p hp).2.1⟩
  obtain ⟨b, hb2, hbS⟩ := crt_exists_one_mod_two_two_mod_primes S hSodd
  -- b ≠ 0: otherwise 0 ≡ 2 (mod p) would force odd p ∣ 2, impossible
  have hb_ge1 : 1 ≤ b := by
    by_contra hb0
    have hb0' : b = 0 := Nat.le_zero.mp (le_of_not_gt hb0)
    rcases hSnonempty with ⟨p, hpS⟩
    have hpb2 : Nat.ModEq p b 2 := hbS p hpS
    have hdiv2 : (p : ℤ) ∣ (2 : ℤ) := (Nat.modEq_iff_dvd).1 (by simpa [hb0'] using hpb2)
    have hpodd : IsOdd p := (hSprop p hpS).2.1
    -- odd primes do not divide 2
    have hdiv2Nat : p ∣ 2 := by simpa using (Int.ofNat_dvd.mp hdiv2)
    exact (odd_prime_not_dvd_two (hSprop p hpS).1 hpodd) hdiv2Nat
  -- For p ∈ S, from p ∣ f p and congruences, deduce p ∤ f b
  have hfb_not_dvd : ∀ p ∈ S, ¬ p ∣ f b := by
    intro p hpS
    have hp' : Nat.Prime p := (hSprop p hpS).1
    have hpfp : p ∣ f p := (hSprop p hpS).2.2
    have hbf : Nat.ModEq p b (f b) :=
      bonza_congr_mod_p_of_p_dvd_fp (f := f) (hf := hf) (p := p) hp' hpfp b hb_ge1
    have hb2' : Nat.ModEq p b 2 := hbS p hpS
    have hfb2 : Nat.ModEq p (f b) 2 := (Nat.ModEq.symm hbf).trans hb2'
    intro hdiv
    have h0 : Nat.ModEq p (f b) 0 := (Nat.modEq_iff_dvd).2 (by simpa using (Int.ofNat_dvd.mpr hdiv))
    have h20 : Nat.ModEq p 2 0 := (Nat.ModEq.symm hfb2).trans h0
    -- odd prime cannot have 2 ≡ 0 (mod p)
    have h20Z : Int.ModEq (p : ℤ) (2 : ℤ) 0 := (nat_modEq_iff_int_modEq).1 h20
    have hdivZ' : (p : ℤ) ∣ ((2 : ℤ) - 0) := (int_modEq_iff_dvd).1 h20Z
    have : p ∣ 2 := by simpa using (Int.ofNat_dvd.mp hdivZ')
    have hpodd : IsOdd p := (hSprop p hpS).2.1
    exact (odd_prime_not_dvd_two hp' hpodd) this
  -- No odd prime divides f b
  have hnoodd : ∀ r : ℕ, Nat.Prime r → IsOdd r → ¬ r ∣ f b := by
    intro r hr hro hdiv
    have hrr : r ∣ f r :=
      bonza_prime_divisor_push (f := f) (hf := hf) (a := b) (r := r) (ha := hb_ge1) (hrp := hr) (hrdiv := hdiv)
    have hrS : r ∈ S := (hmemS r).2 ⟨hr, hro, hrr⟩
    exact hfb_not_dvd r hrS hdiv
  -- Classify f b as 2^e; then oddness of b^b forces e=0 and f b = 1
  have hbpos : 0 < f b := fn_pos_of_divides_selfpow (f := f) (hf := hf) (n := b) hb_ge1
  obtain ⟨e, hfbpow⟩ := pow_two_classification (m := f b) (hmpos := hbpos) (h := hnoodd)
  have hbodd : IsOdd b := odd_of_mod2_eq_one hb2
  have hboddpow : IsOdd (b ^ b) := odd_pow_of_odd (n := b) (m := b) hbodd
  have : e = 0 := by
    by_contra hpos
    have heav : IsEven (2 ^ e) := two_pow_even_of_pos (Nat.pos_of_ne_zero hpos)
    have hdiv : 2 ^ e ∣ b ^ b := by have := bonza_divides_selfpow (f := f) (hf := hf) (a := b) (ha := hb_ge1); simpa [hfbpow] using this
    exact (even_not_dvd_odd (m := 2 ^ e) (n := b ^ b) heav hboddpow) hdiv
  have hfbeq1 : f b = 1 := by simpa [hfbpow, this]
  -- But for p ∈ S, f b ≡ 2 (mod p); contradiction
  rcases hSnonempty with ⟨p, hpS⟩
  have hfb2 : Nat.ModEq p (f b) 2 := (Nat.ModEq.symm (bonza_congr_mod_p_of_p_dvd_fp (f := f) (hf := hf) (p := p) (hSprop p hpS).1 (hSprop p hpS).2.2 b hb_ge1)).trans (hbS p hpS)
  have : Nat.ModEq p 1 2 := by simpa [hfbeq1] using hfb2
  exact (one_ne_two_mod_odd_prime (hSprop p hpS).1 (hSprop p hpS).2.1) this

/-- Case split used in Main: either `Podd f = ∅` or `f n = n` for all `n ≥ 1`.
Infinite case via congruences + infinite prime divisors; finite case reduces to
`Podd f = ∅` by CRT and parity. -/
theorem Podd_empty_or_id
  (f : ℕ → ℕ) (hf : Bonza f) : (Podd f = ∅) ∨ (∀ n, 1 ≤ n → f n = n) := by
  classical
  by_cases hinf : Set.Infinite (Podd f)
  · right; exact id_if_Podd_infinite (f := f) (hf := hf) hinf
  · left
    rcases Set.finite_or_infinite (Podd f) with hfin | hcontra
    · exact Podd_empty_of_finite (f := f) (hf := hf) hfin
    · exact False.elim (hinf hcontra)

end

end Myproj.IMO2025P3
