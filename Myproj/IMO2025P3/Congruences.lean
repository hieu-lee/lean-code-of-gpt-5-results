import Myproj.IMO2025P3.Setup
import Myproj.IMO2025P3.Bonza
import Myproj.IMO2025P3.Axioms
import Mathlib.FieldTheory.Finite.Basic

/-!
Congruence consequences:

If `p` is an odd prime with `p ∣ f(p)`, then for all `b` one has
`b ≡ f(b) [MOD p]`.
-/

namespace Myproj.IMO2025P3

noncomputable section

open Int

variable {f : ℕ → ℕ}

private lemma pow_p_pow_modEq_self
  {p : ℕ} (hp : Nat.Prime p) (x : ℤ) : ∀ s : ℕ, x ^ (p ^ s) ≡ x [ZMOD p]
  | 0 => by simpa using (Int.ModEq.pow_prime_eq_self hp x)
  | s + 1 => by
    have := pow_p_pow_modEq_self hp x s
    -- (x^(p^s))^p ≡ x^p ≡ x [ZMOD p]
    have h1 : (x ^ (p ^ s)) ^ p ≡ x ^ p [ZMOD p] := Int.ModEq.pow _ this
    simpa [pow_mul, pow_succ] using h1.trans (Int.ModEq.pow_prime_eq_self hp x)

lemma bonza_congr_mod_p_of_p_dvd_fp
  (hf : Bonza f) {p : ℕ} (hp : Nat.Prime p)
  (hpfp : p ∣ f p) : ∀ b : ℕ, 1 ≤ b → b ≡ f b [MOD p] := by
  intro b hb
  -- From bonza at (a,b) = (p,b), reduce modulo p
  have hbonza : (f p : ℤ) ∣ ((b : ℤ) ^ p - (f b : ℤ) ^ (f p)) := by
    have hp1 : 1 ≤ p := by exact Nat.succ_le_of_lt hp.pos
    simpa using hf (a := p) (b := b) hp1 hb
  have hZmod_p : (p : ℤ) ∣ ((b : ℤ) ^ p - (f b : ℤ) ^ (f p)) :=
    Int.dvd_trans (Int.ofNat_dvd.mpr hpfp) hbonza
  -- Also, f(p) ∣ p^p, hence f(p) = p^s for some s
  have hfp_dvd : f p ∣ p ^ p := by
    simpa using (bonza_divides_selfpow (f := f) (hf := hf) (a := p) (ha := by exact Nat.succ_le_of_lt hp.pos))
  obtain ⟨s, hs_le, hfps⟩ : ∃ s ≤ p, f p = p ^ s := dvd_prime_pow_eq hp hfp_dvd
  -- Fermat in ZMod p: b^p ≡ b [ZMOD p]
  have hbmod : Int.ModEq (p : ℤ) ((b : ℤ) ^ p) (b : ℤ) :=
    fermat_little_int hp (b : ℤ)
  -- Frobenius on f(b): (f b)^(p^s) ≡ f b [ZMOD p]
  have hfb_pow : Int.ModEq (p : ℤ) ((f b : ℤ) ^ (f p)) (f b : ℤ) := by
    simpa [hfps] using pow_p_pow_modEq_self hp (f b) s
  -- From hf modulo p: b^p ≡ (f b)^(f p) [ZMOD p]
  have hmod1 : Int.ModEq (p : ℤ) ((b : ℤ) ^ p) ((f b : ℤ) ^ (f p)) := by
    -- via the divisibility statement from bonza
    exact (int_modEq_iff_dvd).2 hZmod_p
  -- Chain: b ≡ (f b)^(f p) ≡ f b [ZMOD p]
  have hbf : Int.ModEq (p : ℤ) (b : ℤ) (f b : ℤ) :=
    hbmod.symm.trans (hmod1.trans hfb_pow)
  -- Convert to Nat.ModEq
  have hdiff : (p : ℤ) ∣ ((b : ℤ) - (f b : ℤ)) := (int_modEq_iff_dvd).1 hbf
  have : (p : ℤ) ∣ ((f b : ℤ) - (b : ℤ)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiff.neg_right
  exact (Nat.modEq_iff_dvd).2 this
end

end Myproj.IMO2025P3
