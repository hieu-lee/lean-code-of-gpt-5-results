import Myproj.IMO2025P3.Setup
import Myproj.IMO2025P3.Bonza
import Myproj.IMO2025P3.Axioms
import Myproj.IMO2025P3.Congruences

/-!
Infinite-case lemma: If `Podd f` is infinite, then `f n = n` for all `n ≥ 1`.
This matches the “Case I” in the markdown proof, via the axiom that any
nonzero integer has only finitely many prime divisors.
-/

namespace Myproj.IMO2025P3

noncomputable section

open Int
open Set

variable {f : ℕ → ℕ}

lemma id_if_Podd_infinite (hf : Bonza f)
  (hinf : Set.Infinite (Podd f)) : ∀ n, 1 ≤ n → f n = n := by
  intro n hn
  -- For every p in Podd f, we have n ≡ f(n) [MOD p].
  have hcongr : ∀ {p}, p ∈ Podd f → Nat.ModEq p n (f n) := by
    intro p hp
    rcases hp with ⟨hpprime, _hpodd, hpfp⟩
    exact bonza_congr_mod_p_of_p_dvd_fp (f := f) (hf := hf) (p := p) hpprime hpfp n hn
  -- Hence each such p divides (n - f n) in ℤ.
  have hsubset : Podd f ⊆ {p : ℕ | Nat.Prime p ∧ (p : ℤ) ∣ ((n : ℤ) - (f n : ℤ))} := by
    intro p hp
    rcases hp with ⟨hpprime, hpodd, hpfp⟩
    have hmn : Nat.ModEq p n (f n) := hcongr (by exact And.intro hpprime (And.intro hpodd hpfp))
    -- `Nat.ModEq p n (f n)` ⇒ `(p : ℤ) ∣ (n : ℤ) - (f n : ℤ)`.
    have : (p : ℤ) ∣ ((f n : ℤ) - (n : ℤ)) := (Nat.modEq_iff_dvd).1 hmn
    have h' : (p : ℤ) ∣ ((n : ℤ) - (f n : ℤ)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.neg_right
    exact ⟨hpprime, h'⟩
  have hSinf : Set.Infinite {p : ℕ | Nat.Prime p ∧ (p : ℤ) ∣ ((n : ℤ) - (f n : ℤ))} :=
    hinf.mono hsubset
  -- Apply the axiom: infinitely many prime divisors ⇒ the integer is zero.
  have hz : ((n : ℤ) - (f n : ℤ)) = 0 :=
    int_infinite_prime_divisors_implies_zero (z := ((n : ℤ) - (f n : ℤ))) hSinf
  -- Conclude `f n = n`.
  have : (n : ℤ) = (f n : ℤ) := by
    simpa using sub_eq_zero.mp hz
  exact_mod_cast this.symm

end

end Myproj.IMO2025P3
