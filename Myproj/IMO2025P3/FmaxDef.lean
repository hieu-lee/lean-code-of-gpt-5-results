import Myproj.IMO2025P3.Setup
import Myproj.IMO2025P3.Axioms

/-!
Definition of `fmax` and its immediate evaluations used by the sharpness proof.
-/

namespace Myproj.IMO2025P3

noncomputable section

open Int
open Classical

def fmax (n : ℕ) : ℕ :=
  if n = 1 then 1
  else if IsOdd n then 1
  else if n = 2 then 4
  else 2 ^ (nu2 n + 2)

private lemma odd_even_contra {n : ℕ} (hodd : IsOdd n) (heven : IsEven n) : False := by
  have h0 : n % 2 = 0 := by simpa [IsEven] using heven
  have h1 : n % 2 = 1 := by simpa [IsOdd] using hodd
  exact (Nat.zero_ne_one (by simpa [h0] using h1)).elim

lemma fmax_odd (n : ℕ) (hn : IsOdd n) : fmax n = 1 := by
  by_cases h1 : n = 1
  · simpa [fmax, h1]
  · simp [fmax, h1, hn]

lemma fmax_two : fmax 2 = 4 := by
  -- IsOdd 2 is false since 2 % 2 = 0
  have hmod : 2 % 2 = 0 := Nat.mod_self 2
  have : ¬ IsOdd 2 := by
    intro h
    have : 0 = 1 := by simpa [IsOdd, hmod] using h
    exact Nat.zero_ne_one this
  simp [fmax, this]

lemma fmax_even_ge4_eval {a : ℕ}
  (ha_even : IsEven a) (ha_ne1 : a ≠ 1) (ha_ne2 : a ≠ 2) :
  fmax a = 2 ^ (nu2 a + 2) := by
  unfold fmax
  by_cases h1 : a = 1
  · exact (ha_ne1 h1).elim
  by_cases hodd : IsOdd a
  · exact (odd_even_contra hodd ha_even).elim
  by_cases h2 : a = 2
  · exact (ha_ne2 h2).elim
  · simp [fmax, h1, hodd, h2]

end

end Myproj.IMO2025P3
