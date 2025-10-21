import Myproj.IMO2025P3.Setup
import Myproj.IMO2025P3.Axioms
import Myproj.IMO2025P3.Bonza
import Myproj.IMO2025P3.Congruences
import Myproj.IMO2025P3.TwoAdic
import Myproj.IMO2025P3.Casework
import Myproj.IMO2025P3.Fmax

/-!
Main theorem for IMO 2025 P3: The smallest real constant `c` such that
`f(n) ≤ c n` for all bonza functions `f` and all `n ≥ 1` is `c = 4`.
-/

namespace Myproj.IMO2025P3

noncomputable section

open Int

theorem bound_four (f : ℕ → ℕ) (hf : Bonza f) : ∀ n, 1 ≤ n → f n ≤ 4 * n := by
  -- From casework: either Podd f = ∅, then use 2-adic bound; or if infinite, `f n = n` for `n ≥ 1`.
  have hcase : (Podd f = ∅) ∨ (∀ n, 1 ≤ n → f n = n) := Podd_empty_or_id f hf
  intro n hn; rcases hcase with hP0 | hid
  · exact bound_four_when_Podd_empty (f := f) hf hP0 n hn
  · -- f = id ⇒ f n = n ≤ 4 n
    have hle' : n * 1 ≤ n * 4 := Nat.mul_le_mul_left n (by decide : 1 ≤ 4)
    have hle : n ≤ n * 4 := by simpa [Nat.mul_one] using hle'
    simpa [hid n hn, Nat.mul_comm] using hle

/-! Sharpness via `fmax`.
`fmax` is bonza and attains ratio `fmax(2^k)/(2^k) = 4` for all `k ≥ 2`.
This is now exposed by `fmax_sharpness`. -/

theorem sharpness_four : Bonza fmax ∧ ∀ k ≥ 2, fmax (2 ^ k) = 4 * 2 ^ k :=
  fmax_sharpness

end

end Myproj.IMO2025P3
