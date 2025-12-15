import Mathlib.Tactic
import Myproj.ThmInfinitelyManySGCyclics.Bounds

/-!
Main theorem for `theorems/thm_infinitely_many_sg_cyclics.tex`.
-/

noncomputable section

namespace Myproj

open Filter
open scoped Classical

theorem infinitely_many_sg_cyclics (inputs : SGAnalyticInputs) :
    Set.Infinite {c : ℕ | isSGCyclicNumber c} := by
  -- `Set.Infinite` is definitional `¬ Set.Finite`.
  intro hfinite
  rcases hfinite.exists_finset_coe with ⟨s, hs⟩
  have hbound : ∀ x : ℕ, sgCounting x ≤ s.card := by
    intro x
    have hsubset :
        (Finset.Icc 1 x).filter isSGCyclicNumber ⊆ s := by
      intro n hn
      have hsg : isSGCyclicNumber n := (Finset.mem_filter.mp hn).2
      have : n ∈ (↑s : Set ℕ) := by simpa [hs] using hsg
      simpa using this
    simpa [sgCounting] using Finset.card_le_card hsubset
  have hEventually :
      ∀ᶠ x : ℕ in atTop, (s.card + 1 : ℝ) ≤ (sgCounting x : ℝ) :=
    (tendsto_atTop.1 (sgCounting_tendsto_atTop inputs)) (s.card + 1)
  rcases (eventually_atTop.1 hEventually) with ⟨X, hX⟩
  have hX' : s.card + 1 ≤ sgCounting X := by
    have : (s.card + 1 : ℝ) ≤ (sgCounting X : ℝ) := hX X (le_rfl)
    exact_mod_cast this
  exact (not_lt_of_ge (hbound X)) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hX')

end Myproj

end
