import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Myproj.Definitions
import Myproj.ThmFiroozbakhtCyclics4.Axioms
import Myproj.ThmRosser.Axioms

/-!
Rosser-type lower bound for the enumerator of cyclic numbers, following
`theorems/thm_rosser.tex`.
-/

noncomputable section

namespace Myproj
namespace Rosser

open Real

local notation "c" => Myproj.cyclicEnumerator
local notation "γ" => Myproj.eulerMascheroni

def rosserThreshold : ℕ :=
  Classical.choose eventual_rosser_lower

lemma rosserThreshold_spec {n : ℕ} (hn : rosserThreshold ≤ n) :
    Real.exp γ * (n : ℝ) * Myproj.L3R (n : ℝ) < c n :=
  (Classical.choose_spec eventual_rosser_lower) (n := n) hn

lemma rosser_small_range {n : ℕ}
    (hn₂ : 2 ≤ n) (hn₄₃ : n ≤ 43) (h4 : 4 ≤ n) :
    Real.exp γ * (n : ℝ) * Myproj.L3R (n : ℝ)
      < c n := by
  have hupper := logEnumerator_small_bound h4 hn₄₃
  have hlin := enumerator_linear_lower_bound h4
  exact lt_of_lt_of_le hupper hlin

lemma rosser_small_indices {n : ℕ}
    (hn₄ : 4 ≤ n) (hn₄₃ : n ≤ 43) :
    Real.exp γ * (n : ℝ) * Myproj.L3R (n : ℝ)
      < c n := by
  have hn₂ : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 4) hn₄
  exact rosser_small_range hn₂ hn₄₃ hn₄

lemma rosser_large_indices {n : ℕ} (hn : rosserThreshold ≤ n) :
    Real.exp γ * (n : ℝ) * Myproj.L3R (n : ℝ) < c n :=
  rosserThreshold_spec hn

theorem rosser_bound {n : ℕ} (hn₄ : 4 ≤ n) :
    (n ≤ 43 →
      Real.exp γ * (n : ℝ) * Myproj.L3R (n : ℝ) < c n) ∧
    (rosserThreshold ≤ n →
      Real.exp γ * (n : ℝ) * Myproj.L3R (n : ℝ) < c n) := by
  refine ⟨?_, ?_⟩
  · intro hsmall
    exact rosser_small_indices hn₄ hsmall
  · intro htail
    exact rosser_large_indices htail

end Rosser
end Myproj

end
