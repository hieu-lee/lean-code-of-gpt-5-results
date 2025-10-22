import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Myproj.Definitions
import Myproj.CyclicNumbers.Axioms
import Myproj.ThmLegendreCyclics.Axioms
-- bounds come from axioms aggregated in `Myproj.Axioms`

/-!
Main file for the Legendre analog of cyclic integers. We combine the quantitative
estimate from axioms with a finite verification to obtain the global result.
-/

noncomputable section

namespace Myproj

open scoped Classical BigOperators

lemma legendre_large_case
    {c : ℝ} {N : ℕ}
    (hcpos : 0 < c)
    (hBound :
      ∀ ⦃n : ℕ⦄, N ≤ n → 1 < n →
        ((legendreSquarefreeRough n).card : ℝ)
            - ((legendreObstructedSet n).card : ℝ)
          ≥ c * (n : ℝ) / Real.log (n : ℝ))
    {n : ℕ} (hnN : N ≤ n) (hn1 : 1 < n) :
    ∃ m : ℕ, n ^ 2 < m ∧ m < (n + 1) ^ 2 ∧ isCyclicNumber m := by
  classical
  have hIneq := hBound hnN hn1
  have hlogpos : 0 < Real.log (n : ℝ) := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    exact Real.log_pos this
  have hnposNat : 0 < n := lt_trans (by decide : (0 : ℕ) < 1) hn1
  have hRHSpos : 0 < c * (n : ℝ) / Real.log (n : ℝ) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
    exact div_pos (mul_pos hcpos hnpos) hlogpos
  have hDiffPos :
      0 < ((legendreSquarefreeRough n).card : ℝ)
            - ((legendreObstructedSet n).card : ℝ) :=
    lt_of_lt_of_le hRHSpos hIneq
  have hCardLT_real :
      ((legendreObstructedSet n).card : ℝ)
        < ((legendreSquarefreeRough n).card : ℝ) := by
    simpa [sub_pos] using hDiffPos
  have hCardLT :
      (legendreObstructedSet n).card
        < (legendreSquarefreeRough n).card := by
    exact_mod_cast hCardLT_real
  have hSubset :
      legendreObstructedSet n ⊆ legendreSquarefreeRough n := by
    intro m hm
    exact (Finset.mem_filter.mp hm).1
  -- There exists an element of the squarefree set that is not obstructed,
  -- otherwise the two sets would be equal, contradicting `card` strictness.
  have hExists :
      ∃ m, m ∈ legendreSquarefreeRough n ∧ m ∉ legendreObstructedSet n := by
    classical
    by_contra hnone
    have hSup : legendreSquarefreeRough n ⊆ legendreObstructedSet n := by
      intro x hx
      by_contra hnot
      exact hnone ⟨x, hx, hnot⟩
    have hEq : legendreObstructedSet n = legendreSquarefreeRough n := by
      apply Finset.ext
      intro x
      constructor
      · intro hx; exact hSubset hx
      · intro hx; exact hSup hx
    have : (legendreObstructedSet n).card < (legendreSquarefreeRough n).card := hCardLT
    simpa [hEq] using this
  rcases hExists with ⟨m, hmSquare, hmNotObs⟩
  have hmFilter := Finset.mem_filter.mp hmSquare
  have hmInterval : m ∈ legendreInterval n := hmFilter.1
  have hmProps := hmFilter.2
  have hRough := hmProps.1
  have hSqfree := hmProps.2
  have hNoOb : ¬ legendreObstructed m := by
    intro hcontr
    exact hmNotObs (by
      simpa [legendreObstructedSet] using
        Finset.mem_filter.mpr ⟨hmSquare, hcontr⟩)
  have hCyclic : isCyclicNumber m := by
    refine (squarefree_cyclic_iff_no_arrow hSqfree).mpr ?_
    simpa [legendreObstructed] using hNoOb
  -- bounds from interval membership
  have hmBounds := Finset.mem_Icc.mp hmInterval
  have hLower : n ^ 2 + 1 ≤ m := hmBounds.1
  have hUpper : m ≤ (n + 1) ^ 2 - 1 := hmBounds.2
  have hLowerStrict : n ^ 2 < m := Nat.succ_le_iff.mp hLower
  have hUpperStrict : m < (n + 1) ^ 2 := by
    have hSucc : m + 1 ≤ (n + 1) ^ 2 := Nat.succ_le_succ hUpper
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hSucc
  exact ⟨m, hLowerStrict, hUpperStrict, hCyclic⟩

/--
Legendre analog for cyclic numbers: every Legendre interval contains a cyclic integer.
-/
theorem legendre_analog_cyclics (n : ℕ) (hn : 0 < n) :
    ∃ c : ℕ, n ^ 2 < c ∧ c < (n + 1) ^ 2 ∧ isCyclicNumber c := by
  classical
  obtain ⟨N0, hBound0⟩ := legendre_good_candidates_lower_bound
  -- Use the explicit constant from the axiom
  let c : ℝ := Real.exp (-Myproj.eulerMascheroni) / 8
  have hcpos : 0 < c := by
    have hpos := Real.exp_pos (-Myproj.eulerMascheroni)
    have h8 : 0 < (8 : ℝ) := by norm_num
    exact div_pos hpos h8
  let N := Nat.max N0 3
  -- Adapt `hBound0` (which requires `3 ≤ n`) to the format needed by `legendre_large_case`.
  have hBound : ∀ ⦃n : ℕ⦄, N ≤ n → 1 < n →
      ((legendreSquarefreeRough n).card : ℝ)
        - ((legendreObstructedSet n).card : ℝ)
        ≥ c * (n : ℝ) / Real.log (n : ℝ) := by
    intro n hnN hn1
    have hN0le : N0 ≤ n := le_trans (Nat.le_max_left _ _) hnN
    have hn3 : 3 ≤ n := le_trans (Nat.le_max_right _ _) hnN
    simpa [c] using hBound0 hN0le hn3
  let N₁ := max N 1
  obtain ⟨M, hNM, hSmall⟩ := legendre_small_n_verified N₁
  have hN_le_M : N ≤ M := le_trans (le_max_left _ _) hNM
  have hOne_le_M : 1 ≤ M := le_trans (le_max_right _ _) hNM
  by_cases hcase : n ≤ M
  · exact hSmall hn hcase
  · have hMlt : M < n := lt_of_not_ge hcase
    have hn1 : 1 < n := lt_of_le_of_lt hOne_le_M hMlt
    have hnN : N ≤ n := le_trans hN_le_M (le_of_lt hMlt)
    exact legendre_large_case hcpos hBound hnN hn1

end Myproj

end
