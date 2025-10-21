import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Myproj.Definitions
import Myproj.Axioms

-- Silence style hints to keep focus on the core argument in this file
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

/-!
Dusart analog for cyclics (disproves Conj. 53 of Cohen 2025)

This file mirrors the short contradiction in `theorems/thm_dusart_cyclics.tex`:

- Define `L3(n) = log log log n` and `L4(n) = log log log log n`.
- From Pollack (2022) and de Bruijn (1970), deduce
  `c_n = e^γ n (L3(n) + O(1))` for the nth cyclic number `c_n`.
- Hence there exist `K > 0` and `N` such that for all `n ≥ N`,
  `c_n / (e^γ n) ≤ L3(n) + K`.
- Since `L4(n) → ∞`, enlarge `N` so that `L4(n) > K` for all `n ≥ N`.
- Therefore for such `n`, `c_n < e^γ n (L3(n) + L4(n))`, contradicting the
  proposed lower bound for all `n > 1`.

References in `bib.tex`:
- Pollack (2022) for the counting asymptotic.
- de Bruijn (1970) for asymptotic inversion via conjugates.
- Cohen (2025), Conj. 53 is the conjecture being disproved.
-/

noncomputable section

namespace Myproj

open scoped BigOperators
open Filter Real

-- Use explicit local notations to avoid name resolution issues.
def L₃ (n : ℕ) : ℝ := Real.log (Real.log (Real.log (n : ℝ)))
def L₄ (n : ℕ) : ℝ := Real.log (Real.log (Real.log (Real.log (n : ℝ))))

private lemma tendsto_L₄_atTop_atTop : Tendsto L₄ atTop atTop := by
  -- Compose `natCast → log → log → log → log`.
  have h0 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp h0
  have h2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp h1
  have h3 : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp h2
  have h4 : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (Real.log (n : ℝ))))) atTop atTop :=
    Real.tendsto_log_atTop.comp h3
  simpa [L₄] using h4

/-- Main statement: the universal lower bound `c_n > e^γ n (L3(n)+L4(n))` for all `n>1` is false. -/
theorem dusart_analog_cyclics_counterexample :
    ∃ c : ℕ → ℝ,
      ¬ (∀ n : ℕ, 1 < n → c n > Real.exp eulerMascheroni * (n : ℝ) * (L₃ n + L₄ n)) := by
  classical
  -- Use the axiom-provided enumerating function for cyclic numbers.
  let c := Myproj.cyclicEnumerator
  have hpair : CountingEnumeratingPair cyclicCounting c := Myproj.cyclic_enumerator_pair
  -- From Pollack + de Bruijn, obtain an eventual `O(1)` bound for
  -- `c n / (e^γ n) - L3(n)`.
  have hPollack := pollack_poincare_cyclic_counting
  have hαpos : 0 < Real.exp (-eulerMascheroni) := by
    simpa using Real.exp_pos (-eulerMascheroni)
  have hDeB := deBruijn_asymptotic_inversion_nat
      (C := cyclicCounting) (c := c)
      (L := fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ))))
      (α := Real.exp (-eulerMascheroni))
      hpair L3_slowly_varying_nat L3_eventually_positive hαpos hPollack
  rcases hDeB with ⟨K, N₁, hKpos, hBound⟩
  -- Convert the bound to `c n ≤ e^γ n (L3(n) + K)` eventually.
  have hExpInv' : (Real.exp (-eulerMascheroni))⁻¹ = Real.exp eulerMascheroni := by
    simpa [Real.exp_neg] using (inv_inv (Real.exp eulerMascheroni))
  have hβpos : 0 < Real.exp eulerMascheroni := by
    simpa using Real.exp_pos eulerMascheroni
  have hUpper : ∀ᶠ n : ℕ in atTop,
      c n ≤ Real.exp eulerMascheroni * (n : ℝ) * (L₃ n + K) := by
    -- Strengthen the eventual bound to start from `max N₁ 2` to ensure `0 < n`.
    refine (eventually_ge_atTop (Nat.max N₁ 2)).mono ?_
    intro n hn
    have hnN₁ : N₁ ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hnpos : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    -- From `|c/(β*n) - L3| ≤ K` infer `c/(β*n) ≤ L3 + K`.
    have hbd := hBound (n := n) hnN₁
    have hle : c n / ((1 / Real.exp (-eulerMascheroni)) * (n : ℝ)) ≤ L₃ n + K := by
      have hx : |c n / ((1 / Real.exp (-eulerMascheroni)) * (n : ℝ)) - L₃ n| ≤ K := hbd
      have hx' := (abs_le.mp hx).2
      -- from `a - b ≤ K`, deduce `a ≤ b + K`
      linarith
    -- Multiply both sides by the positive factor `βn := (1/exp(-γ)) * n`.
    set βn : ℝ := (1 / Real.exp (-eulerMascheroni)) * (n : ℝ) with hβndef
    have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
    have hnposNat : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn2
    have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnposNat
    have hβinvpos : 0 < (1 / Real.exp (-eulerMascheroni)) := by
      have : 0 < Real.exp (-eulerMascheroni) := by simpa using Real.exp_pos (-eulerMascheroni)
      simpa [one_div] using inv_pos.mpr this
    have hβnpos : 0 < βn := by
      have : 0 < (1 / Real.exp (-eulerMascheroni)) * (n : ℝ) := mul_pos hβinvpos hnpos'
      simpa [hβndef] using this
    have hscale := mul_le_mul_of_nonneg_right hle (le_of_lt hβnpos)
    -- Simplify the left side to `c n` and rewrite the right side using `hExpInv'`.
    have hβ_simp : (1 / Real.exp (-eulerMascheroni)) = (Real.exp (-eulerMascheroni))⁻¹ := by
      simp [one_div]
    have hβrewrite : βn = Real.exp eulerMascheroni * (n : ℝ) := by
      have := congrArg (fun x => x * (n : ℝ)) (show (1 / Real.exp (-eulerMascheroni)) = (Real.exp (-eulerMascheroni))⁻¹ by simpa [one_div])
      simpa [hβndef, hExpInv'] using this
    have hleft : c n / βn * βn = c n := by
      have hβn_ne : βn ≠ 0 := ne_of_gt hβnpos
      -- (c / βn) * βn = c
      field_simp [hβndef, hβn_ne]
    have hright : (L₃ n + K) * βn = Real.exp eulerMascheroni * (n : ℝ) * (L₃ n + K) := by
      simpa [mul_comm, mul_left_comm, mul_assoc, hβrewrite]
    -- Finish.
    simpa [hleft, hright, mul_comm, mul_left_comm, mul_assoc] using hscale
  -- Since `L4(n) → ∞`, we can ensure `L4(n) > K` for all large `n`.
  have hL4 := tendsto_L₄_atTop_atTop
  have hL4event : ∀ᶠ n : ℕ in atTop, K < L₄ n := by
    -- Using `K + 1 ≤ L4 n` eventually implies `K < L4 n`.
    have hge := (tendsto_atTop.1 hL4) (K + 1)
    refine hge.mono ?_
    intro n hnle
    have : (K : ℝ) < K + 1 := by linarith
    exact lt_of_lt_of_le this hnle
  -- Combine the two eventual properties and contradict the universal lower bound.
  -- Build a single witness `c` and a specific large `n0` where the conjectured bound fails.
  -- Choose a common index where both eventual properties hold.
  rcases (eventually_atTop.1 hUpper) with ⟨N₂, hN₂⟩
  rcases (eventually_atTop.1 hL4event) with ⟨N₃, hN₃⟩
  let N0 : ℕ := Nat.max (Nat.max N₁ N₂) (Nat.max N₃ 2)
  have hN1le : N₁ ≤ N0 := le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hN2le : N₂ ≤ N0 := le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hN3le : N₃ ≤ N0 := le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have h2le  : 2 ≤ N0 := le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  -- Conclude by providing the witness `c` and showing the `∀`-claim fails at `n = N0`.
  refine ⟨c, ?_⟩
  refine not_forall.mpr ?_
  refine ⟨N0, ?_⟩
  -- We need to show: `¬(1 < N0 → c N0 > e^γ N0 (L3+L4))`.
  -- Note `2 ≤ N0`, hence `1 < N0`.
  have h1lt : 1 < N0 := Nat.lt_of_lt_of_le (by decide : 1 < 2) h2le
  have hUpperN : c N0 ≤ Real.exp eulerMascheroni * (N0 : ℝ) * (L₃ N0 + K) :=
    hN₂ (b := N0) hN2le
  have hL4gt : K < L₄ N0 := hN₃ (b := N0) hN3le
  have hsum_lt : L₃ N0 + K < L₃ N0 + L₄ N0 := by linarith
  have hN0posNat : 0 < N0 := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) h2le
  have hβNpos : 0 < Real.exp eulerMascheroni * (N0 : ℝ) :=
    mul_pos hβpos (by exact_mod_cast hN0posNat)
  have hlt' : Real.exp eulerMascheroni * (N0 : ℝ) * (L₃ N0 + K)
        < Real.exp eulerMascheroni * (N0 : ℝ) * (L₃ N0 + L₄ N0) := by
    exact mul_lt_mul_of_pos_left hsum_lt hβNpos
  have hstrict : c N0 < Real.exp eulerMascheroni * (N0 : ℝ) * (L₃ N0 + L₄ N0) :=
    lt_of_le_of_lt hUpperN hlt'
  refine ?_ -- construct the negation of the implication
  intro hconj
  have : c N0 ≤ Real.exp eulerMascheroni * (N0 : ℝ) * (L₃ N0 + L₄ N0) :=
    le_of_lt hstrict
  have : ¬ c N0 > Real.exp eulerMascheroni * (N0 : ℝ) * (L₃ N0 + L₄ N0) :=
    not_lt_of_ge this
  exact this (hconj h1lt)

end Myproj
