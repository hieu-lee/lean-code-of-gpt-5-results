import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Myproj.Definitions
import Myproj.ThmPanaitopol.Axioms
import Myproj.ThmLegendreCyclics.Axioms
import Myproj.ThmVrba.Axioms
import Myproj.ThmIshikawaCyclics.Axioms

/-
Formalisation of Theorem~\ref{thm:panaitopol}: the Panaitopol inequality
`c_{mn} < c_m c_n` fails because `c_{35} = 91 = c_5 c_7`.

The argument follows the LaTeX proof:
1. Record the small enumerator values `c_5 = 7`, `c_7 = 13`.
2. Use the enumerated list of cyclic numbers ≤ 91 (axiomatised in
   `Axioms.lean`) to show exactly `35` cyclic numbers lie below `91`.
3. Deduce `c_{36} > 91` and combine with surjectivity/monotonicity of the
   enumerator to conclude `c_{35} = 91`.
4. Multiply the small values to get the counterexample to the inequality.
-/

namespace Myproj
namespace Panaitopol

open scoped BigOperators
open Finset
open Real

local notation "c" => Myproj.cyclicEnumerator
local notation "C" => Myproj.cyclicCountingReal

/-- Finset used by the counting function at `91`. -/
private def countingFinset91 : Finset ℕ :=
  (Finset.Icc 1 91).filter fun n : ℕ => Myproj.isCyclicNumber n

lemma countingFinset91_eq_cyclic :
    countingFinset91 = cyclicFinsetLe91 := by
  ext n
  constructor
  · intro hn
    have hmem := (Finset.mem_filter).1 hn
    have hnIcc : n ∈ Finset.Icc 1 91 := hmem.1
    have hnUpper : n ≤ 91 := (Finset.mem_Icc).1 hnIcc |>.2
    have hcyc : Myproj.isCyclicNumber n := hmem.2
    exact (cyclic_le_91_classification hnUpper).mp hcyc
  · intro hn
    have hpos : 1 ≤ n := cyclic_le_91_mem_pos hn
    have hle : n ≤ 91 := cyclic_le_91_mem_le hn
    have hcyc : Myproj.isCyclicNumber n :=
      (cyclic_le_91_classification hle).mpr hn
    refine (Finset.mem_filter).2 ?_
    refine And.intro ?_ hcyc
    exact (Finset.mem_Icc).2 ⟨hpos, hle⟩

lemma countingReal_91 :
    C 91 = 35 := by
  unfold Myproj.cyclicCountingReal
  have hf : Nat.floor (91 : ℝ) = 91 := by simp
  have hcard :
      countingFinset91.card = cyclicFinsetLe91.card := by
    simpa [countingFinset91] using
      congrArg Finset.card countingFinset91_eq_cyclic
  have hcount : countingFinset91.card = 35 := by
    simpa [cyclic_le_91_card] using hcard
  have hcountReal : (countingFinset91.card : ℝ) = 35 := by
    exact_mod_cast hcount
  have : (countingFinset91.card : ℝ) = 35 := hcountReal
  simpa [countingFinset91, hf] using this

lemma cyclic_91 : Myproj.isCyclicNumber 91 := by
  have hmem : 91 ∈ cyclicFinsetLe91 := by
    simp [cyclicFinsetLe91, oddCyclicCompositeFinsetLe91,
      oddCyclicCompositeListLe91]
  exact (cyclic_le_91_classification (show 91 ≤ 91 by decide)).mpr hmem

lemma cyclicEnumerator_36_gt_91 :
    (91 : ℝ) < c 36 := by
  refine lt_of_not_ge ?_
  intro hle
  have hmono := Myproj.Ishikawa.cyclicCountingReal_monotone
  have hcount_c36 :
      C (c 36) = (36 : ℝ) := by
    have : 1 ≤ (36 : ℕ) := by decide
    simpa using Myproj.cyclicCountingReal_enumerator_eq (n := 36) this
  have hcount_91 := countingReal_91
  have hle' := hmono hle
  -- `36 ≤ 35` contradiction
  have : (36 : ℝ) ≤ (35 : ℝ) := by
    simpa [hcount_c36, hcount_91] using hle'
  norm_num at this

lemma cyclicEnumerator_35_le_91 :
    c 35 ≤ (91 : ℝ) := by
  obtain ⟨m, hmVal, hmCyc⟩ :=
    Myproj.Ishikawa.cyclicEnumerator_spec (n := 35)
  have hm_ge_nat : 35 ≤ m := by
    have hge := Myproj.cyclicEnumerator_ge_self 35
    have : (35 : ℝ) ≤ (m : ℝ) := by simpa [hmVal] using hge
    exact_mod_cast this
  have hmPos : 0 < m := lt_of_lt_of_le (by decide : 0 < 35) hm_ge_nat
  have hcount_m :
      C (m : ℝ) = (35 : ℝ) := by
    have : 1 ≤ (35 : ℕ) := by decide
    simpa [hmVal] using
      Myproj.cyclicCountingReal_enumerator_eq (n := 35) this
  have hcount_pred :
      C ((m - 1 : ℕ) : ℝ) = (34 : ℝ) := by
    have hinc :=
      Myproj.Ishikawa.cyclicCounting_increment_of_cyclic
        hmCyc hmPos
    have hinc' := (sub_eq_iff_eq_add).mp hinc
    have hsum : C ((m - 1 : ℕ) : ℝ) + 1 = (35 : ℝ) := by
      simpa [hcount_m, add_comm] using hinc'.symm
    linarith
  by_contra hgt
  have hgt' : (91 : ℝ) < c 35 := lt_of_not_ge hgt
  have hm_gt_nat : 91 < m := by
    have : (91 : ℝ) < (m : ℝ) := by simpa [hmVal] using hgt'
    exact_mod_cast this
  have hm_ge_nat' : 92 ≤ m := Nat.succ_le_of_lt hm_gt_nat
  have hm_ge_one : 1 ≤ m := le_trans (by decide : 1 ≤ 35) hm_ge_nat
  have hmono := Myproj.Ishikawa.cyclicCountingReal_monotone
  have hcomp : (91 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    have hm_pred : 91 ≤ m - 1 := by
      have := Nat.sub_le_sub_right hm_ge_nat' 1
      simpa using this
    exact_mod_cast hm_pred
  have hle := hmono hcomp
  have hcount_91 := countingReal_91
  have : (35 : ℝ) ≤ (34 : ℝ) := by
    simpa [hcount_91, hcount_pred] using hle
  norm_num at this

lemma cyclicEnumerator_35_ge_91 :
    (91 : ℝ) ≤ c 35 := by
  obtain ⟨k, hkEval⟩ :=
    Myproj.Ishikawa.cyclicEnumerator_surjective cyclic_91
  have hk_le : k ≤ 35 := by
    by_contra hgt
    have hk_ge : 36 ≤ k :=
      Nat.succ_le_of_lt (lt_of_not_ge hgt)
    have hmono := Myproj.Ishikawa.cyclicEnumerator_strictMono.monotone
    have hle : c 36 ≤ c k := hmono hk_ge
    have hgt' : (91 : ℝ) < c 36 := cyclicEnumerator_36_gt_91
    have : c 36 ≤ (91 : ℝ) := by simpa [hkEval] using hle
    exact not_le_of_gt hgt' this
  have hmono := Myproj.Ishikawa.cyclicEnumerator_strictMono.monotone
  have hle := hmono hk_le
  simpa [hkEval] using hle

lemma cyclicEnumerator_35_eq_91 :
    c 35 = (91 : ℝ) :=
  le_antisymm cyclicEnumerator_35_le_91 cyclicEnumerator_35_ge_91

lemma cyclicEnumerator_5_eq_7 :
    c 5 = (7 : ℝ) := by
  simpa using Myproj.Ishikawa.cyclicEnumerator_five

lemma cyclicEnumerator_7_eq_13 :
    c 7 = (13 : ℝ) := by
  simpa using Myproj.Ishikawa.cyclicEnumerator_seven

lemma cyclicEnumerator_product_5_7 :
    c 35 = c 5 * c 7 := by
  have h35 := cyclicEnumerator_35_eq_91
  have h5 := cyclicEnumerator_5_eq_7
  have h7 := cyclicEnumerator_7_eq_13
  simp [h35, h5, h7, (by norm_num : (7 : ℝ) * 13 = 91)] 

theorem panaitopol_counterexample :
    c (5 * 7) = c 5 * c 7 := by
  simpa [Nat.mul_comm] using cyclicEnumerator_product_5_7

theorem panaitopol_inequality_false :
    ¬ (∀ m n : ℕ, 3 ≤ m → m ≤ n →
        c (m * n) < c m * c n) := by
  intro h
  have hfail := h 5 7 (by decide) (by decide)
  have hEq : c (5 * 7) = c 5 * c 7 := panaitopol_counterexample
  simpa [Nat.mul_comm, hEq] using hfail

end Panaitopol
end Myproj
