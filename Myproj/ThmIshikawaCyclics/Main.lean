import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Myproj.CyclicNumbers.Axioms
import Myproj.Definitions
import Myproj.ThmFiroozbakhtCyclics3.Axioms
import Myproj.ThmFiroozbakhtCyclics4.Axioms
import Myproj.ThmVrba.Axioms
import Myproj.ThmIshikawaCyclics.Axioms

/-!
Formalisation of Theorem \ref{thm:ishikawa} from `theorems/thm_ishikawa.tex`.
We follow the LaTeX proof: a dyadic gap argument handles large indices, an
explicit check covers `3 ≤ n ≤ 21`, and a monotone bound treats the remaining
`n ≥ 22` with `c_{n+2} ≤ 115`.
-/

noncomputable section

namespace Myproj
namespace Ishikawa

open scoped BigOperators
open Real
open Classical

local notation "c" => Myproj.cyclicEnumerator

/-! ### Enumerator values as natural numbers -/

private noncomputable def cNat (n : ℕ) : ℕ := Classical.choose (cyclicEnumerator_spec n)

lemma c_cast (n : ℕ) : c n = (cNat n : ℝ) :=
  (Classical.choose_spec (cyclicEnumerator_spec n)).1

lemma cNat_isCyclic (n : ℕ) : Myproj.isCyclicNumber (cNat n) :=
  (Classical.choose_spec (cyclicEnumerator_spec n)).2

lemma cNat_strictMono : StrictMono cNat := by
  intro m n hmn
  have h := cyclicEnumerator_strictMono hmn
  have : (cNat m : ℝ) < (cNat n : ℝ) := by simpa [c_cast] using h
  exact_mod_cast this

lemma cNat_monotone : Monotone cNat := cNat_strictMono.monotone

/-! ### Counting function helpers -/

lemma count_at_enumerator {n : ℕ} (hn : 1 ≤ n) :
    Myproj.cyclicCountingReal (c n) = (n : ℝ) := by
  simpa using Myproj.cyclicCountingReal_enumerator_eq (n := n) hn

lemma count_le_of_enumerator_le {n : ℕ} {y : ℝ}
    (hn : 1 ≤ n) (hle : c n ≤ y) :
    (n : ℝ) ≤ Myproj.cyclicCountingReal y := by
  have hmono := cyclicCountingReal_monotone hle
  have hcount := count_at_enumerator (n := n) hn
  simpa [hcount]

/-! ### Base equalities -/

lemma base_case_one : c 1 + c 2 = c 3 := by
  simp [c, Myproj.cyclicEnumerator_one, Myproj.cyclicEnumerator_two,
    cyclicEnumerator_three]

lemma base_case_two : c 2 + c 3 = c 4 := by
  simp [c, Myproj.cyclicEnumerator_two, cyclicEnumerator_three,
    cyclicEnumerator_four]

/-! ### Parity facts for the enumerator -/

lemma cNat_one : cNat 1 = 1 := by
  have := c_cast 1
  simpa [c, Myproj.cyclicEnumerator_one] using this

lemma cNat_two : cNat 2 = 2 := by
  have := c_cast 2
  simpa [c, Myproj.cyclicEnumerator_two] using this

lemma gt_two_of_index_ge_three {n : ℕ} (hn : 3 ≤ n) : 2 < cNat n := by
  have hlt : (2 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : (2 : ℕ) < 3) hn
  have h := cNat_strictMono hlt
  simpa [cNat_two] using h

lemma cNat_odd_of_ge_three {n : ℕ} (hn : 3 ≤ n) : Odd (cNat n) := by
  have hcyc := cNat_isCyclic n
  by_contra hEven
  have : cNat n = 2 := even_cyclic_eq_two hcyc hEven
  have hlt := gt_two_of_index_ge_three hn
  exact lt_irrefl _ (by simpa [this] using hlt)

lemma parity_strict {n : ℕ} (hn : 3 ≤ n) :
    c n + c (n + 1) ≠ c (n + 2) := by
  classical
  have hodd₁ := cNat_odd_of_ge_three hn
  have hodd₂ := cNat_odd_of_ge_three (Nat.succ_le_succ hn)
  have hodd₃ := cNat_odd_of_ge_three (Nat.succ_le_succ (Nat.succ_le_succ hn))
  obtain ⟨a, ha⟩ := hodd₁
  obtain ⟨b, hb⟩ := hodd₂
  have hLHS_even : Even (cNat n + cNat (n + 1)) := by
    refine ⟨a + b + 1, ?_⟩
    simp [ha, hb, two_mul, add_comm, add_left_comm, add_assoc, Nat.succ_eq_add_one]
  intro h
  have hNat : cNat n + cNat (n + 1) = cNat (n + 2) := by
    exact_mod_cast (by simpa [c_cast, add_comm, add_left_comm, add_assoc] using h)
  have hRHS_even : Even (cNat (n + 2)) := by
    simpa [hNat] using hLHS_even
  exact hodd₃.not_even hRHS_even

/-! ### Dyadic argument for large `c_{n+2}` -/

lemma large_argument {n : ℕ} (hn : 1 ≤ n) (hx : 50 ≤ c (n + 2)) :
    c n + c (n + 1) > c (n + 2) := by
  classical
  set x : ℝ := c (n + 2)
  have hxC : Myproj.cyclicCountingReal x = (n + 2 : ℝ) := by
    have hx_pos : 1 ≤ n + 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
    simpa [x] using count_at_enumerator (n := n + 2) hx_pos
  have hdelta := dyadic_interval_count (n := x) hx
  have hge : Myproj.cyclicCountingReal x ≥
      Myproj.cyclicCountingReal (x / 2) + 3 := by
    have := add_le_add_right hdelta (Myproj.cyclicCountingReal (x / 2))
    simpa [x, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  have hbound : Myproj.cyclicCountingReal (x / 2) ≤ (n : ℝ) - 1 := by
    have := (le_sub_iff_add_le).2 (by simpa [hxC] using hge)
    simpa [hxC, add_comm, add_left_comm, add_assoc, x] using this
  have hx_lt : (n : ℝ) - 1 < (n : ℝ) :=
    sub_lt_self _ (show (0 : ℝ) < 1 by norm_num)
  have hx_half_lt_cn : x / 2 < c n := by
    by_contra hle
    have hcount := count_le_of_enumerator_le (n := n) hn hle
    have hle' : (n : ℝ) ≤ (n : ℝ) - 1 := le_trans hcount hbound
    exact (not_lt_of_ge hle') hx_lt
  have hx_half_lt_succ : x / 2 < c (n + 1) := by
    have hn_le : n ≤ n + 1 := Nat.le_succ _
    have hmono := cyclicEnumerator_strictMono.monotone hn_le
    have hle : c n ≤ c (n + 1) := hmono
    exact lt_of_lt_of_le hx_half_lt_cn hle
  have hsum := add_lt_add hx_half_lt_cn hx_half_lt_succ
  have hcancel : x / 2 + x / 2 = x := by
    simp [x, div_eq_mul_inv, add_comm, add_left_comm, add_assoc]
  simpa [x, hcancel] using hsum

/-! ### Finite verification `3 ≤ n ≤ 21` -/

private lemma finite_check_aux (k : Fin 19) :
    let n := k.val + 3
    c n + c (n + 1) > c (n + 2) := by
  classical
  fin_cases k using k <;>
    simp [c, add_comm, add_left_comm, add_assoc, Nat.succ_eq_add_one,
      Myproj.cyclicEnumerator_one, Myproj.cyclicEnumerator_two,
      cyclicEnumerator_three, cyclicEnumerator_four, cyclicEnumerator_five,
      cyclicEnumerator_six, cyclicEnumerator_seven, cyclicEnumerator_eight,
      cyclicEnumerator_nine, cyclicEnumerator_ten, cyclicEnumerator_eleven,
      cyclicEnumerator_twelve, cyclicEnumerator_thirteen,
      cyclicEnumerator_fourteen, cyclicEnumerator_fifteen,
      cyclicEnumerator_sixteen, cyclicEnumerator_seventeen,
      cyclicEnumerator_eighteen, cyclicEnumerator_nineteen,
      cyclicEnumerator_twenty, cyclicEnumerator_twentyOne,
      cyclicEnumerator_twentyTwo, cyclicEnumerator_twentyThree] <;> norm_num

lemma finite_check {n : ℕ} (hn₁ : 3 ≤ n) (hn₂ : n ≤ 21) :
    c n + c (n + 1) > c (n + 2) := by
  classical
  set m : ℕ := n - 3 with hm
  have hm_le : m ≤ 18 := by
    have := Nat.sub_le_sub_right hn₂ 3
    simpa [m, hm] using this
  have hm_lt : m < 19 := lt_of_le_of_lt hm_le (by decide : (18 : ℕ) < 19)
  let k : Fin 19 := ⟨m, hm_lt⟩
  have hk : n = k.val + 3 := by
    subst m
    simpa using Nat.sub_add_cancel hn₁
  simpa [hk] using finite_check_aux k

/-! ### Mid-range argument (`n ≥ 22`, `c_{n+2} ≤ 115`) -/

lemma mid_range_argument {n : ℕ} (hn : 22 ≤ n)
    (hBound : c (n + 2) < 118) :
    c n + c (n + 1) > c (n + 2) := by
  classical
  have hmono := cyclicEnumerator_strictMono.monotone
  have hcn_ge : (59 : ℝ) ≤ c n := by
    have := hmono hn
    simpa [c, cyclicEnumerator_twentyTwo] using this
  have hcn1_ge : (61 : ℝ) ≤ c (n + 1) := by
    have := hmono (Nat.succ_le_succ hn)
    simpa [c, cyclicEnumerator_twentyThree, Nat.succ_eq_add_one] using this
  have hlt44 : ¬ 44 ≤ n + 2 := by
    intro h44
    have hge := hmono h44
    have hcontr : (118 : ℝ) ≤ c (n + 2) :=
      le_trans cyclicEnumerator_fortyFour_ge hge
    exact (not_le_of_gt hBound) hcontr
  have hn2_le : n + 2 ≤ 43 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hlt44)
  have hcn2_le : c (n + 2) ≤ 115 := by
    have := hmono hn2_le
    simpa [c, cyclicEnumerator_fortyThree] using this
  have hsum_ge : (120 : ℝ) ≤ c n + c (n + 1) := by
    have : (59 : ℝ) + 61 = 120 := by norm_num
    have := add_le_add hcn_ge hcn1_ge
    simpa [this, add_comm, add_left_comm, add_assoc]
  have hstrict : c (n + 2) < 120 :=
    lt_of_le_of_lt hcn2_le (by norm_num)
  exact lt_of_lt_of_le hstrict hsum_ge

/-! ### Main theorem -/

theorem ishikawa_cyclic_gap {n : ℕ} (hn : 2 < n) :
    c n + c (n + 1) > c (n + 2) := by
  classical
  have hn₁ : 1 ≤ n := Nat.succ_le_of_lt hn
  have hn₃ : 3 ≤ n := Nat.succ_succ_le_of_lt hn
  by_cases hlarge : 50 ≤ c (n + 2)
  · exact large_argument hn₁ hlarge
  · have hsmall : c (n + 2) < 50 := lt_of_not_ge hlarge
    by_cases hn_big : 22 ≤ n
    · have hBound : c (n + 2) < 118 := lt_trans hsmall (by norm_num)
      exact mid_range_argument hn_big hBound
    · have hn₂ : n ≤ 21 := by
        have : n < 22 := Nat.lt_of_not_ge hn_big
        have : n ≤ 21 := Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using this)
        exact this
      exact finite_check hn₃ hn₂

end Ishikawa
end Myproj

end
