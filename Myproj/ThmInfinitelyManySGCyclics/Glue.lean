import Mathlib.Tactic
import Myproj.Definitions
import Myproj.ThmLegendreCyclics.Axioms
import Myproj.ThmInfinitelyManySGCyclics.Definitions

/-!
Logical glue for `theorems/thm_infinitely_many_sg_cyclics.tex` (Steps 2–5).

This file proves that every element of the “good set” `G(x)` is an SG cyclic,
using only elementary reasoning plus Szele's criterion (imported as an axiom
in `Myproj.ThmLegendreCyclics.Axioms`).
-/

noncomputable section

namespace Myproj

open scoped Classical

private def sgBad (x : ℕ) : Finset ℕ :=
  sgS1 x ∪ sgBn x ∪ sgB2n1 x

private lemma mem_sgS0_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) : n ∈ sgS0 x :=
  (Finset.mem_sdiff.mp hn).1

private lemma mem_Icc_of_mem_sgS0 {x n : ℕ} (hn : n ∈ sgS0 x) : n ∈ Finset.Icc 1 x :=
  (Finset.mem_filter.mp hn).1

private lemma mem_Icc_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) : n ∈ Finset.Icc 1 x :=
  mem_Icc_of_mem_sgS0 (mem_sgS0_of_mem_sgG hn)

private lemma rough_left_of_mem_sgS0 {x n : ℕ} (hn : n ∈ sgS0 x) : Rough (sgY x) n :=
  (Finset.mem_filter.mp hn).2.1

private lemma rough_right_of_mem_sgS0 {x n : ℕ} (hn : n ∈ sgS0 x) : Rough (sgY x) (2 * n + 1) :=
  (Finset.mem_filter.mp hn).2.2

private lemma not_mem_sgBad_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) : n ∉ sgBad x :=
  (Finset.mem_sdiff.mp hn).2

private lemma not_mem_sgS1_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) : n ∉ sgS1 x := by
  intro hmem
  -- `sgBad x = (sgS1 x ∪ sgBn x) ∪ sgB2n1 x`
  refine not_mem_sgBad_of_mem_sgG hn ?_
  exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inl hmem

private lemma not_mem_sgBn_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) : n ∉ sgBn x := by
  intro hmem
  refine not_mem_sgBad_of_mem_sgG hn ?_
  exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inr hmem

private lemma not_mem_sgB2n1_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) : n ∉ sgB2n1 x := by
  intro hmem
  refine not_mem_sgBad_of_mem_sgG hn ?_
  exact Finset.mem_union.2 <| Or.inr hmem

private lemma rough_lt_of_prime_dvd {y : ℝ} {m p : ℕ}
    (hrough : Rough y m) (hp : Nat.Prime p) (hpm : p ∣ m) : y < (p : ℝ) := by
  rcases hrough with rfl | h
  · exfalso
    exact hp.not_dvd_one hpm
  · exact h p hp hpm

private lemma squarefree_left_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) : squarefreeNat n := by
  intro p hp
  intro hp2
  have hnS0 : n ∈ sgS0 x := mem_sgS0_of_mem_sgG hn
  have hnIcc : n ∈ Finset.Icc 1 x := mem_Icc_of_mem_sgS0 hnS0
  have hrough : Rough (sgY x) n := rough_left_of_mem_sgS0 hnS0
  have hpdvd : p ∣ n :=
    dvd_trans (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) hp2
  have hyp : sgY x < (p : ℝ) := rough_lt_of_prime_dvd hrough hp hpdvd
  have hmemS1 : n ∈ sgS1 x :=
    Finset.mem_filter.mpr ⟨hnIcc, ⟨p, hp, hyp, Or.inl hp2⟩⟩
  exact (not_mem_sgS1_of_mem_sgG hn) hmemS1

private lemma squarefree_right_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) :
    squarefreeNat (2 * n + 1) := by
  intro p hp
  intro hp2
  have hnS0 : n ∈ sgS0 x := mem_sgS0_of_mem_sgG hn
  have hnIcc : n ∈ Finset.Icc 1 x := mem_Icc_of_mem_sgS0 hnS0
  have hrough : Rough (sgY x) (2 * n + 1) := rough_right_of_mem_sgS0 hnS0
  have hpdvd : p ∣ (2 * n + 1) :=
    dvd_trans (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) hp2
  have hyp : sgY x < (p : ℝ) := rough_lt_of_prime_dvd hrough hp hpdvd
  have hmemS1 : n ∈ sgS1 x :=
    Finset.mem_filter.mpr ⟨hnIcc, ⟨p, hp, hyp, Or.inr hp2⟩⟩
  exact (not_mem_sgS1_of_mem_sgG hn) hmemS1

private lemma no_obstruction_left_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) :
    ¬ ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ p ∣ (q - 1) ∧ p ∣ n ∧ q ∣ n := by
  intro hex
  rcases hex with ⟨p, q, hp, hq, hpq, hpq1, hpn, hqn⟩
  have hnS0 : n ∈ sgS0 x := mem_sgS0_of_mem_sgG hn
  have hnIcc : n ∈ Finset.Icc 1 x := mem_Icc_of_mem_sgS0 hnS0
  have hrough : Rough (sgY x) n := rough_left_of_mem_sgS0 hnS0
  have hyp : sgY x < (p : ℝ) := rough_lt_of_prime_dvd hrough hp hpn
  have hyq : sgY x < (q : ℝ) := rough_lt_of_prime_dvd hrough hq hqn
  have hnot : ¬ p ∣ q := by
    intro hpq_dvd
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq_dvd
    exact (ne_of_lt hpq) this
  have hcop : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hp).2 hnot
  have hpq_dvd : p * q ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpn hqn
  have hmemBn : n ∈ sgBn x :=
    Finset.mem_filter.mpr ⟨hnIcc, ⟨p, q, hp, hq, hyp, hyq, hpq1, hpq_dvd⟩⟩
  exact (not_mem_sgBn_of_mem_sgG hn) hmemBn

private lemma no_obstruction_right_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) :
    ¬ ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ p ∣ (q - 1) ∧ p ∣ (2 * n + 1) ∧ q ∣ (2 * n + 1) := by
  intro hex
  rcases hex with ⟨p, q, hp, hq, hpq, hpq1, hpm, hqm⟩
  have hnS0 : n ∈ sgS0 x := mem_sgS0_of_mem_sgG hn
  have hnIcc : n ∈ Finset.Icc 1 x := mem_Icc_of_mem_sgS0 hnS0
  have hrough : Rough (sgY x) (2 * n + 1) := rough_right_of_mem_sgS0 hnS0
  have hyp : sgY x < (p : ℝ) := rough_lt_of_prime_dvd hrough hp hpm
  have hyq : sgY x < (q : ℝ) := rough_lt_of_prime_dvd hrough hq hqm
  have hnot : ¬ p ∣ q := by
    intro hpq_dvd
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq_dvd
    exact (ne_of_lt hpq) this
  have hcop : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hp).2 hnot
  have hpq_dvd : p * q ∣ (2 * n + 1) := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpm hqm
  have hmemB2 : n ∈ sgB2n1 x :=
    Finset.mem_filter.mpr ⟨hnIcc, ⟨p, q, hp, hq, hyp, hyq, hpq1, hpq_dvd⟩⟩
  exact (not_mem_sgB2n1_of_mem_sgG hn) hmemB2

/-- Step 5: every `n ∈ G(x)` is an SG cyclic. -/
lemma sg_cyclic_of_mem_sgG {x n : ℕ} (hn : n ∈ sgG x) : isSGCyclicNumber n := by
  have hsf_n : squarefreeNat n := squarefree_left_of_mem_sgG hn
  have hsf_m : squarefreeNat (2 * n + 1) := squarefree_right_of_mem_sgG hn
  have hno_n : ¬ ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ p ∣ (q - 1) ∧ p ∣ n ∧ q ∣ n :=
    no_obstruction_left_of_mem_sgG hn
  have hno_m : ¬ ∃ p q : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ p ∣ (q - 1) ∧ p ∣ (2 * n + 1) ∧ q ∣ (2 * n + 1) :=
    no_obstruction_right_of_mem_sgG hn
  have hCyc_n : isCyclicNumber n :=
    (squarefree_cyclic_iff_no_arrow (m := n) hsf_n).2 hno_n
  have hCyc_m : isCyclicNumber (2 * n + 1) :=
    (squarefree_cyclic_iff_no_arrow (m := 2 * n + 1) hsf_m).2 hno_m
  exact ⟨hCyc_n, hCyc_m⟩

/-- The counting function `C_SG(x)` (SG cyclics up to `x`). -/
def sgCounting (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter isSGCyclicNumber).card

lemma sgCounting_ge_sgG (x : ℕ) : (sgG x).card ≤ sgCounting x := by
  classical
  unfold sgCounting
  refine Finset.card_le_card ?_
  intro n hn
  have hnIcc : n ∈ Finset.Icc 1 x := mem_Icc_of_mem_sgG hn
  have hsg : isSGCyclicNumber n := sg_cyclic_of_mem_sgG hn
  exact Finset.mem_filter.mpr ⟨hnIcc, hsg⟩

end Myproj

end
