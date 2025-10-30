import Mathlib.Tactic
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Myproj.CyclicNumbers.Axioms
import Myproj.ThmFiroozbakhtCyclics3.Axioms
import Myproj.ThmFiroozbakhtCyclics4.Axioms

/-
# Firoozbakht analogue for cyclic numbers (Step 4)

Lean translation of `thm_firoozbakht_cyclics_4.tex`. We encode the analytic
inputs—primes are cyclic and Rosser–Schoenfeld bounds—as axioms so the proof
follows the LaTeX argument closely.
-/

noncomputable section

namespace Myproj

open scoped Real
open Filter
open Real

private noncomputable abbrev c (n : ℕ) : ℝ := Myproj.cyclicEnumerator n

/-- The normalised cyclic enumerator `aₙ(k) = c_{n+1}^{1/(n+1+k)}`. -/
def cyclicNormalised (k n : ℕ) : ℝ :=
  Real.rpow (c (n + 1)) (1 / (n + 1 + k : ℝ))

private lemma cyclicEnumerator_pos {n : ℕ} (hn : 0 < n) : 0 < c n := by
  have hge : (n : ℝ) ≤ c n := Myproj.cyclicEnumerator_ge_self n
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact lt_of_lt_of_le hn' hge

private lemma base_ge_one (n : ℕ) : (1 : ℝ) ≤ c (n + 1) := by
  have hge : ((n + 1 : ℕ) : ℝ) ≤ c (n + 1) := Myproj.cyclicEnumerator_ge_self (n + 1)
  have h₁ : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm] using le_trans h₁ hge

private lemma base_gt_one {n : ℕ} (hn : 1 ≤ n) : 1 < c (n + 1) := by
  have hge : ((n + 1 : ℕ) : ℝ) ≤ c (n + 1) := Myproj.cyclicEnumerator_ge_self (n + 1)
  have htwo : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hn
  have hone : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le one_lt_two htwo
  simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm] using lt_of_lt_of_le hone hge

private lemma cyclicNormalised_eq_exp (k n : ℕ) :
    cyclicNormalised k n =
      Real.exp (Real.log (c (n + 1)) / (n + 1 + k : ℝ)) := by
  have hpos : 0 < c (n + 1) := cyclicEnumerator_pos (Nat.succ_pos _)
  simp [cyclicNormalised, Real.rpow_def_of_pos, hpos,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
    Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]

private lemma cyclicNormalised_zero (k : ℕ) :
    cyclicNormalised k 0 = 1 := by
  simp [cyclicNormalised, Myproj.cyclicEnumerator_one, Real.one_rpow]

private lemma cyclicNormalised_one_gt_one (k : ℕ) :
    1 < cyclicNormalised k 1 := by
  have hpos :
      0 < Real.log 2 / (2 + k : ℝ) := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hden : 0 < (2 + k : ℝ) := by
      have : 0 < (k + 2 : ℝ) := by exact_mod_cast Nat.succ_pos (k + 1)
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm] using this
    simpa [div_eq_mul_inv] using div_pos hlog hden
  have hrewrite :
      cyclicNormalised k 1
        = Real.exp (Real.log 2 / (2 + k : ℝ)) := by
    have h := cyclicNormalised_eq_exp k 1
    simp [c, Myproj.cyclicEnumerator_two, Nat.succ_eq_add_one,
      Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] at h
    simpa [add_comm, add_left_comm, add_assoc, one_add_one_eq_two] using h
  have : 1 < Real.exp (Real.log 2 / (2 + k : ℝ)) := by
    simpa [Real.one_lt_exp_iff] using hpos
  simpa [hrewrite] using this

private lemma eventually_cyclicNormalised_lt_one (k : ℕ) :
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n → cyclicNormalised k n < cyclicNormalised k 1 := by
  classical
  obtain ⟨N, hN⟩ := Myproj.eventually_log_cyclicEnumerator_lt k
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hN' : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hlog := hN hN'
  have hx := Real.exp_lt_exp.mpr hlog
  simpa [cyclicNormalised_eq_exp, c, Myproj.cyclicEnumerator_two,
    Nat.succ_eq_add_one, Nat.add_assoc, Nat.cast_add, Nat.cast_one,
    add_comm, add_left_comm, add_assoc, one_add_one_eq_two]
    using hx

private lemma exists_max_normalised (k : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧
      ∀ m : ℕ, cyclicNormalised k m ≤ cyclicNormalised k n := by
  classical
  obtain ⟨N, hN⟩ := eventually_cyclicNormalised_lt_one k
  let M := max N 1
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hN_le_M : N ≤ M := le_max_left _ _
  have htail :
      ∀ ⦃n : ℕ⦄, M ≤ n → cyclicNormalised k n < cyclicNormalised k 1 := by
    intro n hn
    apply hN
    exact le_trans hN_le_M hn
  let s := Finset.range (M + 1)
  have hs_nonempty : s.Nonempty :=
    ⟨0, by
      refine Finset.mem_range.mpr ?_
      exact Nat.succ_pos _⟩
  obtain ⟨n, hn_s, hmax⟩ :=
    s.exists_max_image (fun m => cyclicNormalised k m) hs_nonempty
  have hn_le : n ≤ M := by
    have : n < M + 1 := Finset.mem_range.mp hn_s
    exact Nat.lt_succ_iff.mp this
  have hn_ge_one : 1 ≤ n := by
    have h1_mem : 1 ∈ s := by
      refine Finset.mem_range.mpr ?_
      exact Nat.lt_succ_of_le hM_ge_one
    have hcompare := hmax 1 h1_mem
    have hstrict := cyclicNormalised_one_gt_one k
    by_cases hnz : n = 0
    · have hzero : cyclicNormalised k n = 1 := by simpa [hnz, cyclicNormalised_zero]
      have : cyclicNormalised k 1 ≤ 1 := by simpa [hzero] using hcompare
      exact (not_lt_of_ge this hstrict).elim
    · have hpos : 0 < n := Nat.pos_of_ne_zero hnz
      exact Nat.succ_le_of_lt hpos
  have hbound_le :
      ∀ m ≤ M, cyclicNormalised k m ≤ cyclicNormalised k n := by
    intro m hm
    have hm_mem : m ∈ s := by
      refine Finset.mem_range.mpr ?_
      exact Nat.lt_succ_of_le hm
    exact hmax m hm_mem
  have hmajor :
      ∀ m : ℕ, cyclicNormalised k m ≤ cyclicNormalised k n := by
    intro m
    by_cases hm : m ≤ M
    · exact hbound_le m hm
    · have hgt : M ≤ m := le_of_lt (lt_of_not_ge hm)
      have hlt := htail hgt
      have h1_le : cyclicNormalised k 1 ≤ cyclicNormalised k n :=
        hbound_le 1 hM_ge_one
      exact (hlt.trans_le h1_le).le
  exact ⟨n, hn_ge_one, hmajor⟩

noncomputable def cyclicEnvelopeIndex (k : ℕ) : ℕ :=
  Classical.choose (exists_max_normalised k)

lemma cyclicEnvelopeIndex_pos (k : ℕ) : 1 ≤ cyclicEnvelopeIndex k := by
  classical
  obtain ⟨hpos, _⟩ := Classical.choose_spec (exists_max_normalised k)
  simpa using hpos

lemma cyclicEnvelopeIndex_spec (k : ℕ) :
    ∀ m : ℕ, cyclicNormalised k m ≤
      cyclicNormalised k (cyclicEnvelopeIndex k) := by
  classical
  obtain ⟨_, hmajor⟩ := Classical.choose_spec (exists_max_normalised k)
  simpa using hmajor

/-- `A_𝒞(k)` realised at the chosen maximiser. -/
def cyclicEnvelope (k : ℕ) : ℝ :=
  cyclicNormalised k (cyclicEnvelopeIndex k)

lemma cyclicEnvelope_spec (k : ℕ) :
    ∀ m : ℕ, cyclicNormalised k m ≤ cyclicEnvelope k :=
  cyclicEnvelopeIndex_spec k

lemma envelope_gt_one (k : ℕ) :
    1 < cyclicEnvelope k := by
  have hmem := cyclicEnvelope_spec k 1
  exact lt_of_lt_of_le (cyclicNormalised_one_gt_one k) hmem

private lemma cyclicNormalised_succ_le (k n : ℕ) :
    cyclicNormalised (k + 1) n ≤ cyclicNormalised k n := by
  have hbase : (1 : ℝ) ≤ c (n + 1) := base_ge_one n
  have hpos' : 0 < (n : ℝ) + 1 + k := by
    have : 0 < (n + k + 1 : ℝ) := by exact_mod_cast Nat.succ_pos (n + k)
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using this
  have hpos : 0 < (n + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hpos'
  have hle : 1 / (n + 1 + (k + 1) : ℝ) ≤ 1 / (n + 1 + k : ℝ) := by
    have hden_le :
        (n + 1 + k : ℝ) ≤ (n + 1 + (k + 1) : ℝ) := by
      have : (n + 1 + k : ℝ) + 0 ≤ (n + 1 + k : ℝ) + 1 :=
        add_le_add_left (show (0 : ℝ) ≤ 1 by norm_num) _
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
        using this
    exact one_div_le_one_div_of_le hpos hden_le
  have hmono := Real.monotone_rpow_of_base_ge_one hbase hle
  have hmono' := hmono
  simp [cyclicNormalised, c, Nat.cast_add, Nat.cast_one,
    add_comm, add_left_comm, add_assoc, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] at hmono'
  simpa [cyclicNormalised, c, Nat.cast_add, Nat.cast_one,
    add_comm, add_left_comm, add_assoc, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hmono'

private lemma cyclicNormalised_succ_lt (k n : ℕ) (hn : 1 ≤ n) :
    cyclicNormalised (k + 1) n < cyclicNormalised k n := by
  have hbase : 1 < c (n + 1) := base_gt_one hn
  have hlt : 1 / (n + 1 + (k + 1) : ℝ)
      < 1 / (n + 1 + k : ℝ) := by
    have hpos' : 0 < (n : ℝ) + 1 + k := by
      have : 0 < (n + k + 1 : ℝ) := by exact_mod_cast Nat.succ_pos (n + k)
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using this
    have hpos : 0 < (n + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hpos'
    have hden_lt :
        (n + 1 + k : ℝ) < (n + 1 + (k + 1) : ℝ) := by
      have : (n + 1 + k : ℝ) + 0 < (n + 1 + k : ℝ) + 1 :=
        add_lt_add_left (show (0 : ℝ) < 1 by norm_num) _
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
        using this
    exact one_div_lt_one_div_of_lt hpos hden_lt
  have hpow := Real.rpow_lt_rpow_of_exponent_lt hbase hlt
  have hpow' := hpow
  simp [cyclicNormalised, c, Nat.cast_add, Nat.cast_one,
    add_comm, add_left_comm, add_assoc, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] at hpow'
  simpa [cyclicNormalised, c, Nat.cast_add, Nat.cast_one,
    add_comm, add_left_comm, add_assoc, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hpow'

private lemma envelope_succ_lt (k : ℕ) :
    cyclicEnvelope (k + 1) < cyclicEnvelope k := by
  classical
  let n := cyclicEnvelopeIndex k
  let m := cyclicEnvelopeIndex (k + 1)
  have hm_ge_one : 1 ≤ m := cyclicEnvelopeIndex_pos (k + 1)
  have hlt :
      cyclicNormalised (k + 1) m < cyclicNormalised k m :=
    cyclicNormalised_succ_lt k m hm_ge_one
  have hmajor : cyclicNormalised k m ≤ cyclicNormalised k n := by
    simpa [cyclicEnvelope, n] using cyclicEnvelope_spec k m
  have hstrict := lt_of_lt_of_le hlt hmajor
  simpa [cyclicEnvelope, n, m] using hstrict

/-- Main theorem: `A_𝒞(k)` strictly decreases in `k`. -/
theorem firoozbakht_cyclics_four :
    StrictAnti (fun k : ℕ => cyclicEnvelope k) := by
  classical
  have hsucc : ∀ k : ℕ, cyclicEnvelope (k + 1) < cyclicEnvelope k :=
    envelope_succ_lt
  refine strictAnti_of_succ_lt fun k _ => hsucc k

end Myproj
