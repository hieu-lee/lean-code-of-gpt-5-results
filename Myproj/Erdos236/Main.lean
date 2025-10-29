import Mathlib
import Myproj.Erdos236.Bounds
import Myproj.Erdos236.LargeSieve

/-
# Quantitative bounds toward Erdős 236

This file packages the combinatorial and large sieve inequalities derived in
the helper modules into a single uniform estimate.  The final asymptotic
statement `representationCount n = o(log n)` will be completed in a later
iteration; here we establish a clean `O(z log z)` bound for a natural choice
of truncation parameter `z`.
-/

noncomputable section

namespace Myproj
namespace Erdos236

open Filter
open scoped BigOperators Real

/-- A convenient choice of sieve cut-off depending on `n`. -/
def pivot (n : ℕ) : ℕ :=
  max 17 ((Nat.sqrt (binarySpan n)) + 1)

lemma pivot_ge_seventeen (n : ℕ) : 17 ≤ pivot n :=
  le_max_left _ _

lemma pivot_pos (n : ℕ) : 0 < pivot n :=
  lt_of_lt_of_le (by decide : 0 < 17) (pivot_ge_seventeen n)

lemma pivot_log_pos (n : ℕ) :
    0 < Real.log (pivot n : ℝ) :=
  Real.log_pos <|
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 17)
      (by exact_mod_cast pivot_ge_seventeen n)

lemma binarySpan_le_pivot_sq (n : ℕ) :
    binarySpan n ≤ (pivot n) ^ 2 := by
  classical
  have h₁ := Nat.lt_succ_sqrt' (binarySpan n)
  have h₂ :
      (Nat.sqrt (binarySpan n) + 1) ^ 2 ≤ (pivot n) ^ 2 := by
    have hle : Nat.sqrt (binarySpan n) + 1 ≤ pivot n :=
      le_max_right _ _
    simpa [Nat.pow_two] using Nat.mul_le_mul hle hle
  have hlt := Nat.lt_of_lt_of_le h₁ h₂
  exact hlt.le

/--
For every `n ≥ 1` we obtain a uniform bound of the form
`representationCount n ≤ C z log z` with `z = pivot n`.
-/
lemma representation_three_pivot (n : ℕ) (hn : n ≠ 0) :
    (representationCount n : ℝ)
      ≤ 3 * (pivot n : ℝ) * Real.log (pivot n : ℝ) := by
  classical
  set z := pivot n
  have hz : 17 ≤ z := pivot_ge_seventeen n
  have hz_pos_nat : 0 < z := Nat.lt_of_lt_of_le (Nat.succ_pos 16) hz
  have hz_pos : 0 < (z : ℝ) := by exact_mod_cast hz_pos_nat
  have hz_gt_one_nat : 1 < z := Nat.lt_of_lt_of_le (by decide : 1 < 17) hz
  have hz_gt_one : 1 < (z : ℝ) := by exact_mod_cast hz_gt_one_nat
  have hlog_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  have h₁ :
      (representationCount n : ℝ)
        ≤ (sieveCount n z : ℝ) + (primeCount z : ℝ) :=
    by exact_mod_cast representation_le_sieve_add (n := n) (z := z) hn
  have h₂ :
      (sieveCount n z : ℝ)
        ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2)
            * Real.log (z : ℝ) / (z : ℝ) :=
    by simpa using sieveCount_log_bound (n := n) (z := z) hn hz
  have h₃ :
      (primeCount z : ℝ)
        ≤ 1.25506 * (z : ℝ) / Real.log (z : ℝ) :=
    by simpa using primeCount_upper (z := z) hz
  have hSum :
      (representationCount n : ℝ)
        ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2)
            * Real.log (z : ℝ) / (z : ℝ) +
          1.25506 * (z : ℝ) / Real.log (z : ℝ) :=
    h₁.trans <| add_le_add h₂ h₃
  have hz_le_nat : Nat.sqrt (binarySpan n) + 1 ≤ z :=
    le_max_right _ _
  have hSpan :
      (binarySpan n : ℝ) ≤ (z : ℝ) ^ 2 := by
    have hlt := Nat.lt_succ_sqrt' (binarySpan n)
    have h₁ :
        (binarySpan n : ℝ) ≤
          (Nat.sqrt (binarySpan n) + 1 : ℝ) ^ 2 :=
      (le_of_lt (by exact_mod_cast hlt))
    have hz_le : (Nat.sqrt (binarySpan n) + 1 : ℝ) ≤ (z : ℝ) :=
      by exact_mod_cast hz_le_nat
    have h₂ :
        (Nat.sqrt (binarySpan n) + 1 : ℝ) ^ 2
          ≤ (z : ℝ) ^ 2 := by
      have hMul :=
        mul_le_mul hz_le hz_le (by positivity) hz_pos.le
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hMul
    exact h₁.trans h₂
  have hSieve :
      ((binarySpan n : ℝ) + (z : ℝ) ^ 2) * Real.log (z : ℝ) / (z : ℝ)
        ≤ 2 * (z : ℝ) * Real.log (z : ℝ) := by
    have hNum :
        (binarySpan n : ℝ) + (z : ℝ) ^ 2 ≤ 2 * (z : ℝ) ^ 2 := by
      nlinarith [hSpan]
    have hfactor_nonneg :
        0 ≤ Real.log (z : ℝ) / (z : ℝ) :=
      div_nonneg hlog_pos.le hz_pos.le
    have hMul :=
      mul_le_mul_of_nonneg_right hNum hfactor_nonneg
    have hz_ne : (z : ℝ) ≠ 0 := hz_pos.ne'
    exact
      (by
        simpa [div_eq_mul_inv, hz_ne, pow_two, mul_comm, mul_left_comm,
          mul_assoc]
          using hMul)
  have hPrime :
      1.25506 * (z : ℝ) / Real.log (z : ℝ)
        ≤ (z : ℝ) * Real.log (z : ℝ) := by
    have hConstApprox :
        1.25506 ≤ 16 * (0.6931471803 : ℝ) ^ 2 := by norm_num
    have hlog2_lower : (0.6931471803 : ℝ) ≤ Real.log 2 :=
      (Real.log_two_gt_d9).le
    have hlog2_pos : 0 < Real.log 2 :=
      lt_of_le_of_lt (by norm_num) Real.log_two_gt_d9
    have hLowerSq :
        (0.6931471803 : ℝ) ^ 2 ≤ (Real.log 2) ^ 2 := by
      have :=
        mul_le_mul hlog2_lower hlog2_lower (by norm_num) hlog2_pos.le
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
    have hConst :
        1.25506 ≤ 16 * (Real.log 2) ^ 2 :=
      (le_trans hConstApprox
        (mul_le_mul_of_nonneg_left hLowerSq (by norm_num : (0 : ℝ) ≤ 16)))
    have hz16_nat : 16 ≤ z := le_trans (by decide : 16 ≤ 17) hz
    have hz16 : (16 : ℝ) ≤ z := by exact_mod_cast hz16_nat
    have hlog16 : Real.log (16 : ℝ) = (4 : ℝ) * Real.log 2 := by
      have hpow : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      simpa [hpow] using (Real.log_pow (2 : ℝ) 4)
    have hLogLower :
        4 * Real.log 2 ≤ Real.log (z : ℝ) := by
      have :=
        Real.log_le_log (by norm_num : (0 : ℝ) < 16) hz16
      simpa [hlog16] using this
    have hNonneg2 : 0 ≤ 4 * Real.log 2 := by positivity
    have hAbsLower :
        |4 * Real.log 2| ≤ |Real.log (z : ℝ)| := by
      simpa [abs_of_nonneg hNonneg2, abs_of_nonneg hlog_pos.le]
        using hLogLower
    have hLogSqLower :
        16 * (Real.log 2) ^ 2 ≤ (Real.log (z : ℝ)) ^ 2 := by
      have htemp := (sq_le_sq).2 hAbsLower
      have hconv :
          4 * (4 * (Real.log 2) ^ 2) ≤ (Real.log (z : ℝ)) ^ 2 := by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc]
          using htemp
      have hEq :
          16 * (Real.log 2) ^ 2 = 4 * (4 * (Real.log 2) ^ 2) := by
        ring
      simpa [hEq] using hconv
    have hLower :
        1.25506 ≤ (Real.log (z : ℝ)) ^ 2 :=
      hConst.trans hLogSqLower
    have hfactor_nonneg :
        0 ≤ (z : ℝ) / Real.log (z : ℝ) :=
      div_nonneg hz_pos.le hlog_pos.le
    have hMul :=
      mul_le_mul_of_nonneg_right hLower hfactor_nonneg
    have hz_ne : (z : ℝ) ≠ 0 := hz_pos.ne'
    have hlog_ne : Real.log (z : ℝ) ≠ 0 := hlog_pos.ne'
    exact
      (by
        simpa [div_eq_mul_inv, pow_two, hz_ne, hlog_ne, mul_comm,
          mul_left_comm, mul_assoc]
          using hMul)
  have hTotal :
      (representationCount n : ℝ)
        ≤ 2 * (z : ℝ) * Real.log (z : ℝ) +
            (z : ℝ) * Real.log (z : ℝ) :=
    hSum.trans <| add_le_add hSieve hPrime
  have hSimplify :
      2 * (z : ℝ) * Real.log (z : ℝ) +
          (z : ℝ) * Real.log (z : ℝ)
        = 3 * (z : ℝ) * Real.log (z : ℝ) := by
    have : (3 : ℝ) = 2 + 1 := by norm_num
    simp [this, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm]
  simpa [hSimplify]
    using hTotal

lemma binarySpan_ge_of_pow_le {n k : ℕ} (hk : twoPow k ≤ n) :
    k ≤ binarySpan n := by
  have hmono :=
    Nat.log_mono_right (b := 2) (n := twoPow k) (m := n) hk
  simpa [binarySpan, twoPow, Nat.log_pow Nat.one_lt_two] using hmono

lemma binarySpan_le_log_div (n : ℕ) (hn : 2 ≤ n) :
    (binarySpan n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hn_pos_nat : 0 < n :=
    lt_of_lt_of_le (by decide : 0 < 2) hn
  have hn_ne : n ≠ 0 := (Nat.pos_iff_ne_zero.mp hn_pos_nat)
  have hpow := Nat.pow_log_le_self (b := 2) (x := n) hn_ne
  have hPowReal :
      (2 : ℝ) ^ (binarySpan n) ≤ (n : ℝ) := by
    exact_mod_cast hpow
  have hPow_pos : 0 < (2 : ℝ) ^ (binarySpan n) :=
    pow_pos (by norm_num) _
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hlog :=
    Real.log_le_log hPow_pos hPowReal
  have hlog_pow :
      Real.log ((2 : ℝ) ^ (binarySpan n)) =
        (binarySpan n : ℝ) * Real.log 2 := by
    simpa using Real.log_pow (by norm_num : 0 < (2 : ℝ)) (binarySpan n)
  have hLog2_pos : 0 < Real.log 2 :=
    lt_of_le_of_lt (by norm_num : (0 : ℝ) ≤ 0.6931471803)
      Real.log_two_gt_d9
  have hprod :
      (binarySpan n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    simpa [hlog_pow] using hlog
  exact (le_div_iff₀' hLog2_pos).2
    (by simpa [mul_comm, mul_left_comm] using hprod)

lemma nat_sqrt_cast_le_real_sqrt (m : ℕ) :
    (Nat.sqrt m : ℝ) ≤ Real.sqrt m := by
  have hx : 0 ≤ (Nat.sqrt m : ℝ) := by exact_mod_cast Nat.zero_le _
  have hy : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le _
  have hsq :
      ((Nat.sqrt m : ℝ) ^ 2) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.sqrt_le' m)
  exact (Real.le_sqrt hx hy).2 hsq

/-- A convenient explicit threshold beyond which the analytic bounds hold. -/
def conj8Threshold : ℕ :=
  twoPow 600

lemma twoPow_pos (k : ℕ) : 0 < twoPow k := by
  unfold twoPow
  exact Nat.pow_pos (by decide : 0 < (2 : ℕ))

lemma twoPow_succ (k : ℕ) : twoPow (k + 1) = twoPow k * 2 := by
  unfold twoPow
  simpa [Nat.succ_eq_add_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using Nat.pow_succ (2 : ℕ) k

lemma log_twoPow (k : ℕ) :
    Real.log (twoPow k : ℝ) = (k : ℝ) * Real.log 2 := by
  unfold twoPow
  have hlog :
      Real.log ((2 : ℕ) ^ k : ℝ) = Real.log ((2 : ℝ) ^ k) := by
    simpa using congrArg Real.log (Nat.cast_pow (m := 2) (n := k))
  simpa [hlog] using (Real.log_pow (2 : ℝ) k)

lemma conj8Threshold_eq : conj8Threshold = twoPow 599 * 2 := by
  simpa [conj8Threshold, Nat.succ_eq_add_one] using twoPow_succ 599

lemma log_conj8Threshold :
    Real.log (conj8Threshold : ℝ) = (600 : ℝ) * Real.log 2 := by
  unfold conj8Threshold
  exact log_twoPow 600

lemma binarySpan_ge_600 {n : ℕ} (hn : conj8Threshold ≤ n) :
    600 ≤ binarySpan n := by
  have : twoPow 600 ≤ n := hn
  simpa using binarySpan_ge_of_pow_le (n := n) (k := 600) this

lemma two_le_of_threshold_le {n : ℕ} (hn : conj8Threshold ≤ n) :
    2 ≤ n := by
  have hpos : 0 < twoPow 599 := twoPow_pos _
  have hone : 1 ≤ twoPow 599 :=
    Nat.succ_le_of_lt hpos
  have hbase :
      2 ≤ conj8Threshold := by
    have hmul :
        2 ≤ twoPow 599 * 2 := by
      simpa [Nat.mul_comm] using (Nat.mul_le_mul_right 2 hone)
    simpa [conj8Threshold_eq] using hmul
  exact hbase.trans hn

lemma log_lower_of_threshold {n : ℕ} (hn : conj8Threshold ≤ n) :
    (600 : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
  have hcast :
      ((conj8Threshold : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos_thresh :
      0 < (conj8Threshold : ℝ) := by
    have hpos_nat :
        0 < conj8Threshold := by
      unfold conj8Threshold
      exact twoPow_pos _
    exact_mod_cast hpos_nat
  have hn_pos : 0 < (n : ℝ) := by
    have hn_nat : 0 < n :=
      lt_of_lt_of_le (by decide : 0 < 2) (two_le_of_threshold_le hn)
    exact_mod_cast hn_nat
  have hlog := Real.log_le_log hpos_thresh hcast
  have hlog_thresh := log_conj8Threshold
  calc
    (600 : ℝ) * Real.log 2
        = Real.log (conj8Threshold : ℝ) := hlog_thresh.symm
    _ ≤ Real.log (n : ℝ) := hlog

lemma log_two_ge_two_thirds : (2 / 3 : ℝ) ≤ Real.log 2 := by
  have hlt :
      (2 / 3 : ℝ) < Real.log 2 := by
    have happrox :
        (2 / 3 : ℝ) < 0.6931471803 := by norm_num
    exact lt_trans happrox Real.log_two_gt_d9
  exact hlt.le

lemma sqrt_log_ge_twenty {n : ℕ} (hn : conj8Threshold ≤ n) :
    (20 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
  have hlog_lower := log_lower_of_threshold hn
  have hmul :
      (600 : ℝ) * (2 / 3 : ℝ) ≤ (600 : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left log_two_ge_two_thirds (by norm_num : (0 : ℝ) ≤ 600)
  have hbound :
      (400 : ℝ) ≤ Real.log (n : ℝ) := by
    have h :=
      le_trans hmul hlog_lower
    simpa [show (600 : ℝ) * (2 / 3 : ℝ) = (400 : ℝ) by norm_num] using h
  have hmono := Real.sqrt_le_sqrt hbound
  have hsqrt400 : Real.sqrt (400 : ℝ) = (20 : ℝ) := by norm_num
  simpa [hsqrt400] using hmono

lemma inv_sqrt_log_two_le_two :
    1 / Real.sqrt (Real.log 2) ≤ (2 : ℝ) := by
  have hy : 0 ≤ (2 / 3 : ℝ) := by norm_num
  have hx : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hsq : (1 / 2 : ℝ) ^ 2 ≤ (2 / 3 : ℝ) := by norm_num
  have hhalf :
      (1 / 2 : ℝ) ≤ Real.sqrt (2 / 3 : ℝ) :=
    (Real.le_sqrt hx hy).2 hsq
  have hmono := Real.sqrt_le_sqrt log_two_ge_two_thirds
  have htotal :
      (1 / 2 : ℝ) ≤ Real.sqrt (Real.log 2) :=
    hhalf.trans hmono
  have hlog2_pos : 0 < Real.log 2 :=
    lt_of_le_of_lt (by norm_num : (0 : ℝ) ≤ 0.6931471803)
      Real.log_two_gt_d9
  have hpos : 0 < Real.sqrt (Real.log 2) :=
    Real.sqrt_pos.2 hlog2_pos
  have hineq :
      (1 : ℝ) ≤ 2 * Real.sqrt (Real.log 2) := by
    have :=
      mul_le_mul_of_nonneg_right htotal (by norm_num : (0 : ℝ) ≤ 2)
    simpa [mul_comm, mul_left_comm] using this
  exact (div_le_iff₀ hpos).2 hineq

lemma pivot_le_three_sqrt_log {n : ℕ} (hn : conj8Threshold ≤ n) :
    (pivot n : ℝ) ≤ 3 * Real.sqrt (Real.log (n : ℝ)) := by
  have hn_ge_two : 2 ≤ n := two_le_of_threshold_le hn
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    have hlower := log_lower_of_threshold hn
    have hcoeff :
        0 ≤ (600 : ℝ) * Real.log 2 :=
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 600)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    exact hcoeff.trans hlower
  have hsqrt_large :
      (20 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := sqrt_log_ge_twenty hn
  have hnat_le :
      (Nat.sqrt (binarySpan n) : ℝ) ≤
        Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (Real.log 2) := by
    have h₁ :=
      nat_sqrt_cast_le_real_sqrt (binarySpan n)
    have h₂ :
        Real.sqrt (binarySpan n : ℝ)
          ≤ Real.sqrt (Real.log (n : ℝ) / Real.log 2) := by
      have hbound := binarySpan_le_log_div n hn_ge_two
      exact Real.sqrt_le_sqrt hbound
    have hpos_log2 :
        0 ≤ Real.log 2 :=
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hpos_logn : 0 ≤ Real.log (n : ℝ) := hlog_nonneg
    have hsimp :
        Real.sqrt (Real.log (n : ℝ) / Real.log 2)
          = Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (Real.log 2) :=
      (Real.sqrt_div' _ hpos_log2).trans <| by
        simp [Real.sqrt_mul_self hpos_logn]
    calc
      (Nat.sqrt (binarySpan n) : ℝ)
          ≤ Real.sqrt (binarySpan n : ℝ) := h₁
      _ ≤ Real.sqrt (Real.log (n : ℝ) / Real.log 2) := h₂
      _ = Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (Real.log 2) := hsimp
  have hsum :
      (Nat.sqrt (binarySpan n) : ℝ) + 1
        ≤ (1 / Real.sqrt (Real.log 2) + 1) *
            Real.sqrt (Real.log (n : ℝ)) := by
    have hstep :
        (Nat.sqrt (binarySpan n) : ℝ) + 1
          ≤ Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (Real.log 2) + 1 :=
      add_le_add_right hnat_le 1
    have hhelper :
        Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (Real.log 2) + 1
          ≤ Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (Real.log 2) +
            Real.sqrt (Real.log (n : ℝ)) := by
      have : (1 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) :=
        le_trans (by norm_num) hsqrt_large
      exact add_le_add_left this _
    have hmul :
        (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (Real.log 2) +
            Real.sqrt (Real.log (n : ℝ)))
          = (1 / Real.sqrt (Real.log 2) + 1) *
              Real.sqrt (Real.log (n : ℝ)) := by
      ring_nf
    exact
      hstep.trans
        (hhelper.trans (by simpa [hmul]))
  have hcoeff :
      (1 / Real.sqrt (Real.log 2) + 1)
        ≤ (3 : ℝ) := by
    have := inv_sqrt_log_two_le_two
    linarith
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (Real.log (n : ℝ)) :=
    Real.sqrt_nonneg (Real.log (n : ℝ))
  have hNatTerm :
      ((Nat.sqrt (binarySpan n) + 1 : ℕ) : ℝ)
        ≤ 3 * Real.sqrt (Real.log (n : ℝ)) := by
    have hsum' :
        ((Nat.sqrt (binarySpan n) + 1 : ℕ) : ℝ)
          ≤ (1 / Real.sqrt (Real.log 2) + 1) *
              Real.sqrt (Real.log (n : ℝ)) := by
      simpa using hsum
    have hbound :
        (1 / Real.sqrt (Real.log 2) + 1) *
            Real.sqrt (Real.log (n : ℝ))
          ≤ 3 * Real.sqrt (Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff hsqrt_nonneg
    exact hsum'.trans hbound
  have hSeventeen :
      (17 : ℝ) ≤ 3 * Real.sqrt (Real.log (n : ℝ)) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hsqrt_large (by norm_num : (0 : ℝ) ≤ 3)
    have : (17 : ℝ) ≤ 3 * (20 : ℝ) := by norm_num
    exact this.trans hmul
  have hmax :
      max (17 : ℝ)
          ((Nat.sqrt (binarySpan n) + 1 : ℕ) : ℝ)
        ≤ 3 * Real.sqrt (Real.log (n : ℝ)) :=
    (max_le_iff).2 ⟨hSeventeen, hNatTerm⟩
  simpa [pivot, Nat.cast_max] using hmax

lemma log_pivot_le_log_log {n : ℕ} (hn : conj8Threshold ≤ n) :
    Real.log (pivot n : ℝ) ≤ Real.log (Real.log (n : ℝ)) := by
  have hpivot := pivot_le_three_sqrt_log hn
  have hsqrt_large : (20 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) :=
    sqrt_log_ge_twenty hn
  have hlog_pos :
      0 < Real.log (n : ℝ) := by
    have hconst_pos :
        0 < (600 : ℝ) * Real.log 2 := by
      have hlog2_pos :
          0 < Real.log 2 :=
        Real.log_pos (by norm_num : (1 : ℝ) < 2)
      exact mul_pos (by norm_num : (0 : ℝ) < 600) hlog2_pos
    have hlower := log_lower_of_threshold hn
    exact lt_of_lt_of_le hconst_pos hlower
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := hlog_pos.le
  have hpivot_le_log :
      (pivot n : ℝ) ≤ Real.log (n : ℝ) := by
    have hSqrtGeThree :
        (3 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) :=
      le_trans (by norm_num) hsqrt_large
    have hmul :=
      mul_le_mul_of_nonneg_right hSqrtGeThree
        (Real.sqrt_nonneg (Real.log (n : ℝ)))
    have hsq_pow :
        (Real.sqrt (Real.log (n : ℝ))) ^ 2 = Real.log (n : ℝ) :=
      Real.sq_sqrt hlog_nonneg
    have hmul_sq :
        3 * Real.sqrt (Real.log (n : ℝ)) ≤
            (Real.sqrt (Real.log (n : ℝ))) ^ 2 := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hbound :
        3 * Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
      simpa [hsq_pow] using hmul_sq
    exact hpivot.trans hbound
  have hpivot_pos : 0 < (pivot n : ℝ) :=
    by exact_mod_cast pivot_pos n
  exact Real.log_le_log hpivot_pos hpivot_le_log

lemma representation_bound_large {n : ℕ} (hn : conj8Threshold ≤ n) :
    (representationCount n : ℝ)
      ≤ (60 : ℝ) * Real.sqrt (Real.log (n : ℝ)) *
        Real.log (Real.log (n : ℝ)) := by
  have hn_ne : n ≠ 0 :=
    by
      have hthresh_pos :
          0 < conj8Threshold := by
        unfold conj8Threshold
        exact twoPow_pos _
      have : 0 < n :=
        lt_of_lt_of_le hthresh_pos hn
      exact this.ne'
  have hcount :=
    representation_three_pivot n hn_ne
  have hpivot := pivot_le_three_sqrt_log hn
  have hlog :=
    log_pivot_le_log_log hn
  have hlog_log_pos :
      0 ≤ Real.log (Real.log (n : ℝ)) := by
    have hbound :
        (400 : ℝ) ≤ Real.log (n : ℝ) := by
      have := log_lower_of_threshold hn
      have hmul :
          (600 : ℝ) * (2 / 3 : ℝ)
            ≤ (600 : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left log_two_ge_two_thirds
          (by norm_num : (0 : ℝ) ≤ 600)
      have h :=
        le_trans hmul this
      simpa [show (600 : ℝ) * (2 / 3 : ℝ) = (400 : ℝ) by norm_num] using h
    have hlogn_pos :
        0 < Real.log (n : ℝ) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 400) hbound
    have hLogLog :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 400) hbound
    have hlog400_pos :
        0 ≤ Real.log (400 : ℝ) :=
      (Real.log_pos (by norm_num : (1 : ℝ) < 400)).le
    exact hlog400_pos.trans hLogLog
  have hlog_pivot_pos :
      0 ≤ Real.log (pivot n : ℝ) :=
    (pivot_log_pos n).le
  have hprod :
      (pivot n : ℝ) * Real.log (pivot n : ℝ)
        ≤ (3 * Real.sqrt (Real.log (n : ℝ))) *
            Real.log (Real.log (n : ℝ)) := by
    have hcoeff_nonneg :
        0 ≤ 3 * Real.sqrt (Real.log (n : ℝ)) :=
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (Real.sqrt_nonneg (Real.log (n : ℝ)))
    exact
      mul_le_mul hpivot hlog hlog_pivot_pos hcoeff_nonneg
  have hmul3 :
      3 * (pivot n : ℝ) * Real.log (pivot n : ℝ)
        ≤ 3 * (3 * Real.sqrt (Real.log (n : ℝ))) *
            Real.log (Real.log (n : ℝ)) := by
    have hnonneg :
        0 ≤ Real.log (Real.log (n : ℝ)) := hlog_log_pos
    have hpos3 : 0 ≤ (3 : ℝ) := by norm_num
    have h :=
      mul_le_mul_of_nonneg_right hprod hpos3
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hcount' :
      (representationCount n : ℝ)
        ≤ 3 * (3 * Real.sqrt (Real.log (n : ℝ))) *
            Real.log (Real.log (n : ℝ)) :=
    hcount.trans <| by simpa using hmul3
  have hcoeff :
      3 * (3 * Real.sqrt (Real.log (n : ℝ))) *
          Real.log (Real.log (n : ℝ))
        = (9 : ℝ) * Real.sqrt (Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)) := by ring
  have hcount9 :
      (representationCount n : ℝ)
        ≤ (9 : ℝ) * Real.sqrt (Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)) :=
    by simpa [hcoeff] using hcount'
  have hfinal :
      (9 : ℝ) * Real.sqrt (Real.log (n : ℝ)) *
          Real.log (Real.log (n : ℝ))
        ≤ (60 : ℝ) * Real.sqrt (Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)) := by
    have hcoeff' : (9 : ℝ) ≤ (60 : ℝ) := by norm_num
    have hmult :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff'
          (Real.sqrt_nonneg (Real.log (n : ℝ))))
        hlog_log_pos
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmult
  exact hcount9.trans hfinal

lemma eventually_representation_bound :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      (representationCount n : ℝ)
        ≤ (60 : ℝ) * Real.sqrt (Real.log (n : ℝ)) *
          Real.log (Real.log (n : ℝ)) := by
  refine (eventually_ge_atTop conj8Threshold).mono ?_
  intro n hn
  exact representation_bound_large hn

lemma eventually_log_log_nonneg :
    ∀ᶠ (n : ℕ) in Filter.atTop, 0 ≤ Real.log (Real.log (n : ℝ)) := by
  refine (eventually_ge_atTop conj8Threshold).mono ?_
  intro n hn
  have hbound :
      (400 : ℝ) ≤ Real.log (n : ℝ) := by
    have := log_lower_of_threshold hn
    have hmul :
        (600 : ℝ) * (2 / 3 : ℝ)
          ≤ (600 : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left log_two_ge_two_thirds
        (by norm_num : (0 : ℝ) ≤ 600)
    have h :=
      le_trans hmul this
    simpa [show (600 : ℝ) * (2 / 3 : ℝ) = (400 : ℝ) by norm_num] using h
  have hlogn_pos :
      0 < Real.log (n : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 400) hbound
  have hLogLog :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 400) hbound
  have hlog400_pos :
      0 ≤ Real.log (400 : ℝ) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 400)).le
  exact hlog400_pos.trans hLogLog

theorem representationCount_littleO_log :
    (fun n : ℕ => (representationCount n : ℝ))
      =o[Filter.atTop] fun n => Real.log (n : ℝ) := by
  have hO :
      (fun n : ℕ => (representationCount n : ℝ))
        =O[Filter.atTop]
          fun n =>
            Real.sqrt (Real.log (n : ℝ)) *
              Real.log (Real.log (n : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound (60 : ℝ) ?_
    refine
      (eventually_representation_bound.and eventually_log_log_nonneg).mono
        ?_
    intro n hn
    rcases hn with ⟨hbound, hlog_nonneg⟩
    have hcount_nonneg :
        0 ≤ (representationCount n : ℝ) := by
      exact_mod_cast Nat.zero_le (representationCount n)
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (Real.log (n : ℝ)) :=
      Real.sqrt_nonneg _
    have hprod_nonneg :
        0 ≤ Real.sqrt (Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)) :=
      mul_nonneg hsqrt_nonneg hlog_nonneg
    have hbound'' :
        ‖(representationCount n : ℝ)‖ ≤
          (60 : ℝ) * Real.sqrt (Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)) := by
      simpa [abs_of_nonneg hcount_nonneg] using hbound
    have hrewrite_prod :
        Real.sqrt (Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)) =
          ‖Real.sqrt (Real.log (n : ℝ)) *
              Real.log (Real.log (n : ℝ))‖ :=
      (abs_of_nonneg hprod_nonneg).symm
    have hrewrite :
        (60 : ℝ) * Real.sqrt (Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)) =
          (60 : ℝ) *
            ‖Real.sqrt (Real.log (n : ℝ)) *
                Real.log (Real.log (n : ℝ))‖ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        congrArg (fun t => (60 : ℝ) * t) hrewrite_prod
    simpa [hrewrite] using hbound''
  have hLittleO_base :
      (fun x : ℝ => Real.log (Real.log x))
        =o[Filter.atTop] fun x => (Real.log x) ^ (1 / 2 : ℝ) := by
    have h :=
      isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))
    exact h.comp_tendsto Real.tendsto_log_atTop
  have htarget :
      (fun x : ℝ => (Real.log x) ^ (1 / 2 : ℝ))
        =ᶠ[Filter.atTop] fun x : ℝ => Real.sqrt (Real.log x) :=
    Filter.EventuallyEq.of_eq <| by
      funext x
      simp [Real.sqrt_eq_rpow]
  have hLittleO_real :
      (fun x : ℝ => Real.log (Real.log x))
        =o[Filter.atTop] fun x => Real.sqrt (Real.log x) :=
    hLittleO_base.congr' (Filter.EventuallyEq.rfl) htarget
  have hLittleO_prod_real' :
      (fun x : ℝ =>
          Real.log (Real.log x) * Real.sqrt (Real.log x))
        =o[Filter.atTop]
          (fun x : ℝ =>
              Real.sqrt (Real.log x) * Real.sqrt (Real.log x)) :=
    hLittleO_real.mul_isBigO
      (Asymptotics.isBigO_refl
        (fun x : ℝ => Real.sqrt (Real.log x)) Filter.atTop)
  have hEq :
      (fun x : ℝ =>
          Real.sqrt (Real.log x) * Real.sqrt (Real.log x))
        =ᶠ[Filter.atTop] fun x => Real.log x := by
    refine (eventually_ge_atTop (1 : ℝ)).mono ?_
    intro x hx
    have hx_log_nonneg :
        0 ≤ Real.log x := by
      have hx_log :=
        Real.log_le_log (by norm_num : (0 : ℝ) < 1) hx
      simpa [Real.log_one] using hx_log
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      Real.mul_self_sqrt hx_log_nonneg
  have hcomm :
      (fun x : ℝ =>
          Real.log (Real.log x) * Real.sqrt (Real.log x)) =
        fun x : ℝ =>
          Real.sqrt (Real.log x) * Real.log (Real.log x) := by
    funext x
    simp [mul_comm]
  have hLittleO_prod_real :
      (fun x : ℝ =>
          Real.sqrt (Real.log x) * Real.log (Real.log x))
        =o[Filter.atTop] fun x => Real.log x :=
    hLittleO_prod_real'.congr'
      (Filter.EventuallyEq.of_eq hcomm)
      hEq
  have hLittleO_prod_nat :
      (fun n : ℕ =>
          Real.sqrt (Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)))
        =o[Filter.atTop] fun n => Real.log (n : ℝ) :=
    hLittleO_prod_real.comp_tendsto tendsto_natCast_atTop_atTop
  exact hO.trans_isLittleO hLittleO_prod_nat

private lemma length_filter_range_eq_card_filter
    (p : ℕ → Prop) [DecidablePred p] :
    ∀ n,
      ((List.range n).filter p).length =
        ((Finset.range n).filter p).card := by
  classical
  refine Nat.rec (by simp) ?step
  intro n ih
  have hmem :
      n ∉ (Finset.range n).filter p := by
    simp [Finset.mem_filter, Finset.notMem_range_self]
  by_cases hpn : p n
  · have hlist :
        ((List.range (n + 1)).filter p).length =
          ((Finset.range n).filter p).card + 1 := by
      simp [Nat.succ_eq_add_one, List.range_succ, List.filter_append,
        ih, hpn]
    have hfin :
        ((Finset.range (n + 1)).filter p).card =
          ((Finset.range n).filter p).card + 1 := by
      have hset :
          ((Finset.range (n + 1)).filter p) =
            insert n ((Finset.range n).filter p) := by
        simpa [Nat.succ_eq_add_one, Finset.range_add_one, hpn]
          using
            (Finset.filter_insert (a := n) (s := Finset.range n) (p := p))
      simpa [hset] using
        (Finset.card_insert (s := (Finset.range n).filter p) (a := n) hmem)
    simpa [hlist, hfin]
  · have hlist :
        ((List.range (n + 1)).filter p).length =
          ((Finset.range n).filter p).card := by
      simp [Nat.succ_eq_add_one, List.range_succ, List.filter_append,
        ih, hpn]
    have hfin :
        ((Finset.range (n + 1)).filter p).card =
          ((Finset.range n).filter p).card := by
      have hset :
          ((Finset.range (n + 1)).filter p) =
            (Finset.range n).filter p := by
        simpa [Nat.succ_eq_add_one, Finset.range_add_one, hpn]
          using
            (Finset.filter_insert (a := n) (s := Finset.range n) (p := p))
      simpa [hset]
    simpa [hlist, hfin]

/--
$f(n)$ counts the number of solutions to $n = p + 2^k$ for prime $p$ and $k ≥ 0$.
-/
def f (n : ℕ) : ℕ :=
  ((List.range (Nat.log2 n + 1)).filter fun k => Nat.Prime (n - 2 ^ k)).length

lemma f_eq_representationCount (n : ℕ) :
    f n = representationCount n := by
  classical
  have :=
    length_filter_range_eq_card_filter
      (p := fun k ↦ Nat.Prime (n - 2 ^ k)) (n := Nat.log2 n + 1)
  simpa [f, representationCount, repSet, diffValue, binarySpan,
    Nat.log2_eq_log_two, Nat.succ_eq_add_one, twoPow]
    using this

/--
Let $f(n)$ count the number of solutions to $n = p + 2^k$ for prime $p$ and $k ≥ 0$.
-/
theorem erdos_236 :
    (fun n => (f n : ℝ))
      =o[Filter.atTop] fun n => Real.log (n : ℝ) := by
  simpa [f_eq_representationCount] using representationCount_littleO_log
end Erdos236
end Myproj
