import Mathlib
import Myproj.Erdos236.Bounds
import Myproj.Erdos236.Axioms

/-
# Large sieve bounds for Erdős 236

We specialise the additive large sieve axiom and develop the analytic
inequalities for the sieve quantities `sieveCount` and `residueCount`.
-/

noncomputable section

namespace Myproj
namespace Erdos236

open scoped BigOperators
open Finset Real

lemma cauchySchwarz_sq {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ x ∈ s, f x) ^ 2
      ≤ (s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 := by
  classical
  have :=
    sum_mul_sq_le_sq_mul_sq (s := s)
      (f := fun x => f x) (g := fun _ : α => (1 : ℝ))
  have hleft :
      ∑ x ∈ s, (fun x => f x) x * (fun _ => (1 : ℝ)) x =
        ∑ x ∈ s, f x := by
    simp
  have hright :
      ∑ x ∈ s, (fun _ : α => (1 : ℝ)) x ^ 2 = s.card := by
    simp
  simpa [hleft, hright, mul_comm, mul_left_comm, mul_assoc]
    using this

lemma sum_residueCount_eq_card
    (T : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    ∑ b ∈ range q, residueCount T q b = T.card := by
  classical
  have hmap :
      ∀ t ∈ T, t % q ∈ range q := by
    intro t _
    exact mem_range.mpr (Nat.mod_lt _ hq)
  have hcard :=
    Finset.card_eq_sum_card_fiberwise
      (s := T) (t := range q) (f := fun t => t % q) hmap
  have : ∑ b ∈ range q, #{a ∈ T | a % q = b} = T.card := by
    simpa using hcard.symm
  have hfilter :
      ∀ b, #{a ∈ T | a % q = b} =
        (T.filter fun t => t % q = b).card := by
    intro b
    rfl
  calc
    ∑ b ∈ range q, residueCount T q b
        = ∑ b ∈ range q,
            (T.filter fun t => t % q = b).card := rfl
    _ = ∑ b ∈ range q, #{a ∈ T | a % q = b} := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      simpa [hfilter]
    _ = T.card := this

lemma residueCount_sq_lower
    (T : Finset ℕ) {q : ℕ} (hq : 0 < q) :
    (T.card : ℝ) ^ 2
      ≤ (q : ℝ) *
          ∑ b ∈ range q,
            (residueCount T q b : ℝ) ^ 2 := by
  classical
  have hsumNat := sum_residueCount_eq_card (T := T) hq
  have hsum :
      ∑ b ∈ range q, (residueCount T q b : ℝ) =
        T.card := by
    simpa using congrArg (fun n : ℕ => (n : ℝ)) hsumNat
  have hcs :=
    cauchySchwarz_sq
      (s := range q)
      (f := fun b => (residueCount T q b : ℝ))
  simpa [hsum, Finset.card_range, pow_two, mul_comm,
    mul_left_comm, mul_assoc] using hcs

/-! ### Large sieve bounds specialised to `sieveSet` -/

lemma sieveCount_prime_square_bound
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z) :
    (primeCount z : ℝ) * (sieveCount n z : ℝ) ^ 2
      ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2) *
          (sieveCount n z : ℝ) := by
  classical
  set S := sieveSet n z
  have hRange :
      ∀ t ∈ S, t ≤ binarySpan n := by
    intro t ht
    exact Nat.lt_succ_iff.mp <| mem_range.mp (sieve_subset_range n z ht)
  have hLargeSieve :=
    additiveLargeSieve
      (N := binarySpan n) (Q := z) (T := S) hRange hz
  set primes := (range (z + 1)).filter Nat.Prime
  have hSubset : primes ⊆ Icc 1 z := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hpRange, hpPrime⟩
    exact mem_Icc.mpr ⟨hpPrime.one_le,
      Nat.lt_succ_iff.mp (mem_range.mp hpRange)⟩
  have hNonneg :
      ∀ q ∈ Icc 1 z,
        0 ≤ (q : ℝ) *
            ∑ b ∈ range q,
              (residueCount S q b : ℝ) ^ 2 := by
    intro q hq
    refine mul_nonneg ?_ ?_
    · exact_mod_cast (Nat.zero_le q)
    · exact sum_nonneg fun _ _ => sq_nonneg _
  have hPrimes :
      ∑ p ∈ primes,
          (sieveCount n z : ℝ) ^ 2
        ≤
          ∑ q ∈ Icc 1 z,
            (q : ℝ) *
              ∑ b ∈ range q,
                (residueCount S q b : ℝ) ^ 2 := by
    have hLower :
        ∑ p ∈ primes,
            (sieveCount n z : ℝ) ^ 2
          ≤
            ∑ p ∈ primes,
              (p : ℝ) *
                ∑ b ∈ range p,
                  (residueCount S p b : ℝ) ^ 2 := by
      refine sum_le_sum ?_
      intro p hp
      rcases mem_filter.mp hp with ⟨-, hpPrime⟩
      simpa [S] using
        (residueCount_sq_lower (T := S) (q := p) hpPrime.pos)
    exact le_trans hLower
      (sum_le_sum_of_subset_of_nonneg hSubset
        (by
          intro q hq _
          exact hNonneg q hq))
  have hCount :
      (primeCount z : ℝ) * (sieveCount n z : ℝ) ^ 2
        = ∑ _ ∈ primes,
            (sieveCount n z : ℝ) ^ 2 := by
    simp [primes, primeCount, sum_const, mul_comm,
      mul_left_comm, mul_assoc]
  calc
    (primeCount z : ℝ) * (sieveCount n z : ℝ) ^ 2
        = ∑ _ ∈ primes,
            (sieveCount n z : ℝ) ^ 2 := hCount
    _ ≤ ∑ q ∈ Icc 1 z,
          (q : ℝ) *
            ∑ b ∈ range q,
              (residueCount S q b : ℝ) ^ 2 := hPrimes
    _ ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2) *
          (sieveCount n z : ℝ) := by
      simpa [S] using hLargeSieve

lemma sieveCount_prime_bound
    (n z : ℕ) (hn : n ≠ 0) (hz : 1 ≤ z)
    (hp : 0 < (primeCount z : ℝ)) :
    (sieveCount n z : ℝ)
      ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2) /
          (primeCount z : ℝ) := by
  classical
  have hsq :=
    sieveCount_prime_square_bound
      (n := n) (z := z) hn hz
  by_cases hSzero : sieveCount n z = 0
  · have hnum :
        0 ≤ (binarySpan n : ℝ) + (z : ℝ) ^ 2 := by positivity
    have hden_pos : 0 < (primeCount z : ℝ) := hp
    have hcard_zero :
        (sieveSet n z).card = 0 := by
      simpa [sieveCount] using hSzero
    have :
        (0 : ℝ) ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2) /
            (primeCount z : ℝ) :=
      div_nonneg hnum hden_pos.le
    simpa [sieveCount, hcard_zero] using this
  · have hSpos : 0 < (sieveCount n z : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hSzero
    have hStep :
        (primeCount z : ℝ) * (sieveCount n z : ℝ)
          ≤ (binarySpan n : ℝ) + (z : ℝ) ^ 2 := by
      have hsq' :
          ((primeCount z : ℝ) * (sieveCount n z : ℝ)) *
              (sieveCount n z : ℝ)
            ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2) *
              (sieveCount n z : ℝ) := by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, sieveCount]
          using hsq
      have hineq :=
        le_of_mul_le_mul_right hsq' hSpos
      simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
    have hden_pos : 0 < (primeCount z : ℝ) := hp
    have hGoal :
        (sieveCount n z : ℝ)
          ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2) /
            (primeCount z : ℝ) :=
      (le_div_iff₀' hden_pos).2 hStep
    simpa [sieveCount] using hGoal

lemma sieveCount_log_bound
    (n z : ℕ) (hn : n ≠ 0) (hz : 17 ≤ z) :
    (sieveCount n z : ℝ)
      ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2) * Real.log z / (z : ℝ) := by
  classical
  have hz₁ : 1 ≤ z := le_trans (by decide : 1 ≤ 17) hz
  have hzNat : 0 < z := Nat.lt_of_lt_of_le (Nat.succ_pos 16) hz
  have hzPos : 0 < (z : ℝ) := by exact_mod_cast hzNat
  have hz_gt_one : 1 < (z : ℝ) :=
    by
      have : 1 < z := Nat.lt_of_lt_of_le (by decide : 1 < 17) hz
      exact_mod_cast this
  have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_one
  have hLower := primeCount_lower (z := z) hz
  have hPrimePos :
      0 < (primeCount z : ℝ) :=
    lt_of_lt_of_le (div_pos hzPos hlog_pos) hLower
  have hBound :=
    sieveCount_prime_bound
      (n := n) (z := z) hn hz₁ hPrimePos
  have hrec :
      (1 : ℝ) / (primeCount z : ℝ)
        ≤ Real.log z / (z : ℝ) := by
    have :=
      one_div_le_one_div_of_le
        (div_pos hzPos hlog_pos) hLower
    simpa [one_div, hzPos.ne', hlog_pos.ne'] using this
  have hnum :
      0 ≤ (binarySpan n : ℝ) + (z : ℝ) ^ 2 := by positivity
  have hMul :=
    mul_le_mul_of_nonneg_left hrec hnum
  have hDiv :
      ((binarySpan n : ℝ) + (z : ℝ) ^ 2) /
          (primeCount z : ℝ)
        ≤ ((binarySpan n : ℝ) + (z : ℝ) ^ 2) *
          Real.log z / (z : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hMul
  exact hBound.trans hDiv

end Erdos236
end Myproj
