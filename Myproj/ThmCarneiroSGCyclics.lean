import Mathlib.Tactic
import Myproj.Definitions
import Myproj.Axioms

-- Silence minor style hints in this short counterexample file
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Carneiro analog for SG cyclics (disproves Conj. 51 of Cohen 2025)

This file mirrors the short counterexample proof from the TeX source
`theorems/thm_carneiro_sg_cyclics.tex` step-by-step:

1. Use Szele's criterion (our working definition `isCyclicNumber n :↔ gcd(n, φ(n))=1`)
   to check that 7 and 15 are cyclic, hence 7 is an SG cyclic; and that 11 and 23
   are cyclic, hence 11 is an SG cyclic.
2. Check that none of 8, 9, 10 are cyclic, so none are SG cyclic; conclude that
   7 and 11 are consecutive SG cyclic numbers.
3. Compute the gap 11 − 7 = 4 and compare it against `√(7 log 7)`, using the
   numeric bound `√(7 log 7) < 4` (axiomatized) to obtain a contradiction to the
   conjectured inequality.

References in `bib.tex`:
- Szele (1947) for the cyclic criterion.
- Cohen (2025), Conj. 51 is the conjecture being disproved.
- Apostol (1976) for standard totient formulas (used via axioms here).
-/

noncomputable section

namespace Myproj

open scoped BigOperators
open Nat Real

/-! Helper: totient values from general axioms -/

private lemma totient_7 : Nat.totient 7 = 6 := by
  simpa using totient_prime (by decide : Nat.Prime 7)

private lemma totient_8 : Nat.totient 8 = 4 := by
  -- 8 = 2^3
  have h2 : Nat.Prime 2 := by decide
  have h3 : 0 < (3 : ℕ) := by decide
  simpa using totient_prime_pow (p := 2) (k := 3) h2 h3

private lemma totient_9 : Nat.totient 9 = 6 := by
  -- 9 = 3^2
  have h3 : Nat.Prime 3 := by decide
  have h2 : 0 < (2 : ℕ) := by decide
  simpa using totient_prime_pow (p := 3) (k := 2) h3 h2

private lemma totient_10 : Nat.totient 10 = 4 := by
  -- 10 = 2 * 5 and gcd(2,5)=1, so φ(10)=φ(2)φ(5)=1*4=4.
  have hgcd : Nat.gcd (2 : ℕ) 5 = 1 := by decide
  have hmul := totient_mul_coprime (m := 2) (n := 5) hgcd
  have hφ2 : Nat.totient 2 = 1 := by
    simpa using totient_prime (by decide : Nat.Prime 2)
  have hφ5 : Nat.totient 5 = 4 := by
    simpa using totient_prime (by decide : Nat.Prime 5)
  have : (10 : ℕ) = 2 * 5 := rfl
  simpa [this, hφ2, hφ5] using hmul

private lemma totient_11 : Nat.totient 11 = 10 := by
  simpa using totient_prime (by decide : Nat.Prime 11)

private lemma totient_15 : Nat.totient 15 = 8 := by
  -- 15 = 3 * 5 and gcd(3,5)=1, so φ(15)=φ(3)φ(5)=2*4=8.
  have hgcd : Nat.gcd (3 : ℕ) 5 = 1 := by decide
  have hmul := totient_mul_coprime (m := 3) (n := 5) hgcd
  have hφ3 : Nat.totient 3 = 2 := by
    simpa using totient_prime (by decide : Nat.Prime 3)
  have hφ5 : Nat.totient 5 = 4 := by
    simpa using totient_prime (by decide : Nat.Prime 5)
  have : (15 : ℕ) = 3 * 5 := rfl
  simpa [this, hφ3, hφ5] using hmul

private lemma totient_23 : Nat.totient 23 = 22 := by
  simpa using totient_prime (by decide : Nat.Prime 23)

/-! Step 1: SG cyclicity for 7 and 11 -/

private lemma cyclic_7 : isCyclicNumber 7 := by
  -- gcd(7,6) = 1
  have hgcd : Nat.gcd 7 6 = 1 := by decide
  simpa [isCyclicNumber, totient_7, hgcd]

private lemma cyclic_15 : isCyclicNumber 15 := by
  -- gcd(15,8) = 1
  have hgcd : Nat.gcd 15 8 = 1 := by decide
  simpa [isCyclicNumber, totient_15, hgcd]

private lemma cyclic_11 : isCyclicNumber 11 := by
  -- gcd(11,10) = 1
  have hgcd : Nat.gcd 11 10 = 1 := by decide
  simpa [isCyclicNumber, totient_11, hgcd]

private lemma cyclic_23 : isCyclicNumber 23 := by
  -- gcd(23,22) = 1
  have hgcd : Nat.gcd 23 22 = 1 := by decide
  simpa [isCyclicNumber, totient_23, hgcd]

private lemma sg_cyclic_7 : isSGCyclicNumber 7 := by
  -- 2*7+1 = 15
  have h15 : 2 * 7 + 1 = 15 := by norm_num
  refine And.intro cyclic_7 ?_
  simpa [h15] using cyclic_15

private lemma sg_cyclic_11 : isSGCyclicNumber 11 := by
  -- 2*11+1 = 23
  have h23 : 2 * 11 + 1 = 23 := by norm_num
  refine And.intro cyclic_11 ?_
  simpa [h23] using cyclic_23

/-! Step 2: no SG cyclics in {8,9,10} (since none are cyclic) -/

private lemma not_cyclic_8 : ¬ isCyclicNumber 8 := by
  -- gcd(8,4) = 4 ≠ 1
  have hgcd : Nat.gcd 8 4 = 4 := by decide
  have : Nat.gcd 8 (Nat.totient 8) = 4 := by simpa [totient_8] using hgcd
  simpa [isCyclicNumber, this]

private lemma not_cyclic_9 : ¬ isCyclicNumber 9 := by
  -- gcd(9,6) = 3 ≠ 1
  have hgcd : Nat.gcd 9 6 = 3 := by decide
  have : Nat.gcd 9 (Nat.totient 9) = 3 := by simpa [totient_9] using hgcd
  simpa [isCyclicNumber, this]

private lemma not_cyclic_10 : ¬ isCyclicNumber 10 := by
  -- gcd(10,4) = 2 ≠ 1
  have hgcd : Nat.gcd 10 4 = 2 := by decide
  have : Nat.gcd 10 (Nat.totient 10) = 2 := by simpa [totient_10] using hgcd
  simpa [isCyclicNumber, this]

private lemma not_sg_cyclic_8 : ¬ isSGCyclicNumber 8 := by
  intro h; exact not_cyclic_8 h.left

private lemma not_sg_cyclic_9 : ¬ isSGCyclicNumber 9 := by
  intro h; exact not_cyclic_9 h.left

private lemma not_sg_cyclic_10 : ¬ isSGCyclicNumber 10 := by
  intro h; exact not_cyclic_10 h.left

/-! Step 2 (continued): show 7 and 11 are consecutive SG cyclic numbers -/

lemma consecutiveSG_7_11 : consecutiveSGCyclic 7 11 := by
  refine And.intro ?hlt (And.intro sg_cyclic_7 (And.intro sg_cyclic_11 ?noneBetween))
  · decide
  · intro m hm1 hm2
    have h8le : 8 ≤ m := Nat.succ_le_of_lt hm1
    have h10ge : m ≤ 10 := Nat.le_of_lt_succ hm2
    -- Enumerate using linearity of ℕ
    rcases eq_or_lt_of_le h8le with rfl | hgt8
    · exact not_sg_cyclic_8
    · have h9le : 9 ≤ m := Nat.succ_le_of_lt hgt8
      rcases eq_or_lt_of_le h9le with rfl | hgt9
      · exact not_sg_cyclic_9
      · have h10le : 10 ≤ m := Nat.succ_le_of_lt hgt9
        have : m = 10 := le_antisymm h10ge h10le
        simpa [this] using not_sg_cyclic_10

/-! Step 3: numeric comparison `√(7 log 7) < 4` from axiom -/

/--
Main statement (counterexample): there exist consecutive SG cyclic integers
`7 < 11` with `7 > 3` such that the conjectured inequality fails.

This mirrors the TeX proof and disproves Conj. 51 of Cohen (2025).
-/
theorem carneiro_analog_sg_cyclics_counterexample :
    consecutiveSGCyclic 7 11 ∧ 3 < 7 ∧ ¬ ((11 - 7 : ℝ) < Real.sqrt ((7 : ℝ) * Real.log 7)) := by
  refine ⟨consecutiveSG_7_11, ?_, ?_⟩
  · decide
  · -- Since `√(7 log 7) < 4 = (11-7)`, the strict inequality fails.
    have hlt : Real.sqrt ((7 : ℝ) * Real.log 7) < 4 := sqrt7log7_lt_4
    have hnot : ¬ (4 < Real.sqrt ((7 : ℝ) * Real.log 7)) := not_lt_of_ge (le_of_lt hlt)
    simpa [show (11 - 7 : ℝ) = 4 by norm_num] using hnot

end Myproj
