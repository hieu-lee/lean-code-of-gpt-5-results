import Mathlib
import Myproj.Erdos236.Definitions
import Myproj.Erdos236.Axioms

/-
# Combinatorial bounds for Erdős 236

We reorganise the inequalities needed for the sieve argument. The main
result of this file is the estimate
`representationCount n ≤ sieveCount n z + primeCount z`.
-/

noncomputable section

namespace Myproj
namespace Erdos236

open scoped BigOperators
open Finset

variable {n z : ℕ}

@[simp] lemma mem_repSet {n k : ℕ} :
    k ∈ repSet n ↔
      k ∈ range (binarySpan n + 1) ∧ Nat.Prime (diffValue n k) := by
  simp [repSet]

@[simp] lemma mem_sieveSet {n z k : ℕ} :
    k ∈ sieveSet n z ↔
      k ∈ range (binarySpan n + 1) ∧
        Nat.Coprime (diffValue n k) (oddPrimeProduct z) := by
  simp [sieveSet]

lemma rep_subset_range (n : ℕ) :
    repSet n ⊆ range (binarySpan n + 1) := by
  intro k hk
  exact (mem_repSet.mp hk).1

lemma sieve_subset_range (n z : ℕ) :
    sieveSet n z ⊆ range (binarySpan n + 1) := by
  intro k hk
  exact (mem_sieveSet.mp hk).1

lemma twoPow_le_of_mem_range {n k : ℕ} (hn : n ≠ 0)
    (hk : k ∈ range (binarySpan n + 1)) :
    twoPow k ≤ n := by
  obtain hk' : k ≤ binarySpan n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simpa [twoPow, binarySpan] using
    (Nat.pow_le_of_le_log (b := 2) (hy := hn) hk')

lemma diffValue_add_twoPow {n k : ℕ} (hn : n ≠ 0)
    (hk : k ∈ range (binarySpan n + 1)) :
    diffValue n k + twoPow k = n := by
  have hle := twoPow_le_of_mem_range (n := n) hn hk
  simpa [diffValue, twoPow] using Nat.sub_add_cancel hle

lemma diffValue_injOn_range {n : ℕ} (hn : n ≠ 0) :
    Set.InjOn (fun k => diffValue n k)
      (↑(range (binarySpan n + 1)) : Set ℕ) := by
  classical
  intro a ha b hb h
  have ha' :=
    diffValue_add_twoPow (n := n) hn (by simpa using ha)
  have hb' :=
    diffValue_add_twoPow (n := n) hn (by simpa using hb)
  have hx := congrArg (fun t => t + twoPow a) h
  have hx₁ :
      n = diffValue n b + twoPow a := by
    simpa [ha'] using hx
  have hx₂ :
      diffValue n b + twoPow b =
        diffValue n b + twoPow a := by
    have hx' : diffValue n b + twoPow b = n := by
      simpa [hb']
    exact hx'.trans hx₁
  have hpow : twoPow b = twoPow a :=
    Nat.add_left_cancel hx₂
  exact
    (Nat.pow_right_injective (by decide : 2 ≤ 2))
      (by simpa [twoPow] using hpow.symm)

lemma diffValue_injOn_subset {n : ℕ} (hn : n ≠ 0)
    {S : Finset ℕ} (hS : S ⊆ range (binarySpan n + 1)) :
    Set.InjOn (fun k => diffValue n k) (↑S : Set ℕ) := by
  classical
  intro a ha b hb h
  refine diffValue_injOn_range (n := n) hn ?_ ?_ h
  · exact hS (by simpa using ha)
  · exact hS (by simpa using hb)

lemma mem_oddPrimeSet {z p : ℕ} :
    p ∈ oddPrimeSet z ↔
      p ≤ z ∧ Nat.Prime p ∧ Odd p := by
  constructor
  · intro hp
    rcases mem_filter.mp hp with ⟨hpRange, hpProps⟩
    exact ⟨Nat.lt_succ_iff.mp (mem_range.mp hpRange), hpProps.1, hpProps.2⟩
  · intro h
    obtain ⟨hp_le, hpPrime, hpOdd⟩ := h
    refine mem_filter.mpr ?_
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le hp_le), hpPrime, hpOdd⟩

lemma prime_not_dvd_prod_primes {p : ℕ} (hp : Nat.Prime p) :
    ∀ s : Finset ℕ,
      (∀ q ∈ s, Nat.Prime q ∧ q < p) →
        ¬ p ∣ s.prod id := by
  classical
  refine Finset.induction ?base ?step
  · intro _; simpa using hp.not_dvd_one
  · intro a s ha ih hProps hdiv
    have ha' : Nat.Prime a ∧ a < p :=
      hProps _ (by simp [ha])
    have hRest :
        ∀ q ∈ s, Nat.Prime q ∧ q < p :=
      fun q hq => hProps _ (by simp [hq, ha])
    have hdiv' : p ∣ a * s.prod id := by
      simpa [Finset.prod_insert ha, id] using hdiv
    rcases hp.dvd_mul.mp hdiv' with hpa | htail
    · have hp_eq : p = a :=
        (Nat.prime_dvd_prime_iff_eq hp ha'.1).mp hpa
      exact (lt_irrefl _ (hp_eq ▸ ha'.2))
    · exact ih hRest htail

lemma prime_coprime_oddPrimeProduct {z p : ℕ}
    (hp : Nat.Prime p) (hz : z < p) :
    Nat.Coprime p (oddPrimeProduct z) := by
  classical
  refine hp.coprime_iff_not_dvd.mpr ?_
  intro hdiv
  have hProps :
      ∀ q ∈ oddPrimeSet z, Nat.Prime q ∧ q < p := by
    intro q hq
    rcases mem_oddPrimeSet.mp hq with ⟨hq_le, hqPrime, _⟩
    exact ⟨hqPrime, lt_of_le_of_lt hq_le hz⟩
  exact
    (prime_not_dvd_prod_primes (p := p) hp (oddPrimeSet z) hProps) hdiv

lemma rep_large_primes_subset_sieve {n z : ℕ} (hn : n ≠ 0) :
    ((repSet n).filter fun k => ¬ diffValue n k ≤ z) ⊆ sieveSet n z := by
  classical
  intro k hk
  obtain ⟨hkRep, hkLarge⟩ := mem_filter.mp hk
  obtain ⟨hkRange, hkPrime⟩ := mem_repSet.mp hkRep
  have hkLarge' : z < diffValue n k := Nat.lt_of_not_ge hkLarge
  have hkCoprime :
      Nat.Coprime (diffValue n k) (oddPrimeProduct z) :=
    prime_coprime_oddPrimeProduct hkPrime hkLarge'
  exact mem_filter.mpr ⟨hkRange, hkCoprime⟩

lemma card_small_rep_le {n z : ℕ} (hn : n ≠ 0) :
    ((repSet n).filter fun k => diffValue n k ≤ z).card ≤ primeCount z := by
  classical
  set S := (repSet n).filter fun k => diffValue n k ≤ z
  have hSubset : S ⊆ range (binarySpan n + 1) := by
    intro k hk
    obtain ⟨hkRep, _⟩ := mem_filter.mp hk
    exact rep_subset_range n hkRep
  have hInj :
      Set.InjOn (fun k => diffValue n k) (↑S : Set ℕ) :=
    diffValue_injOn_subset (n := n) hn hSubset
  have hImage :
      S.card = (S.image fun k => diffValue n k).card :=
    (Finset.card_image_of_injOn (s := S) hInj).symm
  have hSub :
      S.image (fun k => diffValue n k)
        ⊆ (range (z + 1)).filter Nat.Prime := by
    intro m hm
    rcases mem_image.mp hm with ⟨k, hkS, rfl⟩
    obtain ⟨hkRep, hkSmall⟩ := mem_filter.mp hkS
    obtain ⟨hkRange, hkPrime⟩ := mem_repSet.mp hkRep
    refine mem_filter.mpr ?_
    exact ⟨mem_range.mpr (Nat.lt_succ_of_le hkSmall), hkPrime⟩
  have hCard :
      ((range (z + 1)).filter Nat.Prime).card = primeCount z := rfl
  calc
    S.card = (S.image fun k => diffValue n k).card := hImage
    _ ≤ ((range (z + 1)).filter Nat.Prime).card :=
      Finset.card_le_card hSub
    _ = primeCount z := hCard

lemma representation_le_sieve_add {n z : ℕ} (hn : n ≠ 0) :
    representationCount n ≤ sieveCount n z + primeCount z := by
  classical
  set S := repSet n
  set small := S.filter fun k => diffValue n k ≤ z
  set large := S.filter fun k => ¬ diffValue n k ≤ z
  have partition :
      S.card = small.card + large.card := by
    simpa [S, small, large, add_comm, add_left_comm, add_assoc] using
      (filter_card_add_filter_neg_card_eq_card
        (s := S) (p := fun k : ℕ => diffValue n k ≤ z)).symm
  have hSmall :=
    card_small_rep_le (n := n) (z := z) hn
  have hLarge :
      large.card ≤ sieveCount n z := by
    have hSub :
        large ⊆ sieveSet n z :=
      rep_large_primes_subset_sieve (n := n) (z := z) hn
    simpa [large, sieveCount, S] using Finset.card_le_card hSub
  have hTotal :
      S.card ≤ sieveCount n z + primeCount z := by
    have := Nat.add_le_add hLarge hSmall
    simpa [partition, S, small, large, sieveCount, representationCount,
      add_comm, add_left_comm, add_assoc] using this
  simpa [representationCount, S] using hTotal

end Erdos236
end Myproj
