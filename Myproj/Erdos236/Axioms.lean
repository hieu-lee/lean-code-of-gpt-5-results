import Mathlib

/-
External inputs for the Erdős problem #236 formalization.
Each axiom records a well-known analytic number theory result together
with a citation obtained via web search (see the attached comments).
-/

noncomputable section

namespace Myproj
namespace Erdos236

open scoped BigOperators

/-- Number of primes `≤ z`. -/
def primeCount (z : ℕ) : ℕ :=
  ((Finset.range (z + 1)).filter Nat.Prime).card

/--
Cardinality of the set `{t ∈ T | t ≡ b mod q}`. We use this to express
the residue-class clustering appearing in the additive large sieve.
-/
def residueCount (T : Finset ℕ) (q b : ℕ) : ℕ :=
  (T.filter fun t => t % q = b).card

/--
Additive large sieve inequality for subsets of `{0, …, N}`.

Source: Kiran S. Kedlaya, *An additive large sieve inequality*,
Theorem 16.5 in “Notes on Analytic Number Theory”
(retrieved 2025-10-25 via https://kskedlaya.org/ant/chap-largesieve.html).
-/
axiom additiveLargeSieve
    (N Q : ℕ) (T : Finset ℕ)
    (hRange : ∀ t ∈ T, t ≤ N)
    (hQpos : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 Q,
        (q : ℝ) *
          ∑ b ∈ Finset.range q,
            ((residueCount T q b : ℝ) ^ 2)
      ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * (T.card : ℝ)

/--
Rosser–Schoenfeld type upper bound
`π(z) ≤ 1.25506 · z / log z` for `z ≥ 17`.

Source: *Prime-counting function* (Wikipedia),
section “Inequalities” citing Rosser–Schoenfeld (1962),
retrieved 2025-10-25 via
https://en.wikipedia.org/wiki/Prime-counting_function.
-/
axiom primeCount_upper (z : ℕ) (hz : 17 ≤ z) :
    (primeCount z : ℝ) ≤ (1.25506 : ℝ) * (z : ℝ) / Real.log z

/--
Rosser–Schoenfeld lower bound
`π(z) ≥ z / log z` for `z ≥ 17`.

Source: *Prime-counting function* (Wikipedia),
section “Inequalities” citing Rosser–Schoenfeld (1962),
retrieved 2025-10-25 via
https://en.wikipedia.org/wiki/Prime-counting_function.
-/
axiom primeCount_lower (z : ℕ) (hz : 17 ≤ z) :
    (z : ℝ) / Real.log z ≤ (primeCount z : ℝ)

end Erdos236
end Myproj
