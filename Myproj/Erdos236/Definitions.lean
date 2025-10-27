import Mathlib
import Myproj.Erdos236.Axioms

/-
Foundational definitions for the Erdős problem #236 development.
We instantiate the counting functions that mirror the LaTeX proof:
* `binarySpan n`    : the truncation height `⌊log₂ n⌋`,
* `twoPow k`        : shorthand for `2^k`,
* `diffValue n k`   : the integers `m_k = n - 2^k`,
* `oddPrimeSet z`   : odd primes up to `z`,
* `oddPrimeProduct z` : the product `P(z)`,
* `repSet n`        : indices `k` with `n - 2^k` prime,
* `sieveSet n z`    : indices counted by `S(z)`.
-/

noncomputable section

namespace Myproj
namespace Erdos236

open scoped BigOperators
open Finset

/-- Binary logarithm cut-off `⌊log₂ n⌋`. -/
def binarySpan (n : ℕ) : ℕ :=
  Nat.log 2 n

/-- Powers of two. -/
def twoPow (k : ℕ) : ℕ :=
  2 ^ k

/-- The values `m_k := n - 2^k`. -/
def diffValue (n k : ℕ) : ℕ :=
  n - twoPow k

/-- Odd primes up to `z`. -/
def oddPrimeSet (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter fun p => Nat.Prime p ∧ Odd p

/-- Product of odd primes `≤ z`. -/
def oddPrimeProduct (z : ℕ) : ℕ :=
  (oddPrimeSet z).prod id

/-- Indices with `n - 2^k` prime. -/
def repSet (n : ℕ) : Finset ℕ :=
  (Finset.range (binarySpan n + 1)).filter fun k => Nat.Prime (diffValue n k)

/-- Number of representations `n = p + 2^k`. -/
def representationCount (n : ℕ) : ℕ :=
  (repSet n).card

/-- Indices counted by `S(z)`. -/
def sieveSet (n z : ℕ) : Finset ℕ :=
  (Finset.range (binarySpan n + 1)).filter fun k =>
    Nat.Coprime (diffValue n k) (oddPrimeProduct z)

/-- The quantity `S(z)` used in the argument. -/
def sieveCount (n z : ℕ) : ℕ :=
  (sieveSet n z).card

end Erdos236
end Myproj
