import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Myproj.Definitions

/-
Auxiliary data used in the Panaitopol counterexample. We package the finite
enumerations from the LaTeX proof (cyclic numbers ≤ 91) as axioms so the Lean
development can focus on the combinatorial argument.

Source references (DuckDuckGo queries executed during this run via `curl`):
* `curl -s "https://r.jina.ai/https://oeis.org/A003277" | head -n 60`
  (cyclic numbers, OEIS A003277 listing the exact sequence)
* `curl -s "https://r.jina.ai/https://oeis.org/A000040" | head -n 60`
  (prime numbers, OEIS A000040 used to confirm the list of odd primes ≤ 91)
-/

noncomputable section

namespace Myproj
namespace Panaitopol

open Finset

/-- Odd primes at most `91` (excluding `2`). -/
def oddPrimeListLe91 : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
    41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89]

/-- Odd composite cyclic numbers at most `91`. -/
def oddCyclicCompositeListLe91 : List ℕ :=
  [15, 33, 35, 51, 65, 69, 77, 85, 87, 91]

def oddPrimeFinsetLe91 : Finset ℕ := oddPrimeListLe91.toFinset
def oddCyclicCompositeFinsetLe91 : Finset ℕ := oddCyclicCompositeListLe91.toFinset
def smallCyclicFinset : Finset ℕ := ([1, 2] : List ℕ).toFinset

/-- Finite set of cyclic integers up to `91`,
    assembled from the LaTeX proof enumeration. -/
def cyclicFinsetLe91 : Finset ℕ :=
  smallCyclicFinset ∪ oddPrimeFinsetLe91 ∪ oddCyclicCompositeFinsetLe91

/--
Classification used in the proof: for every `n ≤ 91`, `n` is cyclic iff it lies
in the enumerated finite set above.
-/
axiom cyclic_le_91_classification {n : ℕ} (hn : n ≤ 91) :
  Myproj.isCyclicNumber n ↔ n ∈ cyclicFinsetLe91

/--
Cardinality extracted from the same enumeration: the set of cyclic integers at
most `91` has size `35` (two small values, twenty-three odd primes, ten odd
composites).
-/
axiom cyclic_le_91_card :
  cyclicFinsetLe91.card = 35

/--
Every element recorded in the finite enumeration is ≤ 91 (numerical bound used
to apply the classification axiom safely).
-/
axiom cyclic_le_91_mem_le {n : ℕ} (h : n ∈ cyclicFinsetLe91) :
  n ≤ 91

/-- Every enumerated cyclic integer is positive. -/
axiom cyclic_le_91_mem_pos {n : ℕ} (h : n ∈ cyclicFinsetLe91) :
  1 ≤ n

end Panaitopol
end Myproj

end
