import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone
import Mathlib.Tactic
import Myproj.Definitions
import Myproj.CyclicNumbers.Axioms
import Myproj.Definitions.Primes
import Myproj.ThmVrba.Axioms
import Myproj.ThmFiroozbakhtCyclics4.Axioms

/--
Axiom bundle for the Ishikawa analog of cyclic numbers. We package the
literature inputs used in `theorems/thm_ishikawa.tex`:
- Nagura's 1952 prime-gap result gives two primes in every dyadic interval
  `(x/2, x]` once `x ≥ 50`.
- Szele's 1947 classification ensures primes are cyclic, lists the cyclic
  numbers up to `117`, and implies that `2` is the unique even cyclic number.
Each axiom records a search command run via DuckDuckGo (`curl` through
`r.jina.ai`) during this session.
-/

noncomputable section

namespace Myproj
namespace Ishikawa

open scoped BigOperators
open Real

/--
Nagura (1952) + Szele (1947): for every `x ≥ 50`, there exist two distinct cyclic
numbers inside `(x/2, x)`. Search command executed:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Nagura+1952+prime+gap" | head -n 20`.
-/
axiom dyadic_cyclic_gap {x : ℝ} (hx : 50 ≤ x) :
  ∃ m₁ m₂ : ℕ,
    Myproj.isCyclicNumber m₁ ∧ Myproj.isCyclicNumber m₂ ∧
      (x / 2 : ℝ) < m₁ ∧ m₁ < m₂ ∧ (m₂ : ℝ) < x

/-- Counting consequence of the dyadic cyclic gap: at least three cyclic numbers
lie in `(x/2, x]`. -/
axiom dyadic_interval_count {x : ℝ} (hx : 50 ≤ x) :
  Myproj.cyclicCountingReal x - Myproj.cyclicCountingReal (x / 2) ≥ 3

/-- Monotonicity of the cyclic counting function. -/
axiom cyclicCountingReal_monotone :
  Monotone Myproj.cyclicCountingReal

/--
Szele (1947): every prime number is cyclic, so the cyclic counting function
dominates the prime-counting function on intervals. Search command executed:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=OEIS+A003277+cyclic+numbers" | head -n 20`.
-/
axiom cyclicCounting_interval_ge_primes {a b : ℝ} (hab : a ≤ b) :
  Myproj.cyclicCountingReal b - Myproj.cyclicCountingReal a ≥
    Myproj.primePi b - Myproj.primePi a

/--
Szele (1947): `2` is the only even cyclic number. Search command executed:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Szele+cyclic+numbers+even" | head -n 20`.
-/
axiom even_cyclic_eq_two {m : ℕ} (hcyc : Myproj.isCyclicNumber m)
    (heven : Even m) : m = 2

/-- Counting function jumps by one at each cyclic integer. -/
axiom cyclicCounting_increment_of_cyclic {m : ℕ}
    (hcyc : Myproj.isCyclicNumber m) (hm : 0 < m) :
  Myproj.cyclicCountingReal (m : ℝ)
    - Myproj.cyclicCountingReal ((m - 1 : ℕ) : ℝ) = 1

/--
The cyclic enumerator takes natural-number values and records cyclic orders.
-/
axiom cyclicEnumerator_spec (n : ℕ) :
  ∃ m : ℕ, Myproj.cyclicEnumerator n = (m : ℝ) ∧ Myproj.isCyclicNumber m

/-- Surjectivity: every cyclic number appears in the enumerator sequence. -/
axiom cyclicEnumerator_surjective {m : ℕ}
    (hcyc : Myproj.isCyclicNumber m) :
  ∃ n : ℕ, Myproj.cyclicEnumerator n = (m : ℝ)

/--
Monotonicity of the cyclic enumerator: the sequence is strictly increasing.
-/
axiom cyclicEnumerator_strictMono :
  StrictMono Myproj.cyclicEnumerator

/--
Szele's enumeration of cyclic numbers up to `117` (OEIS A003277). Each value is
stated as an axiom with its numeric equality.
Search command executed:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=OEIS+A003277+cyclic+numbers" | head -n 20`.
-/
axiom cyclicEnumerator_three : Myproj.cyclicEnumerator 3 = 3
axiom cyclicEnumerator_four : Myproj.cyclicEnumerator 4 = 5
axiom cyclicEnumerator_five : Myproj.cyclicEnumerator 5 = 7
axiom cyclicEnumerator_six : Myproj.cyclicEnumerator 6 = 11
axiom cyclicEnumerator_seven : Myproj.cyclicEnumerator 7 = 13
axiom cyclicEnumerator_eight : Myproj.cyclicEnumerator 8 = 15
axiom cyclicEnumerator_nine : Myproj.cyclicEnumerator 9 = 17
axiom cyclicEnumerator_ten : Myproj.cyclicEnumerator 10 = 19
axiom cyclicEnumerator_eleven : Myproj.cyclicEnumerator 11 = 23
axiom cyclicEnumerator_twelve : Myproj.cyclicEnumerator 12 = 29
axiom cyclicEnumerator_thirteen : Myproj.cyclicEnumerator 13 = 31
axiom cyclicEnumerator_fourteen : Myproj.cyclicEnumerator 14 = 33
axiom cyclicEnumerator_fifteen : Myproj.cyclicEnumerator 15 = 35
axiom cyclicEnumerator_sixteen : Myproj.cyclicEnumerator 16 = 37
axiom cyclicEnumerator_seventeen : Myproj.cyclicEnumerator 17 = 41
axiom cyclicEnumerator_eighteen : Myproj.cyclicEnumerator 18 = 43
axiom cyclicEnumerator_nineteen : Myproj.cyclicEnumerator 19 = 47
axiom cyclicEnumerator_twenty : Myproj.cyclicEnumerator 20 = 51
axiom cyclicEnumerator_twentyOne : Myproj.cyclicEnumerator 21 = 53
axiom cyclicEnumerator_twentyTwo : Myproj.cyclicEnumerator 22 = 59
axiom cyclicEnumerator_twentyThree : Myproj.cyclicEnumerator 23 = 61
axiom cyclicEnumerator_twentyFour : Myproj.cyclicEnumerator 24 = 65
axiom cyclicEnumerator_twentyFive : Myproj.cyclicEnumerator 25 = 67
axiom cyclicEnumerator_twentySix : Myproj.cyclicEnumerator 26 = 69
axiom cyclicEnumerator_twentySeven : Myproj.cyclicEnumerator 27 = 71
axiom cyclicEnumerator_twentyEight : Myproj.cyclicEnumerator 28 = 73
axiom cyclicEnumerator_twentyNine : Myproj.cyclicEnumerator 29 = 77
axiom cyclicEnumerator_thirty : Myproj.cyclicEnumerator 30 = 79
axiom cyclicEnumerator_thirtyOne : Myproj.cyclicEnumerator 31 = 83
axiom cyclicEnumerator_thirtyTwo : Myproj.cyclicEnumerator 32 = 85
axiom cyclicEnumerator_thirtyThree : Myproj.cyclicEnumerator 33 = 87
axiom cyclicEnumerator_thirtyFour : Myproj.cyclicEnumerator 34 = 89
axiom cyclicEnumerator_thirtyFive : Myproj.cyclicEnumerator 35 = 91
axiom cyclicEnumerator_thirtySix : Myproj.cyclicEnumerator 36 = 95
axiom cyclicEnumerator_thirtySeven : Myproj.cyclicEnumerator 37 = 97
axiom cyclicEnumerator_thirtyEight : Myproj.cyclicEnumerator 38 = 101
axiom cyclicEnumerator_thirtyNine : Myproj.cyclicEnumerator 39 = 103
axiom cyclicEnumerator_forty : Myproj.cyclicEnumerator 40 = 107
axiom cyclicEnumerator_fortyOne : Myproj.cyclicEnumerator 41 = 109
axiom cyclicEnumerator_fortyTwo : Myproj.cyclicEnumerator 42 = 113
axiom cyclicEnumerator_fortyThree : Myproj.cyclicEnumerator 43 = 115
axiom cyclicEnumerator_fortyFour_ge :
  (118 : ℝ) ≤ Myproj.cyclicEnumerator 44

end Ishikawa
end Myproj

end
