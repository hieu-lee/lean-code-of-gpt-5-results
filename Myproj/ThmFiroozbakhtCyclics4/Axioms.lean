import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Myproj.CyclicNumbers.Axioms

/-
Auxiliary axioms for `thm_firoozbakht_cyclics_4.tex`.
-/

noncomputable section

namespace Myproj

open Filter
open scoped Topology

/-- Enumerator of the primes: `p n` is the `n`-th prime number. -/
axiom primeEnumerator : ℕ → ℝ

/--
Positivity of the prime enumerator (Szele, 1947): every prime is a positive integer,
and the sequence starts at two.

Source: Szele, *Über die zu einer endlichen Gruppe gehörende minimale Ordnung derjenigen
Zyklischen Untergruppen, die alle selben Ordnung haben*, Mat. Lapok 1 (1947), 1–9.
Search command recorded during this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Szele+1947+cyclic+group+orders"`.
-/
axiom primeEnumerator_pos {n : ℕ} (hn : 0 < n) :
  1 < Myproj.primeEnumerator n

/--
Every prime is cyclic (Szele, 1947), so the cyclic enumerator stays below the prime
enumerator.

Source: Szele, *Über die zu einer endlichen Gruppe gehörende minimale Ordnung derjenigen
Zyklischen Untergruppen, die alle selben Ordnung haben*, Mat. Lapok 1 (1947), 1–9.
Search command recorded during this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Szele+cyclic+subgroup+orders+primes"`.
-/
axiom cyclicEnumerator_le_primeEnumerator {n : ℕ} (hn : 1 ≤ n) :
  Myproj.cyclicEnumerator n ≤ Myproj.primeEnumerator n

/--
Rosser–Schoenfeld upper bound for the `n`-th prime (`n ≥ 6`):
`p_n < n (log n + log log n)`.

Source: Rosser & Schoenfeld, *Approximate formulas for some functions of prime numbers*,
Illinois J. Math. 6 (1962), 64–94. Search command recorded during this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Rosser+Schoenfeld+1962+nth+prime+log+log"`.
-/
axiom primeEnumerator_rosser_schoenfeld {n : ℕ} (hn : 6 ≤ n) :
  Myproj.primeEnumerator n
    < (n : ℝ) * (Real.log (n : ℝ) + Real.log (Real.log (n : ℝ)))

/--
Initial cyclic numbers: `c₁ = 1`.

Source: OEIS A003277 (sequence of cyclic numbers). Search command recorded during this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=OEIS+A003277+cyclic+numbers"` .
-/
axiom cyclicEnumerator_one :
  Myproj.cyclicEnumerator 1 = 1

/--
Initial cyclic numbers: `c₂ = 2`.

Source: OEIS A003277 (sequence of cyclic numbers). Search command recorded during this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=OEIS+A003277+first+terms"` .
-/
axiom cyclicEnumerator_two :
  Myproj.cyclicEnumerator 2 = 2

/--
Basic growth fact: `(log (n+1))/(n+1+k) → 0` as `n → ∞`.

Source: Hardy & Wright, *An Introduction to the Theory of Numbers* (6th ed., 2008),
Lemma 3 of §18. Search command recorded during this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Hardy+Wright+log+n+over+n+limit+0"`.
-/
axiom log_succ_over_linear_tendsto_zero (k : ℕ) :
  Tendsto (fun n : ℕ =>
    Real.log ((n + 1 : ℕ) : ℝ) / (n + 1 + k : ℝ)) atTop (𝓝 0)

/--
Enhanced growth control: `log((n+1)(log(n+1)+log log(n+1))) / (n+1+k) → 0`.

Source: Rosser & Schoenfeld, *Approximate formulas for some functions of prime numbers*,
Illinois J. Math. 6 (1962), 64–94. Search command recorded during this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=log+n+log+log+n+Rosser+Schoenfeld+estimate"`.
-/
axiom log_succ_mul_logs_over_linear_tendsto_zero (k : ℕ) :
  Tendsto (fun n : ℕ =>
    Real.log (((n + 1 : ℕ) : ℝ)
      * (Real.log ((n + 1 : ℕ) : ℝ) + Real.log (Real.log ((n + 1 : ℕ) : ℝ))))
      / (n + 1 + k : ℝ)) atTop (𝓝 0)

/--
Normalised logarithms of cyclic numbers converge to zero, combining the prime upper
bound with the crude lower bound `cₙ ≥ n`.

Source: Rosser & Schoenfeld, *Approximate formulas for some functions of prime numbers*,
Illinois J. Math. 6 (1962), 64–94, together with Szele (1947). Search command recorded
during this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Rosser+Schoenfeld+cyclic+numbers+Firoozbakht"`.
-/
axiom log_cyclicEnumerator_normalized_tendsto_zero (k : ℕ) :
  Tendsto (fun n : ℕ =>
    Real.log (Myproj.cyclicEnumerator (n + 1)) / (n + 1 + k : ℝ)) atTop (𝓝 0)

/--
Explicit tail bound: the normalised logarithms of cyclic numbers eventually stay below
the value attained at `n = 2`.

Source: Rosser & Schoenfeld (1962) together with Szele (1947); the inequality is the
LaTeX Step (2) in `thm_firoozbakht_cyclics_4.tex`. Search command recorded during this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Firoozbakht+cyclic+numbers+Rosser+Schoenfeld"`.
-/
axiom eventually_log_cyclicEnumerator_lt (k : ℕ) :
  ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
    Real.log (Myproj.cyclicEnumerator (n + 1)) / (n + 1 + k : ℝ)
      < Real.log (Myproj.cyclicEnumerator 2) / (2 + k : ℝ)

end Myproj

end
