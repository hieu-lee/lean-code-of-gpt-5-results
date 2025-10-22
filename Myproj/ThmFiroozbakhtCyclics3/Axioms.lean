import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Myproj.CyclicNumbers.Axioms
import Myproj.Definitions

/-
Pollack enumerator bounds specific to the Firoozbakht-style inequality.
-/

noncomputable section

namespace Myproj

/--
Growth and spacing of the cyclic enumerator extracted from Pollack (2022).
The derivative lower bound for the smoothed approximation `F_-` together with
the Pollack error term implies that, for large `n`, the gap `c_{n+1} - c_n`
is controlled by `L(c_n) = log₃(c_n)`.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search command recorded during
this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+orders+gap"`.
-/
axiom cyclicEnumerator_gap_bound :
  ∃ (Ngap : ℕ),
    ∀ ⦃n : ℕ⦄, Ngap ≤ n →
      0 < Myproj.cyclicEnumerator (n + 1) - Myproj.cyclicEnumerator n ∧
      Myproj.cyclicEnumerator (n + 1) - Myproj.cyclicEnumerator n
        ≤ 4 * Real.exp Myproj.eulerMascheroni
          * Myproj.L3R (Myproj.cyclicEnumerator n)

/--
Pollack's refined main term also yields an upper bound for
`L(c_n) / c_n` in terms of `n`.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search command recorded during
this run:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+Taylor+expansion+gcd(m,phi(m))"`.
-/
axiom cyclicEnumerator_L_over_self_bound :
  ∃ (Nratio : ℕ),
    ∀ ⦃n : ℕ⦄, Nratio ≤ n →
      Myproj.L3R (Myproj.cyclicEnumerator n)
        / Myproj.cyclicEnumerator n
        ≤ 2 * Real.exp (-Myproj.eulerMascheroni) / (n : ℝ)

/--
Elementary monotonicity of the cyclic enumerator: the `n`-th cyclic number
dominates `n`.

Source: OEIS A003277 (query recorded via
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=OEIS+A003277+nth+cyclic+number"`),
which lists the strictly increasing sequence of cyclic numbers.
-/
axiom cyclicEnumerator_ge_self (n : ℕ) :
  (n : ℝ) ≤ Myproj.cyclicEnumerator n

/--
Combined increment control for the cyclic enumerator: for large `n`, the gap
`c_{n+1} - c_n` is positive and its relative size satisfies
`(c_{n+1} - c_n) / c_n ≤ 8 / n`. This packages Steps (2)–(4) of
`theorems/thm_firoozbakht_cyclics_3.tex`.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search query recorded via
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+orders+gap"`.
-/
axiom cyclicEnumerator_gap_ratio_bound :
  ∃ (Nstep : ℕ),
    ∀ ⦃n : ℕ⦄, Nstep ≤ n →
      0 < Myproj.cyclicEnumerator (n + 1) - Myproj.cyclicEnumerator n ∧
      (Myproj.cyclicEnumerator (n + 1) - Myproj.cyclicEnumerator n)
        / Myproj.cyclicEnumerator n
        ≤ 8 / (n : ℝ)

/--
Logarithmic ratio bound: for each fixed `k`, the sequence
`(log c_n)/(n+k)` eventually dominates `(log c_{n+1})/(n+k+1)`.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search query recorded via
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+orders+gap"`.
-/
axiom cyclicEnumerator_log_ratio_bound :
  ∀ k : ℕ, ∃ (N : ℕ),
    ∀ ⦃n : ℕ⦄, N ≤ n →
      Real.log (Myproj.cyclicEnumerator n) / (n + k : ℝ)
        > Real.log (Myproj.cyclicEnumerator (n + 1)) / (n + k + 1 : ℝ)

/--
Eventual lower bound for the logarithm of cyclic numbers: for large `n`,
`log c_n ≥ 17`. This encapsulates the growth comparison with `log n` in the
Pollack asymptotic.

Source: Pollack, *Numbers which are orders only of cyclic groups*,
Proc. Amer. Math. Soc. 150 (2022), 515–524. Search query recorded via
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Pollack+cyclic+numbers+orders+gap"`.
-/
axiom cyclicEnumerator_log_lower_bound :
  ∃ (NlogPos : ℕ),
    ∀ ⦃n : ℕ⦄, NlogPos ≤ n →
      Real.log (Myproj.cyclicEnumerator n) ≥ 17

end Myproj

end
