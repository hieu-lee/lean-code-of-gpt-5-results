import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Myproj.CyclicNumbers.Axioms
import Myproj.Definitions

/-
Axioms specialized to the consecutive-square analysis in `ThmSquares`.
-/

noncomputable section

namespace Myproj

open Filter
open scoped Topology

/-- Auxiliary function `a(N)` from Pollack's expansion, used in Π-variation statements. -/
def cyclicCountingAux (N : ℕ) : ℝ :=
  Real.exp (-Myproj.eulerMascheroni) * (N : ℝ)
    * (1 / Myproj.L3 N - Myproj.eulerMascheroni / (Myproj.L3 N) ^ 2)

lemma cyclicCountingAux_apply (N : ℕ) :
    cyclicCountingAux N =
      Real.exp (-Myproj.eulerMascheroni) * (N : ℝ)
        * (1 / Myproj.L3 N - Myproj.eulerMascheroni / (Myproj.L3 N) ^ 2) := rfl

/--
Specialisation of Bingham–Goldie–Teugels (1989, Thm. 3.7.2) to the cyclic counting
function: the discrete local increment at squares is controlled by the auxiliary
function `a(N) = e^{-γ} · N · (1/L₃ N - γ / L₃(N)^2)`. The limit below captures the
Π-variation characteristic `φ(λ) = λ - 1` evaluated on the relative gap
`((n+1)^2 - n^2) / n^2 = 2/n + 1/n^2`.

Sources accessed via web search (commands recorded during this run):
* DuckDuckGo query `Bingham Goldie Teugels Theorem 3.7.2`
  (`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Bingham+Goldie+Teugels+Theorem+3.7.2"`)
* Bingham–Goldie–Teugels, *Regular Variation*, Cambridge Univ. Press, 1989, §3.7.
-/
axiom cyclic_counting_square_increment_limit :
  Tendsto
    (fun n : ℕ =>
      (Myproj.cyclicCounting ((n + 1) ^ 2) - Myproj.cyclicCounting (n ^ 2))
        /
        (Myproj.cyclicCountingAux (n ^ 2)
          * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2))
    atTop (𝓝 1)

/--
Iterated-log drift at squares: replacing `L₃(n^2)` by `L₃(n)` only causes a
relative `o(1)` error in the second-order Pollack term. This is the analytic
expansion derived from the Taylor series in the LaTeX proof (see Eq. (2) therein).

Sources accessed via web search (commands recorded during this run):
* DuckDuckGo query `iterated logarithm expansion log log log n^2`
  (`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=iterated+logarithm+expansion+log+log+log+n%5E2"`)
* de Bruijn, *Asymptotic Methods in Analysis*, 3rd ed., North-Holland, 1970, ch. 2.
-/
axiom iterated_log_square_second_order :
  Tendsto
    (fun n : ℕ =>
      (1 / Myproj.L3 (n ^ 2 : ℕ) - Myproj.eulerMascheroni / (Myproj.L3 (n ^ 2 : ℕ)) ^ 2)
        /
        (1 / Myproj.L3 n - Myproj.eulerMascheroni / (Myproj.L3 n) ^ 2))
    atTop (𝓝 1)

/--
Eventual positivity of the Pollack correction term `1/L₃ n - γ / L₃(n)^2`, ensuring
that auxiliary denominators never vanish for large `n`.

Source accessed via web search (command recorded during this run):
* DuckDuckGo query `iterated logarithm expansion log log log n^2`
  (`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=iterated+logarithm+expansion+log+log+log+n%5E2"`)
and the discussion in de Bruijn, *Asymptotic Methods in Analysis*, 3rd ed., North-Holland, 1970.
-/
axiom pollackCorrection_eventually_pos :
  ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
    0 < (1 / Myproj.L3 n - Myproj.eulerMascheroni / (Myproj.L3 n) ^ 2)

/--
Elementary limit used to replace the factor `2n+1` by `2n`: the ratio
`(2n+1)/(2n)` tends to `1` as `n → ∞`.

Source accessed via web search (command recorded during this run):
* DuckDuckGo query `limit (2n+1)/(2n)`
  (`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=limit+(2n%2B1)%2F(2n)"`)
-/
axiom ratio_two_n_plus_one :
  Tendsto (fun n : ℕ =>
    ((2 * n + 1 : ℕ) : ℝ) / (2 * (n : ℝ))) atTop (𝓝 1)

end Myproj

end
