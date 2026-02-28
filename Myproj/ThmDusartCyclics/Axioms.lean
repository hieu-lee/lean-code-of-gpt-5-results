import Mathlib.Data.Real.Basic
import Myproj.CyclicNumbers.Axioms
import Myproj.Definitions.IteratedLogs

/-!
Axiom bundle for `theorems/thm_dusart_cyclics.tex`.

Only literature-level inputs are axiomatized; the theorem file keeps the
logical contradiction structure from the TeX proof.

Web sources used to pin references:

* Pollack asymptotic (cyclic counting):
  `WebFetch("https://arxiv.org/abs/2007.09734")`
  (Paul Pollack, *Numbers which are orders only of cyclic groups*,
  Proc. Amer. Math. Soc. 150 (2022), 515--524; arXiv:2007.09734).
* de Bruijn conjugate/inversion framework:
  `WebSearch("de Bruijn conjugate theorem slowly varying function")`
  and `WebSearch("Bingham Goldie Teugels Regular Variation asymptotic inverse")`.
  Standard reference: Bingham--Goldie--Teugels, *Regular Variation* (CUP, 1989),
  section on de Bruijn conjugates/inversion (`§1.5.7` and nearby inversion results).
-/

noncomputable section

namespace Myproj
namespace ThmDusartCyclics

/--
General asymptotic-inversion consequence used in the Dusart-style contradiction:
there are constants `K > 0` and `N` such that for all `n >= N`,
`c_n / (e^gamma n) <= L3(n) + K`, where `c_n` is the cyclic enumerator.

Interpretation:
* Pollack gives `C(x) = e^{-gamma} x / L3(x) * (1 + O(1 / L3(x)))`.
* de Bruijn-type inversion then yields `c_n = e^gamma n (L3(n) + O(1))`.
* This axiom records the uniform upper-bound form needed in the proof.
-/
axiom eventual_upper_bound_ratio :
  ∃ (K : ℝ) (N : ℕ), 0 < K ∧
    ∀ ⦃n : ℕ⦄, N ≤ n →
      Myproj.cyclicEnumerator n
        / (Real.exp Myproj.eulerMascheroni * (n : ℝ))
      ≤ Myproj.L3 n + K

end ThmDusartCyclics
end Myproj

end
