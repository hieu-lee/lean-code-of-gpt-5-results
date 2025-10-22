import Myproj.HighDensityLattices.Axioms

/-!
Formalization of the high-density lattice abundance result from
`chosen_sphere_result.json`.
We invoke the global axiom `high_density_lattices_statement` sourced from
Klartag (2025).
-/

noncomputable section

namespace Myproj
namespace HighDensityLattices

open scoped BigOperators
open Real

theorem abundance_high_density_lattices :
    ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
        ∃ S : Finset (UnimodularLattice n),
          (S.card : ℝ) ≥ Real.exp (c * (n : ℝ) * Real.log (n : ℝ)) ∧
          (∀ {L} (hL : L ∈ S),
              latticeDelta L ≥ c * (n : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ n) ∧
              latticeSecondMoment L ≤ C * (n : ℝ)) ∧
          ∀ {L₁} (h₁ : L₁ ∈ S) {L₂} (h₂ : L₂ ∈ S),
            L₁ ≠ L₂ → ¬ gammaEquiv L₁ L₂ :=
  high_density_lattices_statement

end HighDensityLattices
end Myproj
