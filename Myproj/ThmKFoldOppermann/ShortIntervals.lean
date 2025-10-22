import Myproj.ThmKFoldOppermann.Axioms
import Myproj.Definitions

/-
Lightweight wrappers around the analytic axioms used in the `k`-fold
Oppermann proof for primes.
-/

noncomputable section

namespace Myproj
namespace ThmKFoldOppermann

open Real

lemma primesLeft_eventually :
    ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
      Myproj.primesLeft n ≥ (n : ℝ) / (200 * Real.log (n : ℝ)) :=
  primesLeft_lower_bound

lemma primesRight_eventually :
    ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
      Myproj.primesRight n ≥ (n : ℝ) / (300 * Real.log (n : ℝ)) :=
  primesRight_lower_bound

lemma eventually_nat_div_log_ge' (k : ℕ) :
    ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
      (n : ℝ) / Real.log (n : ℝ) ≥ k :=
  eventually_nat_div_log_ge k

end ThmKFoldOppermann
end Myproj
