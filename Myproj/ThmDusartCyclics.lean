import Mathlib.Data.Real.Basic
import Myproj.CyclicNumbers.Axioms
import Myproj.Definitions.IteratedLogs
import Myproj.ThmDusartCyclics.Main

/-!
Compatibility shim for the folderized Dusart module.

The full formalization now lives in `Myproj/ThmDusartCyclics/Main.lean`.
This file keeps the historical theorem name/module path available.
-/

noncomputable section

namespace Myproj

/--
Compatibility statement matching the prior API:
there exists an enumerator `c` for which the proposed Dusart-style universal
lower bound fails.
-/
theorem dusart_analog_cyclics_counterexample :
    ∃ c : ℕ → ℝ,
      ¬ (∀ n : ℕ, 1 < n →
        c n > Real.exp Myproj.eulerMascheroni * (n : ℝ) * (Myproj.L3 n + Myproj.L4 n)) := by
  refine ⟨Myproj.cyclicEnumerator, ?_⟩
  simpa using Myproj.ThmDusartCyclics.dusart_analog_cyclics_false

end Myproj

end
