import Mathlib
import Myproj.DisconnectedR3Expanders.Definitions
import Myproj.DisconnectedR3Expanders.Patterns
import Myproj.DisconnectedR3Expanders.BedgeSums
import Myproj.DisconnectedR3Expanders.Axioms

/-!
Auxiliary data for the fibered graphs `Y_N`: the `FiberInstance` packaging and
canonical triangle weightings on each fiber.
-/

noncomputable section

namespace Myproj
namespace DisconnectedR3Expanders

open Classical

/-- Data required for the fiber construction: a degree `m` and a Ramanujan base. -/
structure FiberInstance : Type :=
  (m : ℕ)
  (hm : 3 ≤ m)
  (data : RamanujanBase m)

/-- Convenience projection extracting the underlying bipartite base graph. -/
def BaseGraph.ofInstance (F : FiberInstance) : BaseGraph F.m := F.data.base

namespace BaseGraph

variable {m : ℕ} {B : BaseGraph m}

/-- Canonical triangle weighting on a fiber indexed by `x`. -/
def hEdgeWeight (x : B.coarseVertex) (h : Hedge B) : Weight :=
  let a := hLabel (B := B) x (Hedge.i h)
  let b := hLabel (B := B) x (Hedge.j h)
  if (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) then weight1
  else if (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4) then weight3
  else weight2

end BaseGraph

end DisconnectedR3Expanders
end Myproj
