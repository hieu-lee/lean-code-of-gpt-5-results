import Mathlib.Data.Real.Basic
import Myproj.DisconnectedR3Expanders.Definitions

/-
Ramanujan-family axioms used in the `DisconnectedR3Expanders` folder.
-/

noncomputable section

namespace Myproj
namespace DisconnectedR3Expanders

/--
Ramanujan base data: an `m`-regular bipartite graph together with spectral
information on its adjacency matrix.
Source: Brouwer–Haemers, *Spectra of Graphs* (2011), Section 3.1.
-/
structure RamanujanBase (m : ℕ) : Type :=
  (base : BaseGraph m)
  (sigma₁ sigma₂ : ℝ)
  (sigma₁_eq : sigma₁ = m)
  (sigma₂_nonneg : 0 ≤ sigma₂)
  (sigma₂_le : sigma₂ ≤ 2 * Real.sqrt (m - 1))

/--
Arbitrarily large bipartite Ramanujan graphs exist for every degree.
Source: Marcus–Spielman–Srivastava (2015), *Interlacing Families I: Bipartite
Ramanujan Graphs of All Degrees*, Theorem 1.2.
-/
axiom ramanujan_family_exists
  {m : ℕ} (hm : 3 ≤ m) :
  ∀ k : ℕ, ∃ data : RamanujanBase m, k ≤ data.base.N

end DisconnectedR3Expanders
end Myproj

end
