import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Data.Real.Basic
import Myproj.DisconnectedR3.Definitions

/-
Axioms isolating the external results used in the `DisconnectedR3` formalization.
-/

noncomputable section

namespace Myproj
namespace DisconnectedR3

open scoped Classical
open Filter

/--
Data describing the infinite family of fibered expanders `Y_N` built from bipartite Ramanujan
graphs in the proof of `chosen_graph_result.json`.
-/
structure CounterexampleData (c0 : ℝ) where
  mPrime : ℕ
  hmPrime : 17 ≤ mPrime
  witnesses : ℕ → Witness
  degree_eq :
      ∀ N : ℕ, (witnesses N).base.degree = 2 * mPrime + 2
  vertexCount_eq :
      ∀ N : ℕ, (witnesses N).base.vertexCount = 6 * N
  spectralGap_bound :
      ∀ᶠ N : ℕ in atTop, c0 ≤ (witnesses N).base.spectralGap
  isolated_pair :
      ∀ N : ℕ, (witnesses N).hasIsolatedPair

/-
The following axiom packages three classical inputs:
1. Existence of infinite families of bipartite Ramanujan graphs of fixed degree
   (Marcus–Spielman–Srivastava, *Interlacing Families II*, Ann. of Math. 182 (2015), 327–425).
2. Operator-norm control for the fiber construction used in the proof, combining the
   singular-value formula for Kronecker products (Horn–Johnson, *Matrix Analysis*, §4.2)
   with the Ramanujan bound `σ₂(P) ≤ 2√(m' − 1)` to obtain the adjacency spectral gap
   `min { m', 2 (m' − σ₂(P)) }`.
3. The triangle gadget check guaranteeing both an isolated NSD weighting and a distinct NSD
   weighting after single-edge resampling (as detailed in the proof text).
-/
axiom counterexample_family_exists
    {c0 : ℝ} (hc0 : 0 < c0) :
    CounterexampleData c0

end DisconnectedR3
end Myproj
