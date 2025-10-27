import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Basic

/-
Helper definitions for the `DisconnectedR3` development.
-/

noncomputable section

namespace Myproj
namespace DisconnectedR3

open scoped Classical

/-- Record capturing the quantitative information attached to a `d`-regular expander. -/
structure ExpanderInstance where
  /-- Number of vertices of the underlying `d`-regular graph. -/
  vertexCount : ℕ
  /-- Common degree of every vertex in the base graph. -/
  degree : ℕ
  /-- Adjacency spectral gap of the base graph. -/
  spectralGap : ℝ

/-- `R₃(G)` data: the vertices are neighbor-sum-distinguishing `{1,2,3}`-weightings. -/
structure R3Data where
  weighting : Type
  [weightingFintype : Fintype weighting]
  graph : SimpleGraph weighting

attribute [instance] R3Data.weightingFintype

/-- A combined record bundling an expander together with its `R₃(G)` graph. -/
structure Witness where
  base : ExpanderInstance
  r3 : R3Data

/-- There exist an isolated NSD weighting and a distinct NSD weighting. -/
def Witness.hasIsolatedPair (W : Witness) : Prop :=
  ∃ ω ω', ω ≠ ω' ∧ W.r3.graph.degree ω = 0

/-- `R₃(G)` is connected precisely when the underlying simple graph is connected. -/
def Witness.r3Connected (W : Witness) : Prop :=
  W.r3.graph.Connected

/--
If `R₃(G)` has an isolated vertex and another distinct vertex, then it is disconnected.
-/
lemma r3_not_connected_of_isolated {W : Witness}
    (h : W.hasIsolatedPair) :
    ¬ W.r3Connected := by
  classical
  obtain ⟨ω, ω', hneq, hdeg⟩ := h
  intro hconn
  haveI : Nontrivial W.r3.weighting := ⟨⟨ω, ω', hneq⟩⟩
  have hdegpos :
      0 < W.r3.graph.degree ω := by
    classical
    simpa using
      (hconn.preconnected.degree_pos_of_nontrivial ω)
  exact (Nat.ne_of_lt hdegpos) (by simpa [hdeg])

end DisconnectedR3
end Myproj
