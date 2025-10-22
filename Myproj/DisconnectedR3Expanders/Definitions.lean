import Mathlib

/-!
Foundational definitions for the R₃ reconfiguration framework attached to the
Ramanujan-based fiber construction.
-/

noncomputable section

namespace Myproj
namespace DisconnectedR3Expanders

open scoped BigOperators
open Classical

/-- Edge weights take values in `{1,2,3}` (represented as `Fin 3`). -/
abbrev Weight := Fin 3

/-- Numerical value of an edge weight as a natural number. -/
def weightNat (w : Weight) : ℕ := w.val + 1

/-- Numerical value of an edge weight as an integer. -/
def weightInt (w : Weight) : ℤ := weightNat w

@[simp] def weight1 : Weight := ⟨0, by decide⟩
@[simp] def weight2 : Weight := ⟨1, by decide⟩
@[simp] def weight3 : Weight := ⟨2, by decide⟩

@[simp] lemma weightInt_val (w : Weight) :
    weightInt w = (w.val : ℤ) + 1 := by
  simp [weightInt, weightNat, Int.ofNat, Nat.succ_eq_add_one]

/-- Addition by one modulo three on `Fin 3`. -/
def rotate (i : Fin 3) : Fin 3 :=
  ⟨(i.val + 1) % 3, by
      have : (i.val + 1) % 3 < 3 := Nat.mod_lt _ (by decide)
      simpa using this⟩

@[simp] lemma rotate_val (i : Fin 3) : (rotate i).val = (i.val + 1) % 3 := rfl

@[simp] lemma rotate_zero :
    rotate (0 : Fin 3) = 1 := by
  ext
  simp [rotate]

@[simp] lemma rotate_one :
    rotate (1 : Fin 3) = 2 := by
  ext
  simp [rotate, Nat.succ_eq_add_one]

@[simp] lemma rotate_two :
    rotate (2 : Fin 3) = 0 := by
  ext
  simp [rotate, Nat.succ_eq_add_one]

/-- Base data of an `m`-regular bipartite graph on `2N` vertices. -/
structure BaseGraph (m : ℕ) where
  N : ℕ
  edgeSet : Finset (Fin N × Fin N)
  left_regular :
    ∀ ℓ : Fin N,
      (edgeSet.filter fun e => e.1 = ℓ).card = m
  right_regular :
    ∀ r : Fin N,
      (edgeSet.filter fun e => e.2 = r).card = m

namespace BaseGraph

variable {m : ℕ} (B : BaseGraph m)

/-- Coarse vertices split into left/right sides. -/
abbrev coarseVertex := Sum (Fin B.N) (Fin B.N)

/-- Actual vertices are coarse vertices equipped with a fiber index in `Fin 3`. -/
abbrev vertex := coarseVertex B × Fin 3

/-- Triangle (H) edges over a coarse vertex. -/
@[simp] abbrev Hedge :=
  coarseVertex B × {p : Fin 3 × Fin 3 // p.1 < p.2}

namespace Hedge

variable {B}

@[simp] def coarse (h : Hedge B) : BaseGraph.coarseVertex B := h.1
@[simp] def pair (h : Hedge B) : Fin 3 × Fin 3 := h.2.1
@[simp] def i (h : Hedge B) : Fin 3 := (pair h).1
@[simp] def j (h : Hedge B) : Fin 3 := (pair h).2
@[simp] lemma hij (h : Hedge B) : i h < j h := h.2.2

end Hedge

/-- Bipartite (B) edges are determined by an underlying coarse edge, a fiber index,
    and a twist indicating whether the right index shifts by `+1` (mod 3). -/
@[simp] abbrev Bedge :=
  {e : Fin B.N × Fin B.N // e ∈ B.edgeSet} × Fin 3 × Bool

namespace Bedge

variable {B}

@[simp] def leftIndex (e : Bedge B) : Fin B.N := (e.1.1).1
@[simp] def rightIndex (e : Bedge B) : Fin B.N := (e.1.1).2
@[simp] def layer (e : Bedge B) : Fin 3 := e.2.1
@[simp] def twisted (e : Bedge B) : Bool := e.2.2

/-- Left endpoint of a B-edge. -/
def left (e : Bedge B) : BaseGraph.vertex B :=
  (Sum.inl (leftIndex e), layer e)

/-- Right endpoint of a B-edge. -/
def right (e : Bedge B) : BaseGraph.vertex B :=
  let target := if twisted e then rotate (layer e) else layer e
  (Sum.inr (rightIndex e), target)

end Bedge

/-- Ambient edge type for the fiber graph. -/
@[simp] abbrev Edge := Sum (Hedge B) (Bedge B)

def Edge.endpoints : Edge B → BaseGraph.vertex B × BaseGraph.vertex B
  | Sum.inl h => ((Hedge.coarse h, Hedge.i h), (Hedge.coarse h, Hedge.j h))
  | Sum.inr e => (Bedge.left e, Bedge.right e)

namespace Edge

variable {B}

@[simp] lemma endpoints_fst (E : Edge B) :
    (E.endpoints).fst = match E with
    | Sum.inl h => (Hedge.coarse h, Hedge.i h)
    | Sum.inr e => Bedge.left e := by cases E <;> rfl

@[simp] lemma endpoints_snd (E : Edge B) :
    (E.endpoints).snd = match E with
    | Sum.inl h => (Hedge.coarse h, Hedge.j h)
    | Sum.inr e => Bedge.right e := by cases E <;> rfl

/-- Predicate expressing that `v` is incident with `E`. -/
def incident (v : BaseGraph.vertex B) (E : Edge B) : Prop :=
  v = E.endpoints.fst ∨ v = E.endpoints.snd

end Edge

@[simp] lemma incident_comm {B : BaseGraph m}
    {v : BaseGraph.vertex B} {E : Edge B} :
    Edge.incident v E ↔ v = E.endpoints.fst ∨ v = E.endpoints.snd := Iff.rfl

/-- Weightings on the edge set. -/
abbrev Weighting := Edge B → Weight

/-- Vertex sum of a weighting at a vertex. -/
def vertexSum (ω : Weighting B) (v : BaseGraph.vertex B) : ℤ := by
  classical
  exact ∑ e : Edge B, if Edge.incident v e then weightInt (ω e) else 0

/-- Neighbor-sum distinguishing property. -/
def IsNSD (ω : Weighting B) : Prop :=
  ∀ e : Edge B, vertexSum B ω e.endpoints.fst ≠ vertexSum B ω e.endpoints.snd

/-- Two weightings differ on exactly one edge. -/
def singleEdgeDiff (ω ω' : Weighting B) : Prop :=
  ∃ e : Edge B, ω e ≠ ω' e ∧ ∀ e', e' ≠ e → ω e' = ω' e'

@[simp] lemma singleEdgeDiff_symm {ω ω' : Weighting B} :
    singleEdgeDiff B ω ω' → singleEdgeDiff B ω' ω := by
  classical
  rintro ⟨e, hne, hrest⟩
  refine ⟨e, hne.symm, ?_⟩
  intro e' he'
  have := hrest e' he'
  simpa using this.symm

/-- Adjacency in the reconfiguration graph `R₃`. -/
def R3Adj (ω ω' : Weighting B) : Prop :=
  IsNSD B ω ∧ IsNSD B ω' ∧ singleEdgeDiff B ω ω'

@[simp] lemma R3Adj_symm {ω ω' : Weighting B} :
    R3Adj B ω ω' → R3Adj B ω' ω := by
  classical
  rintro ⟨hω, hω', hdiff⟩
  refine ⟨hω', hω, singleEdgeDiff_symm (B := B) hdiff⟩

/-- Reachability via successive single-edge resamplings. -/
def R3Reachable (ω ω' : Weighting B) : Prop :=
  Relation.ReflTransGen (R3Adj B) ω ω'

/-- Weightings with no outgoing single-edge resamplings. -/
def IsIsolated (ω : Weighting B) : Prop :=
  IsNSD B ω ∧ ∀ ω', R3Adj B ω ω' → ω' = ω

end BaseGraph

end DisconnectedR3Expanders
end Myproj
