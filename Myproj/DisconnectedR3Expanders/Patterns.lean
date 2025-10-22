import Mathlib
import Myproj.DisconnectedR3Expanders.Definitions

/-!
Common patterns for the fibered construction: H-sum labellings and canonical
pairs of vertex sums.
-/

noncomputable section

namespace Myproj
namespace DisconnectedR3Expanders

open Classical

namespace BaseGraph

variable {m : ℕ} {B : BaseGraph m}

/-- H-sums on left fibers: indices `0,1,2` correspond to `3,4,5`. -/
def leftHSum : Fin 3 → ℤ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 4
  | _ => 5

/-- H-sums on right fibers: indices `0,1,2` correspond to `4,5,3`. -/
def rightHSum : Fin 3 → ℤ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 5
  | _ => 3

@[simp] lemma leftHSum_values (i : Fin 3) : leftHSum i ∈ ({3, 4, 5} : Finset ℤ) := by
  classical
  fin_cases i <;> simp [leftHSum]

@[simp] lemma rightHSum_values (i : Fin 3) : rightHSum i ∈ ({3, 4, 5} : Finset ℤ) := by
  classical
  fin_cases i <;> simp [rightHSum]

/-- H-sum labelling depending on the side of the coarse vertex. -/
def hLabel : B.coarseVertex → Fin 3 → ℤ
  | Sum.inl _ => leftHSum
  | Sum.inr _ => rightHSum

/-- Catalogue of all H/B sum pairs occurring in the construction. -/
def canonicalPairs : Finset (ℤ × ℤ) :=
  ({⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 3⟩, ⟨3, 5⟩, ⟨4, 3⟩, ⟨5, 4⟩} : Finset (ℤ × ℤ))

/-- Sum pair attached to an H-edge in fiber `x`. -/
def hPair (x : B.coarseVertex) (h : Hedge B) : ℤ × ℤ :=
  (hLabel (B := B) x (Hedge.i h), hLabel (B := B) x (Hedge.j h))

/-- Sum pair attached to a B-edge. -/
def bPair (e : Bedge B) : ℤ × ℤ :=
  let j := if Bedge.twisted e then rotate (Bedge.layer e) else Bedge.layer e
  (leftHSum (Bedge.layer e), rightHSum j)

/-- Characterisations of incident B-edges. -/
@[simp] lemma incident_left_iff (ℓ : Fin B.N) (i : Fin 3) (e : Bedge B) :
    Edge.incident (B := B) (Sum.inl ℓ, i) (Sum.inr e)
      ↔ Bedge.leftIndex e = ℓ ∧ Bedge.layer e = i := by
  classical
  unfold Edge.incident Edge.endpoints
  simp [Bedge.left, Bedge.right, Prod.ext_iff, eq_comm, and_left_comm, and_assoc]

@[simp] lemma incident_right_iff (r : Fin B.N) (j : Fin 3) (e : Bedge B) :
    Edge.incident (B := B) (Sum.inr r, j) (Sum.inr e)
      ↔ Bedge.rightIndex e = r ∧
          (if Bedge.twisted e then rotate (Bedge.layer e) else Bedge.layer e) = j := by
  classical
  unfold Edge.incident Edge.endpoints
  simp [Bedge.left, Bedge.right, Prod.ext_iff, eq_comm, and_left_comm, and_assoc]

/-- Absolute difference for any canonical pair is either `1` or `2`. -/
lemma canonicalPairs_abs {a b : ℤ}
    (h : (a, b) ∈ canonicalPairs) : |a - b| = 1 ∨ |a - b| = 2 := by
  classical
  have : (a, b) = (3, 4) ∨ (a, b) = (4, 5) ∨ (a, b) = (5, 3) ∨
      (a, b) = (3, 5) ∨ (a, b) = (4, 3) ∨ (a, b) = (5, 4) := by
    simpa [canonicalPairs] using h
  rcases this with h1 | h2 | h3 | h4 | h5 | h6
  all_goals
    simp [h1, h2, h3, h4, h5, h6]

/-- Canonical pairs never have equal coordinates. -/
lemma canonicalPairs_ne {a b : ℤ}
    (h : (a, b) ∈ canonicalPairs) : a ≠ b := by
  classical
  have := canonicalPairs_abs (B := B) h
  intro hEq
  have : |a - b| = 0 := by simpa [hEq]
  rcases this with habs | habs <;> simp [habs] at this

/-- Sum pairs on left fibers lie in the canonical list. -/
lemma left_pair_mem (i j : Fin 3) (hij : i < j) :
    (leftHSum i, leftHSum j) ∈ canonicalPairs := by
  classical
  fin_cases i <;> fin_cases j <;> try cases hij <;>
    simp [leftHSum, canonicalPairs]

/-- Sum pairs on right fibers lie in the canonical list. -/
lemma right_pair_mem (i j : Fin 3) (hij : i < j) :
    (rightHSum i, rightHSum j) ∈ canonicalPairs := by
  classical
  fin_cases i <;> fin_cases j <;> try cases hij <;>
    simp [rightHSum, canonicalPairs]

/-- Every H-edge sum pair belongs to the canonical list. -/
lemma hPair_mem (x : B.coarseVertex) (h : Hedge B) :
    hPair (B := B) x h ∈ canonicalPairs := by
  classical
  rcases x with ⟨ℓ | r⟩
  · rcases h with ⟨_, ⟨⟨i, j⟩, hij⟩⟩
    simpa [hPair, hLabel, Hedge.i, Hedge.j, Hedge.pair]
      using left_pair_mem (B := B) i j hij
  · rcases h with ⟨_, ⟨⟨i, j⟩, hij⟩⟩
    simpa [hPair, hLabel, Hedge.i, Hedge.j, Hedge.pair]
      using right_pair_mem (B := B) i j hij

/-- Every B-edge sum pair belongs to the canonical list. -/
lemma bPair_mem (e : Bedge B) : bPair (B := B) e ∈ canonicalPairs := by
  classical
  cases htw : Bedge.twisted e
  · simp [bPair, htw, canonicalPairs]
  · simp [bPair, htw, canonicalPairs]

end BaseGraph

end DisconnectedR3Expanders
end Myproj
