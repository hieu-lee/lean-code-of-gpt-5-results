import Mathlib
import Myproj.DisconnectedR3Expanders.Definitions
import Myproj.DisconnectedR3Expanders.Patterns

/-!
Evaluation of B-edge contributions under uniform weights.
-/

noncomputable section

namespace Myproj
namespace DisconnectedR3Expanders

open scoped BigOperators
open Classical

namespace BaseGraph

variable {m : ℕ} {B : BaseGraph m}

/-- Sum of the B-edge contributions at a left vertex when all B-edges carry weight `wB`. -/
lemma sum_bedges_left_const (ℓ : Fin B.N) (i : Fin 3) (wB : Weight) :
    ∑ e : Bedge B,
        (if Bedge.leftIndex e = ℓ ∧ Bedge.layer e = i then (weightInt wB : ℤ) else 0)
      = ((2 * m : ℕ) : ℤ) * weightInt wB := by
  classical
  have h₁ :
      ∑ e : Bedge B,
          (if Bedge.leftIndex e = ℓ ∧ Bedge.layer e = i then (weightInt wB : ℤ) else 0)
        =
        ∑ edge : {e // e ∈ B.edgeSet},
          ∑ layer' : Fin 3,
            ∑ _twist : Bool,
              (if edge.1.1 = ℓ ∧ layer' = i then (weightInt wB : ℤ) else 0) := by
    simpa [Bedge, Bedge.leftIndex, Bedge.layer]
      using (Fintype.sum_prod_type
        (f := fun p : {e // e ∈ B.edgeSet} × (Fin 3 × Bool) =>
          let edge := p.1.1
          let layer' := p.2.1
          if edge.1 = ℓ ∧ layer' = i then (weightInt wB : ℤ) else 0)).symm
  have h_bool :
      ∀ edge : {e // e ∈ B.edgeSet} → ∀ layer' : Fin 3,
        ∑ _twist : Bool,
            (if edge.1.1 = ℓ ∧ layer' = i then (weightInt wB : ℤ) else 0)
          =
            if edge.1.1 = ℓ ∧ layer' = i then (2 : ℤ) * weightInt wB else 0 := by
    intro edge layer'
    simp [two_mul, add_comm, add_left_comm, add_assoc]
  have h₂ :
      ∑ edge : {e // e ∈ B.edgeSet},
          ∑ layer' : Fin 3,
            ∑ _twist : Bool,
              (if edge.1.1 = ℓ ∧ layer' = i then (weightInt wB : ℤ) else 0)
        =
        ∑ edge : {e // e ∈ B.edgeSet},
          ∑ layer' : Fin 3,
            if edge.1.1 = ℓ ∧ layer' = i then (2 : ℤ) * weightInt wB else 0 := by
    refine Finset.sum_congr rfl ?_
    intro edge _
    refine Finset.sum_congr rfl ?_
    intro layer' _
    exact h_bool edge layer'
  have h₃ :
      ∑ edge : {e // e ∈ B.edgeSet},
          ∑ layer' : Fin 3,
            if edge.1.1 = ℓ ∧ layer' = i then (2 : ℤ) * weightInt wB else 0
        =
        ∑ edge : {e // e ∈ B.edgeSet},
          if edge.1.1 = ℓ then (2 : ℤ) * weightInt wB else 0 := by
    refine Finset.sum_congr rfl ?_
    intro edge _
    by_cases hEdge : edge.1.1 = ℓ
    · subst hEdge
      refine Finset.sum_eq_single i ?_ ?_
      · intro layer' hlayer'
        by_cases hli : layer' = i
        · subst hli; simp
        · simp [hli]
      · intro hi
        have : (i : Fin 3) ∉ (Finset.univ : Finset (Fin 3)) := by simpa using hi
        simp [this]
    · simp [hEdge]
  have h_edges :
      ∑ edge : {e // e ∈ B.edgeSet},
          if edge.1.1 = ℓ then (2 : ℤ) * weightInt wB else 0
        =
        ((B.edgeSet.filter fun e => e.1 = ℓ).card : ℤ) * ((2 : ℤ) * weightInt wB) := by
    have :
        ∑ edge : {e // e ∈ B.edgeSet},
            if edge.1.1 = ℓ then (2 : ℤ) * weightInt wB else 0
          =
          ∑ e in B.edgeSet.filter fun e => e.1 = ℓ, (2 : ℤ) * weightInt wB := by
      refine (Finset.sum_subtype (s := B.edgeSet) ?_ ?_).symm
      · intro e; exact if e.1 = ℓ then (2 : ℤ) * weightInt wB else 0
      · intro e he
        by_cases h : e.1 = ℓ
        · simp [Finset.mem_filter, he, h]
        · simp [Finset.mem_filter, he, h]
    have hconst :
        ∑ e in B.edgeSet.filter fun e => e.1 = ℓ, (2 : ℤ) * weightInt wB
          = (B.edgeSet.filter fun e => e.1 = ℓ).card • ((2 : ℤ) * weightInt wB) :=
      Finset.sum_const_nsmul _ _
    have hmul :
        (B.edgeSet.filter fun e => e.1 = ℓ).card • ((2 : ℤ) * weightInt wB)
          = ((B.edgeSet.filter fun e => e.1 = ℓ).card : ℤ) * ((2 : ℤ) * weightInt wB) :=
      by simpa [nsmul_eq_mul]
    simpa [this, hconst, hmul]
  have hcard : (B.edgeSet.filter fun e => e.1 = ℓ).card = m := B.left_regular ℓ
  have h_final :
      ∑ e : Bedge B,
          (if Bedge.leftIndex e = ℓ ∧ Bedge.layer e = i then (weightInt wB : ℤ) else 0)
        = ((B.edgeSet.filter fun e => e.1 = ℓ).card : ℤ) * ((2 : ℤ) * weightInt wB) := by
    simpa [h₁, h₂, h₃] using h_edges
  simpa [h_final, hcard, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc,
    bit0, Nat.cast_ofNat]

/-- Sum of the B-edge contributions at a right vertex when all B-edges carry weight `wB`. -/
lemma sum_bedges_right_const (r : Fin B.N) (j : Fin 3) (wB : Weight) :
    ∑ e : Bedge B,
        (if Bedge.rightIndex e = r ∧
            (if Bedge.twisted e then rotate (Bedge.layer e) else Bedge.layer e) = j
          then (weightInt wB : ℤ) else 0)
      = ((2 * m : ℕ) : ℤ) * weightInt wB := by
  classical
  have h₁ :
      ∑ e : Bedge B,
          (if Bedge.rightIndex e = r ∧
              (if Bedge.twisted e then rotate (Bedge.layer e) else Bedge.layer e) = j
            then (weightInt wB : ℤ) else 0)
        =
        ∑ edge : {e // e ∈ B.edgeSet},
          ∑ layer' : Fin 3,
            ∑ twist : Bool,
              (if edge.1.2 = r ∧
                  (if twist then rotate layer' else layer') = j
                then (weightInt wB : ℤ) else 0) := by
    simpa [Bedge, Bedge.rightIndex, Bedge.layer, Bedge.twisted]
      using (Fintype.sum_prod_type
        (f := fun p : {e // e ∈ B.edgeSet} × (Fin 3 × Bool) =>
          let edge := p.1.1
          let layer' := p.2.1
          let twist := p.2.2
          if edge.2 = r ∧ (if twist then rotate layer' else layer') = j then
            (weightInt wB : ℤ) else 0)).symm
  have h_bool :
      ∀ edge : {e // e ∈ B.edgeSet} → ∀ layer' : Fin 3,
        ∑ twist : Bool,
            (if edge.1.2 = r ∧
                (if twist then rotate layer' else layer') = j
              then (weightInt wB : ℤ) else 0)
          =
        if edge.1.2 = r then
          ((if layer' = j then weightInt wB else 0) +
            (if rotate layer' = j then weightInt wB else 0))
        else 0 := by
    intro edge layer'
    by_cases hEdge : edge.1.2 = r
    · subst hEdge
      simp [Bool.forall_bool, add_comm, add_left_comm, add_assoc]
    · simp [hEdge]
  have h₂ :
      ∑ edge : {e // e ∈ B.edgeSet},
          ∑ layer' : Fin 3,
            ∑ twist : Bool,
              (if edge.1.2 = r ∧
                  (if twist then rotate layer' else layer') = j
                then (weightInt wB : ℤ) else 0)
        =
        ∑ edge : {e // e ∈ B.edgeSet},
          ∑ layer' : Fin 3,
            if edge.1.2 = r then
              ((if layer' = j then weightInt wB else 0) +
                (if rotate layer' = j then weightInt wB else 0))
            else 0 := by
    refine Finset.sum_congr rfl ?_
    intro edge _
    refine Finset.sum_congr rfl ?_
    intro layer' _
    exact h_bool edge layer'
  have h_layers :
      ∑ layer' : Fin 3,
          ((if layer' = j then weightInt wB else 0) +
            (if rotate layer' = j then weightInt wB else 0))
        = (2 : ℤ) * weightInt wB := by
    classical
    fin_cases j using Fin.cases <;>
      simp [Fin.sum_univ_three, rotate_zero, rotate_one, rotate_two,
        add_comm, add_left_comm, add_assoc]
  have h₃ :
      ∑ edge : {e // e ∈ B.edgeSet},
          ∑ layer' : Fin 3,
            if edge.1.2 = r then
              ((if layer' = j then weightInt wB else 0) +
                (if rotate layer' = j then weightInt wB else 0))
            else 0
        =
        ∑ edge : {e // e ∈ B.edgeSet},
          if edge.1.2 = r then (2 : ℤ) * weightInt wB else 0 := by
    refine Finset.sum_congr rfl ?_
    intro edge _
    by_cases hEdge : edge.1.2 = r
    · subst hEdge
      simpa [h_layers]
    · simp [hEdge]
  have h_edges :
      ∑ edge : {e // e ∈ B.edgeSet},
          if edge.1.2 = r then (2 : ℤ) * weightInt wB else 0
        =
        ((B.edgeSet.filter fun e => e.2 = r).card : ℤ) * ((2 : ℤ) * weightInt wB) := by
    have :
        ∑ edge : {e // e ∈ B.edgeSet},
            if edge.1.2 = r then (2 : ℤ) * weightInt wB else 0
          =
          ∑ e in B.edgeSet.filter fun e => e.2 = r, (2 : ℤ) * weightInt wB := by
      refine (Finset.sum_subtype (s := B.edgeSet) ?_ ?_).symm
      · intro e; exact if e.2 = r then (2 : ℤ) * weightInt wB else 0
      · intro e he
        by_cases h : e.2 = r
        · simp [Finset.mem_filter, he, h]
        · simp [Finset.mem_filter, he, h]
    have hconst :
        ∑ e in B.edgeSet.filter fun e => e.2 = r, (2 : ℤ) * weightInt wB
          = (B.edgeSet.filter fun e => e.2 = r).card • ((2 : ℤ) * weightInt wB) :=
      Finset.sum_const_nsmul _ _
    have hmul :
        (B.edgeSet.filter fun e => e.2 = r).card • ((2 : ℤ) * weightInt wB)
          = ((B.edgeSet.filter fun e => e.2 = r).card : ℤ) * ((2 : ℤ) * weightInt wB) :=
      by simpa [nsmul_eq_mul]
    simpa [this, hconst, hmul]
  have hcard : (B.edgeSet.filter fun e => e.2 = r).card = m := B.right_regular r
  have h_final :
      ∑ e : Bedge B,
          (if Bedge.rightIndex e = r ∧
              (if Bedge.twisted e then rotate (Bedge.layer e) else Bedge.layer e) = j
            then (weightInt wB : ℤ) else 0)
        = ((B.edgeSet.filter fun e => e.2 = r).card : ℤ) * ((2 : ℤ) * weightInt wB) := by
    simpa [h₁, h₂, h₃] using h_edges
  simpa [h_final, hcard, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc,
    bit0, Nat.cast_ofNat]

end BaseGraph

end DisconnectedR3Expanders
end Myproj
