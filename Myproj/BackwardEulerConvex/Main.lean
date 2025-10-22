import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Myproj.BackwardEulerConvex.Axioms

/-!
Formalization of the convexity statement and its strongly convex refinement for the implicit
(backward Euler / proximal point) scheme described in
`research mode traces/chosen_convex_result.json`.
-/

noncomputable section

namespace Myproj
namespace BackwardEulerConvex

open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {grad : E → E} {η : ℝ} {μ : ℝ} {x : ℕ → E}

/-- Step differences `sₙ = x_{n+1} - x_n`. -/
def step (x : ℕ → E) (n : ℕ) : E := x (n.succ) - x n

/-- Objective gaps `Δₙ = f(x_n) - f(x_{n+1})`. -/
def gap (f : E → ℝ) (x : ℕ → E) (n : ℕ) : ℝ := f (x n) - f (x n.succ)

/-- Second differences `δₙ = Δₙ - Δ_{n+1}`. -/
def secondDiff (f : E → ℝ) (x : ℕ → E) (n : ℕ) : ℝ :=
  gap f x n - gap f x n.succ

lemma secondDiff_eval (n : ℕ) :
    secondDiff f x n = f (x (n + 2)) - 2 * f (x (n + 1)) + f (x n) := by
  simp [secondDiff, gap, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul]

/-- Convexity of the objective values along the implicit scheme. -/
lemma secondDiff_nonneg
    (hstep : ∀ n, x (n + 1) = x n - η • grad (x (n + 1)))
    (hgrad : ∀ y, HasGradientAt f (grad y) y)
    (hconvex : ConvexOn ℝ (Set.univ : Set E) f)
    (hη : 0 < η) :
    ∀ n, 0 ≤ secondDiff f x n := by
  intro n
  have := Myproj.backward_euler_second_diff_nonneg hη f grad x hstep hconvex hgrad n
  simpa [secondDiff_eval (f := f) (x := x) n, add_comm, add_left_comm, add_assoc]
    using this

/-- `Δ_{n+1} ≤ Δ_n` for every implicit step. -/
lemma gap_succ_le
    (hstep : ∀ n, x (n + 1) = x n - η • grad (x (n + 1)))
    (hgrad : ∀ y, HasGradientAt f (grad y) y)
    (hconvex : ConvexOn ℝ (Set.univ : Set E) f)
    (hη : 0 < η) (n : ℕ) :
    gap f x (n + 1) ≤ gap f x n := by
  have h := secondDiff_nonneg (f := f) (grad := grad) (η := η) (x := x)
    hstep hgrad hconvex hη n
  simpa [secondDiff, sub_eq_add_neg] using sub_nonneg.mp h

@[simp] lemma gap_of_constant_step {n : ℕ} (h : x (n + 1) = x n) : gap f x n = 0 := by
  simp [gap, h]

/-- Under strong convexity every non-trivial step yields a strict decrease of the gaps. -/
lemma gap_succ_lt_of_step_ne_zero
    (hstep : ∀ n, x (n + 1) = x n - η • grad (x (n + 1)))
    (hgrad : ∀ y, HasGradientAt f (grad y) y)
    (hstrong : StrongConvexOn (Set.univ : Set E) μ f)
    (hη : 0 < η) (hμ : 0 < μ) {n : ℕ} (hs : x (n + 1) ≠ x n) :
    gap f x (n + 1) < gap f x n := by
  have hδ := Myproj.backward_euler_second_diff_pos hη hμ f grad x hstep hstrong hgrad n hs
  have hδ' : 0 < secondDiff f x n := by
    simpa [secondDiff_eval (f := f) (x := x) n, add_comm, add_left_comm, add_assoc]
      using hδ
  have : 0 < gap f x n - gap f x (n + 1) := by
    simpa [secondDiff, sub_eq_add_neg] using hδ'
  exact sub_pos.mp this

end BackwardEulerConvex
end Myproj
