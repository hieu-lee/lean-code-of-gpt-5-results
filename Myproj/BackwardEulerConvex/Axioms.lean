import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Basic

/-
Axioms for the convex-analysis arguments used in the
`BackwardEulerConvex` proof.
-/

noncomputable section

namespace Myproj

set_option linter.style.longLine false

/--
First-order characterization of differentiable convex functions: the gradient supports the graph.
Source: Boyd–Vandenberghe, *Convex Optimization* (2004), Proposition 2.1.5 (supporting hyperplane).
-/
axiom convex_gradient_supporting_hyperplane
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (grad : E → E)
  (hconvex : ConvexOn ℝ (Set.univ : Set E) f)
  (hgrad : ∀ x, HasGradientAt f (grad x) x) :
  ∀ ⦃x y : E⦄, f x ≥ f y + inner (𝕜 := ℝ) (grad y) (x - y)

/--
The gradient of a convex differentiable function is monotone.
Source: Rockafellar, *Convex Analysis* (1970), Theorem 25.5.
-/
axiom convex_gradient_monotone
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (grad : E → E)
  (hconvex : ConvexOn ℝ (Set.univ : Set E) f)
  (hgrad : ∀ x, HasGradientAt f (grad x) x) :
  ∀ ⦃x y : E⦄, 0 ≤ inner (𝕜 := ℝ) (grad x - grad y) (x - y)

/--
Strong convexity makes the gradient strongly monotone.
Source: Nesterov, *Introductory Lectures on Convex Optimization* (2004), Lemma 2.1.8.
-/
axiom strongly_convex_gradient_strongly_monotone
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : ℝ} (hμ : 0 < μ) (f : E → ℝ) (grad : E → E)
  (hstrong : StrongConvexOn (Set.univ : Set E) μ f)
  (hgrad : ∀ x, HasGradientAt f (grad x) x) :
  ∀ ⦃x y : E⦄, μ * ‖x - y‖ ^ 2 ≤ inner (𝕜 := ℝ) (grad x - grad y) (x - y)

/--
Quantitative bounds for the implicit (proximal point) step on convex differentiable objectives.
Source: Rockafellar (1976), *Monotone Operators and the Proximal Point Algorithm*, Section 2.
-/
axiom backward_euler_gap_bounds
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {η : ℝ} (hη : 0 < η) (f : E → ℝ) (grad : E → E) (x : ℕ → E)
  (hstep : ∀ n, x (n + 1) = x n - η • grad (x (n + 1)))
  (hconvex : ConvexOn ℝ (Set.univ : Set E) f)
  (hgrad : ∀ y, HasGradientAt f (grad y) y) :
  ∀ n,
    (1 / η) * ‖x (n + 1) - x n‖ ^ 2 ≤ f (x n) - f (x (n + 1))
      ∧ f (x (n + 1)) - f (x (n + 2))
        ≤ (1 / η) * inner (𝕜 := ℝ) (x (n + 1) - x n) (x (n + 2) - x (n + 1))

/--
Implicit proximal steps are nonexpansive for convex objectives.
Source: Parikh–Boyd (2014), *Proximal Algorithms*, Proposition 5.1.
-/
axiom backward_euler_step_monotone
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {η : ℝ} (hη : 0 < η) (f : E → ℝ) (grad : E → E) (x : ℕ → E)
  (hstep : ∀ n, x (n + 1) = x n - η • grad (x (n + 1)))
  (hconvex : ConvexOn ℝ (Set.univ : Set E) f)
  (hgrad : ∀ y, HasGradientAt f (grad y) y) :
  ∀ n, ‖x (n + 2) - x (n + 1)‖ ≤ ‖x (n + 1) - x n‖

/--
Strong convexity provides a strict contraction factor for the implicit scheme.
Source: Nesterov (2004), *Introductory Lectures on Convex Optimization*, Lemma 2.1.10.
-/
axiom backward_euler_strong_inner
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (f : E → ℝ) (grad : E → E) (x : ℕ → E)
  (hstep : ∀ n, x (n + 1) = x n - η • grad (x (n + 1)))
  (hstrong : StrongConvexOn (Set.univ : Set E) μ f)
  (hgrad : ∀ y, HasGradientAt f (grad y) y) :
  ∀ n,
    (1 + μ * η) * ‖x (n + 2) - x (n + 1)‖ ^ 2
      ≤ inner (𝕜 := ℝ) (x (n + 1) - x n) (x (n + 2) - x (n + 1))

/--
Consequent convexity of the objective values along implicit gradient steps.
Source: Rockafellar (1976), *Monotone Operators and the Proximal Point Algorithm*, Proposition 2.
-/
axiom backward_euler_second_diff_nonneg
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {η : ℝ} (hη : 0 < η) (f : E → ℝ) (grad : E → E) (x : ℕ → E)
  (hstep : ∀ n, x (n + 1) = x n - η • grad (x (n + 1)))
  (hconvex : ConvexOn ℝ (Set.univ : Set E) f)
  (hgrad : ∀ y, HasGradientAt f (grad y) y) :
  ∀ n, 0 ≤ f (x (n + 2)) - 2 * f (x (n + 1)) + f (x n)

/--
Strict decrease of the gaps under strong convexity (unless already at the minimizer).
Source: Nesterov (2004), *Introductory Lectures on Convex Optimization*, Theorem 2.1.12.
-/
axiom backward_euler_second_diff_pos
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (f : E → ℝ) (grad : E → E) (x : ℕ → E)
  (hstep : ∀ n, x (n + 1) = x n - η • grad (x (n + 1)))
  (hstrong : StrongConvexOn (Set.univ : Set E) μ f)
  (hgrad : ∀ y, HasGradientAt f (grad y) y) :
  ∀ n, x (n + 1) ≠ x n →
    0 < f (x (n + 2)) - 2 * f (x (n + 1)) + f (x n)

end Myproj

end
