import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Myproj.Definitions
import Myproj.Axioms
import Myproj.ThmSquares.Auxiliary

/-
Main statement: asymptotic for `C((n+1)^2) - C(n^2)` mirroring Theorem~\ref{thm:squares}.
-/

noncomputable section

namespace Myproj

open scoped Topology
open Filter

def squareDelta (n : ℕ) : ℝ :=
  Myproj.cyclicCounting ((n + 1) ^ 2) - Myproj.cyclicCounting (n ^ 2)

def squareAux (n : ℕ) : ℝ :=
  Myproj.cyclicCountingAux (n ^ 2) * ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ) ^ 2

def squareBase (n : ℕ) : ℝ :=
  Real.exp (-Myproj.eulerMascheroni) * (2 : ℝ) * (n : ℝ) * pollackCorrection n

def squareTarget (n : ℕ) : ℝ :=
  ((2 : ℝ) * (n : ℝ) / (Real.exp Myproj.eulerMascheroni * Myproj.L3 n))
    * (1 - Myproj.eulerMascheroni / Myproj.L3 n)

lemma squareBase_eq_target (n : ℕ) : squareBase n = squareTarget n := by
  have h_exp : Real.exp (-Myproj.eulerMascheroni)
      = (Real.exp Myproj.eulerMascheroni)⁻¹ := by
    simpa using Real.exp_neg Myproj.eulerMascheroni
  have h_factor :
      pollackCorrection n =
        (1 / Myproj.L3 n) * (1 - Myproj.eulerMascheroni / Myproj.L3 n) := by
    simp [pollackCorrection_apply, div_eq_mul_inv, sub_eq_add_neg, pow_two, mul_comm,
      mul_left_comm, mul_assoc, mul_add]
  simp [squareBase, squareTarget, h_exp, h_factor, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]

lemma ratio_delta_aux_tendsto :
    Tendsto (fun n : ℕ => squareDelta n / squareAux n) atTop (𝓝 1) := by
  simpa [squareDelta, squareAux] using cyclic_counting_square_increment_limit

lemma ratio_aux_base_tendsto :
    Tendsto (fun n : ℕ => squareAux n / squareBase n) atTop (𝓝 1) := by
  simpa [squareAux, squareBase] using aux_ratio_to_target

lemma eventual_factorization :
    (fun n : ℕ => squareDelta n / squareBase n)
      =ᶠ[atTop]
    (fun n : ℕ =>
      (squareDelta n / squareAux n) * (squareAux n / squareBase n)) := by
  have hAuxPos := eventually_pos_aux_square
  have hBasePos := eventually_pos_target
  refine (hAuxPos.and hBasePos).mono ?_
  intro n h
  rcases h with ⟨hAux, hBase⟩
  have hAux_ne : squareAux n ≠ 0 := ne_of_gt hAux
  have hBase_ne : squareBase n ≠ 0 := ne_of_gt hBase
  have hId :
      (squareDelta n / squareAux n) * (squareAux n / squareBase n)
        = squareDelta n / squareBase n := by
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hAux_ne, hBase_ne]
  exact hId.symm

lemma ratio_delta_base_tendsto :
    Tendsto (fun n : ℕ => squareDelta n / squareBase n) atTop (𝓝 1) := by
  have hMul :
      Tendsto (fun n : ℕ =>
        (squareDelta n / squareAux n) * (squareAux n / squareBase n))
        atTop (𝓝 (1 * 1)) :=
    (ratio_delta_aux_tendsto.mul ratio_aux_base_tendsto)
  have hProd : Tendsto (fun n : ℕ =>
      (squareDelta n / squareAux n) * (squareAux n / squareBase n))
      atTop (𝓝 1) := by simpa using hMul
  exact Filter.Tendsto.congr' eventual_factorization.symm hProd

/--
Asymptotic for consecutive-square increments of the cyclic counting function.
This matches Theorem~\ref{thm:squares} from the LaTeX proof.
-/
theorem cyclic_between_squares_asymptotic :
    Tendsto (fun n : ℕ =>
      (Myproj.cyclicCounting ((n + 1) ^ 2) - Myproj.cyclicCounting (n ^ 2))
        /
      (((2 : ℝ) * (n : ℝ)) / (Real.exp Myproj.eulerMascheroni * Myproj.L3 n)
        * (1 - Myproj.eulerMascheroni / Myproj.L3 n)))
      atTop (𝓝 1) := by
  have h := ratio_delta_base_tendsto
  refine (Filter.Tendsto.congr' ?_ h)
  have hEq :
      (fun n : ℕ => squareBase n) =ᶠ[atTop] (fun n : ℕ => squareTarget n) :=
    Filter.Eventually.of_forall squareBase_eq_target
  refine hEq.symm.mono ?_
  intro n hEqn
  have hEqn' : squareTarget n = squareBase n := by simpa using hEqn
  have hResult : squareDelta n / squareTarget n = squareDelta n / squareBase n := by
    simpa using congrArg (fun x => squareDelta n / x) hEqn'
  simpa [squareDelta, squareTarget, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hResult.symm

end Myproj

end
