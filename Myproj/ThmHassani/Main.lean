import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic
import Myproj.Definitions
import Myproj.CyclicNumbers.Axioms
import Myproj.ThmVrba.Axioms
import Myproj.ThmHassani.Axioms

/-!
We formalise Hassani's analog (`theorems/thm_hassani.tex`), proving that the
ratio between the arithmetic and geometric means of cyclic numbers satisfies
`Aₙ / Gₙ → e / 2`.  The argument follows the LaTeX proof verbatim, importing
the analytic axioms established in `Myproj.ThmHassani.Axioms`.
-/

noncomputable section

namespace Myproj
namespace Hassani

open Filter
open scoped Topology

local notation "c" => Myproj.cyclicEnumerator
local notation "C" => Myproj.cyclicCountingReal
local notation "S" => Myproj.Hassani.S
local notation "J" => Myproj.Hassani.J
local notation "A" => Myproj.Hassani.A
local notation "G" => Myproj.Hassani.G

/-- Convenience sequence `c_{n+1}`. -/
def cSeq (n : ℕ) : ℝ := c (n + 1)

lemma cSeq_pos (n : ℕ) : 0 < cSeq n := by
  have hge : ((n + 1 : ℕ) : ℝ) ≤ c (n + 1) :=
    Myproj.cyclicEnumerator_ge_self (n + 1)
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  exact lt_of_lt_of_le hpos hge

lemma G_pos_succ (n : ℕ) : 0 < G (n + 1) := by
  simpa [Nat.succ_eq_add_one] using cyclicGeomMean_pos (n := n + 1)

@[simp] lemma C_eval (n : ℕ) : C (cSeq n) = ((n + 1 : ℕ) : ℝ) := by
  simpa [cSeq, Nat.succ_eq_add_one] using
    Myproj.cyclicCountingReal_enumerator_eq (n := n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))

lemma A_eval (n : ℕ) : A (n + 1) = S (cSeq n) / ((n + 1 : ℕ) : ℝ) := by
  simpa [cSeq, Nat.succ_eq_add_one] using
    A_eval_enumerator (n := n + 1) (Nat.succ_le_succ (Nat.zero_le n))

lemma A_over_c_formula (n : ℕ) :
    A (n + 1) / cSeq n = S (cSeq n) / (cSeq n * C (cSeq n)) := by
  have hA := A_eval n
  have hS :
      S (cSeq n) =
        (Finset.range (n + 1)).sum (fun k => c (k.succ)) := by
    simpa [cSeq, Nat.succ_eq_add_one] using
      S_eval_enumerator (n := n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))
  have hc : cSeq n ≠ 0 := (cSeq_pos n).ne'
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  calc
    A (n + 1) / cSeq n
        = (S (cSeq n) / ((n + 1 : ℕ) : ℝ)) / cSeq n := by
          simpa [hA, hS]
    _ = S (cSeq n) / (((n + 1 : ℕ) : ℝ) * cSeq n) := by
          field_simp [hc, hn]
    _ = S (cSeq n) / (cSeq n * ((n + 1 : ℕ) : ℝ)) := by simp [mul_comm]
    _ = S (cSeq n) / (cSeq n * C (cSeq n)) := by simpa [C_eval n, mul_comm]

lemma tendsto_cSeq : Tendsto cSeq atTop atTop := by
  simpa [cSeq, Nat.succ_eq_add_one] using cyclicEnumerator_succ_tendsto

lemma tendsto_S_ratio :
    Tendsto (fun n : ℕ => S (cSeq n) / (cSeq n * C (cSeq n))) atTop
      (𝓝 (1 / 2 : ℝ)) := by
  simpa [cSeq, Nat.succ_eq_add_one] using
    S_over_xC_tendsto_half.comp tendsto_cSeq

lemma tendsto_A_over_c :
    Tendsto (fun n : ℕ => A (n + 1) / cSeq n) atTop (𝓝 (1 / 2 : ℝ)) :=
  by simpa [A_over_c_formula] using tendsto_S_ratio

lemma tendsto_log_ratio :
    Tendsto (fun n : ℕ => Real.log (cSeq n / G (n + 1))) atTop (𝓝 1) := by
  have h := J_over_C_sub_log_tendsto_zero.comp tendsto_cSeq
  have hratio :
      Tendsto (fun n : ℕ =>
          Real.log (cSeq n) - J (cSeq n) / C (cSeq n)) atTop (𝓝 1) := by
    have hconst :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have hdiff := hconst.sub h
    have hf :
        (fun n : ℕ => Real.log (cSeq n) - J (cSeq n) / C (cSeq n)) =
          fun n : ℕ =>
            (1 : ℝ) - (J (cSeq n) / C (cSeq n)
                - (Real.log (cSeq n) - 1)) := by
      funext n; ring
    simpa [hf, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiff
  have hpos₁ : ∀ n, 0 < cSeq n := cSeq_pos
  have hpos₂ : ∀ n, 0 < G (n + 1) := G_pos_succ
  have hlog_div :
      (fun n : ℕ => Real.log (cSeq n) - J (cSeq n) / C (cSeq n))
        = fun n : ℕ => Real.log (cSeq n / G (n + 1)) := by
    funext n
    have hG := log_G_eval_enumerator (n := n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))
    have hC := C_eval n
    calc
      Real.log (cSeq n) - J (cSeq n) / C (cSeq n)
          = Real.log (cSeq n) - J (cSeq n) / ((n + 1 : ℕ) : ℝ) :=
                by simpa [hC]
      _ = Real.log (cSeq n) - Real.log (G (n + 1)) :=
                by simpa [cSeq, Nat.succ_eq_add_one, sub_eq_add_neg]
                  using hG.symm
      _ = Real.log (cSeq n / G (n + 1)) := by
                simpa [sub_eq_add_neg] using
                  (Real.log_div (ne_of_gt (hpos₁ n)) (ne_of_gt (hpos₂ n))).symm
  have hratio' : Tendsto (fun n : ℕ => Real.log (cSeq n / G (n + 1))) atTop (𝓝 1) := by
    convert hratio using 1
    funext n
    have := congrArg (fun f : ℕ → ℝ => f n) hlog_div
    simpa using this.symm
  exact hratio'

lemma tendsto_ratio :
    Tendsto (fun n : ℕ => cSeq n / G (n + 1)) atTop (𝓝 (Real.exp 1)) := by
  have hpos : ∀ n : ℕ, 0 < cSeq n / G (n + 1) := fun n =>
    div_pos (cSeq_pos n) (G_pos_succ n)
  have h := tendsto_log_ratio.rexp
  have hf :
      (fun n : ℕ => Real.exp (Real.log (cSeq n / G (n + 1)))) =
        fun n : ℕ => cSeq n / G (n + 1) := by
    funext n
    simpa using Real.exp_log (hpos n)
  refine h.congr' ?_
  exact hf.eventuallyEq

lemma hassani_limit_succ :
    Tendsto (fun n : ℕ => A (n + 1) / G (n + 1)) atTop (𝓝 (Real.exp 1 / 2)) := by
  have hA := tendsto_A_over_c
  have hG := tendsto_ratio
  have hprod : Tendsto (fun n : ℕ =>
      (A (n + 1) / cSeq n) * (cSeq n / G (n + 1))) atTop
        (𝓝 ((1 / 2 : ℝ) * Real.exp 1)) := Tendsto.mul hA hG
  have hfactor :
      (fun n : ℕ =>
        (A (n + 1) / cSeq n) * (cSeq n / G (n + 1))) =
        fun n : ℕ => A (n + 1) / G (n + 1) := by
    funext n
    have hc : cSeq n ≠ 0 := (cSeq_pos n).ne'
    have hG0 : G (n + 1) ≠ 0 := (G_pos_succ n).ne'
    field_simp [div_eq_mul_inv, hc, hG0, mul_comm, mul_left_comm, mul_assoc]
  have hlimit : Tendsto (fun n : ℕ => A (n + 1) / G (n + 1)) atTop
      (𝓝 ((1 / 2 : ℝ) * Real.exp 1)) := by
    convert hprod using 1
    funext n
    have := congrArg (fun f : ℕ → ℝ => f n) hfactor
    simpa using this.symm
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlimit

/-- Hassani analog: `A_n / G_n → e / 2`. -/
theorem hassani_limit :
    Tendsto (fun n : ℕ => A (n + 1) / G (n + 1)) atTop (𝓝 (Real.exp 1 / 2)) :=
  hassani_limit_succ

end Hassani
end Myproj
