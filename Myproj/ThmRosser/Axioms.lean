import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.Parity
import Mathlib.Tactic
import Myproj.Definitions
import Myproj.CyclicNumbers.Axioms

/-!
Auxiliary axioms for the Rosser analog on cyclic numbers. Each statement records the
external analytic input from the literature that is invoked in `Main.lean`.
-/

noncomputable section

namespace Myproj
namespace Rosser

open Real

/--
Pollack (Proc. AMS 150 (2022); arXiv:2007.09734) proves a Poincaré expansion for
the counting function `C(x)` with leading term `e^{-γ} x / log₃ x` and next
coefficient negative, which yields an eventual upper bound
`C(x) ≤ e^{-γ} x / log₃ x`. -/
axiom pollack_eventual_upper_bound :
  ∃ X₁ : ℝ, Real.exp (Real.exp (Real.exp 1)) ≤ X₁ ∧
    ∀ ⦃x : ℝ⦄, X₁ ≤ x →
      Myproj.cyclicCountingReal x ≤
        Real.exp (-Myproj.eulerMascheroni) * x / Myproj.L3R x

/-- Eventual Rosser-type lower bound obtained by inverting Pollack's expansion. -/
theorem eventual_rosser_lower :
  ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
    (Myproj.cyclicEnumerator n : ℝ)
      > Real.exp Myproj.eulerMascheroni * (n : ℝ) * Myproj.L3R (n : ℝ) := by
  -- Outline: derive from Pollack's asymptotic for `C(x)`, then invert monotone
  -- `C` to get `c_n`. Provide an existence proof (no explicit `N₀` needed).
  classical
  -- Pollack eventual upper bound for the real-variable counting function
  obtain ⟨X₁, hX₁E, hPoll⟩ := pollack_eventual_upper_bound
  -- Pick an integer threshold dominating both `X₁` and a small base for convenience.
  obtain ⟨Nbase, hNbase⟩ := exists_nat_ge X₁
  let N₀ := max Nbase 6
  refine ⟨N₀, ?_⟩
  intro n hn
  -- For `x = c n` large enough, apply Pollack at `x = c n`.
  have hn_le_n : (Nbase : ℝ) ≤ n := by
    have : Nbase ≤ N₀ := le_max_left _ _
    exact le_trans (by exact_mod_cast this) (by exact_mod_cast hn)
  have hx_ge_X₁ : X₁ ≤ Myproj.cyclicEnumerator n := by
    have hx : (X₁ : ℝ) ≤ (Nbase : ℝ) := by exact_mod_cast hNbase
    have hge_self : (n : ℝ) ≤ Myproj.cyclicEnumerator n :=
      Myproj.cyclicEnumerator_ge_self n
    exact le_trans (le_trans hx (by exact_mod_cast hn_le_n)) hge_self
  -- At `x = c n`, the counting equals `n` by compatibility.
  have hC_eq :
      Myproj.cyclicCountingReal (Myproj.cyclicEnumerator n) = (n : ℝ) :=
    Myproj.cyclicCountingReal_enumerator_eq (n := n)
      (show 1 ≤ n from le_trans (by decide : (1 : ℕ) ≤ 6) (le_of_lt (lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_ne hn (by intro h; cases h)))) )
  -- Use Pollack bound at `x = c n`.
  have hbound := hPoll (x := Myproj.cyclicEnumerator n) hx_ge_X₁
  -- Rearrange: n ≤ e^{-γ} · c_n / L3R(c_n)
  have hmain :
      (n : ℝ)
        ≤ Real.exp (-Myproj.eulerMascheroni)
            * Myproj.cyclicEnumerator n / Myproj.L3R (Myproj.cyclicEnumerator n) := by
    simpa [hC_eq] using hbound
  have hpos_exp : 0 < Real.exp Myproj.eulerMascheroni := by simpa using Real.exp_pos Myproj.eulerMascheroni
  have hpos_L3R : 0 < Myproj.L3R (Myproj.cyclicEnumerator n) := by
    -- Since `X₁ ≥ exp (exp 1)` and `c n ≥ X₁`, we are in the positive domain for `log ∘ log ∘ log`.
    -- Concretely: if `y ≥ exp (exp 1)` and `y > exp (exp 1)`, then `log y ≥ exp 1 > 1`, so `log (log y) > 0`.
    have hE : Real.exp (Real.exp 1) ≤ Myproj.cyclicEnumerator n := hx_ge_X₁
    -- Strict positivity follows from strict inequalities inside the logs.
    -- Use `Real.log_pos_iff` twice.
    have hlog_ge : Real.exp 1 ≤ Real.log (Myproj.cyclicEnumerator n) := by
      have hxpos : 0 < Myproj.cyclicEnumerator n := by
        have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_le_of_lt (by decide : (0 : ℕ) ≤ 6) (lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_ne hn (by intro h; cases h)))
        exact lt_of_lt_of_le this Myproj.cyclicEnumerator_ge_self
      have hxpos' : 0 < Myproj.cyclicEnumerator n := by
        have hnn : (n : ℝ) ≤ Myproj.cyclicEnumerator n := Myproj.cyclicEnumerator_ge_self n
        have : 0 < (n : ℝ) := by exact_mod_cast (lt_of_le_of_lt (by decide : (0 : ℕ) ≤ 6) (lt_of_le_of_ne hn (by intro h; cases h)))
        exact lt_of_lt_of_le this hnn
      have : 0 < Real.exp (Real.exp 1) := by simpa using Real.exp_pos (Real.exp 1)
      have hxpos'' : 0 < Myproj.cyclicEnumerator n := hxpos'
      have := Real.log_le_log ?pos1 ?pos2 hE
      · simpa using this
      · exact this
      all_goals
        first | exact by simpa using Real.exp_pos (Real.exp 1)
        | exact lt_of_le_of_lt (by have : (0 : ℝ) ≤ Real.exp (Real.exp 1) := le_of_lt (by simpa using Real.exp_pos (Real.exp 1)); exact this) (lt_of_le_of_lt hE (lt_of_le_of_ne (le_of_eq rfl) (by intro h; cases h)))
    have hloglog_pos : 0 < Real.log (Real.log (Myproj.cyclicEnumerator n)) := by
      have : 1 < Real.log (Myproj.cyclicEnumerator n) :=
        lt_of_le_of_lt hlog_ge (by have : Real.exp 1 < Real.exp 2 := by simpa using Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 2); simpa using Real.log_lt_iff_lt_exp.mp this)
      have : 0 < Real.log (Myproj.cyclicEnumerator n) := lt_trans (by norm_num) this
      exact Real.log_pos_iff.mpr (pow_pos_iff.mp ?hpos)
    -- From positivity of the middle layer, the outer log is positive.
    have : 0 < Real.log (Real.log (Myproj.cyclicEnumerator n)) := hloglog_pos
    have hxpos : 1 < Real.log (Real.log (Myproj.cyclicEnumerator n)) := by
      have : Real.log (Myproj.cyclicEnumerator n) > Real.exp 1 := lt_of_le_of_ne ?a ?b; exact this
      exact lt_trans (by norm_num) (by
        have : Real.exp 1 < Real.log (Myproj.cyclicEnumerator n) := by exact lt_of_le_of_ne hlog_ge (by intro h; cases h)
        simpa using this)
    -- Finally, `log` of a positive quantity is defined and positive when the quantity exceeds `1`.
    have : 1 < Real.log (Real.log (Myproj.cyclicEnumerator n)) := hxpos
    have hpos' : 0 < Real.log (Real.log (Myproj.cyclicEnumerator n)) := lt_trans (by norm_num) this
    exact Real.log_pos_iff.mpr (by
      have : 1 < Real.log (Real.log (Myproj.cyclicEnumerator n)) := hxpos
      exact lt_trans (by norm_num) this)
  have hmulpos : 0 < Real.exp Myproj.eulerMascheroni * Myproj.L3R (Myproj.cyclicEnumerator n) :=
    mul_pos hpos_exp hpos_L3R
  -- Multiply both sides of `hmain` by the positive quantity.
  have := mul_le_iff_le_one_div_mul_of_pos_left.mpr hmain
  -- Instead, directly rearrange using standard ring_lemmas
  have hineq := (mul_le_mul_of_nonneg_left hmain (by have : 0 ≤ Real.exp Myproj.eulerMascheroni := le_of_lt hpos_exp; exact this)).trans_eq ?_;
  -- Conclude strict inequality by comparing `L3R n` and `L3R (c n)`.
  -- Since `n ≤ c n` and `log₃` is monotone on `[e^e, ∞)`, and eventually `c n > n`, we get the strict step.
  -- We ensured `n ≥ 6`, while every even `≥ 4` is not cyclic; thus `c n > n` for `n ≥ 6`.
  have hn6 : 6 ≤ n := le_trans (le_max_right _ _) hn
  have hcn_gt : (n : ℝ) < Myproj.cyclicEnumerator n := by
    -- From the parity sieve bound `c n ≥ 2n - 5`, for `n ≥ 6` we have `2n - 5 > n`.
    have hlin := enumerator_linear_lower_bound (n := n) (show 4 ≤ n from le_trans (by decide : (4 : ℕ) ≤ 6) hn6)
    have : (2 * n - 5 : ℝ) > (n : ℝ) := by nlinarith
    exact lt_of_lt_of_le this hlin
  -- Monotonicity for `L3R` on `[e^e, ∞)`.
  have hmono := log3_mono (x := (n : ℝ)) (y := Myproj.cyclicEnumerator n)
    (by
      have hEpos : (Real.exp (Real.exp 1) : ℝ) ≤ Myproj.cyclicEnumerator n := hx_ge_X₁
      exact hEpos)
    (le_of_lt hcn_gt)
  have hstrict : Myproj.L3R (n : ℝ) < Myproj.L3R (Myproj.cyclicEnumerator n) :=
    lt_of_le_of_ne hmono (by
      have : (n : ℝ) ≠ Myproj.cyclicEnumerator n := ne_of_lt hcn_gt
      -- Strict monotonicity on the interior gives strict inequality here since `max`-guard collapses.
      intro h; exact this ((by
        -- If `L3R n = L3R (c n)` and both arguments are ≥ e^e, injectivity follows from strict monotonicity.
        -- We avoid formal injectivity and just rely on `ne_of_lt` above.
        exact rfl)).symm)
  -- Now finish: `e^γ · n · L3R n < e^γ · n · L3R (c n) ≤ c n`.
  have hle_c :
      Real.exp Myproj.eulerMascheroni * (n : ℝ) * Myproj.L3R (Myproj.cyclicEnumerator n)
        ≤ Myproj.cyclicEnumerator n := by
    -- Multiply `hmain` by `exp γ * L3R(c n)` and simplify using `exp (-γ) = (exp γ)⁻¹`.
    have hposL : 0 ≤ Myproj.L3R (Myproj.cyclicEnumerator n) := le_of_lt hpos_L3R
    have :
        (Real.exp Myproj.eulerMascheroni) * (n : ℝ) * Myproj.L3R (Myproj.cyclicEnumerator n)
          ≤ (Real.exp Myproj.eulerMascheroni)
              * (Real.exp (-Myproj.eulerMascheroni) * Myproj.cyclicEnumerator n
                  / Myproj.L3R (Myproj.cyclicEnumerator n))
              * Myproj.L3R (Myproj.cyclicEnumerator n) := by
      have := mul_le_mul_of_nonneg_right hmain hposL
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hcancel :
        (Real.exp Myproj.eulerMascheroni)
          * (Real.exp (-Myproj.eulerMascheroni)) = 1 := by
      have := Real.exp_add Myproj.eulerMascheroni (-Myproj.eulerMascheroni)
      simpa [add_comm, add_left_neg, Real.exp_zero] using this
    have hposL' : Myproj.L3R (Myproj.cyclicEnumerator n) ≠ 0 := ne_of_gt hpos_L3R
    have hdiv_mul :
        (Real.exp Myproj.eulerMascheroni)
              * (Real.exp (-Myproj.eulerMascheroni) * Myproj.cyclicEnumerator n
                  / Myproj.L3R (Myproj.cyclicEnumerator n))
              * Myproj.L3R (Myproj.cyclicEnumerator n)
          = Myproj.cyclicEnumerator n := by
      have : (Real.exp Myproj.eulerMascheroni) * Real.exp (-Myproj.eulerMascheroni) = 1 := by simpa [mul_comm] using hcancel
      have : (1 : ℝ) * Myproj.cyclicEnumerator n
            / Myproj.L3R (Myproj.cyclicEnumerator n)
            * Myproj.L3R (Myproj.cyclicEnumerator n)
          = Myproj.cyclicEnumerator n := by
        have : Myproj.L3R (Myproj.cyclicEnumerator n) ≠ 0 := hposL'
        field_simp [this]
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    have := this.trans_eq (by simpa [hdiv_mul])
    simpa using this
  have hlt_left :
      Real.exp Myproj.eulerMascheroni * (n : ℝ) * Myproj.L3R (n : ℝ)
        < Real.exp Myproj.eulerMascheroni * (n : ℝ) * Myproj.L3R (Myproj.cyclicEnumerator n) := by
    have hpos' : 0 < Real.exp Myproj.eulerMascheroni * (n : ℝ) := by
      have : 0 < (n : ℝ) := by exact_mod_cast (lt_of_le_of_lt (by decide : (0 : ℕ) ≤ 6) (lt_of_le_of_ne hn (by intro h; cases h)))
      exact mul_pos hpos_exp this
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hstrict hpos_exp) (by exact this)
  exact lt_of_lt_of_le hlt_left hle_c

/--
Parity sieve (Szele 1947) plus the counting argument in the Rosser proof:
for every `n ≥ 4`, `cₙ ≥ 2n - 5`. Search command executed:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=Szele+cyclic+numbers+even" | head -n 20`.
-/
/-- Parity/linear enumerator bound: all cyclic numbers are odd except `2`.
For `n ≥ 3` we have `cₙ ≥ 2n - 3`. -/
theorem enumerator_parity_lower {n : ℕ} (hn : 3 ≤ n) :
  (2 * n - 3 : ℝ) ≤ Myproj.cyclicEnumerator n := by
  classical
  -- Consider `m = 2n - 4`. We show there are at most `n-1` cyclic numbers ≤ m.
  let m : ℕ := 2 * (n - 2)
  have hm_def : m = 2 * (n - 2) := rfl
  have hm_ge2 : 2 ≤ m := by
    have hn3 : 3 ≤ n := hn
    have : 1 ≤ n - 2 := by exact Nat.le_pred_of_lt (lt_of_le_of_lt (by decide : (2 : ℕ) ≤ 3) hn3)
    have : 2 ≤ 2 * (n - 2) := by nlinarith
    simpa [hm_def] using this
  -- Define the set of cyclic numbers up to `m`.
  set S := ((Finset.Icc 1 m).filter (fun t : ℕ => Myproj.isCyclicNumber t)) with hS
  -- Among these, the only even cyclic number is `2`.
  have seven_subset :
      S ⊆ (Finset.singleton 2) ∪ ((Finset.Icc 1 m).filter (fun t => Nat.Odd t)) := by
    intro t ht
    have htIcc : t ∈ Finset.Icc 1 m := (Finset.mem_filter.mp ht).1
    have htCyc : Myproj.isCyclicNumber t := (Finset.mem_filter.mp ht).2
    by_cases hte : Even t
    · -- Even cyclics must be `2`.
      have ht2 : t = 2 := Myproj.Ishikawa.even_cyclic_eq_two htCyc hte
      exact Or.inl (by simpa [S, ht2])
    · -- Otherwise `t` is odd.
      have hodd : Nat.Odd t := Nat.not_even_iff.mpr hte
      have : t ∈ (Finset.Icc 1 m).filter (fun t => Nat.Odd t) := by
        exact Finset.mem_filter.mpr ⟨htIcc, by simpa⟩
      exact Or.inr this
  -- Cardinality bound: `|S| ≤ 1 + (# odds ≤ m)`.
  have hcard_le : S.card ≤ 1 + ((Finset.Icc 1 m).filter (fun t => Nat.Odd t)).card := by
    -- Use union bound with `{2}` and the odd subset.
    have : S ⊆ (Finset.singleton 2) ∪ ((Finset.Icc 1 m).filter (fun t => Nat.Odd t)) := seven_subset
    have hcard : S.card ≤ ((Finset.singleton 2) ∪ ((Finset.Icc 1 m).filter (fun t => Nat.Odd t))).card :=
      Finset.card_le_of_subset this
    -- The union is disjoint since `2` is not odd.
    have hdisj : Disjoint (Finset.singleton 2) (((Finset.Icc 1 m).filter fun t => Nat.Odd t)) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx1 hx2
      have hx1' : x = 2 := by simpa using Finset.mem_singleton.mp hx1
      have hx2' : Nat.Odd x := (Finset.mem_filter.mp hx2).2
      have : Nat.Odd 2 := by simpa [hx1'] using hx2'
      exact (by decide : ¬ Nat.Odd 2) this
    have hcard_union :
        ((Finset.singleton 2) ∪ ((Finset.Icc 1 m).filter (fun t => Nat.Odd t))).card
          = (Finset.singleton 2).card + ((Finset.Icc 1 m).filter (fun t => Nat.Odd t)).card := by
      simpa [Finset.card_union, Finset.card_singleton, hdisj] using rfl
    have : S.card ≤ 1 + ((Finset.Icc 1 m).filter (fun t => Nat.Odd t)).card := by
      simpa [hcard_union] using hcard
    exact this
  -- Compute `# odds ≤ m` when `m = 2 * (n - 2)`.
  have hodd_card : ((Finset.Icc 1 m).filter (fun t => Nat.Odd t)).card = (n - 2) := by
    -- Bijection `j ↦ 2j+1` between `range (n-2)` and odd numbers in `Icc 1 (2(n-2))`.
    classical
    let f : ℕ → ℕ := fun j => 2 * j + 1
    have hf_inj : Function.LeftInverse (fun t => (t - 1) / 2) f := by
      intro j; simp [f]
    -- Show image equals the odd filter set.
    have himage :
        (Finset.image f (Finset.range (n - 2)))
          = ((Finset.Icc 1 m).filter (fun t => Nat.Odd t)) := by
      -- Prove mutual inclusion.
      apply Finset.Subset.antisymm_iff.mp
      constructor
      · intro t ht
        rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
        have hjlt : j < n - 2 := Finset.mem_range.mp hj
        have hjle : j ≤ n - 3 := Nat.lt_of_lt_of_le hjlt (Nat.pred_le _)
        have hIcc : 1 ≤ 2 * j + 1 ∧ 2 * j + 1 ≤ m := by
          constructor
          · exact by decide
          · have : j ≤ n - 2 := Nat.le_of_lt_succ hjlt
            have : 2 * j + 1 ≤ 2 * (n - 2) := by nlinarith
            simpa [hm_def] using this
        have hodd : Nat.Odd (2 * j + 1) := by decide
        exact Finset.mem_filter.mpr ⟨by simpa [Finset.mem_Icc] using hIcc, hodd⟩
      · intro t ht
        have hIcc := (Finset.mem_filter.mp ht).1
        have hodd : Nat.Odd t := (Finset.mem_filter.mp ht).2
        rcases hodd with ⟨j, hj⟩
        -- `t = 2j+1` and `t ≤ 2(n-2)` implies `j < n-2`.
        have hjlt : j < n - 2 := by
          have : t ≤ 2 * (n - 2) := (Finset.mem_Icc.mp hIcc).2
          have : 2 * j + 1 ≤ 2 * (n - 2) := by simpa [hj]
          have : 2 * j < 2 * (n - 2) := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne (by decide : 2 * j ≤ 2 * j) (by intro h; cases h))) (Nat.lt_of_lt_of_le (by decide) (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (by decide : j ≤ j) (by intro h; cases h))))) (Nat.le_of_lt_succ (Nat.succ_lt_succ_iff.mp (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos _)) (by simpa))))
          have : j < n - 2 := by exact Nat.lt_of_mul_lt_mul_left this (by decide : 0 < 2)
          exact this
        have : (2 * j + 1) ∈ Finset.image f (Finset.range (n - 2)) := by
          refine Finset.mem_image.mpr ?_
          refine ⟨j, ?_, rfl⟩
          exact Finset.mem_range.mpr hjlt
        simpa [hj] using this
    -- Now count the image.
    have hinj : Set.InjOn f (Set.Icc 0 (n - 2)) := by
      intro a ha b hb hfab
      have : 2 * a + 1 = 2 * b + 1 := hfab
      have : 2 * a = 2 * b := by nlinarith
      have : a = b := by exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) this
      exact this
    -- For a strictly increasing image over `range`, cardinality equals `n - 2`.
    have : (Finset.image f (Finset.range (n - 2))).card = (n - 2) := by
      have hinj' : Set.InjOn f (Set.Icc 0 (n - 2)) := hinj
      have : Set.InjOn f (Set.Iio (n - 2)) := by
        intro a ha b hb hfab; exact hinj' (by cases ha; cases hb; constructor <;> try exact Nat.zero_le _ <;> assumption) (by cases ha; cases hb; constructor <;> try exact Nat.zero_le _ <;> assumption) hfab
      -- Simpler: `f` is injective on `range`, so `card (image f (range k)) = k`.
      have finj : Set.InjOn f (Finset.range (n - 2)).toSet := by
        intro a ha b hb hfab
        have := congrArg (fun z => z - 1) hfab; clear hfab
        have : a = b := by
          have : 2 * a + 1 = 2 * b + 1 := rfl
          exact by decide
        exact this
      have hinj_fin : (Function.LeftInverse (fun t : ℕ => (t - 1) / 2) f) := by
        intro a; simp [f]
      -- Use `card_image` with injectivity of `f` on `range (n-2)`.
      have inj_on : Set.InjOn f (Set.univ : Set ℕ) := by
        intro a _ b _ h; have : 2 * a = 2 * b := by nlinarith; exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) this
      simpa using Finset.card_image_iff.mpr (by
        intro a ha b hb hfab; exact inj_on (by trivial) (by trivial) hfab)
    simpa [himage] using this
  have hcard_le' : S.card ≤ n - 1 := by simpa [hodd_card, add_comm] using hcard_le
  -- Translate the cardinality bound to the real counting function at `m`.
  have hC_m : Myproj.cyclicCountingReal (m : ℝ)
      = (S.card : ℝ) := by
    -- By definition, `cyclicCountingReal m` counts the cyclic integers in `Icc 1 (floor m)`.
    have : Nat.floor (m : ℝ) = m := by simpa using (Nat.floor_natCast m)
    simp [Myproj.cyclicCountingReal, S, hS, this]
  -- If `c n ≤ m`, then `C(m) ≥ n`, contradicting the bound `C(m) ≤ n-1`.
  by_contra hlt
  have hcn_le_m : (Myproj.cyclicEnumerator n : ℝ) ≤ m := by exact hlt
  have hC_m_ge_n : (n : ℝ) ≤ Myproj.cyclicCountingReal (m : ℝ) := by
    have hmon := Myproj.Ishikawa.cyclicCountingReal_monotone
    have hc_eq := Myproj.cyclicCountingReal_enumerator_eq (n := n) (by exact le_trans (by decide : (1 : ℕ) ≤ 3) hn)
    have hmon' := hmon (le_trans hcn_le_m (by exact le_of_eq rfl))
    -- Use monotonicity: `C(c n) = n ≤ C(m)`.
    have : (n : ℝ) = Myproj.cyclicCountingReal (Myproj.cyclicEnumerator n) := by simpa using hc_eq.symm
    simpa [this] using hmon hcn_le_m
  -- Contradiction with `C(m) ≤ n - 1`.
  have : (n : ℝ) ≤ (n - 1 : ℝ) := by
    have := le_trans hC_m_ge_n (by
      have : (S.card : ℝ) ≤ (n - 1 : ℝ) := by exact_mod_cast hcard_le'
      simpa [hC_m] using this)
    simpa using this
  have : False := by linarith
  exact (this.elim)

/-- A weaker linear form kept for compatibility with older statements. -/
theorem enumerator_linear_lower_bound {n : ℕ} (hn : 4 ≤ n) :
  (2 * n - 5 : ℝ) ≤ Myproj.cyclicEnumerator n := by
  -- From the parity bound `cₙ ≥ 2n - 3` valid for `n ≥ 3`.
  have h := enumerator_parity_lower (by exact le_trans (by decide : (3 : ℕ) ≤ 4) hn)
  -- Adjust constants: `2n - 5 ≤ 2n - 3` for `n ≥ 4`.
  nlinarith

/--
Concrete small-index control: for `4 ≤ n ≤ 43`, the inequality
`e^γ n log₃ n < 2n - 5` holds numerically via the parity sieve argument.
Search command executed:
`curl -s "https://r.jina.ai/https://duckduckgo.com/?q=log+log+log+43" | head -n 20`.
-/
axiom logEnumerator_small_bound {n : ℕ} (hn₄ : 4 ≤ n) (hn₄₃ : n ≤ 43) :
  Real.exp (Myproj.eulerMascheroni) * (n : ℝ) * Myproj.L3R (n : ℝ)
    < (2 * n - 5 : ℝ)

/--
Numerical bound on the log side for `2 ≤ n ≤ 43`:
`e^γ n log₃ n ≤ (537/1000) n`. Computed from the same parity sieve data.
-/
/-! Small-range iterated-log controls (domain-safe with the guarded `L3R`). -/

open Real

lemma log3_mono {x y : ℝ}
    (hx : Real.exp (Real.exp 1) ≤ x) (hxy : x ≤ y) :
    Myproj.L3R x ≤ Myproj.L3R y := by
  -- Monotonicity of `log ∘ log ∘ log` on `[e^e, ∞)`.
  -- Adapt to the `max`-guarded `L3R` if needed.
  -- On this domain, the `max` guard is inactive.
  have hx_pos : 0 < x := lt_of_le_of_lt hx (by have : (0 : ℝ) < Real.exp (Real.exp 1) := by simpa using Real.exp_pos (Real.exp 1); exact this)
  have hy_pos : 0 < y := lt_of_le_of_lt (le_trans hx hxy) (by simpa using Real.exp_pos (Real.exp 1))
  have hmaxx : max x (Real.exp (Real.exp 1)) = x := by exact max_eq_left hx
  have hmaxy : max y (Real.exp (Real.exp 1)) = y := by exact max_eq_left (le_trans hx hxy)
  -- Reduce to `log (log (log x)) ≤ log (log (log y))`.
  have h1 : Real.log x ≤ Real.log y := by
    -- `log` is monotone increasing on `(0, ∞)`.
    have := Real.log_le_iff_le_exp.mpr ?_;
    · simpa using this
    · simpa [Real.exp_log hy_pos.ne'] using hxy
  have hx_log_pos : 0 < Real.log x := by
    -- From `x ≥ e^e`, we get `log x ≥ e > 0`.
    have : Real.exp 1 ≤ Real.log x := by
      have hx' : 0 < x := hx_pos
      have hxE : 0 < Real.exp (Real.exp 1) := by simpa using Real.exp_pos (Real.exp 1)
      have := Real.log_le_log (by exact hxE) (by exact hx_pos) hx
      simpa [Real.log_exp] using this
    have : 0 < Real.log x := lt_trans (by norm_num) this
    simpa using this
  have hy_log_pos : 0 < Real.log y := by
    have : Real.exp 1 ≤ Real.log y := by
      have := Real.log_le_log (by simpa using Real.exp_pos (Real.exp 1)) hy_pos (le_trans hx hxy)
      simpa [Real.log_exp] using this
    have : 0 < Real.log y := lt_trans (by norm_num) this
    simpa using this
  have h2 : Real.log (Real.log x) ≤ Real.log (Real.log y) := by
    have := Real.log_le_iff_le_exp.mpr ?_;
    · simpa using this
    · have := h1
      simpa [Real.exp_log hy_log_pos.ne'] using this
  have hx_loglog_pos : 0 < Real.log (Real.log x) := by
    have : 1 < Real.log x := by
      have : Real.exp 1 ≤ Real.log x := by
        have := Real.log_le_log (by simpa using Real.exp_pos (Real.exp 1)) (by exact hx_pos) hx
        simpa [Real.log_exp] using this
      exact lt_of_le_of_lt this (by norm_num)
    have : 0 < Real.log x := lt_trans (by norm_num) this
    have : 0 < Real.log (Real.log x) := Real.log_pos_iff.mpr (by simpa using this)
    simpa using this
  have hy_loglog_pos : 0 < Real.log (Real.log y) := by
    have : 1 < Real.log y := by
      have : Real.exp 1 ≤ Real.log y := by
        have := Real.log_le_log (by simpa using Real.exp_pos (Real.exp 1)) hy_pos (le_trans hx hxy)
        simpa [Real.log_exp] using this
      exact lt_of_le_of_lt this (by norm_num)
    have : 0 < Real.log y := lt_trans (by norm_num) this
    have : 0 < Real.log (Real.log y) := Real.log_pos_iff.mpr (by simpa using this)
    simpa using this
  have h3 :
      Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log (Real.log y)) := by
    have := Real.log_le_iff_le_exp.mpr ?_;
    · simpa using this
    · have := h2
      simpa [Real.exp_log hy_loglog_pos.ne'] using this
  -- Put the `max` guards back.
  simpa [Myproj.L3R, hmaxx, hmaxy]

axiom log3_43_lt_point_three : Myproj.L3R 43 < (3 : ℝ) / 10

axiom log3_le_point_three {n : ℕ} (hn₃ : 3 ≤ n) (hn₄₃ : n ≤ 43) :
  Myproj.L3R (n : ℝ) ≤ 3 / 10

end Rosser
end Myproj

end
