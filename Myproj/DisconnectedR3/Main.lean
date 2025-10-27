import Myproj.DisconnectedR3.Axioms

/-
Main theorem: for every positive constant `c₀` there are infinitely many `d`-regular expanders
with adjacency spectral gap at least `c₀` whose `R₃(G)` graph is disconnected.
-/

noncomputable section

namespace Myproj
namespace DisconnectedR3

open scoped Classical
open Filter

/-!
### Infinite family of counterexamples
-/

private lemma counterexample_eventually
    {c0 : ℝ} (data : CounterexampleData c0) :
    ∃ d : ℕ, ∃ N₁ : ℕ,
      ∀ {N : ℕ}, N₁ ≤ N →
        (data.witnesses N).base.degree = d ∧
        (data.witnesses N).base.vertexCount = 6 * N ∧
        c0 ≤ (data.witnesses N).base.spectralGap ∧
        ¬ (data.witnesses N).r3Connected := by
  refine ⟨2 * data.mPrime + 2, ?_⟩
  have hDegree :
      ∀ᶠ N : ℕ in atTop,
        (data.witnesses N).base.degree = 2 * data.mPrime + 2 :=
    Filter.Eventually.of_forall data.degree_eq
  have hCount :
      ∀ᶠ N : ℕ in atTop,
        (data.witnesses N).base.vertexCount = 6 * N :=
    Filter.Eventually.of_forall data.vertexCount_eq
  have hGap :
      ∀ᶠ N : ℕ in atTop,
        c0 ≤ (data.witnesses N).base.spectralGap :=
    data.spectralGap_bound
  have hDisc :
      ∀ᶠ N : ℕ in atTop,
        ¬ (data.witnesses N).r3Connected :=
    Filter.Eventually.of_forall fun N =>
      r3_not_connected_of_isolated (data.isolated_pair N)
  have hAll :
      ∀ᶠ N : ℕ in atTop,
        (data.witnesses N).base.degree = 2 * data.mPrime + 2 ∧
        (data.witnesses N).base.vertexCount = 6 * N ∧
        c0 ≤ (data.witnesses N).base.spectralGap ∧
        ¬ (data.witnesses N).r3Connected :=
    (hDegree.and (hCount.and (hGap.and hDisc))).mono
      (by
        intro N h
        rcases h with ⟨hdeg, hrest⟩
        rcases hrest with ⟨hcount, hgap, hdisc⟩
        exact ⟨hdeg, hcount, hgap, hdisc⟩)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hAll
  refine ⟨N₁, ?_⟩
  intro N hle
  exact hN₁ N hle

theorem infinitely_many_disconnected
    {c0 : ℝ} (hc0 : 0 < c0) :
    ∃ d : ℕ,
      ∀ᶠ N : ℕ in atTop,
        ((counterexample_family_exists hc0).witnesses N).base.degree = d ∧
        ((counterexample_family_exists hc0).witnesses N).base.vertexCount = 6 * N ∧
        c0 ≤ ((counterexample_family_exists hc0).witnesses N).base.spectralGap ∧
        ¬ ((counterexample_family_exists hc0).witnesses N).r3Connected := by
  let data := counterexample_family_exists hc0
  obtain ⟨d, N₁, hN₁⟩ := counterexample_eventually data
  refine ⟨d, ?_⟩
  refine Filter.eventually_atTop.2 ?_
  refine ⟨N₁, ?_⟩
  intro N hle
  have h := hN₁ hle
  rcases h with ⟨hdeg, hcount, hgap, hdisc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [data] using hdeg
  · simpa [data] using hcount
  · simpa [data] using hgap
  · simpa [data] using hdisc

/-- Reformulation of the main statement: there is no universal spectral-gap threshold
forcing `R₃(G)` to be connected for all sufficiently large regular expanders. -/
theorem no_universal_constant :
    ¬ ∃ (c0 : ℝ) (_ : 0 < c0),
        ∀ d : ℕ, ∃ N0 : ℕ,
          ∀ ⦃W : Witness⦄,
            W.base.degree = d →
            c0 ≤ W.base.spectralGap →
            N0 ≤ W.base.vertexCount →
            W.r3Connected := by
  classical
  intro h
  rcases h with ⟨c0, hc0, hAll⟩
  let data := counterexample_family_exists hc0
  obtain ⟨d', N1, hN1⟩ := counterexample_eventually data
  obtain ⟨N0, hN0⟩ := hAll d'
  let N := max N0 N1
  have hProp := hN1 (N := N) (le_max_right _ _)
  rcases hProp with ⟨hdeg, hcount, hgap, hdisc⟩
  have hLarge :
      N0 ≤ (data.witnesses N).base.vertexCount := by
    have hN0_le : N0 ≤ N := le_max_left _ _
    have hN_le : N ≤ 6 * N := by
      have h16 : 1 ≤ 6 := by decide
      simpa [Nat.one_mul] using (Nat.mul_le_mul_right N h16)
    have hN0_le_6N : N0 ≤ 6 * N := le_trans hN0_le hN_le
    simpa [hcount] using hN0_le_6N
  have hConn :=
    hN0 (W := data.witnesses N)
      (by simpa [hdeg]) hgap hLarge
  exact hdisc hConn

end DisconnectedR3
end Myproj
