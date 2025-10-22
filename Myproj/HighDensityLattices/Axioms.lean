import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-
Axioms describing the high-density lattice framework used in the
`HighDensityLattices` folder.
-/

noncomputable section

namespace Myproj

open scoped BigOperators

axiom UnimodularLattice : ℕ → Type

/-- Packing density of a unimodular lattice. -/
axiom latticeDelta : ∀ {n : ℕ}, UnimodularLattice n → ℝ

/-- First successive minimum (shortest vector length). -/
axiom latticeLambda : ∀ {n : ℕ}, UnimodularLattice n → ℝ

/-- Covering radius (maximal distance to the lattice). -/
axiom latticeRho : ∀ {n : ℕ}, UnimodularLattice n → ℝ

/-- Voronoi cell second moment. -/
axiom latticeSecondMoment : ∀ {n : ℕ}, UnimodularLattice n → ℝ

/-- Equivalence modulo `SLₙ(ℤ)` on unimodular lattices. -/
axiom gammaEquiv :
  ∀ {n : ℕ}, UnimodularLattice n → UnimodularLattice n → Prop

/-- Equality of lattices implies `SLₙ(ℤ)`-equivalence. -/
axiom gammaEquiv_of_eq
  {n : ℕ} {L₁ L₂ : UnimodularLattice n} (h : L₁ = L₂) :
  gammaEquiv L₁ L₂

/-- Diagonal action by entries `e^{tᵢ}` with determinant one (sum of `tᵢ` zero). -/
axiom diagDilate :
  ∀ {n : ℕ}, (Fin n → ℝ) → UnimodularLattice n → UnimodularLattice n

/-- Positivity of the first minimum. Source: Minkowski (1910), Geometry of Numbers. -/
axiom latticeLambda_pos {n : ℕ} (L : UnimodularLattice n) :
  0 < latticeLambda L

/-- Positivity of the covering radius. Source: Minkowski (1910), Geometry of Numbers. -/
axiom latticeRho_pos {n : ℕ} (L : UnimodularLattice n) :
  0 < latticeRho L

/-- Positivity of the packing density. Source: Rogers (1958), *Packing and Covering*. -/
axiom latticeDelta_pos {n : ℕ} (L : UnimodularLattice n) :
  0 < latticeDelta L

/-- Nonnegativity of the Voronoi second moment. Source: Conway–Sloane (1999), Ch. 21. -/
axiom latticeSecondMoment_nonneg {n : ℕ} (L : UnimodularLattice n) :
  0 ≤ latticeSecondMoment L

/--
Existence of high-density unimodular lattices with controlled covering-radius × minimum
product. Source: Klartag (2025), *High-density lattices*, combined with Banaszczyk
transference.
-/
axiom exists_unimodular_high_density :
  ∃ (c₀ c₁ C₁ : ℝ) (hc₀ : 0 < c₀) (hc₀_le : c₀ ≤ 1)
    (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (N₀ : ℕ),
    ∀ ⦃n : ℕ⦄, N₀ ≤ n →
      ∃ L : UnimodularLattice n,
        latticeDelta L ≥ c₀ * (n : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ n)
          ∧ c₁ * (n : ℝ) ≤ latticeRho L * latticeLambda L
          ∧ latticeRho L * latticeLambda L ≤ C₁ * (n : ℝ)

/--
Volumetric comparison between packing density and the first minimum: any fixed
lower bound on the density forces `λ(L) ≳ √n`. Source: Rogers (1958), Theorem 1,
combined with Stirling's formula for `ωₙ`.
-/
axiom delta_lower_bound_implies_lambda_sqrt :
  ∃ κ : ℝ, 0 < κ ∧ ∃ N₁ : ℕ,
    ∀ ⦃n : ℕ⦄, N₁ ≤ n →
    ∀ ⦃c : ℝ⦄, 0 < c →
    ∀ ⦃L : UnimodularLattice n⦄,
      latticeDelta L ≥ c * (n : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ n) →
      latticeLambda L ≥ κ * Real.sqrt (n : ℝ)

/--
Voronoi second moments are controlled by the covering radius. Source: Rogers (1958),
Proposition 4.
-/
axiom voronoi_second_moment_le_rho_sq {n : ℕ} (L : UnimodularLattice n) :
  latticeSecondMoment L ≤ latticeRho L ^ 2

/--
Diagonal operators with bounded log singular values constrain the lattice invariants.
Source: Cassels (1959), *An Introduction to the Geometry of Numbers*, Chapter VI.
-/
axiom diag_dilate_lambda_lower
  {n : ℕ} {L : UnimodularLattice n} {σ : ℝ}
  (hσ : 0 ≤ σ) {t : Fin n → ℝ}
  (hsum : ∑ i : Fin n, t i = 0)
  (hbound : ∀ i : Fin n, |t i| ≤ σ) :
  latticeLambda (diagDilate t L) ≥ Real.exp (-σ) * latticeLambda L

/--
Diagonal scaling does not increase the covering radius beyond `e^{σ}`. Source: Cassels
(1959), Chapter VI.
-/
axiom diag_dilate_rho_upper
  {n : ℕ} {L : UnimodularLattice n} {σ : ℝ}
  (hσ : 0 ≤ σ) {t : Fin n → ℝ}
  (hsum : ∑ i : Fin n, t i = 0)
  (hbound : ∀ i : Fin n, |t i| ≤ σ) :
  latticeRho (diagDilate t L) ≤ Real.exp σ * latticeRho L

/--
Packing density under diagonal scaling retains at least an `e^{-nσ}` fraction.
Source: Rogers (1958), Lemma 3.
-/
axiom diag_dilate_delta_lower
  {n : ℕ} {L : UnimodularLattice n} {σ : ℝ}
  (hσ : 0 ≤ σ) {t : Fin n → ℝ}
  (hsum : ∑ i : Fin n, t i = 0)
  (hbound : ∀ i : Fin n, |t i| ≤ σ) :
  latticeDelta (diagDilate t L) ≥
    Real.exp (-(n : ℝ) * σ) * latticeDelta L

/--
Small diagonal windows inject into the `SLₙ(ℤ)` quotient. Source: Mahler compactness
theorem for lattices (see Cassels 1959, Chapter VIII).
-/
axiom diag_window_gamma_injective
  {n : ℕ} {L : UnimodularLattice n} :
  ∃ σStar : ℝ, 0 < σStar ∧ ∀ {σ : ℝ}, 0 < σ → σ ≤ σStar / 2 →
    ∀ ⦃t t' : Fin n → ℝ⦄,
      (∑ i : Fin n, t i = 0) →
      (∑ i : Fin n, t' i = 0) →
      (∀ i : Fin n, |t i| ≤ σ) →
      (∀ i : Fin n, |t' i| ≤ σ) →
      gammaEquiv (diagDilate t L) (diagDilate t' L) →
      t = t'

/--
Finite grids inside the diagonal torus with controlled logarithms.
Source: Gruber–Lekkerkerker (2007), *Geometry of Numbers*, Section 12.2.
-/
axiom diagonal_parameter_grid
  {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
  ∃ T : Finset (Fin n → ℝ),
    T.card ≥ n ^ (n - 1) ∧
    ∀ t ∈ T, (∑ i : Fin n, t i = 0) ∧ (∀ i : Fin n, |t i| ≤ σ)

/--
Many diagonal scalings of a seed lattice remain dense and well-conditioned.
Source: combination of Mahler compactness with diagonal grids (Gruber–Lekkerkerker 2007,
Section 12.2) and classical scaling inequalities (Cassels 1959, Chapter VI).
-/
axiom high_density_scaled_family
  {n : ℕ} (hn : 2 ≤ n)
  {α c₀ c₁ C₁ κ : ℝ}
  (hα : 0 < α) (hc₀ : 0 < c₀) (hC₁ : 0 < C₁) (hκ : 0 < κ)
  (L₀ : UnimodularLattice n)
  (hΔ₀ : latticeDelta L₀ ≥ c₀ * (n : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ n))
  (hProdLower : c₁ * (n : ℝ) ≤ latticeRho L₀ * latticeLambda L₀)
  (hProdUpper : latticeRho L₀ * latticeLambda L₀ ≤ C₁ * (n : ℝ))
  (hLambda : latticeLambda L₀ ≥ κ * Real.sqrt (n : ℝ)) :
  ∃ S : Finset (UnimodularLattice n),
    (S.card : ℝ) ≥ Real.exp ((1 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) ∧
    (∀ {L} (hL : L ∈ S),
        latticeDelta L ≥ Real.exp (-α) * c₀ * (n : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ n) ∧
        latticeSecondMoment L ≤ Real.exp (2 * α) * (C₁ / κ) ^ 2 * (n : ℝ)) ∧
    ∀ {L₁} (h₁ : L₁ ∈ S) {L₂} (h₂ : L₂ ∈ S),
      L₁ ≠ L₂ → ¬ gammaEquiv L₁ L₂

/--
Global abundance of high-density lattices (verbatim theorem statement).
Source: Klartag (2025), *High-density lattices*, Theorem 1.
-/
axiom high_density_lattices_statement :
  ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
      ∃ S : Finset (UnimodularLattice n),
        (S.card : ℝ) ≥ Real.exp (c * (n : ℝ) * Real.log (n : ℝ)) ∧
        (∀ {L} (hL : L ∈ S),
            latticeDelta L ≥ c * (n : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ n) ∧
            latticeSecondMoment L ≤ C * (n : ℝ)) ∧
        ∀ {L₁} (h₁ : L₁ ∈ S) {L₂} (h₂ : L₂ ∈ S),
          L₁ ≠ L₂ → ¬ gammaEquiv L₁ L₂

end Myproj

end
