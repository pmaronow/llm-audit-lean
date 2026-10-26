import AronowAudit.P011.Wave1.CorollaryThreeBlueprint

/-!
# P011-T35: refutation of the package's generic OLS guarantee

The printed guarantee (package README line 3, vignette lines 100–105, formal paper
reading) asserts, for every
full-column-rank fixed design with a correctly specified mean model and `θ = olsTheta D j`,
that `V̂₁(A)` is `Conservative` and the printed interval has `PrintedConservativeCoverage`.
`Target` is the exact negation.

Witness for P011-T35: the T31 path family is itself a
correctly specified, full-rank OLS intercept problem. Rows `(1, μ_i)` with `μ` repeating
`(2,-4,2)`, coefficients `b = (0,1)`, `j = 0`: `DᵀD = diag(3K, 24K)`, the `n`-scaled intercept
weights are all `1 = θ_i`, and the T32 failure of conservativeness applies (T33's coverage
failure also holds but is not needed for the negated conjunction).

This statement concerns the formal V̂₁ reading only; it implies nothing about the vignette's
empirical standard errors, and the separate finite-n R-helper discrepancy is not involved.
-/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PackageOLS

open AronowAudit.P011 AronowAudit.P011.Wave1.PropositionOne AronowAudit.P011.Wave1.CorollaryOne
  MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Matrix

noncomputable section

/-- The fixed design at index `k`: rows `(1, μ_i)`, `μ = (2,-4,2)` repeated `k+1` times. -/
def olsDesign (k : ℕ) : Matrix (Fin (PF.size k)) (Fin 2) ℝ := fun i j =>
  if j = 0 then 1 else (![2, -4, 2] : Fin 3 → ℝ) (localIndex (by decide) i)

/-- True coefficients `b = (0,1)`: intercept zero (the target `β = 0`). -/
def olsCoef : Fin 2 → ℝ := ![0, 1]

/-! ## Target -/

/-- **Target (P011-T35).** Negation of the printed generic OLS guarantee. -/
def Target : Prop :=
  ¬ ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 → Valid F →
      ∀ (p : ℕ) (j : Fin p) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : Fin p → ℝ),
        (∀ k, ((D k)ᵀ * D k).det ≠ 0) → (∀ k, MeanModel (F.model k) (D k) b) →
        (∀ k i, (F.model k).theta i = olsTheta (D k) j i) →
        ∀ (A : ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)),
          (∀ k y, Maximizes (F.model k).R (F.model k).d
            (fun B => V1 B (weighted (F.model k) y)) (A k y)) →
          Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y)) ∧
            PrintedConservativeCoverage F (fun k y => V1 (A k y) (weighted (F.model k) y))

/-- Explicit OLS witness to the failure of the printed guarantee (P011-T35). -/
def Witness : Prop :=
  Scaling PF 6 2 (29 / 15) 2 ∧ Valid PF ∧ (∀ k, ((olsDesign k)ᵀ * olsDesign k).det ≠ 0) ∧
    (∀ k, MeanModel (PF.model k) (olsDesign k) olsCoef) ∧
    (∀ k i, (PF.model k).theta i = olsTheta (olsDesign k) (0 : Fin 2) i) ∧
    (∀ k y, Maximizes (PF.model k).R (PF.model k).d
      (fun B => V1 B (weighted (PF.model k) y)) (oracleChoice k y)) ∧
    ¬ (Conservative PF oracleV1 ∧ PrintedConservativeCoverage PF oracleV1)

/-! ## OLS design properties -/

/-- The design Gram matrix is `diag(3K,24K)`, where `K = k+1`. -/
def N1 : Prop :=
  ∀ k : ℕ, (olsDesign k)ᵀ * olsDesign k = Matrix.diagonal ![3 * ((k : ℝ) + 1), 24 * ((k : ℝ) + 1)]

/-- The path-family outcome law satisfies the mean model for `olsDesign`
and coefficients `(0,1)`. -/
def N2 : Prop := ∀ k : ℕ, MeanModel (PF.model k) (olsDesign k) olsCoef

/-- Under the Gram matrix identity `N1`, the OLS intercept weights equal
the path-family weights at every index and unit. -/
def N3 : Prop := N1 → ∀ (k : ℕ) (i : Fin (PF.size k)),
  (PF.model k).theta i = olsTheta (olsDesign k) (0 : Fin 2) i

/-! ## Refutation from the OLS witness -/

/-- Full column rank from the Gram matrix (N1). -/
theorem det_ne_zero_of (h1 : N1) (k : ℕ) : ((olsDesign k)ᵀ * olsDesign k).det ≠ 0 := by
  rw [h1 k, Matrix.det_diagonal, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  positivity

/-- The stated properties imply the explicit OLS witness. -/
theorem assemble_witness (p1 : PropositionOne.N1) (p2 : PropositionOne.N2)
    (p3 : PropositionOne.N3) (p4 : PropositionOne.N4) (p5 : PropositionOne.N5)
    (p6 : PropositionOne.N6) (p7 : PropositionOne.N7) (p8 : PropositionOne.N8)
    (p9 : PropositionOne.N9) (p10 : PropositionOne.N10)
    (q1 : CorollaryOne.N1) (q3 : CorollaryOne.N3) (h1 : N1) (h2 : N2) (h3 : N3) : Witness :=
  ⟨scaling_of p1 p2 p3 p4 p5 p6 p7, valid_of q1, det_ne_zero_of h1, h2, h3 h1, maximizes_of q1,
    fun hc => not_conservative_of p2 p5 p7 p8 p9 p10 q3 hc.1⟩

/-- The stated witness properties imply the refutation of the generic OLS guarantee. -/
theorem assemble (p1 : PropositionOne.N1) (p2 : PropositionOne.N2)
    (p3 : PropositionOne.N3) (p4 : PropositionOne.N4) (p5 : PropositionOne.N5)
    (p6 : PropositionOne.N6) (p7 : PropositionOne.N7) (p8 : PropositionOne.N8)
    (p9 : PropositionOne.N9) (p10 : PropositionOne.N10)
    (q1 : CorollaryOne.N1) (q3 : CorollaryOne.N3) (h1 : N1) (h2 : N2) (h3 : N3) : Target := by
  intro hall
  obtain ⟨hS, hV, hdet, hmean, hθ, hM, hnot⟩ :=
    assemble_witness p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q1 q3 h1 h2 h3
  exact hnot (hall PF 6 2 (29 / 15) 2 hS hV 2 0 olsDesign olsCoef hdet hmean hθ oracleChoice hM)

end

end AronowAudit.P011.Wave1.PackageOLS
