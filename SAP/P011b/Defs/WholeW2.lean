import Mathlib
import SAP.P011b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section

/-- OLS identities on a single finite sample. Integrable coordinate means and full
column rank suffice; no scaling, boundedness, or positive variance is assumed. -/
def FiniteOLSIdentitiesW2 : Prop :=
  ∀ (n p : ℕ), 0 < p → p ≤ n →
  ∀ (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ) (b : Fin p → ℝ) (j : Fin p),
    (Dᵀ * D).det ≠ 0 → MeanModel m D b →
    (∀ i, m.theta i = olsTheta D j i) →
    (∀ y, betaHat m y = ols D y j) ∧ beta m = b j ∧
    (∀ i, expectation m (fun y => weighted m y i) = olsTheta D j i * (D *ᵥ b) i ∧
      delta m i = olsTheta D j i * (D *ᵥ b) i - b j)

/-- Exact shifts hold for all data vectors, even outside a mean model. The raw
centred products shift by theta_i (D c)_i - c_j. -/
def OLSShiftIdentitiesW2 : Prop :=
  ∀ (n p : ℕ), 0 < p → p ≤ n →
  ∀ (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ) (j : Fin p),
    (Dᵀ * D).det ≠ 0 → (∀ i, m.theta i = olsTheta D j i) →
    ∀ (y : Fin n → ℝ) (c : Fin p → ℝ),
      ols D (y + D *ᵥ c) = ols D y + c ∧
      fittedResidual m D (ols D) (y + D *ᵥ c) = fittedResidual m D (ols D) y ∧
      (∀ A : Graph n,
        VResidual A (fittedResidual m D (ols D) (y + D *ᵥ c)) =
          VResidual A (fittedResidual m D (ols D) y)) ∧
      centered (weighted m (y + D *ᵥ c)) = centered (weighted m y) +
        (fun i => m.theta i * (D *ᵥ c) i - c j)

/-- An intercept column makes every other coefficient and the residual objective
invariant under every constant outcome shift. -/
def InterceptShiftIdentitiesW2 : Prop :=
  ∀ (n p : ℕ), 0 < p → p ≤ n →
  ∀ (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ) (j j₀ : Fin p),
    (Dᵀ * D).det ≠ 0 → (∀ i, m.theta i = olsTheta D j i) →
    (∀ i, D i j₀ = 1) → j ≠ j₀ →
    ∀ (y : Fin n → ℝ) (t : ℝ),
      ols D (y + fun _ => t) j = ols D y j ∧
      fittedResidual m D (ols D) (y + fun _ => t) = fittedResidual m D (ols D) y ∧
      ∀ A : Graph n,
        VResidual A (fittedResidual m D (ols D) (y + fun _ => t)) =
          VResidual A (fittedResidual m D (ols D) y)

/-- A graph can be chosen separately at each data vector; all selections attaining
the finite maximum have the same Borel objective value, including at ties. -/
abbrev GraphSelectionW2 (F : Family) :=
  ∀ k, (Fin (F.size k) → ℝ) → Graph (F.size k)

def RawMaximizingW2 (F : Family) (A : GraphSelectionW2 F) : Prop :=
  ∀ k y, Maximizes (F.model k).R (F.model k).d
    (fun B => V1 B (weighted (F.model k) y)) (A k y)

def AllRawMaxConservativeW2 (F : Family) : Prop :=
  ∀ A : GraphSelectionW2 F, RawMaximizingW2 F A →
    Conservative F (fun k y => V1 (A k y) (weighted (F.model k) y))

/-- Finite compatible maxima of measurable objectives have measurable values,
even when an arbitrary maximizing selection itself is not measurable. -/
def CompatibleMaximaMeasurableW2 : Prop :=
  ∀ (n : ℕ) (R G : Graph n) (d : Fin n → ℕ), Compatible R d G →
  ∀ (f : Graph n → (Fin n → ℝ) → ℝ), (∀ B, Measurable (f B)) →
  ∀ (A : (Fin n → ℝ) → Graph n), (∀ y, Maximizes R d (fun B => f B y) (A y)) →
    Measurable (fun y => f (A y) y)

/-- The raw oracle has the moving mean-bias limit and the two oracle equivalences.
Under valid constraints, nonnegative liminf bias suffices for every maximum.
Equal unit means give both oracle consistency and maximal conservativeness. -/
def RawOracleConclusionsW2 : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
    InProbability F (fun k y => scaledOracle F k y - scaledTrue F k)
      (fun k => meanBias (F.model k)) ∧
    (InProbability F (scaledOracle F) (scaledTrue F) ↔
      Tendsto (fun k => meanBias (F.model k)) atTop (𝓝 0)) ∧
    (Conservative F (fun k y => V1 (F.model k).G (weighted (F.model k) y)) ↔
      0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop) ∧
    (Valid F → (∃ A : GraphSelectionW2 F, RawMaximizingW2 F A) ∧
      (0 ≤ Filter.liminf (fun k => meanBias (F.model k)) atTop →
        AllRawMaxConservativeW2 F)) ∧
    ((∀ k i, expectation (F.model k) (fun y => weighted (F.model k) y i) =
        beta (F.model k)) →
      InProbability F (scaledOracle F) (scaledTrue F) ∧
      (Valid F → AllRawMaxConservativeW2 F))

/-- The lower binary-star design, with intercept and centred covariate. -/
def starDesignW2 (K : ℕ) : Matrix (Fin (4 * K)) (Fin 2) ℝ :=
  fun i j => if j = 0 then 1 else
    (![3, -1, -1, -1] : Fin 4 → ℝ) (localIndex (by decide) i)

def starCoefW2 : Fin 2 → ℝ := ![3/8, 1/8]

/-- Removing recruitment edges changes only compatibility, not the law, true
dependency graph, coefficient weights, or degree caps. -/
def unforcedModelW2 (K : ℕ) : Model (4 * K) :=
  { starModel false K with R := emptyGraph (4 * K) }

def unforcedFamilyW2 : Family where
  size := fun k => 4 * (k + 1)
  positive := by intro k; omega
  grows := (starFamily false).grows
  model := fun k => unforcedModelW2 (k + 1)

/-- Nonnecessity for the compatible maximum, as required by corrected clause (i).
The true graph is feasible, as is the empty graph. The independent binary-star
blocks obey the standing setting; no dependence between different blocks is added. -/
def RawMaximumWitnessW2 : Prop :=
  Scaling unforcedFamilyW2 1 3 (27/128) 2 ∧ Valid unforcedFamilyW2 ∧
  (∀ k,
    ((starDesignW2 (k+1))ᵀ * starDesignW2 (k+1)).det ≠ 0 ∧
    MeanModel (unforcedFamilyW2.model k) (starDesignW2 (k+1)) starCoefW2 ∧
    (∀ i, (unforcedFamilyW2.model k).theta i = olsTheta (starDesignW2 (k+1)) 0 i) ∧
    scaledTrue unforcedFamilyW2 k = 27/128 ∧
    meanBias (unforcedFamilyW2.model k) = -3/128 ∧
    Compatible (unforcedFamilyW2.model k).R (unforcedFamilyW2.model k).d
      (emptyGraph (unforcedFamilyW2.size k)) ∧
    (∀ y, (unforcedFamilyW2.size k : ℝ) *
      V1 (emptyGraph (unforcedFamilyW2.size k)) (weighted (unforcedFamilyW2.model k) y) =
        sampleVariance (weighted (unforcedFamilyW2.model k) y))) ∧
  InProbability unforcedFamilyW2
    (fun k y => sampleVariance (weighted (unforcedFamilyW2.model k) y)) (fun _ => 15/64) ∧
  (∃ A : GraphSelectionW2 unforcedFamilyW2, RawMaximizingW2 unforcedFamilyW2 A) ∧
  AllRawMaxConservativeW2 unforcedFamilyW2 ∧
  Filter.liminf (fun k => meanBias (unforcedFamilyW2.model k)) atTop < 0

/-- A two-point intercept/slope design demonstrating that raw slope variance can
change: zero outcomes and a shift by one give raw estimates 0 and 1/2. -/
def shiftDesignW2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 1, 1]

def shiftModelW2 : Model 2 where
  law := Measure.dirac 0
  probability := by infer_instance
  theta := ![-1, 1]
  G := emptyGraph 2
  R := emptyGraph 2
  d := fun _ => 0

def RawSlopeShiftWitnessW2 : Prop :=
  (shiftDesignW2ᵀ * shiftDesignW2).det ≠ 0 ∧
  MeanModel shiftModelW2 shiftDesignW2 0 ∧
  (∀ i, shiftModelW2.theta i = olsTheta shiftDesignW2 1 i) ∧
  (∀ i, shiftDesignW2 i 0 = 1) ∧
  ols shiftDesignW2 0 1 = ols shiftDesignW2 (fun _ => 1) 1 ∧
  fittedResidual shiftModelW2 shiftDesignW2 (ols shiftDesignW2) 0 =
    fittedResidual shiftModelW2 shiftDesignW2 (ols shiftDesignW2) (fun _ => 1) ∧
  V1 (emptyGraph 2) (weighted shiftModelW2 0) = 0 ∧
  V1 (emptyGraph 2) (weighted shiftModelW2 (fun _ => 1)) = 1/2

/-- Euclidean row bounds, bounded raw responses, and a uniform positive lower
bound for the normalized Gram quadratic form (equivalently its least eigenvalue). -/
def DesignRegularW2 (F : Family) (p : ℕ)
    (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) : Prop :=
  ∃ Bx By lam : ℝ, 0 ≤ Bx ∧ 0 ≤ By ∧ 0 < lam ∧
    (∀ k i, l2 (D k i) ≤ Bx) ∧
    (∀ k, ∀ᵐ y ∂(F.model k).law, ∀ i, |y i| ≤ By) ∧
    ∀ k z, lam * l2 z ^ 2 ≤ quadratic ((1 / (F.size k : ℝ)) • ((D k)ᵀ * D k)) z

/-- Delta_i = theta_i x_i^T (bHat-b), with the deterministic b allowed to vary by row. -/
def olsDeltaW2 {n p : ℕ} (m : Model n) (D : Matrix (Fin n) (Fin p) ℝ)
    (b : Fin p → ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => m.theta i * (D *ᵥ (ols D y - b)) i

/-- The precise displayed bound in clause (iii); it uses the true graph degree. -/
def perturbationRHSW2 {n : ℕ} (c : ℝ) (e d : Fin n → ℝ) : ℝ :=
  (1 + c) * (2 * (l2 e / Real.sqrt (n : ℝ)) * (l2 d / Real.sqrt (n : ℝ)) +
    l2 d ^ 2 / (n : ℝ))

def perturbationErrorW2 {n : ℕ} (G : Graph n) (e d : Fin n → ℝ) : ℝ :=
  |quadratic (oracleMatrix G) (e - d) - quadratic (oracleMatrix G) e| / (n : ℝ)

/-- Residual conclusions with fixed p and j, but arbitrary deterministic b_n.
The perturbation inequality holds at every data vector; its bound, its left side,
and the scaled residual oracle error converge in probability to zero. -/
def ResidualOLSConclusionsW2 : Prop :=
  ∀ (F : Family) (c1 c2 c3 c4 : ℝ), Scaling F c1 c2 c3 c4 →
  ∀ (p : ℕ) (j : Fin p) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ)
    (b : ℕ → Fin p → ℝ),
    0 < p → (∀ k, p ≤ F.size k) →
    (∀ k, ((D k)ᵀ * D k).det ≠ 0) →
    (∀ k, MeanModel (F.model k) (D k) (b k)) →
    (∀ k i, (F.model k).theta i = olsTheta (D k) j i) →
    DesignRegularW2 F p D →
    Tight F (fun k y => Real.sqrt (F.size k : ℝ) * l2 (ols (D k) y - b k)) ∧
    (∀ k y, fittedResidual (F.model k) (D k) (ols (D k)) y =
      trueResidual (F.model k) (D k) (b k) y - olsDeltaW2 (F.model k) (D k) (b k) y) ∧
    (∀ k y, perturbationErrorW2 (F.model k).G
      (trueResidual (F.model k) (D k) (b k) y) (olsDeltaW2 (F.model k) (D k) (b k) y) ≤
      perturbationRHSW2 c2 (trueResidual (F.model k) (D k) (b k) y)
        (olsDeltaW2 (F.model k) (D k) (b k) y)) ∧
    InProbability F (fun k y => perturbationRHSW2 c2
      (trueResidual (F.model k) (D k) (b k) y) (olsDeltaW2 (F.model k) (D k) (b k) y))
      (fun _ => 0) ∧
    InProbability F (fun k y => perturbationErrorW2 (F.model k).G
      (trueResidual (F.model k) (D k) (b k) y) (olsDeltaW2 (F.model k) (D k) (b k) y))
      (fun _ => 0) ∧
    InProbability F (fun k y => (F.size k : ℝ) * VResidual (F.model k).G
      (fittedResidual (F.model k) (D k) (ols (D k)) y)) (scaledTrue F) ∧
    (Valid F →
      (∃ A : GraphSelectionW2 F, ∀ k y, Maximizes (F.model k).R (F.model k).d
        (fun B => VResidual B (fittedResidual (F.model k) (D k) (ols (D k)) y)) (A k y)) ∧
      ∀ A : GraphSelectionW2 F,
        (∀ k y, Maximizes (F.model k).R (F.model k).d
          (fun B => VResidual B (fittedResidual (F.model k) (D k) (ols (D k)) y)) (A k y)) →
        Conservative F (fun k y => VResidual (A k y)
          (fittedResidual (F.model k) (D k) (ols (D k)) y)))

/-- P011-T16; regression example, pp. 2240–2241; (3.1), p. 2242; package
vignette lines 100–105. Corrected claim (2026-11-04).
For a full-rank fixed-design OLS coefficient, weighted unit means and their offsets
have the exact stated formulas. Under Assumption 2 the raw oracle has the moving
mean-bias limit, is consistent exactly when that bias tends to zero, and is
conservative exactly when its liminf is nonnegative. With valid constraints this
condition suffices for every compatible maximum, but is not necessary in general,
as the independent binary-star regression with empty recruitment demonstrates.
Equal weighted unit means suffice for consistency and maximal conservativeness.
Every design-space outcome shift leaves fitted residual products and all residual
objectives unchanged and has the stated effect on raw centred products. With an
intercept, constant shifts preserve slopes and residual objectives, but can change
raw slope variance, as an explicit two-point example shows. Under Assumption 2,
fixed dimension, uniformly bounded rows and outcomes, and a uniformly coercive
normalized Gram matrix, OLS has the root-n rate. The displayed normalized residual
perturbation inequality holds and its right side tends to zero in probability;
the residual oracle is consistent and every compatible residual maximum is
conservative. Deterministic coefficients and targets may vary with sample size.
The usual measure-theoretic conditions are assumed. -/
def T16WholeStatement_W2 : Prop :=
  FiniteOLSIdentitiesW2 ∧ OLSShiftIdentitiesW2 ∧ InterceptShiftIdentitiesW2 ∧
  RawOracleConclusionsW2 ∧ RawMaximumWitnessW2 ∧ RawSlopeShiftWitnessW2 ∧
  ResidualOLSConclusionsW2 ∧ CompatibleMaximaMeasurableW2

end
end SAP.P011b
