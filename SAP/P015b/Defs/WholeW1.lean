import Mathlib
import SAP.P015b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P015b

universe u

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- The literal fitted squared-residual weighted mean. Singular finite regressions
and zero finite denominators use the existing totalized definitions; neither
exception is assumed to disappear almost surely at a deterministic sample size. -/
def fittedWeightedMean {Ω : Type*} {K : ℕ} (D Z : ℕ → Ω → ℝ)
    (X : ℕ → Ω → Fin K → ℝ) (n : ℕ) (s : Ω) : ℝ :=
  (∑ i : Fin n, fittedTreatmentResidual D X n s i ^ 2 * Z i s) /
    (∑ i : Fin n, fittedTreatmentResidual D X n s i ^ 2)

/-- P015-T23; pp. 255–256 (PDF pp. 6–7), expression (9).
For iid measurable observations with a linear conditional treatment mean, the
seven integrable moment families and nonsingular population control Gram in the
claim's sufficient regularity reading, and positive mean population weight, the
mean formed with fitted squared treatment residuals converges in probability to
E[w Z]/E[w], the effective population mean. Finite singular samples and zero
fitted denominators use the package's totalized conventions. -/
def T23WholeStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Z : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hZ : ∀ i, Measurable (Z i))
    (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s, Z i s, X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s, Z i s, X i s))
      (fun s => (D 0 s, Z 0 s, X 0 s)) P P)
    (ω : Fin (K + 1) → ℝ)
    (hlinear : P[D 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[P]
      fun s => dotProduct (controlVector (X 0 s)) ω)
    (hreg : EffectiveMeanRegularity P D Z X ω),
    TendstoInMeasure P (fittedWeightedMean D Z X) atTop
      (fun _ => (∫ s, squaredPopulationResidual P (D 0) (X 0) s * Z 0 s ∂P) /
        (∫ s, squaredPopulationResidual P (D 0) (X 0) s ∂P))

/-- The intercept-only population treatment projection under common assignment. -/
def randomAssignmentCenter {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : Ω → ℝ) (K : ℕ) : Fin (K + 1) → ℝ :=
  Fin.cases (∫ s, D s ∂P) (fun _ => 0)

/-- The population identities in the proof of Corollary A.1. The moment and
positive-variance guards express the existence of its expectations and ratio. -/
def RandomizationWholePopulation : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : Ω → ℝ) (X : Ω → Fin K → ℝ)
    (hD : Measurable D) (hY : Measurable Y₀) (hτ : Measurable τ) (hX : Measurable X)
    (hrandom : IndepFun D (fun s => (Y₀ s, τ s, X s)) P)
    (h₂ : MemLp D 2 P) (hτi : Integrable τ P) (hpos : 0 < variance D P),
    (P[D | MeasurableSpace.comap X inferInstance] =ᵐ[P] fun _ => ∫ s, D s ∂P) ∧
    (squaredPopulationResidual P D X =ᵐ[P] fun s => (D s - ∫ t, D t ∂P) ^ 2) ∧
    IndepFun (squaredPopulationResidual P D X) τ P ∧
    Integrable (squaredPopulationResidual P D X) P ∧
    Integrable (fun s => squaredPopulationResidual P D X s * τ s) P ∧
    (∫ s, squaredPopulationResidual P D X s ∂P) = variance D P ∧
    (0 < ∫ s, squaredPopulationResidual P D X s ∂P) ∧
    (∫ s, squaredPopulationResidual P D X s * τ s ∂P) =
      (∫ s, squaredPopulationResidual P D X s ∂P) * (∫ s, τ s ∂P) ∧
    (∫ s, squaredPopulationResidual P D X s * τ s ∂P) /
      (∫ s, squaredPopulationResidual P D X s ∂P) = ∫ s, τ s ∂P

/-- Both actual estimators in Corollary A.1, under its eight-family reading of
regularity. No structure beyond a measurable sampling space is required. -/
def RandomizedWholeConvergence : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ)
    (D Y₀ τ : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ)
    (hD : ∀ i, Measurable (D i)) (hY : ∀ i, Measurable (Y₀ i))
    (hτ : ∀ i, Measurable (τ i)) (hX : ∀ i, Measurable (X i))
    (hiid : iIndepFun (fun i s => (D i s, Y₀ i s, τ i s, X i s)) P)
    (hident : ∀ i, IdentDistrib (fun s => (D i s, Y₀ i s, τ i s, X i s))
      (fun s => (D 0 s, Y₀ 0 s, τ 0 s, X 0 s)) P P)
    (hrandom : IndepFun (D 0) (fun s => (Y₀ 0 s, τ 0 s, X 0 s)) P)
    (hreg : RegressionRegularity P D Y₀ τ X),
    TendstoInMeasure P (treatmentEstimate D Y₀ τ X) atTop (fun _ => ∫ s, τ 0 s ∂P) ∧
    TendstoInMeasure P (fittedWeightedMean D τ X) atTop (fun _ => ∫ s, τ 0 s ∂P)

/-- P015-T24; p. 263 (PDF p. 14), Corollary A.1; p. 256 (PDF p. 7).
Common random assignment makes the population treatment mean conditional on
controls constant and the squared residual weight independent of the effect.
Its mean is the positive treatment variance; the product expectation factors
and the weighted-effect ratio cancels to the average effect. Under iid sampling
and the eight-family regularity reading, both the actual OLS treatment estimate
and the intermediate fitted-weight effect ratio converge in probability to
that average effect, on every measurable sampling space. -/
def T24WholeStatement : Prop :=
  RandomizedWholeConvergence.{u} ∧ RandomizationWholePopulation.{u}

/-- A full-rank one-group design with a unit intercept and binary treatment. -/
def t10WitnessDesign : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- The precision of the admissible one-group witness with S = 0 and variance 1. -/
def t10WitnessPrecision : Matrix (Fin 2) (Fin 2) ℝ :=
  precisionMatrix 0 (t10WitnessDesign.transpose * t10WitnessDesign) 1

/-- The one-group pooling map H inverse P. -/
def t10WitnessMap : Matrix (Fin 2) (Fin 2) ℝ :=
  t10WitnessPrecision⁻¹ * t10WitnessPrecision

/-- The printed claim is false: P015-T10; p. 257 (PDF p. 8), corrected
random-coefficient pooling description, final equivalence in clause (iii).
With one full-rank group, zero coefficient covariance and error variance one,
the pooling map is the identity. Its off-treatment row is zero, but the
prescribed scalar weight zero fails on treatment coefficient one. Off-treatment
zeros alone characterize existence of scalar weights; for prescribed weights
the diagonal entries must also equal those weights. -/
def T10WholeStatement : Prop :=
  (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ∧ (0 : ℝ) < 1 ∧
  (∀ i, t10WitnessDesign i 0 = 1) ∧
  (t10WitnessDesign.transpose * t10WitnessDesign).det = 1 ∧
  sampleCoefficients t10WitnessDesign ![0, 1] = ![0, 1] ∧
  t10WitnessPrecision = t10WitnessDesign.transpose * t10WitnessDesign ∧
  t10WitnessMap = 1 ∧
  (∀ j : Fin 2, j ≠ 1 → t10WitnessMap 1 j = 0) ∧
  (∑ j : Fin 2, t10WitnessMap 1 j * (![0, 1] : Fin 2 → ℝ) j) ≠
    0 * (![0, 1] : Fin 2 → ℝ) 1 ∧
  ¬ (∀ t : Fin 2 → ℝ, (∑ j, t10WitnessMap 1 j * t j) = 0 * t 1)

/-- Membership in the binary logistic family with one common parameter vector
for every unit. Conditional success probabilities are conditional expectations
of the success indicators, and their equalities are almost sure. -/
def CommonLogisticModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ) (Y D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ) : Prop :=
  (∀ i, Measurable (Y i)) ∧ (∀ i, Measurable (D i)) ∧
  (∀ i, Measurable (X i)) ∧ (∀ i, ∀ᵐ s ∂P, Y i s = 0 ∨ Y i s = 1) ∧
  ∃ α β : ℝ, ∃ γ : Fin K → ℝ, ∀ i,
    P[fun s => if Y i s = 1 then (1 : ℝ) else 0 |
      MeasurableSpace.comap (fun s => (D i s, X i s)) inferInstance] =ᵐ[P]
        fun s => sigmoidMean (α + β * D i s + dotProduct (X i s) γ)

/-- P015-T14; p. 257 (PDF p. 8), logistic display; Appendix C, p. 265 (PDF p. 16).
The binary logistic model specifies common real intercept, treatment and control
coefficients for which the conditional success probability given treatment and
controls is 1/(1+exp(-predictor)). Model membership supplies those parameters.
The printed unconditional probability cannot equal both predictions at distinct
treatments with fixed controls and a nonzero treatment coefficient.
The usual measure-theoretic conditions are assumed; the conditional-probability
equalities hold almost surely. -/
def T14WholeStatement : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ℕ) (Y D : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin K → ℝ),
    CommonLogisticModel P K Y D X ↔
      (∀ i, Measurable (Y i)) ∧ (∀ i, Measurable (D i)) ∧
      (∀ i, Measurable (X i)) ∧ (∀ i, ∀ᵐ s ∂P, Y i s = 0 ∨ Y i s = 1) ∧
      ∃ α β : ℝ, ∃ γ : Fin K → ℝ, ∀ i,
        P[fun s => if Y i s = 1 then (1 : ℝ) else 0 |
          MeasurableSpace.comap (fun s => (D i s, X i s)) inferInstance] =ᵐ[P]
            fun s => 1 / (1 + Real.exp (-(α + β * D i s + dotProduct (X i s) γ)))) ∧
  T14Statement

/-- The continuous linear functional given by the logistic score vector. -/
def logisticScoreMap {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (Y : N → ℝ) (θ : Q → ℝ) : (Q → ℝ) →L[ℝ] ℝ :=
  ∑ j, residualEquation W (fun _ => 1) Y sigmoidMean θ j • ContinuousLinearMap.proj j

/-- Logistic likelihood differentiability, with the score as its full Frechet
 differential, for all designs including singular and empty designs. -/
def UnrestrictedLogisticScore : Prop :=
  ∀ (N K : ℕ) (W : Matrix (Fin N) (Fin (K + 2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i = 0 ∨ Y i = 1) (θ : Fin (K + 2) → ℝ),
    HasFDerivAt (binaryLogLikelihood W (fun _ => 1) Y sigmoidMean)
      (logisticScoreMap W Y θ) θ

/-- Unique affine surrogate root and its exact OLS scaling, under precisely the
population-free finite rank and nonzero-scale conditions of clause (iii). -/
def AffineWholeRoot : Prop :=
  ∀ (N K : ℕ) (W : Matrix (Fin N) (Fin (K + 2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i = 0 ∨ Y i = 1) (hW : ∀ i, W i 0 = 1)
    (hQ : (W.transpose * W).det ≠ 0) (b c : ℝ) (hc : c ≠ 0),
    (∃! θ : Fin (K + 2) → ℝ,
      residualEquation W (fun _ => 1) Y (fun a => b + c * a) θ = 0) ∧
    (∀ θ, residualEquation W (fun _ => 1) Y (fun a => b + c * a) θ = 0 →
      affineCoefficients 0 b c θ = sampleCoefficients W Y ∧
        sampleCoefficients W Y 1 = c * θ 1)

/-- P015-T21; p. 265 (PDF p. 16), Appendix C; main text p. 257 (PDF p. 8).
For every binary sample the logistic log likelihood is Frechet differentiable
with score sum W_i'(Y_i - sigmoid(W_i theta)), without a rank assumption.
Affine coefficients give identical observation predictors and residual equations.
If W'W is nonsingular and the affine scale is nonzero, the surrogate equations
have a unique root whose affine transform is OLS; its treatment coefficient
multiplied by the scale equals the OLS treatment coefficient. -/
def T21WholeStatement : Prop :=
  UnrestrictedLogisticScore ∧ AffinePredictorIdentity ∧ AffineWholeRoot

end
end SAP.P015b
