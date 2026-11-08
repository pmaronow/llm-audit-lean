import SAP.P032.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

variable {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
  [DecidableEq R] [DecidableEq M] [DecidableEq P]

def pairMomentStatement : Prop :=
  (∀ r, finiteMean negativePairDistribution (fun ω => pairErrorValues ω r) = 0) ∧
    (∀ r s, finiteMean negativePairDistribution (fun ω => pairErrorValues ω r * pairErrorValues ω s) =
      pairCovariance (-1) r s) ∧
    (∀ r, finiteMean positivePairDistribution (fun ω => pairErrorValues ω r) = 0) ∧
    (∀ r s, finiteMean positivePairDistribution (fun ω => pairErrorValues ω r * pairErrorValues ω s) =
      pairCovariance 1 r s)

def pairSamplingStatement : Prop :=
  (∀ ω r, |pairErrorValues ω r| ≤ 1) ∧
    (pairCovariance (-1)).PosDef ∧ (pairCovariance 1).PosDef ∧
    (pairIntercept.transpose*pairIntercept).det ≠ 0 ∧
    (pairSlope.transpose*pairSlope).det ≠ 0 ∧
    finiteVar negativePairDistribution (fun ω => (leastSquares pairIntercept (pairErrorValues ω)) 0) = 1/4 ∧
    finiteVar positivePairDistribution (fun ω => (leastSquares pairSlope (pairErrorValues ω)) 0) = 1/4 ∧
    finiteVar positivePairDistribution (fun ω => (leastSquares pairIntercept (pairErrorValues ω)) 0) = 3/4

def pairSpectrumStatement : Prop :=
  pairCovariance (-1) * (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.diagonal ![1/2,3/2] ∧
    pairCovariance 1 * (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.diagonal ![3/2,1/2] ∧
    (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) *
      ((1/2 : ℝ) • (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ)) = 1

def pairInterceptStatement : Prop :=
  let X : Matrix (Fin 2) (Fin 1) ℝ := pairIntercept
    let c : Fin 1 → ℝ := fun _ => 1
    let h := X *ᵥ (olsBread X *ᵥ c)
    (X.transpose * X).det ≠ 0 ∧ h = ![1/2,1/2] ∧
      quadForm (pairCovariance (-1)) h = 1/4 ∧
      quadForm (dyadicRestriction pairDyads (pairCovariance (-1))) h = 1/2 ∧
      quadForm (pairCovariance (-1)) h <
        quadForm (dyadicRestriction pairDyads (pairCovariance (-1))) h

def pairSlopeStatement : Prop :=
  let X : Matrix (Fin 2) (Fin 1) ℝ := pairSlope
    let c : Fin 1 → ℝ := fun _ => 1
    let h := X *ᵥ (olsBread X *ᵥ c)
    (X.transpose * X).det ≠ 0 ∧ h = ![-1/2,1/2] ∧
      quadForm (pairCovariance 1) h = 1/4 ∧
      quadForm (dyadicRestriction pairDyads (pairCovariance 1)) h = 1/2 ∧
      quadForm (pairCovariance 1) ![1/2,1/2] = 3/4 ∧
      quadForm (dyadicRestriction pairDyads (pairCovariance 1)) ![1/2,1/2] = 1/2

def fourMomentStatement : Prop :=
  (∀ r, finiteMean fourDistribution (fun ω => fourErrorValues ω r) = 0) ∧
    (∀ r s, finiteMean fourDistribution
      (fun ω => fourErrorValues ω r * fourErrorValues ω s) = fourCovariance r s)

def blockPositivityStatement : Prop :=
  fourCovariance.PosDef ∧ sixCovariance.PosDef

def blockSpectrumStatement : Prop :=
  fourSpectralInverse*fourSpectralBasis = 1 ∧
    fourCovariance*fourSpectralBasis = fourSpectralBasis*Matrix.diagonal ![7/4,3/4,3/4,3/4] ∧
    sixSpectralInverse*sixSpectralBasis = 1 ∧
    sixCovariance*sixSpectralBasis = sixSpectralBasis*Matrix.diagonal ![1/4,1/4,1,3/2,3/2,3/2]

def fourPopulationStatement : Prop :=
  quadForm fourCovariance (fun _ => (1/4 : ℝ)) = 3/16 ∧
    quadForm (dyadicRestriction fourDyadData fourCovariance) (fun _ => (1/4 : ℝ)) = 5/16 ∧
    finiteVar fourDistribution
      (fun ω => (1/4 : ℝ)*∑ r, fourErrorValues ω r) = 3/16

def sixMomentStatement : Prop :=
  (∀ r : Fin 6, finiteMean sixSignDistribution (fun a => sixErrorValues a r) = 0) ∧
    (∀ r s : Fin 6, finiteMean sixSignDistribution
      (fun a => sixErrorValues a r*sixErrorValues a s) = sixCovariance r s)

def sixPopulationStatement : Prop :=
  (∀ r, ∑ s, sixCovariance r s = 1) ∧
    (∀ r, ∑ s, dyadicRestriction sixDyadData sixCovariance r s = 3/2) ∧
    (∀ r, ∑ s, dyadicMask sixDyadData r s = 5) ∧
    quadForm sixCovariance (fun _ => (1/6 : ℝ)) = 1/6 ∧
    quadForm (dyadicRestriction sixDyadData sixCovariance) (fun _ => (1/6 : ℝ)) = 1/4 ∧
    quadForm (fun r s => recordMask r s * sixCovariance r s) (fun _ => (1/6 : ℝ)) = 1/6

def sixBoundStatement : Prop :=
  ∀ a : Fin 13 → Fin 2, ∀ r : Fin 6, |sixErrorValues a r| ≤ Real.sqrt 2+1/2

/-- Exact fits of the intercept model, including its contrast weights. -/
def interceptFitStatement (u : R → ℝ) : Prop :=
  leastSquares onesDesign u = (fun _ => recordMean u) ∧
  fitResidual onesDesign u = (fun r => u r - recordMean u) ∧
  (onesDesign : Matrix R (Fin 1) ℝ) *ᵥ
    (olsBread (onesDesign : Matrix R (Fin 1) ℝ) *ᵥ (fun _ : Fin 1 => (1 : ℝ))) =
    (fun _ => (Fintype.card R : ℝ)⁻¹)

/-- A measurable infinite independent realization of the given atom weights. -/
def iidRealizationExists {S : Type} [MeasurableSpace S] (weights : S → ℝ) : Prop :=
  ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ μ : Measure Ω, ∃ block : ℕ → Ω → S,
    IsProbabilityMeasure μ ∧ (∀ b, Measurable (block b)) ∧ iIndepFun block μ ∧
    (∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (weights a))

/-- Four-observation blocks, with actual residual estimates and sampling variances.
Limits use m+1 blocks so every sampling variance in a ratio is positive. -/
def fourReplicationStatement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → Fin 16),
    (∀ b, Measurable (block b)) → iIndepFun block μ →
    (∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (fourDistribution.weight a)) →
    (∀ m : ℕ, 1 ≤ m →
      (∀ ω, interceptFitStatement (fourReplicatedErrors block m ω)) ∧
      ((∀ ω, (4*(m : ℝ))^2 * residualInterceptVariance (fourReplicatedDyads m) (fourReplicatedErrors block m ω) =
      (∑ b : Fin m, ∑ pair : Fin 2, (fourIncidentPairTotal block b.val ω pair)^2) -
        8*(m : ℝ)*(recordMean (fourReplicatedErrors block m ω))^2) ∧
    variance (fun ω => recordMean (fourReplicatedErrors block m ω)) μ = 3/(16*(m : ℝ)) ∧
    (∫ ω, residualInterceptVariance (fourReplicatedDyads m) (fourReplicatedErrors block m ω) ∂μ) =
      (10*(m : ℝ)-3)/(32*(m : ℝ)^2) ∧
    (∫ ω, residualInterceptVariance (fourReplicatedDyads m) (fourReplicatedErrors block m ω) ∂μ) -
      variance (fun ω => recordMean (fourReplicatedErrors block m ω)) μ =
      (4*(m : ℝ)-3)/(32*(m : ℝ)^2) ∧
    variance (fun ω => recordMean (fourReplicatedErrors block m ω)) μ <
      (∫ ω, residualInterceptVariance (fourReplicatedDyads m) (fourReplicatedErrors block m ω) ∂μ))) ∧
    TendstoInMeasure μ
      (fun m ω => residualInterceptVariance (fourReplicatedDyads (m+1))
        (fourReplicatedErrors block (m+1) ω) /
        variance (fun ω => recordMean (fourReplicatedErrors block (m+1) ω)) μ)
      atTop (fun _ => (5/3 : ℝ))

/-- Independent six-edge blocks and the almost-sure scaled-estimator limit. -/
def sixReplicationStatement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → (Fin 13 → Fin 2)),
    (∀ b, Measurable (block b)) → iIndepFun block μ →
    (∀ b a, μ {ω | block b ω = a} = (1/8192 : ENNReal)) →
    (∀ m : ℕ, 1 ≤ m →
      (∀ ω, interceptFitStatement (sixReplicatedErrors block m ω)) ∧
      ((∀ b r, (∫ ω, sixErrorValues (block b ω) r ∂μ) = 0) ∧
    (∀ b r s, (∫ ω, sixErrorValues (block b ω) r * sixErrorValues (block b ω) s ∂μ) =
      sixCovariance r s) ∧
    (∀ b, (∫ ω, sixIncidentQuadratic (block b ω) ∂μ) = 9) ∧
    (∀ ω, (6*(m : ℝ))*residualInterceptVariance (sixReplicatedDyads m) (sixReplicatedErrors block m ω) =
      (∑ b : Fin m, sixIncidentQuadratic (block b.val ω))/(6*(m : ℝ)) -
        5*(recordMean (sixReplicatedErrors block m ω))^2) ∧
    variance (fun ω => recordMean (sixReplicatedErrors block m ω)) μ = 1/(6*(m : ℝ)) ∧
    quadForm (dyadicRestriction (sixReplicatedDyads m)
      (errorMoments μ (fun r ω => sixReplicatedErrors block m ω r)))
      (fun _ => (6*(m : ℝ))⁻¹) = 3/(2*(6*(m : ℝ))) ∧
    quadForm (fun r s => recordMask r s *
      errorMoments μ (fun r ω => sixReplicatedErrors block m ω r) r s)
      (fun _ => (6*(m : ℝ))⁻¹) = 1/(6*(m : ℝ)) ∧
    (∫ ω, residualInterceptVariance (sixReplicatedDyads m) (sixReplicatedErrors block m ω) ∂μ) =
      3/(2*(6*(m : ℝ)))-5/(6*(m : ℝ))^2 ∧
    ((variance (fun ω => recordMean (sixReplicatedErrors block m ω)) μ <
      (∫ ω, residualInterceptVariance (sixReplicatedDyads m) (sixReplicatedErrors block m ω) ∂μ)) ↔ 2 ≤ m))) ∧
    (∫ ω, residualInterceptVariance (sixReplicatedDyads 1)
      (sixReplicatedErrors block 1 ω) ∂μ) = 1/9 ∧
    ((∫ ω, residualInterceptVariance (sixReplicatedDyads 1)
      (sixReplicatedErrors block 1 ω) ∂μ) <
      variance (fun ω => recordMean (sixReplicatedErrors block 1 ω)) μ) ∧
    (∀ᵐ ω ∂μ, Tendsto
      (fun m : ℕ => (6*((m+1 : ℕ) : ℝ))*residualInterceptVariance
        (sixReplicatedDyads (m+1)) (sixReplicatedErrors block (m+1) ω))
      atTop (nhds (3/2 : ℝ)))

/-- All six counterexample constructions in the recorded target. -/
def T1Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  pairMomentStatement ∧ pairSamplingStatement ∧ pairSpectrumStatement ∧
  pairInterceptStatement ∧ pairSlopeStatement ∧ fourMomentStatement ∧
  blockPositivityStatement ∧ blockSpectrumStatement ∧ fourPopulationStatement ∧
  (∀ a, interceptFitStatement (fourErrorValues a)) ∧
  sixMomentStatement ∧ sixPopulationStatement ∧ sixBoundStatement ∧
  (∀ a, interceptFitStatement (sixErrorValues a)) ∧
  distributionMeasure sixSignDistribution = sixProductMeasure ∧
  iidRealizationExists fourDistribution.weight ∧
  iidRealizationExists sixSignDistribution.weight ∧
  fourReplicationStatement Ω ∧ sixReplicationStatement Ω

end
end SAP.P032
