import SAP.P032.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- The coefficient of one ordered record pair in the decomposition. -/
def pairCoefficient {R M : Type*} [Fintype M] [DecidableEq R] [DecidableEq M]
    (d : R → DyadData M) (r s : R) : ℝ :=
  (∑ i, memberMask d i r s) - repeatedMask d r s -
    ((Fintype.card M : ℝ)-2)*recordMask r s

/-- Common-score decomposition, exhaustive coefficients, and subject-id discrepancies. -/
def T4Statement (R M P G : Type*) [Fintype R] [Fintype M] [Fintype P]
    [DecidableEq R] [DecidableEq M] [DecidableEq P] [DecidableEq G] : Prop :=
  (∀ (d : R → DyadData M) (z : R → P → ℝ),
    (∑ i, scoreCovariance (memberMask d i) z) - scoreCovariance (repeatedMask d) z -
      ((Fintype.card M : ℝ)-2) • scoreCovariance recordMask z =
      scoreCovariance (dyadicMask d) z) ∧
  (∀ (d : R → DyadData M) (r s : R),
    pairCoefficient d r s = dyadicMask d r s ∧
    (r = s → pairCoefficient d r s = (Fintype.card M : ℝ)-1-((Fintype.card M : ℝ)-2)) ∧
    (r ≠ s → (d r).members = (d s).members → pairCoefficient d r s = 2-1-0) ∧
    ((d r).members ≠ (d s).members → ((d r).members ∩ (d s).members).card = 1 →
      pairCoefficient d r s = 1-0-0) ∧
    (¬((d r).members ∩ (d s).members).Nonempty → pairCoefficient d r s = 0)) ∧
  (∀ a b : DyadData M,
    (a.members = b.members ∧ (a.members ∩ b.members).card = 2) ∨
    (a.members ≠ b.members ∧ (a.members ∩ b.members).card ≤ 1)) ∧
  (∀ (d : R → DyadData M) (z : R → P → ℝ) (g : R → G),
    let V₀ := scoreCovariance recordMask z
    let Vᵢ := scoreCovariance (subjectMask g) z
    let Vᵣ := scoreCovariance (dyadicMask d) z
    let C := (∑ i, scoreCovariance (memberMask d i) z) - scoreCovariance (repeatedMask d) z
    let k := (Fintype.card M : ℝ)-2
    Vᵢ = V₀ + scoreCovariance (subjectCrossMask g) z ∧
    C-k • Vᵢ = Vᵣ+k • (V₀-Vᵢ) ∧
    C-k • Vᵢ = Vᵣ-k • scoreCovariance (subjectCrossMask g) z ∧
    (Function.Injective g → Vᵢ = V₀ ∧ C-k • Vᵢ = Vᵣ) ∧
    (∀ α : ℝ, C-k • (α • Vᵢ) = Vᵣ+k • (V₀-α • Vᵢ))) ∧
  survivalDiscrepancyStatement

/-- Fixed-design population variance comparison on arbitrary probability spaces. -/
def T2Statement (R M P Ω : Type*) [Fintype R] [Fintype M] [Fintype P]
    [DecidableEq R] [DecidableEq M] [DecidableEq P] [MeasurableSpace Ω] : Prop :=
  (∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (d : R → DyadData M)
      (X : Matrix R P ℝ), (X.transpose*X).det ≠ 0 →
    ∀ (β : P → ℝ) (u : R → Ω → ℝ),
      (∀ r, MemLp (u r) 2 μ) → (∀ r, ∫ ω, u r ω ∂μ = 0) →
      let A := errorMoments μ u
      let AD := dyadicRestriction d A
      let V := fun c => variance
        (fun ω => c ⬝ᵥ leastSquares X (X *ᵥ β + fun r => u r ω)) μ
      (∀ c : P → ℝ,
        let h := X *ᵥ (olsBread X *ᵥ c)
        (∀ ω, c ⬝ᵥ leastSquares X (X *ᵥ β + fun r => u r ω) - c ⬝ᵥ β =
          h ⬝ᵥ (fun r => u r ω)) ∧
        V c = quadForm A h ∧ quadForm A h = quadForm (sandwichCovariance X A) c ∧
        quadForm A h - quadForm AD h = omittedSum d A h ∧
        (quadForm AD h ≤ V c ↔ 0 ≤ omittedSum d A h) ∧
        (quadForm AD h < V c ↔ 0 < omittedSum d A h) ∧
        (V c < quadForm AD h ↔ omittedSum d A h < 0)) ∧
      ((∀ c, quadForm AD (X *ᵥ (olsBread X *ᵥ c)) ≤ V c) ↔
        (sandwichCovariance X (A-AD)).PosSemidef) ∧
      ((sandwichCovariance X (A-AD)).PosSemidef ↔
        (X.transpose*(A-AD)*X).PosSemidef)) ∧
  pairMomentStatement ∧ pairSamplingStatement ∧ pairInterceptStatement ∧ pairSlopeStatement ∧
  omittedSum pairDyads (pairCovariance (-1)) ![1/2,1/2] = -1/4 ∧
  omittedSum pairDyads (pairCovariance 1) ![1/2,1/2] = 1/4 ∧
  omittedSum pairDyads (pairCovariance 1) ![-1/2,1/2] = -1/4 ∧
  pairCovariance 1 0 1 > 0 ∧ pairCovariance 1 1 0 > 0

/-- The unadjusted OLS residual decomposition display only. -/
def T11Statement (R M P : Type*) [Fintype R] [Fintype M] [Fintype P]
    [DecidableEq R] [DecidableEq M] [DecidableEq P] : Prop :=
  ∀ (d : R → DyadData M) (X : Matrix R P ℝ), (X.transpose*X).det ≠ 0 →
    (∀ i : M, ∃ r : R, i ∈ (d r).members) → ∀ Y : R → ℝ,
    plugInCovariance X (fitResidual X Y) (dyadicMask d) =
      (∑ i, plugInCovariance X (fitResidual X Y) (memberMask d i)) -
      plugInCovariance X (fitResidual X Y) (repeatedMask d) -
      ((Fintype.card M : ℝ)-2) • plugInCovariance X (fitResidual X Y) recordMask

/-- Finite-variance average identity and all shared-country sign cases. -/
def T12Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ],
    (∀ Y₁ Y₂ : Ω → ℝ, MemLp Y₁ 2 μ → MemLp Y₂ 2 μ →
      variance (outcomeAverage Y₁ Y₂) μ = naiveAverageVariance μ Y₁ Y₂ +
        (1/2 : ℝ)*covariance Y₁ Y₂ μ) ∧
    (∀ Z : Fin 5 → Ω → ℝ, (∀ i, MemLp (Z i) 2 μ) →
      (∀ i j, i ≠ j → covariance (Z i) (Z j) μ = 0) → ∀ a b c d : ℝ,
      let Y := countryOutcomes Z a b c d
      let Vn := naiveAverageVariance μ Y.1 Y.2
      let V := variance (outcomeAverage Y.1 Y.2) μ
      covariance Y.1 Y.2 μ = a*c*variance (Z 0) μ ∧
      V = Vn+(a*c/2)*variance (Z 0) μ ∧
      (0 < a*c → 0 < variance (Z 0) μ → Vn < V) ∧
      (a*c < 0 → 0 < variance (Z 0) μ → V < Vn) ∧
      (a*c = 0 ∨ variance (Z 0) μ = 0 → V = Vn))

end
end SAP.P032
