import SAP.P015a.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a
noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable
universe u v

def T1Statement : Prop :=
  rareWitness ∧
  (conditionalProbability (rareProbability (1/1000000)) binaryCovariate binaryTreatment 0 1 = 1/1000000 ∧
   conditionalProbability (rareProbability (1/1000000)) binaryCovariate binaryTreatment 0 0 = 1-1/1000000 ∧
   conditionalProbability (rareProbability (1/1000000)) binaryCovariate binaryTreatment 1 1 = 1/2 ∧
   conditionalProbability (rareProbability (1/1000000)) binaryCovariate binaryTreatment 1 0 = 1/2 ∧
   conditionalMean (rareProbability (1/1000000)) binaryCovariate
     (residualWeight (rareProbability (1/1000000)) binaryCovariate binaryTreatment) 0 =
     (1/1000000)*(1-1/1000000) ∧
   eventMass (effectiveLaw (rareProbability (1/1000000)) binaryCovariate binaryTreatment) (fun a => binaryCovariate a=0) =
     ((1/1000000)*(1-1/1000000))/((1/1000000)*(1-1/1000000)+1/4) ∧
   0 < mean (rareProbability (1/1000000)) (residualWeight (rareProbability (1/1000000)) binaryCovariate binaryTreatment))

def T2Statement : Prop :=
  multivaluedWitness.{u} ∧
  (conditionalMean uniformProbability binaryCovariate (residualWeight uniformProbability binaryCovariate multivaluedTreatment) 0 = 1/4 ∧
   conditionalMean uniformProbability binaryCovariate (residualWeight uniformProbability binaryCovariate multivaluedTreatment) 1 = 1)

def T3Statement : Prop :=
  fittedZeroWitness ∧
  (fun i => fittedResidual fittedZeroControls fittedZeroTreatment (leastSquares fittedZeroControls fittedZeroTreatment) i ^ 2) =
    (![0,0,1/4,1/4] : Fin 4 → ℝ)

def T4Statement : Prop :=
  positivityRepair.{u,v} ∧
  (∀ {Ω : Type u} {B : Type v} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (h₂ : MemLp D 2 P) (x : B) (hx : 0 < P {s | X s=x}),
    (cellVariance P X D x = 0 → ∀ d d' : ℝ, d ≠ d' →
      ¬ (0 < cellProbability P X D x d ∧ 0 < cellProbability P X D x d')) ∧
    ((∀ᵐ s ∂P, D s=0 ∨ D s=1) →
      cellProbability P X D x 0 = 1-cellProbability P X D x 1 ∧
      (0 < cellVariance P X D x ↔ 0 < cellProbability P X D x 0 ∧ 0 < cellProbability P X D x 1)) ∧
    (0 < (∫ s, discreteResidualWeight P X D s ∂P) →
      Integrable (discreteResidualWeight P X D) P →
      IsProbabilityMeasure (discreteEffectiveLaw P X D) ∧
      ((∀ᵐ s ∂P, D s=0 ∨ D s=1) →
        0 < discreteEffectiveLaw P X D {s | X s=x} →
        0 < cellVariance P X D x ∧
        0 < cellProbability (discreteEffectiveLaw P X D) X D x 0 ∧
        0 < cellProbability (discreteEffectiveLaw P X D) X D x 1)))

def T5Statement : Prop :=
  oddsWitness ∧
  (∀ η : ℝ, 0 < η → likelihoodMultiplier oddsInverseLink η = 1/η)

def T6Statement : Prop :=
  probitWitness ∧
  (Set.Nonempty {a : ℝ | 3/4 ≤ standardNormalCDF a} ∧
   BddBelow {a : ℝ | 3/4 ≤ standardNormalCDF a}) ∧
  (∀ v : Fin 3 → ℝ,
    HasDerivAt (fun t => logLikelihood probitDesign (fun _ => 8) probitCounts standardNormalCDF
      (fun j => (![0,0,probitQuantile] : Fin 3 → ℝ) j+t*v j))
      (∑ i, probitMultiplier (probitDesign.mulVec ![0,0,probitQuantile] i)*
        (probitCounts i-8*standardNormalCDF (probitDesign.mulVec ![0,0,probitQuantile] i))*probitDesign.mulVec v i) 0)

def T7Statement : Prop :=
  squareLinkWitness ∧
  (∀ θ : Fin 3 → ℝ,
    let γ : Fin 3 → ℝ := ![θ 0-θ 1/2, θ 1, θ 2-θ 1/4]
    γ 1 = θ 1 ∧ ∀ i : Fin 6,
      dotProduct (![1,squareLinkTreatment i,squareLinkCovariate i] : Fin 3 → ℝ) γ = squareLinkDesign.mulVec θ i) ∧
  (∀ α β γ : ℝ, ∃ θ : Fin 3 → ℝ,
    (![θ 0-θ 1/2, θ 1, θ 2-θ 1/4] : Fin 3 → ℝ) = ![α,β,γ]) ∧
  Integrable unitTreatment squareLinkUnitLaw ∧
  (∀ a ε : ℝ, Integrable (fun s => unitPotentialOutcome a ε (unitTreatment s) s) squareLinkUnitLaw)

def T8Statement : Prop :=
  (∀ (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hprob : ∀ η∈I, 0 < m η ∧ m η<1)
    (θ v : Fin (K+2) → ℝ) (hθ : ∀ i, W.mulVec θ i∈I),
  HasDerivAt (fun t : ℝ => logLikelihood W (fun _ => 1) Y m (θ+t • v))
      (∑ i, likelihoodMultiplier m (W.mulVec θ i)*(Y i-m (W.mulVec θ i))*W.mulVec v i) 0) ∧
  (∀ η : ℝ, HasDerivAt inverseLogit (inverseLogit η*(1-inverseLogit η)) η ∧
    likelihoodMultiplier inverseLogit η = 1) ∧
  (∀ {N : Type u} {Q : Type v} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (j₀ : Q) (hW : ∀ i, W i j₀=1)
    (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ) (carrier : ℝ → ℝ) (I support : Set ℝ)
    (hfamily : ValidCanonicalFamily ν κ s carrier I support)
    (Y : N → ℝ) (hY : ∀ i, Y i∈support) (θ : Q → ℝ)
    (hθ : ∀ i, W.mulVec θ i∈I) (hκ : ∀ i, DifferentiableAt ℝ κ (W.mulVec θ i)),
  (∀ v : Q → ℝ, HasDerivAt
      (fun t => canonicalSampleLikelihood W κ s (fun i => Y i) (fun i => carrier (Y i)) (fun j => θ j+t*v j))
      (s⁻¹*(∑ i, (Y i-deriv κ (W.mulVec θ i))*W.mulVec v i)) 0) ∧
    ((∀ j, s⁻¹*(∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0) ↔
      ∀ j, (∑ i, W i j*(Y i-deriv κ (W.mulVec θ i)))=0)) ∧
  (∀ (η : ℝ),
  (MeasureTheory.IsProbabilityMeasure
        (logisticResponseLaw η) ∧
      MeasureTheory.Integrable (fun y : ℝ => y)
        (logisticResponseLaw η) ∧
      (∫ y : ℝ, y ∂(logisticResponseLaw η)) =
        inverseLogit η ∧
      inverseLogit η =
        deriv (fun a : ℝ => Real.log (1 + Real.exp a)) η) ∧
    (MeasureTheory.IsProbabilityMeasure
        (poissonLogResponseLaw η) ∧
      MeasureTheory.Integrable (fun n : ℕ => (n : ℝ))
        (poissonLogResponseLaw η) ∧
      (∫ n : ℕ, (n : ℝ) ∂(poissonLogResponseLaw η)) =
        Real.exp η ∧
      Real.exp η = deriv Real.exp η)) ∧
  (∀ (N K : ℕ) (W : Matrix (Fin N) (Fin (K+2)) ℝ)
    (Y : Fin N → ℝ) (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (θ v : Fin (K+2) → ℝ),
  HasDerivAt (fun t => logLikelihood W (fun _ => 1) Y standardNormalCDF (fun j => θ j+t*v j))
      (∑ i, probitMultiplier (W.mulVec θ i)*(Y i-standardNormalCDF (W.mulVec θ i))*W.mulVec v i) 0 ∧
    ¬ ∃ c : ℝ, ∀ η : ℝ, probitMultiplier η = c) ∧
  (standardNormalCDF 0=1/2 ∧ deriv probitMultiplier 0=0) ∧
  (∀ (N K : ℕ)
    (W : Matrix (Fin N) (Fin (K+2)) ℝ) (Y : Fin N → ℝ)
    (hY : ∀ i, Y i=0 ∨ Y i=1) (hW : ∀ i, W i 0=1)
    (I : Set ℝ) (hI : IsOpen I) (m : ℝ → ℝ)
    (hm : DifferentiableOn ℝ m I) (hprob : ∀ η∈I, 0 < m η ∧ m η<1)
    (η₀ p₀ : ℝ) (hη : η₀∈I) (hp : 0<p₀) (hu : p₀<1) (hmean : m η₀=p₀)
    (hm₂ : DifferentiableAt ℝ (deriv m) η₀),
  let θ₀ : Fin (K+2) → ℝ := fun j => if j=0 then η₀ else 0
    let h := likelihoodMultiplier m
    let h₀ := h η₀
    let f₀ := deriv m η₀
    let h₁ := deriv h η₀
    let r := W.transpose.mulVec (fun i => Y i-p₀)
    let A := W.transpose*W
    let B : Matrix (Fin (K+2)) (Fin (K+2)) ℝ := fun j k => ∑ i, (Y i-p₀)*W i j*W i k
    ∀ δ : Fin (K+2) → ℝ,
      (fun j => ∑ i, W i j*firstTaylorPolynomial (fun η => h η*(Y i-m η)) η₀ (W.mulVec (θ₀+δ) i)) =
        h₀ • r+((-h₀*f₀) • A+h₁ • B).mulVec δ)

def T12Statement : Prop :=
  (∀ (p : ℝ), 0 < p → p < 1 →
    (∀ a, firstTaylorPolynomial inverseLogit (logOdds p) a = p+p*(1-p)*(a-logOdds p)) ∧
    (fun a => inverseLogit a-(p+p*(1-p)*(a-logOdds p))) =O[𝓝 (logOdds p)]
      (fun a => (a-logOdds p)^2)) ∧
  (∀ (p r ρ : ℝ) (hp : 0 < p) (hu : p < 1)
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρ : ρ < Real.sqrt ((logOdds p)^2+Real.pi^2)),
  let fc := fun z : ℂ => (1+Complex.exp (-z))⁻¹
    let M := sSup ((fun z : ℂ => ‖fc z‖) '' Metric.sphere ((logOdds p : ℝ) : ℂ) ρ)
    (((fun z : ℂ => ‖fc z‖) '' Metric.sphere ((logOdds p : ℝ) : ℂ) ρ).Nonempty →
    BddAbove ((fun z : ℂ => ‖fc z‖) '' Metric.sphere ((logOdds p : ℝ) : ℂ) ρ) →
    ((∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt fc s ((logOdds p : ℝ) : ℂ) ∧
      s.radius = ENNReal.ofReal (Real.sqrt ((logOdds p)^2+Real.pi^2))) ∧
    (∀ N : ℕ, ∀ a : ℝ, |a-logOdds p| ≤ r →
      |inverseLogit a-inverseLogitTaylor N (logOdds p) a| ≤ M*(r/ρ)^(N+1)/(1-r/ρ)) ∧
    Tendsto (fun N : ℕ => M*(r/ρ)^(N+1)/(1-r/ρ)) atTop (𝓝 0))))

def T13Statement : Prop :=
  ∀ (p : ℝ) (hp : 0 < p) (hu : p < 1),
  (∀ a, HasDerivAt inverseLogit (Real.exp a/(1+Real.exp a)^2) a) ∧
    inverseLogit (logOdds p) = p ∧
    deriv inverseLogit (logOdds p) = Real.exp (logOdds p)/(1+Real.exp (logOdds p))^2 ∧
    deriv inverseLogit (logOdds p) = p*(1-p) ∧
    (∀ a, firstTaylorPolynomial inverseLogit (logOdds p) a = p+p*(1-p)*(a-logOdds p) ∧
      firstTaylorPolynomial inverseLogit (logOdds p) a = (p-p*(1-p)*logOdds p)+p*(1-p)*a) ∧
    logOdds (1/2) = 0 ∧
    Real.exp (logOdds (1/2))/(1+logOdds (1/2))^2 = 1 ∧
    deriv inverseLogit (logOdds (1/2)) = 1/4

def T16Statement : Prop :=
  (10800420763/10000000000 < Real.exp (77/1000) ∧
    Real.exp (77/1000) < 10800420765/10000000000 ∧
    (10800420765/10000000000 : ℝ) < 6/5 ∧
    800420763/100000000 < 100*(Real.exp (77/1000)-1) ∧
    100*(Real.exp (77/1000)-1) < 800420765/100000000) ∧
  (∀ (α β d controls : ℝ),
  Real.exp (α+β*(d+1)+controls)/Real.exp (α+β*d+controls) = Real.exp β) ∧
  (let W : Matrix (Fin 4) (Fin 2) ℝ := !![1,0;1,0;1,1;1,1]
    let S : Fin 4 → ℝ := ![1,1,0,3]
    let Y := fun i => Real.log ((1+S i)/2)
    leastSquares W Y 1=0 ∧ Real.exp (leastSquares W Y 1)=1 ∧
    (Real.log (1/2)+Real.log 2)/2=0 ∧
    (S 0+S 1)/2=1 ∧ (S 2+S 3)/2=3/2 ∧ ((3/2:ℝ)/1-1)*100=50) ∧
  (let W : Matrix (Fin 4) (Fin 2) ℝ := !![1,0;1,0;1,1;1,1]; (W.transpose*W).det = 4)

def T19Statement : Prop :=
  ∀ {Ω : Type u} {B : Type v} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → ℝ) (X : Ω → B),
    Measurable D → Measurable X → MemLp D 2 P →
    P[populationResidualWeight P D X | MeasurableSpace.comap X inferInstance] = conditionalTreatmentVariance P D X ∧
    ((∀ᵐ s ∂P, D s=0 ∨ D s=1) → conditionalTreatmentVariance P D X =ᵐ[P]
      fun s => P[D | MeasurableSpace.comap X inferInstance] s*
        (1-P[D | MeasurableSpace.comap X inferInstance] s))

end
end SAP.P015a
