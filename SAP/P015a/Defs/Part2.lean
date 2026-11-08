import SAP.P015a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000

def rareWitness : Prop :=
  (IsProbabilityVector (rareProbability (1/1000000)) ∧
    (∀ a d, rarePotentialOutcome a d = rarePotentialOutcome a 0 + (1 + binaryCovariate a) * d) ∧
    ConditionalIndependent (rareProbability (1/1000000)) binaryCovariate
      (fun a => (rarePotentialOutcome a 0, 1 + binaryCovariate a)) binaryTreatment ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      conditionalMean (rareProbability (1/1000000)) binaryCovariate binaryTreatment x =
        1/1000000 + (1/2 - 1/1000000) * x ∧
      0 < conditionalProbability (rareProbability (1/1000000)) binaryCovariate binaryTreatment x 0 ∧
      0 < conditionalProbability (rareProbability (1/1000000)) binaryCovariate binaryTreatment x 1) ∧
    conditionalMean (rareProbability (1/1000000)) binaryCovariate
      (residualWeight (rareProbability (1/1000000)) binaryCovariate binaryTreatment) 0 = 999999/1000000000000 ∧
    conditionalMean (rareProbability (1/1000000)) binaryCovariate
      (residualWeight (rareProbability (1/1000000)) binaryCovariate binaryTreatment) 1 = 1/4 ∧
    eventMass (rareProbability (1/1000000)) (fun a => binaryCovariate a = 0) = 1/2 ∧
    eventMass (effectiveLaw (rareProbability (1/1000000)) binaryCovariate binaryTreatment)
      (fun a => binaryCovariate a = 0) = 999999/250000999999 ∧
    (999999/250000999999 : ℝ) < 1/250000 ∧
    rareIPW (1/1000000) = ![0,1000000,-4,8] ∧
    mean (rareProbability (1/1000000)) (fun a => 1+binaryCovariate a) = 3/2 ∧
    mean (rareProbability (1/1000000)) (rareIPW (1/1000000)) = 3/2 ∧
    mean (rareProbability (1/1000000)) (fun a => rareIPW (1/1000000) a ^ 2) = 500020 ∧
    variance (rareProbability (1/1000000)) (rareIPW (1/1000000)) = 2000071/4 ∧
    mean (effectiveLaw (rareProbability (1/1000000)) binaryCovariate binaryTreatment)
      (fun a => 1+binaryCovariate a) = 500000999999/250000999999 ∧
    (500000999999/250000999999 : ℝ) ≠ 3/2) ∧
  (∀ (ε : ℝ) (hε : 0 < ε) (hu : ε < 1/2),
    IsProbabilityVector (rareProbability ε) ∧
    (∀ a d, rarePotentialOutcome a d = rarePotentialOutcome a 0+(1+binaryCovariate a)*d) ∧
    ConditionalIndependent (rareProbability ε) binaryCovariate (fun a => (rarePotentialOutcome a 0,1+binaryCovariate a)) binaryTreatment ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      conditionalMean (rareProbability ε) binaryCovariate binaryTreatment x = ε+(1/2-ε)*x ∧
      0 < conditionalProbability (rareProbability ε) binaryCovariate binaryTreatment x 0 ∧
      0 < conditionalProbability (rareProbability ε) binaryCovariate binaryTreatment x 1) ∧
    eventMass (effectiveLaw (rareProbability ε) binaryCovariate binaryTreatment) (fun a => binaryCovariate a=0) =
      ε*(1-ε)/(ε*(1-ε)+1/4) ∧
    0 < eventMass (effectiveLaw (rareProbability ε) binaryCovariate binaryTreatment) (fun a => binaryCovariate a=0) ∧
    eventMass (effectiveLaw (rareProbability ε) binaryCovariate binaryTreatment) (fun a => binaryCovariate a=0) < 4*ε) ∧
  (let p := rareProbability (1/1000000);
    let W : Matrix (Fin 4) (Fin 3) ℝ := fun i => ![1,binaryTreatment i,binaryCovariate i];
    Matrix.det (fun j k => mean p (fun i => W i j*W i k)) ≠ 0 ∧
    populationCoefficients p W (fun i => rarePotentialOutcome i (binaryTreatment i)) 1 = 500000999999/250000999999) ∧
  (∀ (n : ℕ) (hn : 1 ≤ n),
    IsProbabilityVector (independentDrawLaw (rareProbability (1/1000000)) n) ∧
    mean (independentDrawLaw (rareProbability (1/1000000)) n)
      (empiricalMean (rareIPW (1/1000000)) n) = 3/2 ∧
    variance (independentDrawLaw (rareProbability (1/1000000)) n)
      (empiricalMean (rareIPW (1/1000000)) n) = 2000071/(4*n) ∧
    (∀ δ : ℝ, 0 < δ → eventMass (independentDrawLaw (rareProbability (1/1000000)) n)
      (fun a => δ ≤ |empiricalMean (rareIPW (1/1000000)) n a-3/2|) ≤
        2000071/(4*n*δ^2))) ∧
  (∀ (δ : ℝ) (hδ : 0 < δ),
    Tendsto (fun n : ℕ => eventMass (independentDrawLaw (rareProbability (1/1000000)) n)
      (fun a => δ ≤ |empiricalMean (rareIPW (1/1000000)) n a-3/2|)) atTop (𝓝 0))

def multivaluedWitness : Prop :=
  (IsProbabilityVector uniformProbability ∧
    (∀ a, conditionalMean uniformProbability binaryCovariate multivaluedTreatment (binaryCovariate a) = 1/2 + binaryCovariate a/2) ∧
    residualWeight uniformProbability binaryCovariate multivaluedTreatment = ![1/4,1/4,1,1] ∧
    (∀ a, 0 < residualWeight uniformProbability binaryCovariate multivaluedTreatment a) ∧
    mean uniformProbability (residualWeight uniformProbability binaryCovariate multivaluedTreatment) = 5/8 ∧
    effectiveLaw uniformProbability binaryCovariate multivaluedTreatment = ![1/10,1/10,2/5,2/5] ∧
    eventMass (effectiveLaw uniformProbability binaryCovariate multivaluedTreatment) (fun a => binaryCovariate a = 0) = 1/5 ∧
    eventMass (effectiveLaw uniformProbability binaryCovariate multivaluedTreatment) (fun a => binaryCovariate a = 1) = 4/5 ∧
    conditionalProbability uniformProbability binaryCovariate multivaluedTreatment 1 1 = 0 ∧
    conditionalProbability (effectiveLaw uniformProbability binaryCovariate multivaluedTreatment) binaryCovariate multivaluedTreatment 1 1 = 0 ∧
    ConditionalIndependent uniformProbability binaryCovariate (fun a => (outcomeWorldA a 0, outcomeWorldA a 1, outcomeWorldA a 2)) multivaluedTreatment ∧
    ConditionalIndependent uniformProbability binaryCovariate (fun a => (outcomeWorldB a 0, outcomeWorldB a 1, outcomeWorldB a 2)) multivaluedTreatment ∧
    (∀ a, outcomeWorldA a (multivaluedTreatment a) = multivaluedTreatment a ∧ outcomeWorldB a (multivaluedTreatment a) = multivaluedTreatment a) ∧
    mean uniformProbability (effectContrast outcomeWorldA 0 1) = 1 ∧
    mean uniformProbability (effectContrast outcomeWorldB 0 1) = 2 ∧
    mean (effectiveLaw uniformProbability binaryCovariate multivaluedTreatment) (effectContrast outcomeWorldA 0 1) = 1 ∧
    mean (effectiveLaw uniformProbability binaryCovariate multivaluedTreatment) (effectContrast outcomeWorldB 0 1) = 13/5) ∧
  ((∀ d : ℝ, (0 < conditionalProbability uniformProbability binaryCovariate multivaluedTreatment 0 d ∧
      0 < conditionalProbability uniformProbability binaryCovariate multivaluedTreatment 1 d) ↔ d=0) ∧
    (∀ d : ℝ, (0 < conditionalProbability (effectiveLaw uniformProbability binaryCovariate multivaluedTreatment) binaryCovariate multivaluedTreatment 0 d ∧
      0 < conditionalProbability (effectiveLaw uniformProbability binaryCovariate multivaluedTreatment) binaryCovariate multivaluedTreatment 1 d) ↔ d=0)) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (draw : ℕ → Ω → Fin 4)
    (hdraw : UniformIndependentSampling P draw) (T : ∀ n : ℕ, (Fin n → ℝ × ℝ × ℝ) → ℝ),
    ¬ (TendstoInMeasure P
      (fun n s => T n (fun i => observedTriple outcomeWorldA (draw i s))) atTop (fun _ => (1:ℝ)) ∧
      TendstoInMeasure P
      (fun n s => T n (fun i => observedTriple outcomeWorldB (draw i s))) atTop (fun _ => (2:ℝ))) ∧
    ¬ (TendstoInMeasure P
      (fun n s => T n (fun i => observedTriple outcomeWorldA (draw i s))) atTop (fun _ => (1:ℝ)) ∧
      TendstoInMeasure P
      (fun n s => T n (fun i => observedTriple outcomeWorldB (draw i s))) atTop (fun _ => (13/5:ℝ))))

def fittedZeroWitness : Prop :=
  (IsProbabilityVector uniformProbability ∧
    (∀ x ∈ ({0,1} : Finset ℝ), ∀ d ∈ ({0,1} : Finset ℝ),
      conditionalProbability uniformProbability binaryCovariate binaryTreatment x d = 1/2) ∧
    (∀ x ∈ ({0,1} : Finset ℝ),
      conditionalMean uniformProbability binaryCovariate (residualWeight uniformProbability binaryCovariate binaryTreatment) x = 1/4) ∧
    (1/4 : ℝ)^4 = 1/256 ∧ (0 : ℝ) < 1/256 ∧
    fittedZeroControls.transpose * fittedZeroControls = !![4,2;2,2] ∧
    fittedZeroControls.transpose.mulVec fittedZeroTreatment = ![1,1] ∧
    (!![4,2;2,2] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![0,1/2] = ![1,1] ∧
    (fittedZeroControls.transpose * fittedZeroControls).det ≠ 0 ∧
    fittedResidual fittedZeroControls fittedZeroTreatment ![0,1/2] = ![0,0,-1/2,1/2] ∧
    (fun a => fittedResidual fittedZeroControls fittedZeroTreatment ![0,1/2] a ^ 2) = ![0,0,1/4,1/4] ∧
    fittedZeroDesign.transpose * fittedZeroDesign = !![4,1,2;1,1,1;2,1,2] ∧
    (fittedZeroDesign.transpose * fittedZeroDesign).det = 2) ∧
  (leastSquares fittedZeroControls fittedZeroTreatment=![0,1/2] ∧
    fittedResidual fittedZeroControls fittedZeroTreatment (leastSquares fittedZeroControls fittedZeroTreatment)=![0,0,-1/2,1/2] ∧
    independentDrawLaw uniformProbability 4 (![0,0,2,3] : Fin 4 → Fin 4)=1/256) ∧
  (∀ i : Fin 4, fittedZeroControls i 1=binaryCovariate ((![0,0,2,3] : Fin 4 → Fin 4) i) ∧
      fittedZeroTreatment i=binaryTreatment ((![0,0,2,3] : Fin 4 → Fin 4) i))

def oddsWitness : Prop :=
  ((∀ i, 0 < oddsDesign.mulVec ![1,0,1] i) ∧
    (∀ i, 0 < oddsCounts i ∧ oddsCounts i < 12) ∧
    residualEquation oddsDesign (fun _ => 12) oddsCounts oddsInverseLink ![1,0,1] = 0 ∧
    likelihoodScore oddsDesign (fun _ => 12) oddsCounts oddsInverseLink ![1,0,1] = ![2/3,1/3,-2/3] ∧
    likelihoodScore oddsDesign (fun _ => 12) oddsCounts oddsInverseLink ![1,0,1] ≠ 0) ∧
  (¬ ∀ θ : Fin 3 → ℝ, (∀ i, 0 < oddsDesign.mulVec θ i) →
    logLikelihood oddsDesign (fun _ => 12) oddsCounts oddsInverseLink θ ≤
      logLikelihood oddsDesign (fun _ => 12) oddsCounts oddsInverseLink ![1,0,1]) ∧
  ((oddsDesign.transpose*oddsDesign).det = 36) ∧
  ((∀ i : Fin 2 × Fin 3, oddsDesign i 0=1 ∧ (oddsDesign i 1=0 ∨ oddsDesign i 1=1) ∧
      oddsCounts i = (if i.2=0 then (7:ℝ) else if i.2=1 then 6 else 10)) ∧
    (∀ i : Fin 2 × Fin 3, oddsInverseLink (oddsDesign.mulVec ![1,0,1] i)=
      (![1/2,2/3,3/4] : Fin 3 → ℝ) i.2) ∧
    ((12:ℝ) • (oddsDesign.transpose*oddsDesign)).det=62208 ∧
    (∀ v : Fin 3 → ℝ, HasDerivAt
      (fun t => logLikelihood oddsDesign (fun _ => 12) oddsCounts oddsInverseLink
        (fun j => (![1,0,1] : Fin 3 → ℝ) j+t*v j))
      (dotProduct (![2/3,1/3,-2/3] : Fin 3 → ℝ) v) 0))

def probitWitness : Prop :=
  (0 < probitQuantile ∧ probitQuantile < 7/10 ∧
    standardNormalCDF (-probitQuantile) = 1/4 ∧ standardNormalCDF 0 = 1/2 ∧ standardNormalCDF probitQuantile = 3/4 ∧
    residualEquation probitDesign (fun _ => 8) probitCounts standardNormalCDF ![0,0,probitQuantile] = 0 ∧
    likelihoodScore probitDesign (fun _ => 8) probitCounts standardNormalCDF ![0,0,probitQuantile] =
      ![4*(probitMultiplier probitQuantile-probitMultiplier 0),2*(probitMultiplier probitQuantile-probitMultiplier 0),0] ∧
    probitMultiplier probitQuantile = (16/3)*standardNormalDensity probitQuantile ∧ probitMultiplier 0 = 4*standardNormalDensity 0 ∧
    13/625 < 2*(probitMultiplier probitQuantile-probitMultiplier 0) ∧
    ¬ ∀ θ : Fin 3 → ℝ,
      logLikelihood probitDesign (fun _ => 8) probitCounts standardNormalCDF θ ≤
      logLikelihood probitDesign (fun _ => 8) probitCounts standardNormalCDF ![0,0,probitQuantile]) ∧
  ((∀ i : Fin 2 × Fin 3, probitDesign i 0=1 ∧ (probitDesign i 1=0 ∨ probitDesign i 1=1) ∧
      0<probitCounts i ∧ probitCounts i<8) ∧
    ((8:ℝ) • (probitDesign.transpose*probitDesign)).det=18432)

def squareLinkWitness : Prop :=
  (SquareLinkMLDerivative (1/16) (120/119) ∧ SquareLinkMLDerivative 0 1 ∧
    (∀ ε, |ε| ≤ 1/16 → mean squareLinkProbability (squareLinkResponseProbability (1/16) ε) = 1/4) ∧
    (∀ ε, |ε| ≤ 1/16 → populationCoefficients squareLinkProbability squareLinkDesign (squareLinkResponseProbability (1/16) ε) 1 = ε) ∧
    (120/119 : ℝ) ≠ 1) ∧
  (IsProbabilityVector squareLinkProbability ∧
    (fun j k => mean squareLinkProbability (fun i => squareLinkDesign i j*squareLinkDesign i k)) =
      (!![1,0,0;0,5/24,0;0,0,2/3] : Matrix (Fin 3) (Fin 3) ℝ) ∧
    (fun j k => mean squareLinkProbability
      (fun i => squareLinkDesign i j*squareLinkDesign i k*(squareLinkBaseline (1/16) (squareLinkCovariate i)-1/4))) =
      (!![0,0,0;0,-1/384,0;0,0,1/24] : Matrix (Fin 3) (Fin 3) ℝ) ∧
    ((-32/9 : ℝ) • (!![0,0,0;0,-1/384,0;0,0,1/24] : Matrix (Fin 3) (Fin 3) ℝ) -
      (16/3 : ℝ) • !![1,0,0;0,5/24,0;0,0,2/3]) = !![-16/3,0,0;0,-119/108,0;0,0,-100/27] ∧
    (∀ t : Fin 3 → ℝ,
      (!![-16/3,0,0;0,-119/108,0;0,0,-100/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec t+
        ![0,10/9,0] = 0 ↔ t = ![0,120/119,0]) ∧
    (120/119 : ℝ) ≠ 1) ∧
  (∀ (ε : ℝ) (hε : |ε| ≤ 1/16),
    mean squareLinkProbability (squareLinkResponseProbability (1/16) ε)=1/4 ∧
    populationCoefficients squareLinkProbability squareLinkDesign (squareLinkResponseProbability (1/16) ε) 1=ε) ∧
  (IsProbabilityMeasure uniformUnitInterval) ∧
  (IsProbabilityMeasure squareLinkUnitLaw) ∧
  (∀ (a ε : ℝ) (ha : a=0 ∨ a=1/16) (hε : |ε|≤1/16),
    (∀ x ∈ ({-1,0,1} : Finset ℝ), squareLinkUnitLaw {s | unitCovariate s=x}=1/3) ∧
    (∀ᵐ s ∂squareLinkUnitLaw, unitTreatment s=0 ∨ unitTreatment s=1) ∧
    (∀ᵐ s ∂squareLinkUnitLaw, 0≤unitUniform s ∧ unitUniform s≤1) ∧
    (∀ u : ℝ, 0≤u → u≤1 →
      squareLinkUnitLaw {s | unitUniform s≤u}=ENNReal.ofReal u) ∧
    IndepFun unitUniform (fun s => (unitCovariate s,unitTreatment s)) squareLinkUnitLaw ∧
    CondIndepFun (MeasurableSpace.comap unitCovariate inferInstance)
      (Measurable.comap_le (show Measurable unitCovariate from measurable_fst.fst))
      (fun s => (unitPotentialOutcome a ε 0 s,unitEffect a ε s)) unitTreatment squareLinkUnitLaw ∧
    squareLinkUnitLaw[unitTreatment | MeasurableSpace.comap unitCovariate inferInstance] =ᵐ[squareLinkUnitLaw]
      (fun s => squareLinkPropensity (unitCovariate s)) ∧
    (∀ᵐ s ∂squareLinkUnitLaw, unitPotentialOutcome a ε (unitTreatment s) s=
      unitPotentialOutcome a ε 0 s+unitEffect a ε s*unitTreatment s) ∧
    squareLinkUnitLaw[(fun s => unitPotentialOutcome a ε (unitTreatment s) s) |
      MeasurableSpace.comap (fun s => (unitCovariate s,unitTreatment s)) inferInstance] =ᵐ[squareLinkUnitLaw]
      (fun s => squareLinkBaseline a (unitCovariate s)+ε*(unitTreatment s-squareLinkPropensity (unitCovariate s))) ∧
    (∫ s, unitPotentialOutcome a ε (unitTreatment s) s ∂squareLinkUnitLaw)=1/4) ∧
  ((∀ η : ℝ, 0<η → η<1 → likelihoodMultiplier squareInverseLink η=2/(η*(1-η^2))) ∧
    deriv squareInverseLink (1/2)=1 ∧ likelihoodMultiplier squareInverseLink (1/2)=16/3 ∧
    deriv (likelihoodMultiplier squareInverseLink) (1/2)= -32/9 ∧
    squareLinkScore (1/16) 0 ![1/2,0,0]=0 ∧
    (∀ v : Fin 3 → ℝ, HasDerivAt
      (fun t => squareLinkScore (1/16) 0 (fun j => (![1/2,0,0] : Fin 3 → ℝ) j+t*v j))
      ((!![-16/3,0,0;0,-119/108,0;0,0,-100/27] : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) 0) ∧
    HasDerivAt (fun ε => squareLinkScore (1/16) ε ![1/2,0,0]) ![0,10/9,0] 0 ∧
    (∀ a ε θ v, (a=0 ∨ a=1/16) → |ε| ≤ 1/16 → SquareLinkAdmissible θ → HasDerivAt
      (fun t => squareLinkExpectedLikelihood a ε (fun j => θ j+t*v j)) (dotProduct (squareLinkScore a ε θ) v) 0))

def positivityRepair : Prop :=
  (∀ {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSingletonClass B] [Countable B] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (D : Ω → ℝ) (hX : Measurable X) (hD : Measurable D)
    (h₂ : MemLp D 2 P),
    (∀ x, 0 < P {s | X s = x} →
      (∀ d d', d ≠ d' → 0 < cellProbability P X D x d → 0 < cellProbability P X D x d' →
        0 < cellVariance P X D x) ∧
      (cellVariance P X D x = 0 → ∀ᵐ s ∂conditionalCellLaw P X x, D s = cellExpectation P X D x)) ∧
    ((∀ᵐ s ∂P, D s = 0 ∨ D s = 1) → ∀ x, 0 < P {s | X s = x} →
      cellVariance P X D x = cellProbability P X D x 1*(1-cellProbability P X D x 1) ∧
      (0 < cellVariance P X D x ↔ 0 < cellProbability P X D x 1 ∧ cellProbability P X D x 1 < 1)) ∧
    (0 < (∫ s, discreteResidualWeight P X D s ∂P) →
      Integrable (discreteResidualWeight P X D) P →
      ∀ x, 0 < P {s | X s = x} →
      (discreteEffectiveLaw P X D {s | X s = x}).toReal =
        (P {s | X s = x}).toReal*cellVariance P X D x/(∫ s, discreteResidualWeight P X D s ∂P) ∧
      (discreteEffectiveLaw P X D {s | X s = x} = 0 ↔ cellVariance P X D x = 0) ∧
      ((∀ᵐ s ∂P, D s = 0 ∨ D s = 1) →
        0 < cellProbability P X D x 1 → cellProbability P X D x 1 < 1 →
        cellProbability (discreteEffectiveLaw P X D) X D x 1 = 1-cellProbability P X D x 1 ∧
        cellProbability (discreteEffectiveLaw P X D) X D x 0 = cellProbability P X D x 1))) ∧
  (rareWitness) ∧
  (multivaluedWitness.{0}) ∧
  (fittedZeroWitness)

end
end SAP.P015a
