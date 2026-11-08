import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015a

noncomputable section
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000

def mean {A : Type*} [Fintype A] (p Z : A → ℝ) : ℝ := ∑ a, p a * Z a

def IsProbabilityVector {A : Type*} [Fintype A] (p : A → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

noncomputable def eventMass {A : Type*} [Fintype A] (p : A → ℝ) (E : A → Prop) : ℝ :=
  ∑ a, if E a then p a else 0

noncomputable def conditionalMean {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (Z : A → ℝ) (x : B) : ℝ :=
  mean p (fun a => if X a = x then Z a else 0) / eventMass p (fun a => X a = x)

noncomputable def conditionalProbability {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (D : A → ℝ) (x : B) (d : ℝ) : ℝ :=
  eventMass p (fun a => X a = x ∧ D a = d) / eventMass p (fun a => X a = x)

noncomputable def residualWeight {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (D : A → ℝ) : A → ℝ :=
  fun a => (D a - conditionalMean p X D (X a)) ^ 2

noncomputable def effectiveLaw {A B : Type*} [Fintype A] (p : A → ℝ)
    (X : A → B) (D : A → ℝ) : A → ℝ :=
  fun a => p a * residualWeight p X D a / mean p (residualWeight p X D)

noncomputable def ConditionalIndependent {A B C : Type*} [Fintype A]
    (p : A → ℝ) (X : A → B) (U : A → C) (D : A → ℝ) : Prop :=
  ∀ x u d, eventMass p (fun a => X a = x ∧ U a = u ∧ D a = d) *
      eventMass p (fun a => X a = x) =
    eventMass p (fun a => X a = x ∧ U a = u) *
      eventMass p (fun a => X a = x ∧ D a = d)

def effectContrast {A : Type*} (Y : A → ℝ → ℝ) (d d' : ℝ) : A → ℝ :=
  fun a => (Y a d' - Y a d) / (d' - d)

def inverseProbabilityVariable {A : Type*} (D Y e : A → ℝ) : A → ℝ :=
  fun a => D a * Y a / e a - (1 - D a) * Y a / (1 - e a)

def variance {A : Type*} [Fintype A] (p Z : A → ℝ) : ℝ :=
  mean p (fun a => (Z a - mean p Z) ^ 2)

def populationCoefficients {A Q : Type*} [Fintype A] [Fintype Q] [DecidableEq Q]
    (p : A → ℝ) (W : Matrix A Q ℝ) (Y : A → ℝ) : Q → ℝ :=
  Matrix.mulVec (((fun j k => mean p (fun i => W i j*W i k)) : Matrix Q Q ℝ)⁻¹)
    (fun j => mean p (fun i => W i j*Y i))

def binaryCovariate : Fin 4 → ℝ := ![0,0,1,1]

def binaryTreatment : Fin 4 → ℝ := ![0,1,0,1]

def rareProbability (ε : ℝ) : Fin 4 → ℝ := ![(1-ε)/2, ε/2, 1/4, 1/4]

def rarePotentialOutcome (a : Fin 4) (d : ℝ) : ℝ := 2 * binaryCovariate a + (1 + binaryCovariate a) * d

noncomputable def rareIPW (ε : ℝ) : Fin 4 → ℝ :=
  inverseProbabilityVariable binaryTreatment (fun a => rarePotentialOutcome a (binaryTreatment a))
    (fun a => ε + (1/2 - ε) * binaryCovariate a)

def uniformProbability : Fin 4 → ℝ := ![1/4,1/4,1/4,1/4]

def multivaluedTreatment : Fin 4 → ℝ := ![0,1,0,2]

def outcomeWorldA (_ : Fin 4) (d : ℝ) : ℝ := d

def outcomeWorldB (a : Fin 4) (d : ℝ) : ℝ := if binaryCovariate a = 1 ∧ d = 1 then 3 else d

noncomputable def leastSquares {N Q : Type*} [Fintype N] [Fintype Q] [DecidableEq Q]
    (W : Matrix N Q ℝ) (Y : N → ℝ) : Q → ℝ :=
  (W.transpose * W)⁻¹.mulVec (W.transpose.mulVec Y)

def fittedResidual {N Q : Type*} [Fintype Q] (V : Matrix N Q ℝ)
    (D : N → ℝ) (ω : Q → ℝ) : N → ℝ := fun i => D i - V.mulVec ω i

def fittedZeroControls : Matrix (Fin 4) (Fin 2) ℝ := !![1,0; 1,0; 1,1; 1,1]

def fittedZeroDesign : Matrix (Fin 4) (Fin 3) ℝ := !![1,0,0; 1,0,0; 1,0,1; 1,1,1]

def fittedZeroTreatment : Fin 4 → ℝ := ![0,0,0,1]

def independentDrawLaw {A : Type*} [Fintype A] (p : A → ℝ) (n : ℕ) : (Fin n → A) → ℝ :=
  fun a => ∏ i, p (a i)

def empiricalMean {A : Type*} (Z : A → ℝ) (n : ℕ) (a : Fin n → A) : ℝ :=
  (∑ i, Z (a i))/(n : ℝ)

def observedTriple (Y : Fin 4 → ℝ → ℝ) (a : Fin 4) : ℝ × ℝ × ℝ :=
  (binaryCovariate a,multivaluedTreatment a,Y a (multivaluedTreatment a))

def UniformIndependentSampling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (draw : ℕ → Ω → Fin 4) : Prop :=
  (∀ i, Measurable (draw i)) ∧ iIndepFun draw P ∧
    ∀ i a, P {s | draw i s=a}=ENNReal.ofReal (uniformProbability a)

def inverseLogit : ℝ → ℝ := Real.sigmoid

def logOdds (p : ℝ) : ℝ := Real.log (p / (1-p))

def firstTaylorPolynomial (f : ℝ → ℝ) (c a : ℝ) : ℝ := f c + deriv f c * (a-c)

def bernoulliLogLikelihood (m : ℝ → ℝ) (n k η : ℝ) : ℝ :=
  k*Real.log (m η) + (n-k)*Real.log (1-m η)

def likelihoodMultiplier (m : ℝ → ℝ) (η : ℝ) : ℝ := deriv m η/(m η*(1-m η))

def canonicalContribution (κ : ℝ → ℝ) (s y r η : ℝ) : ℝ :=
  (y*η-κ η)/s+r

def residualEquation {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (n k : N → ℝ) (m : ℝ → ℝ) (θ : Q → ℝ) : Q → ℝ :=
  fun j => ∑ i, W i j*(k i-n i*m (W.mulVec θ i))

def likelihoodScore {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (n k : N → ℝ) (m : ℝ → ℝ) (θ : Q → ℝ) : Q → ℝ :=
  fun j => ∑ i, W i j*likelihoodMultiplier m (W.mulVec θ i)*(k i-n i*m (W.mulVec θ i))

def logLikelihood {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (n k : N → ℝ) (m : ℝ → ℝ) (θ : Q → ℝ) : ℝ :=
  ∑ i, bernoulliLogLikelihood m (n i) (k i) (W.mulVec θ i)

def oddsDesign : Matrix (Fin 2 × Fin 3) (Fin 3) ℝ :=
  fun i => ![1,(i.1 : ℝ),(i.2 : ℝ)]

def oddsCounts (i : Fin 2 × Fin 3) : ℝ := ![7,6,10] i.2

def oddsInverseLink (η : ℝ) : ℝ := η/(1+η)

def standardNormalCDF (a : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) a

def standardNormalDensity (a : ℝ) : ℝ := ProbabilityTheory.gaussianPDFReal 0 1 a

def probitQuantile : ℝ := sInf {a : ℝ | 3/4 ≤ standardNormalCDF a}

def probitDesign : Matrix (Fin 2 × Fin 3) (Fin 3) ℝ :=
  fun i => ![1,(i.1 : ℝ),(i.2 : ℝ)-1]

def probitCounts (i : Fin 2 × Fin 3) : ℝ := ![3,2,7] i.2

def probitMultiplier (η : ℝ) : ℝ := standardNormalDensity η/(standardNormalCDF η*(1-standardNormalCDF η))

def squareLinkCovariate : Fin 6 → ℝ := ![-1,-1,0,0,1,1]

def squareLinkTreatment : Fin 6 → ℝ := ![0,1,0,1,0,1]

def squareLinkProbability : Fin 6 → ℝ := ![1/4,1/12,1/6,1/6,1/12,1/4]

def squareLinkPropensity (x : ℝ) : ℝ := 1/2+x/4

def squareLinkBaseline (a x : ℝ) : ℝ := 1/4+a*(3*x^2-2)

def squareLinkDesign : Matrix (Fin 6) (Fin 3) ℝ := fun i => ![1,squareLinkTreatment i-squareLinkPropensity (squareLinkCovariate i),squareLinkCovariate i]

def squareLinkPotential (a ε x u d : ℝ) : ℝ := if u ≤ squareLinkBaseline a x+ε*(d-squareLinkPropensity x) then 1 else 0

def squareLinkResponseProbability (a ε : ℝ) (i : Fin 6) : ℝ :=
  squareLinkBaseline a (squareLinkCovariate i)+ε*(squareLinkTreatment i-squareLinkPropensity (squareLinkCovariate i))

def squareInverseLink (η : ℝ) : ℝ := η^2

def squareLinkExpectedLikelihood (a ε : ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  ∑ i, squareLinkProbability i*bernoulliLogLikelihood squareInverseLink 1 (squareLinkResponseProbability a ε i) (squareLinkDesign.mulVec θ i)

def SquareLinkAdmissible (θ : Fin 3 → ℝ) : Prop := ∀ i, 0 < squareLinkDesign.mulVec θ i ∧ squareLinkDesign.mulVec θ i < 1

def SquareLinkMLDerivative (a b : ℝ) : Prop :=
  ∃ θ : ℝ → Fin 3 → ℝ, θ 0 = ![1/2,0,0] ∧
    (∃ r : ℝ, 0 < r ∧ r ≤ 1/16 ∧ ∀ ε, |ε| < r → SquareLinkAdmissible (θ ε) ∧
      (∀ t, SquareLinkAdmissible t → squareLinkExpectedLikelihood a ε t ≤ squareLinkExpectedLikelihood a ε (θ ε)) ∧
      (∀ t, SquareLinkAdmissible t → squareLinkExpectedLikelihood a ε t = squareLinkExpectedLikelihood a ε (θ ε) → t = θ ε)) ∧
    HasDerivAt (fun ε => θ ε 1) b 0

def conditionalCellLaw {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B) (x : B) : Measure Ω :=
  (P {s | X s = x})⁻¹ • P.restrict {s | X s = x}

def cellExpectation {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (x : B) : ℝ := ∫ s, D s ∂conditionalCellLaw P X x

def cellVariance {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (x : B) : ℝ := ∫ s, (D s-cellExpectation P X D x)^2 ∂conditionalCellLaw P X x

def cellProbability {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (x : B) (d : ℝ) : ℝ := (conditionalCellLaw P X x {s | D s = d}).toReal

def discreteResidualWeight {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) (s : Ω) : ℝ := (D s-cellExpectation P X D (X s))^2

def discreteEffectiveLaw {Ω B : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → B)
    (D : Ω → ℝ) : Measure Ω :=
  (ENNReal.ofReal (∫ s, discreteResidualWeight P X D s ∂P))⁻¹ •
    P.withDensity (fun s => ENNReal.ofReal (discreteResidualWeight P X D s))

def inverseLogitTaylor (N : ℕ) (c a : ℝ) : ℝ := taylorWithinEval inverseLogit N Set.univ c a

def canonicalSampleLikelihood {N Q : Type*} [Fintype N] [Fintype Q]
    (W : Matrix N Q ℝ) (κ : ℝ → ℝ) (s : ℝ) (Y carrier : N → ℝ) (θ : Q → ℝ) : ℝ :=
  ∑ i, canonicalContribution κ s (Y i) (carrier i) (W.mulVec θ i)

def ValidCanonicalFamily (ν : Measure ℝ) (κ : ℝ → ℝ) (s : ℝ) (carrier : ℝ → ℝ)
    (I support : Set ℝ) : Prop :=
  0<s ∧ IsOpen I ∧ MeasurableSet support ∧ ν supportᶜ=0 ∧
    ∀ η ∈ I, Integrable (fun y => Real.exp (canonicalContribution κ s y (carrier y) η)) ν ∧
      (∫ y, Real.exp (canonicalContribution κ s y (carrier y) η) ∂ν)=1

def populationResidualWeight {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) (D : Ω → ℝ) (X : Ω → B) (s : Ω) : ℝ :=
  (D s-P[D | MeasurableSpace.comap X inferInstance] s)^2

def conditionalTreatmentVariance {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) (D : Ω → ℝ) (X : Ω → B) : Ω → ℝ :=
  P[populationResidualWeight P D X | MeasurableSpace.comap X inferInstance]

def uniformUnitInterval : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance uniformUnitInterval_finite : IsFiniteMeasure uniformUnitInterval := by
  unfold uniformUnitInterval
  infer_instance

def squareLinkUnitLaw : Measure ((ℝ×ℝ)×ℝ) :=
  ∑ i : Fin 6, (squareLinkProbability i).toNNReal •
    (Measure.dirac (squareLinkCovariate i,squareLinkTreatment i)).prod uniformUnitInterval

instance squareLinkUnitLaw_finite : IsFiniteMeasure squareLinkUnitLaw := by
  unfold squareLinkUnitLaw
  infer_instance

def unitCovariate (s : (ℝ×ℝ)×ℝ) : ℝ := s.1.1

def unitTreatment (s : (ℝ×ℝ)×ℝ) : ℝ := s.1.2

def unitUniform (s : (ℝ×ℝ)×ℝ) : ℝ := s.2

def unitPotentialOutcome (a ε d : ℝ) (s : (ℝ×ℝ)×ℝ) : ℝ :=
  squareLinkPotential a ε (unitCovariate s) (unitUniform s) d

def unitEffect (a ε : ℝ) (s : (ℝ×ℝ)×ℝ) : ℝ :=
  unitPotentialOutcome a ε 1 s-unitPotentialOutcome a ε 0 s

def squareLinkScore (a ε : ℝ) (θ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => mean squareLinkProbability (fun i => squareLinkDesign i j*
    likelihoodMultiplier squareInverseLink (squareLinkDesign.mulVec θ i)*
      (squareLinkResponseProbability a ε i-squareInverseLink (squareLinkDesign.mulVec θ i)))

noncomputable def logisticResponseLaw (η : ℝ) : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0
    ⟨inverseLogit η, by
      constructor
      · exact (Real.sigmoid_pos η).le
      · exact (Real.sigmoid_lt_one η).le⟩

noncomputable def poissonLogResponseLaw (η : ℝ) : MeasureTheory.Measure ℕ :=
  ProbabilityTheory.poissonMeasure
    ⟨Real.exp η, (Real.exp_pos η).le⟩

end
end SAP.P015a
