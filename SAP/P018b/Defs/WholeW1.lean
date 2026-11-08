import Mathlib
import SAP.P018b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix.Norms.Elementwise

/-! Whole statements for W1. All probability assertions assume the usual
measure-theoretic conditions. Infinite moments are nonnegative extended integrals. -/

def wholeOverlap4 : Matrix (Fin 6) (Fin 6) ℝ :=
  fun d f => if (sixMembers d ∩ sixMembers f).Nonempty then 1 else 0

def wholeCycle : Fin 6 → ℝ := ![1,-1,0,0,-1,1]

def wholeInterceptX (E : Type) : E → Vec 1 := fun _ _ => 1

/-- Zero padding onto the first four labelled units; no subtraction of natural indices. -/
def wholePaddedY {N : ℕ} (d : Dyad N) : ℝ :=
  if (firstUnit d).val = 0 ∧ (secondUnit d).val = 1 then 1 else
  if (firstUnit d).val = 0 ∧ (secondUnit d).val = 2 then -1 else
  if (firstUnit d).val = 1 ∧ (secondUnit d).val = 3 then -1 else
  if (firstUnit d).val = 2 ∧ (secondUnit d).val = 3 then 1 else 0

/-- The six dyads, with the paper's ordering, as actual two-element subsets. -/
def wholeSixDyad (d : Fin 6) : Dyad 4 :=
  ⟨sixMembers d, by fin_cases d <;> norm_num [sixMembers, dyads]⟩

def wholeSimulationDesign {N : ℕ} (ω : SimulationIndex N 1 → ℝ) : Dyad N → Vec 2 :=
  fun d => ![1, |simulationX ω (firstUnit d) - simulationX ω (secondUnit d)|]

def wholeSimulationResponse {N : ℕ} (ω : SimulationIndex N 1 → ℝ) (d : Dyad N) : ℝ :=
  |simulationX ω (firstUnit d) - simulationX ω (secondUnit d)| + simulationError ω d 0

def wholeTwentyPoint : SimulationIndex 20 1 → ℝ
  | Sum.inl i => if i.val = 0 then 1 else if i.val = 1 then 2 else
      if i.val = 2 then 3 else if i.val = 3 then 4 else 5/2
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (d,_)) => wholePaddedY d

def wholeSimulationSlope (ω : SimulationIndex 20 1 → ℝ) : ℝ :=
  sampleVariance members (wholeSimulationDesign ω) (wholeSimulationResponse ω) 1 1

/-- P018-T17; p. 567 (PDF p. 4), equation (3) and the following sentence;
p. 570 (PDF p. 7), Fig. 1 caption.
All five negative-variance witnesses are asserted: the six-edge spectrum and cycle,
the intercept fit and every zero-padded extension, the full-rank two-coefficient
fit and negative definiteness, its bounded iid-unit population and labelled event,
and the N=20 normal-design witness with positive probability. The usual
measure-theoretic conditions are assumed. The covariance in (d) is also identified as the
Gaussian limit covariance and the limit of the linear-approximation targets;
ordinary finite-sample coefficient moments are not asserted. -/
def T17WholeStatement : Prop :=
  wholeOverlap4.charpoly =
    (Polynomial.X - Polynomial.C 5) * (Polynomial.X - Polynomial.C 1)^3 *
      (Polynomial.X + Polynomial.C 1)^2 ∧
  wholeOverlap4.mulVec wholeCycle = -wholeCycle ∧
  (∑ d, wholeCycle d) = 0 ∧ (∑ d, (wholeCycle d)^2) = 4 ∧
  (sampleGram (wholeInterceptX (Fin 6))).det = 6 ∧
  sampleOLS (wholeInterceptX (Fin 6)) wholeCycle = 0 ∧
  (∀ d, fittedResidual (wholeInterceptX (Fin 6)) wholeCycle d = wholeCycle d) ∧
  sampleVariance sixMembers (wholeInterceptX (Fin 6)) wholeCycle 0 0 = -1/9 ∧
  (sampleVariance sixMembers (wholeInterceptX (Fin 6)) wholeCycle 0 0 < 0) ∧
  (∀ N : ℕ, 4 < N →
    (sampleGram (wholeInterceptX (Dyad N))).det = Dreal N ∧ 0 < Dreal N ∧
    sampleOLS (wholeInterceptX (Dyad N)) wholePaddedY = 0 ∧
    (∀ d, fittedResidual (wholeInterceptX (Dyad N)) wholePaddedY d = wholePaddedY d) ∧
    sampleVariance members (wholeInterceptX (Dyad N)) wholePaddedY 0 0 = -4/(Dreal N)^2 ∧
    sampleVariance members (wholeInterceptX (Dyad N)) wholePaddedY 0 0 < 0) ∧
  negativeSampleFacts ∧
  meat sixMembers (fun d => score (negativeX d) (negativeE d)) = !![-34/25,-2;-2,-98/25] ∧
  (sampleVariance sixMembers negativeX negativeY).det = 52/15625 ∧
  0 < (sampleVariance sixMembers negativeX negativeY).det ∧
  Matrix.trace (sampleVariance sixMembers negativeX negativeY) < 0 ∧
  (-(sampleVariance sixMembers negativeX negativeY)).PosDef ∧
  (∀ j : Fin 2, ¬ ∃ r : ℝ, r^2 = sampleVariance sixMembers negativeX negativeY j j) ∧
  negativePopulationFacts ∧
  (∀ u v : Fin 4 × Bool, 0 ≤ finiteNegativeKernel.X u v 1 ∧
    finiteNegativeKernel.X u v 1 ≤ 3 ∧ -2 ≤ finiteNegativeKernel.Y u v ∧
    finiteNegativeKernel.Y u v ≤ 5) ∧
  (populationGram finiteNegativeKernel).det = 15/16 ∧
  projectionGamma finiteNegativeKernel = !![226/225,284/225;284/225,5971/3600] ∧
  (limitingTarget finiteNegativeKernel).det = 67072/50625 ∧
  (∀ ω : Fin 4 → Fin 4 × Bool, (∀ i, ω i = (i,true)) →
    (∀ d : Fin 6, design finiteNegativeKernel ω (wholeSixDyad d) = negativeX d) ∧
    (∀ d : Fin 6, response finiteNegativeKernel ω (wholeSixDyad d) = negativeY d)) ∧
  sampleGram (wholeSimulationDesign wholeTwentyPoint) = !![190,74;74,100] ∧
  (sampleGram (wholeSimulationDesign wholeTwentyPoint)).det = 13524 ∧
  sampleOLS (wholeSimulationDesign wholeTwentyPoint) (wholeSimulationResponse wholeTwentyPoint) =
    ![37/3381,3286/3381] ∧
  wholeSimulationSlope wholeTwentyPoint = -31032915283/43557147269307 ∧
  wholeSimulationSlope wholeTwentyPoint < 0 ∧
  0 < simulationLaw 20 1 {ω |
    (sampleGram (wholeSimulationDesign ω)).det ≠ 0 ∧ wholeSimulationSlope ω < 0} ∧
  Tendsto (trueTarget finiteNegativeKernel) atTop (𝓝 (limitingTarget finiteNegativeKernel)) ∧
  (∃ ν : Measure (Vec 2), centeredNormalLaw ν (limitingTarget finiteNegativeKernel) ∧
    weakLimit (unitSampleLaw finiteNegativeKernel)
      (fun N ω => Real.sqrt N • coefficientError finiteNegativeKernel ω) ν)

/-- The expanded diagonal-plus-neighbour middle factor, for actual regressor rows. -/
def wholeExpandedMeat {N k : ℕ} (X : Dyad N → Vec k) (e : Dyad N → ℝ) : Mat k :=
  ∑ d, ((e d)^2 • outer (X d) (X d) +
    ∑ f ∈ neighbors d, (e d * e f) • outer (X d) (X f))

/-- P018-T18; p. 567 (PDF p. 4), sentence after Proposition 1.
The incidence and score formulas express the symmetric estimator as a difference
of two positive semidefinite matrices. It can have negative fitted-OLS diagonals.
Truncation is contractive and preserves the stated probability limit; negative
diagonals become rare for a target bounded away from zero. A real standard error
exists precisely on the nonnegative domain. The optional truncated convention
changes finite-sample values and entails no universal coverage guarantee.
The usual measure-theoretic conditions are assumed. -/
def T18WholeStatement : Prop :=
  T18Statement ∧
  (∀ N k : ℕ, 2 ≤ N → ∀ (X : Dyad N → Vec k) (e : Dyad N → ℝ),
    let P := (sampleGram X)⁻¹
    wholeExpandedMeat X e = meat members (fun d => score (X d) (e d)) ∧
    P.transpose = P ∧
    (sandwich P (wholeExpandedMeat X e)).transpose = sandwich P (wholeExpandedMeat X e)) ∧
  (sampleGram negativeX).det ≠ 0 ∧
  ¬ (sampleVariance sixMembers negativeX negativeY).PosSemidef ∧
  (∀ {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
    (μ : ∀ N, Measure (Ω N)) (_hμ : ∀ N, IsProbabilityMeasure (μ N))
    (v : ∀ N, Ω N → ℝ) (V : ℕ → ℝ),
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, c ≤ V N) →
    inProbability μ (fun N ω => (N : ℝ)*v N ω - V N) →
    Tendsto (fun N => (μ N {ω | v N ω < 0}).toReal) atTop (𝓝 0)) ∧
  (∀ v : ℝ, (0 ≤ v → standardError v = some (Real.sqrt v)) ∧
    (v < 0 → standardError v = none ∧ (¬ ∃ r : ℝ, r^2 = v) ∧
      Real.sqrt (max v 0) = 0)) ∧
  (∀ m : ℕ, ∀ v : Fin m → ℝ,
    (univ.filter (fun j => standardError (v j) = none)).card =
      (univ.filter (fun j => v j < 0)).card) ∧
  (∀ c : ℝ,
    (unitSampleLaw finiteNegativeKernel 4 {ω |
      |sampleOLS (design finiteNegativeKernel ω) (response finiteNegativeKernel ω) 0 -
          populationBeta finiteNegativeKernel 0| >
      |c| * Real.sqrt (max
        (sampleVariance members (design finiteNegativeKernel ω) (response finiteNegativeKernel ω) 0 0) 0)}).toReal
        ≥ 1/4096)

/-! Explicit unit model for T19. `level` is M-1 and `label` is C-1. Hidden
unit coordinates are permitted; the four used coordinates have the exact joint law. -/
structure WholeRareModel (U : Type) [MeasurableSpace U] where
  μ : Measure U
  level : U → ℕ
  label : U → ℕ
  A : U → Bool
  B : U → Bool

def wholeRareLaw {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  IsProbabilityMeasure F.μ ∧ Measurable F.level ∧ Measurable F.label ∧
  Measurable F.A ∧ Measurable F.B ∧
  (∀ u, F.label u < F.level u + 1) ∧
  ∀ (m : ℕ) (c : Fin (m+1)) (a b : Bool),
    F.μ {u | F.level u = m ∧ F.label u = c.val ∧ F.A u = a ∧ F.B u = b} =
      ENNReal.ofReal ((2 : ℝ)^(-(m+1 : ℤ)) / ((m+1 : ℝ)*4))

def wholeRareDelta (m : ℕ) : ℝ := 1 / ((m : ℝ)^2 * (2 : ℝ)^(m*m+2))
def wholeRareSmall {U : Type} [MeasurableSpace U] (F : WholeRareModel U) (u v : U) : Prop :=
  F.level u = F.level v ∧ F.label u ≠ F.label v

instance {U : Type} [MeasurableSpace U] (F : WholeRareModel U) (u v : U) :
    Decidable (wholeRareSmall F u v) := inferInstanceAs (Decidable (_ ∧ _))

def wholeRareS {U : Type} [MeasurableSpace U] (F : WholeRareModel U) (u v : U) : ℝ :=
  if wholeRareSmall F u v then wholeRareDelta (F.level u+1) else 1

def wholeRareA {U : Type} [MeasurableSpace U] (F : WholeRareModel U) (u v : U) : ℝ :=
  if wholeRareSmall F u v then signValue (F.A u) + signValue (F.A v) else 0

def wholeRareKernel {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : RepeatedKernel U 2 :=
  ⟨F.μ, fun _ _ => 2,
    fun _ _ t u v => ![1,1+(if t.val=0 then wholeRareS F u v else -wholeRareS F u v)],
    fun _ _ t u v => signValue (F.B u)+signValue (F.B v)+
      (if t.val=0 then wholeRareA F u v else -wholeRareA F u v)⟩

def wholeRareScale {U : Type} [MeasurableSpace U] {N : ℕ}
    (F : WholeRareModel U) (ω : Fin N → U) (d : Dyad N) : ℝ :=
  wholeRareS F (ω (firstUnit d)) (ω (secondUnit d))
def wholeRareSignal {U : Type} [MeasurableSpace U] {N : ℕ}
    (F : WholeRareModel U) (ω : Fin N → U) (d : Dyad N) : ℝ :=
  wholeRareA F (ω (firstUnit d)) (ω (secondUnit d))
def wholeRareSsq {U : Type} [MeasurableSpace U] {N : ℕ}
    (F : WholeRareModel U) (ω : Fin N → U) : ℝ := ∑ d : Dyad N, (wholeRareScale F ω d)^2

def wholeRareMeanA {U : Type} [MeasurableSpace U] {N : ℕ}
    (F : WholeRareModel U) (ω : Fin N → U) : ℝ := (∑ i, signValue (F.A (ω i))) / N

def wholeRareMeanB {U : Type} [MeasurableSpace U] {N : ℕ}
    (F : WholeRareModel U) (ω : Fin N → U) : ℝ := (∑ i, signValue (F.B (ω i))) / N

def wholeRareEvent {U : Type} [MeasurableSpace U] (F : WholeRareModel U) (N m : ℕ) :
    Set (Fin N → U) :=
  {ω | (∀ i, F.level (ω i) = m) ∧ Function.Injective (fun i => F.label (ω i))}

def wholeRareDispersion {U : Type} [MeasurableSpace U] {N : ℕ}
    (F : WholeRareModel U) (ω : Fin N → U) : ℝ :=
  ∑ i, (signValue (F.A (ω i)) - wholeRareMeanA F ω)^2

def wholeRareQ {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : ℝ :=
  ∫ uv, (wholeRareS F uv.1 uv.2)^2 ∂ F.μ.prod F.μ

/-- Printed h_M, with M=m+1, used by the unit projection of the slope score. -/
def wholeRareh (m : ℕ) : ℝ :=
  (2 : ℝ)^(-(m+1 : ℤ)) * (1-1/(m+1 : ℝ)) * wholeRareDelta (m+1)

def wholeRareHterm (m : ℕ) : ℝ :=
  (2 : ℝ)^(-3*(m+1 : ℤ)) * (1-1/(m+1 : ℝ))^2 * (wholeRareDelta (m+1))^2

def wholeRareH : ℝ := ∑' m : ℕ, wholeRareHterm m

def wholeRareV {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : ℝ :=
  4*wholeRareH/(wholeRareQ F)^2

def wholeRareLimitMatrix {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Mat 2 :=
  !![4+wholeRareV F,-wholeRareV F;-wholeRareV F,wholeRareV F]

/-- Finite target normalizations and weighted estimators, matching S6--S7. -/
def wholeRepeatedH {U : Type} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : Mat k :=
  (repeatedL R N)⁻¹ • meanMat (repeatedLaw R N) (repeatedGram R)
def wholeRepeatedTarget {U : Type} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) (N : ℕ) : Mat k :=
  ((N : ℝ)/(repeatedL R N)^2) • sandwich (wholeRepeatedH R N)⁻¹
    (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N, repeatedBlockScore R (repeatedBeta R N) ω d))
def wholeWeightedGram {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (ω : Fin N → U) : Mat k :=
  ∑ d : Dyad N, ∑ t, w d t • outer (repeatedX R ω d t) (repeatedX R ω d t)
def wholeWeightedXY {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (ω : Fin N → U) : Vec k :=
  ∑ d : Dyad N, ∑ t, score (repeatedX R ω d t) (w d t * repeatedY R ω d t)
def wholeWeightedOLS {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (ω : Fin N → U) : Vec k :=
  (wholeWeightedGram R w ω)⁻¹.mulVec (wholeWeightedXY R w ω)
def wholeWeightedBeta {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Vec k :=
  (meanMat (repeatedLaw R N) (wholeWeightedGram R w))⁻¹.mulVec
    (meanVec (repeatedLaw R N) (wholeWeightedXY R w))
def wholeWeightedBlockScore {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (ω : Fin N → U) (d : Dyad N) : Vec k :=
  ∑ t, score (repeatedX R ω d t) (w d t * (repeatedY R ω d t - dot (repeatedX R ω d t) β))
def wholeWeightedH {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Mat k :=
  (Dreal N)⁻¹ • meanMat (repeatedLaw R N) (wholeWeightedGram R w)
def wholeWeightedVariance {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (ω : Fin N → U) : Mat k :=
  sandwich (wholeWeightedGram R w ω)⁻¹
    (meat members (wholeWeightedBlockScore R w (wholeWeightedOLS R w ω) ω))
def wholeWeightedTarget {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) : Mat k :=
  ((N : ℝ)/(Dreal N)^2) • sandwich (wholeWeightedH R w)⁻¹
    (varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N,
      wholeWeightedBlockScore R w (wholeWeightedBeta R w) ω d))

/-- Independent uniform auxiliary labels, with records in the two ordered directions.
Record 0 goes from the first endpoint to the second; record 1 reverses it.
The plus record goes from smaller to larger auxiliary label. On ties both records
use the plus value, so the common directed-kernel identity holds pointwise; ties
have probability zero under the auxiliary law. -/
def wholeRareDirected {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : RepeatedKernel (U × ℝ) 2 :=
  ⟨F.μ.prod (volume.restrict (Set.Icc (0 : ℝ) 1)), fun _ _ => 2,
    fun N d t u v => (wholeRareKernel F).X N d
      (if u.2 = v.2 then (0 : Fin 2) else if u.2 < v.2 then t else Fin.rev t) u.1 v.1,
    fun N d t u v => (wholeRareKernel F).Y N d
      (if u.2 = v.2 then (0 : Fin 2) else if u.2 < v.2 then t else Fin.rev t) u.1 v.1⟩

def wholeRareMoments {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N : ℕ, 3 ≤ N →
    (∫⁻ ω, ENNReal.ofReal ((repeatedOLS (wholeRareKernel F) ω 1)^2) ∂ repeatedLaw (wholeRareKernel F) N) = ∞ ∧
    (∫⁻ ω, ENNReal.ofReal |repeatedOLS (wholeRareKernel F) ω 1| ∂ repeatedLaw (wholeRareKernel F) N) = ∞) ∧
  (∀ N : ℕ, 4 ≤ N →
    (∫⁻ ω, ENNReal.ofReal (max (repeatedVariance (wholeRareKernel F) ω 1 1) 0)
      ∂ repeatedLaw (wholeRareKernel F) N) = ∞ ∧
    (∫⁻ ω, ENNReal.ofReal (max (-repeatedVariance (wholeRareKernel F) ω 1 1) 0)
      ∂ repeatedLaw (wholeRareKernel F) N) < ∞)

def wholeRareLimits {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  0 < wholeRareV F ∧ (wholeRareLimitMatrix F).PosDef ∧
  (wholeRareLimitMatrix F).det = 4*wholeRareV F ∧
  inProbability (repeatedLaw (wholeRareKernel F)) (fun N ω =>
    (N : ℝ) • repeatedVariance (wholeRareKernel F) ω - wholeRareLimitMatrix F) ∧
  ∃ ν : Measure (Vec 2), centeredNormalLaw ν (wholeRareLimitMatrix F) ∧
    weakLimit (repeatedLaw (wholeRareKernel F))
      (fun N ω => Real.sqrt N • (repeatedOLS (wholeRareKernel F) ω - repeatedBeta (wholeRareKernel F) N)) ν

def wholeRareBounds {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N d t u v j, 0 ≤ (wholeRareKernel F).X N d t u v j ∧
    (wholeRareKernel F).X N d t u v j ≤ 2) ∧
  (∀ N d t u v, |(wholeRareKernel F).Y N d t u v| ≤ 4)

def wholeRareConditionalMean {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N d t, MeasureTheory.condExp
    (MeasurableSpace.comap (fun ω : Fin N → U => repeatedX (wholeRareKernel F) ω) inferInstance)
    (repeatedLaw (wholeRareKernel F) N) (fun ω => repeatedY (wholeRareKernel F) ω d t)
      =ᵐ[repeatedLaw (wholeRareKernel F) N] 0)

def wholeRarePopulation {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N, repeatedBeta (wholeRareKernel F) N = 0) ∧
  2/3 ≤ wholeRareQ F ∧
  wholeRareQ F ≤ 1 ∧
  (∀ N : ℕ, 2 ≤ N → wholeRepeatedH (wholeRareKernel F) N = !![1,1;1,1+wholeRareQ F] ∧
    (wholeRepeatedH (wholeRareKernel F) N).det = wholeRareQ F)

def wholeRareFiniteFit {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N : ℕ, 2 ≤ N → ∀ ω : Fin N → U,
    0 < wholeRareSsq F ω ∧
    (repeatedGram (wholeRareKernel F) ω).det = 4*Dreal N*wholeRareSsq F ω ∧
    0 < (repeatedGram (wholeRareKernel F) ω).det ∧
    repeatedOLS (wholeRareKernel F) ω =
      ![2*wholeRareMeanB F ω - (∑ d : Dyad N, wholeRareScale F ω d*wholeRareSignal F ω d)/wholeRareSsq F ω,
        (∑ d : Dyad N, wholeRareScale F ω d*wholeRareSignal F ω d)/wholeRareSsq F ω] ∧
    (∀ d t, repeatedY (wholeRareKernel F) ω d t -
        dot (repeatedX (wholeRareKernel F) ω d t) (repeatedOLS (wholeRareKernel F) ω) =
      signValue (F.B (ω (firstUnit d))) + signValue (F.B (ω (secondUnit d))) - 2*wholeRareMeanB F ω +
      (if t.val=0 then 1 else -1) * (wholeRareSignal F ω d -
        repeatedOLS (wholeRareKernel F) ω 1 * wholeRareScale F ω d)) ∧
    (∀ d t, |repeatedY (wholeRareKernel F) ω d t -
      dot (repeatedX (wholeRareKernel F) ω d t) (repeatedOLS (wholeRareKernel F) ω)| ≤ 8) ∧
    (let r := fun d => wholeRareSignal F ω d - repeatedOLS (wholeRareKernel F) ω 1*wholeRareScale F ω d
     repeatedVariance (wholeRareKernel F) ω 1 1 =
       (∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then
         (wholeRareScale F ω d*r d)*(wholeRareScale F ω f*r f) else 0) / (wholeRareSsq F ω)^2))

def wholeRareEventMoments {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N m : ℕ, 3 ≤ N → N ≤ m+1 →
    (repeatedLaw (wholeRareKernel F) N (wholeRareEvent F N m)).toReal =
      (2 : ℝ)^(-((m+1 : ℤ)*N)) * (Nat.descFactorial (m+1) N : ℝ) / (m+1 : ℝ)^N ∧
    0 < repeatedLaw (wholeRareKernel F) N (wholeRareEvent F N m) ∧
    (∀ ω ∈ wholeRareEvent F N m, repeatedOLS (wholeRareKernel F) ω 1 =
      2*wholeRareMeanA F ω / wholeRareDelta (m+1)) ∧
    Integrable (fun ω => (repeatedOLS (wholeRareKernel F) ω 1)^2)
      ((repeatedLaw (wholeRareKernel F) N).restrict (wholeRareEvent F N m)) ∧
    (∫ ω, (repeatedOLS (wholeRareKernel F) ω 1)^2
      ∂ (repeatedLaw (wholeRareKernel F) N).restrict (wholeRareEvent F N m)) /
      (repeatedLaw (wholeRareKernel F) N (wholeRareEvent F N m)).toReal =
        4 / ((N : ℝ)*(wholeRareDelta (m+1))^2))

def wholeRareGrowth {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N m : ℕ, 3 ≤ N → N*(N-1) ≤ m+1 →
    (1/2 : ℝ) ≤ (Nat.descFactorial (m+1) N : ℝ) / (m+1 : ℝ)^N ∧
    ENNReal.ofReal ((32/(N : ℝ))*(m+1 : ℝ)^4*(2 : ℝ)^(2*(m+1 : ℤ)^2-(m+1 : ℤ)*(N : ℤ))) ≤
      ∫⁻ ω, ENNReal.ofReal ((repeatedOLS (wholeRareKernel F) ω 1)^2)
        ∂ (repeatedLaw (wholeRareKernel F) N).restrict (wholeRareEvent F N m) ∧
    (2 : ℝ)^((m+1)^2) ≤ (32/(N : ℝ))*(m+1 : ℝ)^4*(2 : ℝ)^(2*(m+1 : ℤ)^2-(m+1 : ℤ)*(N : ℤ)))

def wholeRareSandwichFacts {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N : ℕ, 2 ≤ N →
    (∀ m ω, ω ∈ wholeRareEvent F N m → repeatedVariance (wholeRareKernel F) ω 1 1 =
      ((N : ℝ)-2)*((N : ℝ)-3)*wholeRareDispersion F ω /
        ((Dreal N)^2*(wholeRareDelta (m+1))^2)) ∧
    (∫ ω, wholeRareDispersion F ω ∂ repeatedLaw (wholeRareKernel F) N) = N-1 ∧
    (∀ m, N ≤ m+1 →
      (∫ ω, wholeRareDispersion F ω
        ∂ (repeatedLaw (wholeRareKernel F) N).restrict (wholeRareEvent F N m)) /
        (repeatedLaw (wholeRareKernel F) N (wholeRareEvent F N m)).toReal = N-1) ∧
    (∀ ω, (∀ m, ω ∉ wholeRareEvent F N m) →
      |repeatedVariance (wholeRareKernel F) ω 1 1| ≤ 16*(Dreal N)^2))

def wholeRareDirectedEquality {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N, ∀ᵐ ω ∂ repeatedLaw (wholeRareDirected F) N,
    Function.Injective (fun i => (ω i).2) ∧
    wholeWeightedOLS (wholeRareDirected F) (fun _ _ => 1) ω =
      repeatedOLS (wholeRareKernel F) (fun i => (ω i).1) ∧
    wholeWeightedVariance (wholeRareDirected F) (fun _ _ => 1) ω =
      repeatedVariance (wholeRareKernel F) (fun i => (ω i).1))

def wholeRareDirectedMoments {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  (∀ N, 3 ≤ N →
    (∫⁻ ω, ENNReal.ofReal ((wholeWeightedOLS (wholeRareDirected F) (fun _ _ => 1) ω 1)^2)
      ∂ repeatedLaw (wholeRareDirected F) N) = ∞ ∧
    (∫⁻ ω, ENNReal.ofReal |wholeWeightedOLS (wholeRareDirected F) (fun _ _ => 1) ω 1|
      ∂ repeatedLaw (wholeRareDirected F) N) = ∞) ∧
  (∀ N, 4 ≤ N →
    (∫⁻ ω, ENNReal.ofReal (max (wholeWeightedVariance (wholeRareDirected F) (fun _ _ => 1) ω 1 1) 0)
      ∂ repeatedLaw (wholeRareDirected F) N) = ∞ ∧
    (∫⁻ ω, ENNReal.ofReal (max (-wholeWeightedVariance (wholeRareDirected F) (fun _ _ => 1) ω 1 1) 0)
      ∂ repeatedLaw (wholeRareDirected F) N) < ∞)

def wholeRareDirectedLimits {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  inProbability (repeatedLaw (wholeRareDirected F)) (fun N ω =>
    (N : ℝ) • wholeWeightedVariance (wholeRareDirected F) (fun _ _ => 1) ω - wholeRareLimitMatrix F) ∧
  (∃ ν : Measure (Vec 2), centeredNormalLaw ν (wholeRareLimitMatrix F) ∧
    weakLimit (repeatedLaw (wholeRareDirected F))
      (fun N ω => Real.sqrt N • wholeWeightedOLS (wholeRareDirected F) (fun _ _ => 1) ω) ν)

/-- P018-T19; p. 567 (PDF p. 4), Corollary 1; pp. 573--574 (PDF pp. 10--11),
Appendix B; p. 575 (PDF p. 12), Corollary 2.
The explicit rare-category iid model satisfies (a)--(g): bounded records,
conditional mean zero and population rank, full sample rank, the exact OLS and
residual formulas and uniform residual bound, exact rare-event probabilities and
conditional second moments with their exponential lower bounds, infinite slope
moments and infinite positive but finite negative sandwich mean, the nondegenerate
Gaussian and sandwich limits, and the independent-uniform directed unit-weight
version with the same estimators and failures. The usual measure-theoretic
conditions are assumed for the finite quantities; divergent moments are asserted
as extended nonnegative integrals. Event index m below represents printed M=m+1. -/
def T19WholeStatement : Prop :=
  ∃ (U : Type) (_mU : MeasurableSpace U) (F : WholeRareModel U),
  wholeRareLaw F ∧ RepeatedStanding (wholeRareKernel F) ∧
  wholeRareBounds F ∧ wholeRareConditionalMean F ∧ wholeRarePopulation F ∧
  wholeRareFiniteFit F ∧ wholeRareEventMoments F ∧ wholeRareGrowth F ∧
  wholeRareMoments F ∧ wholeRareSandwichFacts F ∧
  Summable wholeRareHterm ∧ 0 < wholeRareH ∧ wholeRareLimits F ∧
  wholeRareDirectedEquality F ∧ wholeRareDirectedMoments F ∧ wholeRareDirectedLimits F

/-- An admissible directed unit-weight version of the rare witness, satisfying
all C2 structural and limiting-design hypotheses, not just boundedness and rank. -/
def wholeDirectedAdmissibility {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  let R := wholeRareDirected F
  RepeatedStanding R ∧
  (∃ (X : (U × ℝ) → (U × ℝ) → Vec 2) (Y : (U × ℝ) → (U × ℝ) → ℝ)
    (dir : ∀ N, (d : Dyad N) → Fin (R.T N d) → Bool),
    (∀ N d, Function.Injective (dir N d)) ∧
    (∀ N d t u v, R.X N d t u v = (if dir N d t then X v u else X u v) ∧
      R.Y N d t u v = (if dir N d t then Y v u else Y u v))) ∧
  (!![2,2;2,2+2*wholeRareQ F] : Mat 2).PosDef ∧
  Tendsto (fun N : ℕ => wholeWeightedH (N := N) R (fun _ _ => 1)) atTop
    (𝓝 (!![2,2;2,2+2*wholeRareQ F] : Mat 2)) ∧
  (∀ N, 2 ≤ N → wholeWeightedBeta (N := N) R (fun _ _ => 1) = 0) ∧
  (∀ N, 2 ≤ N → ∀ᵐ ω ∂ repeatedLaw R N,
    (wholeWeightedGram R (fun _ _ => 1) ω).det ≠ 0)

/-- Actual coefficient moments and UI fail in the admissible directed version. -/
def wholeDirectedMomentFailure {U : Type} [MeasurableSpace U] (F : WholeRareModel U) : Prop :=
  let R := wholeRareDirected F
  (∀ N, 3 ≤ N →
    ¬ MemLp (fun ω => wholeWeightedOLS R (fun _ _ => 1) ω 1 -
      wholeWeightedBeta (N := N) R (fun _ _ => 1) 1) 2 (repeatedLaw R N) ∧
    ¬ Integrable (fun ω => wholeWeightedOLS R (fun _ _ => 1) ω 1 -
      wholeWeightedBeta (N := N) R (fun _ _ => 1) 1) (repeatedLaw R N)) ∧
  ¬ uiSquares (repeatedLaw R) (fun N ω => Real.sqrt N •
    (wholeWeightedOLS R (fun _ _ => 1) ω - wholeWeightedBeta (N := N) R (fun _ _ => 1)))

/-- The fixed-size bounded-data hypotheses in the finite covariance identity. -/
def wholeRepeatedAtSize {U : Type} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (N : ℕ) : Prop :=
  IsProbabilityMeasure R.μ ∧ (∀ d : Dyad N, 0 < R.T N d) ∧
  (∀ d t, Measurable (fun uv : U × U => R.X N d t uv.1 uv.2) ∧
    Measurable (fun uv : U × U => R.Y N d t uv.1 uv.2)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ d t, ∀ᵐ uv ∂ R.μ.prod R.μ,
    ‖R.X N d t uv.1 uv.2‖ ≤ C ∧ |R.Y N d t uv.1 uv.2| ≤ C)

/-- P018-T20; p. 567 (PDF p. 4), Corollary 1; p. 575 (PDF p. 12), Corollary 2.
Restricted version of P018-T20(ii), under the C1 and C2 premises stated below;
the finite covariance identities, the UI-based actual-covariance implication,
the moment-failure examples and the deterministic-limit equivalence are included.
The retained covariance targets and explicit consistency premises are stated here;
no equivalence to an unsupplied canonical T10 contract is claimed.
Write L_N = sum_d T(N,d), D_N = N(N-1)/2, G_N = sum_dt X_dt X_dt', and
G_w,N = sum_dt w_dt X_dt X_dt'. Each population coefficient is the inverse
expected Gram times its corresponding expected XY sum. Define the population
residuals using those coefficients, the block scores b_d = sum_t X_dt epsilon_dt
and b_w,d = sum_t w_dt X_dt epsilon_w,dt, and their sums S_r and S_w.
Set H_r,N = E[G_N]/L_N and H_w,N = E[G_w,N]/D_N. The targets are
V_r,N = (N/L_N^2) H_r,N^-1 Var(S_r) H_r,N^-1 and
V_w,N = (N/D_N^2) H_w,N^-1 Var(S_w) H_w,N^-1.
The finite identities assume iid units, bounded measurable records with positive
record counts, N >= 2 and nonsingular H_r,N or H_w,N; fixed real weights suffice.
They identify these targets with the covariances of H_r,N^-1 (sqrt(N)/L_N) S_r
and H_w,N^-1 (sqrt(N)/D_N) S_w respectively.
Weak convergence with uniformly integrable squared scaled errors gives mean and
actual covariance convergence; subtraction of a convergent target is valid.
Bounded data and sample and population rank alone do not give those moments or
uniform integrability. The directed unit-weight witness satisfies the common-
kernel and positive limiting-design conditions. Deterministic covariance convergence
is exactly convergence in probability of constant random matrices. The usual
measure-theoretic conditions are assumed.
Restriction: For canonical clause (ii), retain only consistency under the following explicit C1 and C2
premises; equivalence with the unsupplied canonical P018-T10 hypotheses is not asserted. C1 assumes iid
units, measurable uniformly bounded common record-index pair kernels with an intercept, 1 <= T(N,d) <= T0
for one fixed T0, H_r,N tending to a positive definite H, and (N/L_N^2) times the sum over ordered
overlapping dyads d,f of E[b_d] E[b_f] transpose tending to zero, including diagonal pairs. C2 assumes iid
units, measurable uniformly bounded records with an intercept, at most two records per dyad, one common
ordered-pair kernel used in original or reversed endpoint order with injective Boolean record orientations,
deterministic weights with positive scales a_N and a uniform finite bound 0 < w_Ndt/a_N <= C, and H_(w/a),N
tending to a positive definite limit. These are substantive model and limit premises, not usual
measure-theoretic existence conditions. The finite covariance identities, UI-based actual-covariance
implication, moment-failure examples and deterministic-limit equivalence are retained. -/
def T20WholeStatement : Prop :=
  (∀ {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k),
    wholeRepeatedAtSize R N → 2 ≤ N → (wholeRepeatedH R N).det ≠ 0 →
    let S := fun ω => ∑ d : Dyad N, repeatedBlockScore R (repeatedBeta R N) ω d
    meanVec (repeatedLaw R N) S = 0 ∧
    wholeRepeatedTarget R N = varMat (repeatedLaw R N) (fun ω =>
      (wholeRepeatedH R N)⁻¹.mulVec ((Real.sqrt N/repeatedL R N) • S ω)) ∧
    meanMat (repeatedLaw R N) (fun ω => (repeatedL R N)⁻¹ • repeatedGram R ω) = wholeRepeatedH R N ∧
    (∀ᵐ ω ∂ repeatedLaw R N, (repeatedGram R ω).det ≠ 0 →
      Real.sqrt N • (repeatedOLS R ω - repeatedBeta R N) =
      ((repeatedL R N)⁻¹ • repeatedGram R ω)⁻¹.mulVec ((Real.sqrt N/repeatedL R N) • S ω)) ∧
    (∀ a, MemLp (fun ω => ((wholeRepeatedH R N)⁻¹.mulVec
      ((Real.sqrt N/repeatedL R N) • S ω)) a) 2 (repeatedLaw R N))) ∧
  (∀ {U : Type} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ),
    wholeRepeatedAtSize R N → 2 ≤ N → (wholeWeightedH R w).det ≠ 0 →
    let S := fun ω => ∑ d : Dyad N, wholeWeightedBlockScore R w (wholeWeightedBeta R w) ω d
    meanVec (repeatedLaw R N) S = 0 ∧
    wholeWeightedTarget R w = varMat (repeatedLaw R N) (fun ω =>
      (wholeWeightedH R w)⁻¹.mulVec ((Real.sqrt N/Dreal N) • S ω)) ∧
    meanMat (repeatedLaw R N) (fun ω => (Dreal N)⁻¹ • wholeWeightedGram R w ω) = wholeWeightedH R w ∧
    (∀ᵐ ω ∂ repeatedLaw R N, (wholeWeightedGram R w ω).det ≠ 0 →
      Real.sqrt N • (wholeWeightedOLS R w ω - wholeWeightedBeta R w) =
      ((Dreal N)⁻¹ • wholeWeightedGram R w ω)⁻¹.mulVec ((Real.sqrt N/Dreal N) • S ω)) ∧
    (∀ a, MemLp (fun ω => ((wholeWeightedH R w)⁻¹.mulVec
      ((Real.sqrt N/Dreal N) • S ω)) a) 2 (repeatedLaw R N))) ∧
  (∀ {U : Type} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k),
    RepeatedStanding R →
    (∃ fX : ℕ → U → U → Vec k, ∃ fY : ℕ → U → U → ℝ,
      ∀ N d (t : Fin (R.T N d)) u v, R.X N d t u v = fX t.val u v ∧ R.Y N d t u v = fY t.val u v) →
    (∃ T0 : ℕ, ∀ N d, R.T N d ≤ T0) →
    ∀ H : Mat k, H.PosDef → Tendsto (wholeRepeatedH R) atTop (𝓝 H) →
    Tendsto (fun N : ℕ => ((N : ℝ)/(repeatedL R N)^2) • meat members
      (fun d : Dyad N => meanVec (repeatedLaw R N) (fun ω => repeatedBlockScore R (repeatedBeta R N) ω d)))
      atTop (𝓝 0) →
    inProbability (repeatedLaw R) (fun N ω => (N : ℝ) • repeatedVariance R ω - wholeRepeatedTarget R N)) ∧
  (∀ {U : Type} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k),
    RepeatedStanding R → (∀ N d, R.T N d ≤ 2) →
    ∀ (X : U → U → Vec k) (Y : U → U → ℝ)
      (dir : ∀ N, (d : Dyad N) → Fin (R.T N d) → Bool),
    (∀ N d, Function.Injective (dir N d)) →
    (∀ N d t u v, R.X N d t u v = (if dir N d t then X v u else X u v) ∧
      R.Y N d t u v = (if dir N d t then Y v u else Y u v)) →
    ∀ (w : ∀ N, (d : Dyad N) → Fin (R.T N d) → ℝ) (a : ℕ → ℝ),
    (∀ N, 0 < a N) → (∃ C : ℝ, ∀ N d t, 0 < w N d t/a N ∧ w N d t/a N ≤ C) →
    ∀ H : Mat k, H.PosDef →
    Tendsto (fun N => wholeWeightedH R (fun d t => w N d t/a N)) atTop (𝓝 H) →
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • wholeWeightedVariance R (w N) ω - wholeWeightedTarget R (w N))) ∧
  (∀ {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N, Measure (Ω N)) (_hμ : ∀ N, IsProbabilityMeasure (μ N))
    (e : ∀ N, Ω N → Vec k) (ν : Measure (Vec k)),
    let ξ := fun (N : ℕ) ω => Real.sqrt N • e N ω
    (∀ N a, MemLp (fun ω => e N ω a) 2 (μ N)) →
    weakLimit μ ξ ν → uiSquares μ ξ → (∀ a, MemLp (fun x : Vec k => x a) 2 ν) →
    meanVec ν id = 0 →
    Tendsto (fun N => meanVec (μ N) (ξ N)) atTop (𝓝 0) ∧
    (∀ N : ℕ, (N : ℝ) • varMat (μ N) (e N) = varMat (μ N) (ξ N)) ∧
    Tendsto (fun N : ℕ => (N : ℝ) • varMat (μ N) (e N)) atTop (𝓝 (varMat ν id)) ∧
    (∀ V : ℕ → Mat k, Tendsto V atTop (𝓝 (varMat ν id)) →
      Tendsto (fun N : ℕ => (N : ℝ) • varMat (μ N) (e N) - V N) atTop (𝓝 0))) ∧
  (∃ (U : Type) (_mU : MeasurableSpace U) (R : RepeatedKernel U 2),
    RepeatedStanding R ∧ (∀ N, 2 ≤ N → (wholeRepeatedH R N).det > 0) ∧
    (∀ N, 2 ≤ N → ∀ ω : Fin N → U, (repeatedGram R ω).det > 0) ∧
    (∀ N, 3 ≤ N →
      ¬ MemLp (fun ω => repeatedOLS R ω 1 - repeatedBeta R N 1) 2 (repeatedLaw R N) ∧
      ¬ Integrable (fun ω => wholeWeightedOLS R (fun _ _ => 1) ω 1 -
        wholeWeightedBeta (N := N) R (fun _ _ => 1) 1) (repeatedLaw R N)) ∧
    ¬ uiSquares (repeatedLaw R) (fun N ω => Real.sqrt N • (repeatedOLS R ω - repeatedBeta R N))) ∧
  (∃ (U : Type) (_mU : MeasurableSpace U) (F : WholeRareModel U),
    wholeRareLaw F ∧ wholeDirectedAdmissibility F ∧ wholeDirectedMomentFailure F) ∧
  (∀ {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N, Measure (Ω N)) (_hμ : ∀ N, IsProbabilityMeasure (μ N)) (A : ℕ → Mat k),
    Tendsto A atTop (𝓝 0) ↔ inProbability μ (fun N _ => A N))

/-- Unconditional sparse score second moment, without a conditional-mean-zero assumption. -/
def wholeCorrectedSigma {U : Type} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) : Mat k :=
  ∑ d : Dyad N, ∑ f : Dyad N, if overlap d f then
    meanMat (unitSampleLaw K N) (fun ω =>
      (epsilon K ω d * epsilon K ω f) • outer (design K ω d) (design K ω f)) else 0

/-- Uniform [-1,1] nonlinear witness from the audit. -/
def wholeNonlinearKernel : Kernel ℝ 2 :=
  ⟨ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1),
    fun z t => ![1,2+z+t], fun z t => (z+t)^2⟩

/-- P018-T21; p. 566 (PDF p. 3), equation (2), term B.
The expectation belongs before the braces in each neighbour summand. There are
2(N-2) neighbours per dyad, N(N-1)(N-2) ordered distinct-neighbour pairs and
D(2N-3) ordered overlapping pairs including the diagonal. The diagonal-plus-
neighbour conditional-covariance expression equals the sparse conditional sum
term by term. It is not the score variance in general: that variance is the
unconditional sparse score second moment. The bounded uniform nonlinear model
has zero conditional-covariance sum but the displayed nonzero score variance at
N=3. The usual measure-theoretic conditions are assumed. -/
def T21WholeStatement : Prop :=
  (∀ N : ℕ, 2 ≤ N → Fintype.card (Dyad N) = N.choose 2 ∧
    (∀ d : Dyad N, (neighbors d).card = 2*(N-2)) ∧
    (∑ d : Dyad N, (neighbors d).card) = N*(N-1)*(N-2) ∧
    (univ.filter (fun p : Dyad N × Dyad N => overlap p.1 p.2)).card = N.choose 2*(2*N-3)) ∧
  T21Statement ∧
  (∀ {U : Type} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k), Standing K →
    varMat (unitSampleLaw K N) (scoreSum K) = wholeCorrectedSigma K N) ∧
  Standing wholeNonlinearKernel ∧ populationBeta wholeNonlinearKernel = ![2/3,0] ∧
  printedSigma wholeNonlinearKernel 3 = 0 ∧
  varMat (unitSampleLaw wholeNonlinearKernel 3) (scoreSum wholeNonlinearKernel) =
    !![12/5,24/5;24/5,4712/315] ∧
  printedSigma wholeNonlinearKernel 3 ≠
    varMat (unitSampleLaw wholeNonlinearKernel 3) (scoreSum wholeNonlinearKernel)

end SAP.P018b
