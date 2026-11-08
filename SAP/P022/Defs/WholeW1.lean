import Mathlib
import SAP.P022.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section

/-- Convergence in probability when each row has its own finite assignment law. -/
def designConvergence (d : ℕ → Design)
    (X : (q : ℕ) → Assignment (d q) → ℝ) (a : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → Tendsto (fun q => designProbability (d q)
    (fun π => η ≤ |X q π - a|)) atTop (𝓝 0)

def rowSize (S : ExperimentSequence) (q : ℕ) : ℝ := (S.design q).N

def effectError (S : ExperimentSequence) (q : ℕ) (π : Assignment (S.design q)) : ℝ :=
  estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π -
    averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)

def rowTrueVariance (S : ExperimentSequence) (q : ℕ) : ℝ :=
  trueVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)

def rowBound (S : ExperimentSequence) (B : BoundSide) (q : ℕ) : ℝ :=
  populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) B

def rowEstimate (S : ExperimentSequence) (B : BoundSide) (q : ℕ)
    (π : Assignment (S.design q)) : ℝ :=
  estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) B π

def centeredUpperError (S : ExperimentSequence) (q : ℕ)
    (π : Assignment (S.design q)) : ℝ :=
  rowSize S q * (rowEstimate S .H q π - rowBound S .H q)

def wrongUpperError (S : ExperimentSequence) (q : ℕ)
    (π : Assignment (S.design q)) : ℝ :=
  rowSize S q * |rowEstimate S .H q π - rowTrueVariance S q|

def bernoulliHalfCDF (x : ℝ) : ℝ := if x < 0 then 0 else if x < 1 then 1 / 2 else 1

/-- The second witness uses one-based unit i+1, hence the denominator i+3. -/
def perturbedCornerWitness : ExperimentSequence :=
  { cornerWitness with
    y1 := fun i => cornerWitness.y1 i - 1 / ((i : ℝ) + 3)
    y0 := fun i => cornerWitness.y0 i - 1 / ((i : ℝ) + 3) }

def perturbedThreshold (q : ℕ) : ℝ := 1 - 1 / (2 * ((q : ℝ) + 6))

/-- Marginal CDFs on the extended line for the point mass at zero. -/
def originExtendedCDF (x : EReal) : ℝ := if 0 ≤ x then 1 else 0

def originExtendedLeftCDF (x : EReal) : ℝ := if 0 < x then 1 else 0

def OriginPartitionMesh (P : ℕ) (s : Fin (P + 1) → EReal) (η : ℝ) : Prop :=
  StrictMono s ∧ s 0 = ⊥ ∧ s (Fin.last P) = ⊤ ∧
    ∀ i : Fin P, originExtendedLeftCDF (s i.succ) <
      originExtendedCDF (s i.castSucc) + η / 2

def CornerLawFacts : Prop :=
  (∀ t x, lawCDF cornerLaw t x = bernoulliHalfCDF x) ∧
  (∀ t, lawMean cornerLaw t = 1 / 2 ∧ lawVariance cornerLaw t = 1 / 4) ∧
  lawCovariance cornerLaw = 0 ∧ NonsingularLaw cornerLaw

def ReciprocalExtraFacts : Prop :=
  (∀ i, |reciprocalWitness.y1 i| ≤ 1 ∧ |reciprocalWitness.y0 i| ≤ 1) ∧
  UniformSquareIntegrability reciprocalWitness ∧
  (∀ q t, empiricalCDF (rowOutcomes reciprocalWitness t q) 0 = 1 ∧
    empiricalLeftCDF (rowOutcomes reciprocalWitness t q) 0 = 1 ∧
    lawCDF originLaw t 0 = 1 ∧ lawLeftCDF originLaw t 0 = 0) ∧
  (∀ q t, empiricalCDF (rowOutcomes reciprocalWitness t q) (reciprocalThreshold q) = 1 ∧
    lawCDF originLaw t (reciprocalThreshold q) = 0 ∧
    ∀ π, sampledCDF reciprocalWitness t q π (reciprocalThreshold q) = 1)

/-- The complete, finite probability identities at the witnesses' respective tolerances. -/
def CertainCDFError (S : ExperimentSequence) (H : JointLaw) (η : ℝ) : Prop :=
  ∀ t q,
    designProbability (S.design q) (fun π => η ≤
      cdfDistance (lawCDF H t) (sampledCDF S t q π)) = 1 ∧
    rowSize S q * designProbability (S.design q) (fun π => η ≤
      cdfDistance (lawCDF H t) (sampledCDF S t q π)) = rowSize S q

def PerturbedAtomFacts : Prop :=
  (∀ i, |perturbedCornerWitness.y1 i| < 1 ∧ |perturbedCornerWitness.y0 i| < 1) ∧
  UniformSquareIntegrability perturbedCornerWitness ∧
  (∀ t, Tendsto (fun q => empiricalCDF (rowOutcomes perturbedCornerWitness t q) 0)
    atTop (𝓝 (1 / 2 : ℝ))) ∧
  (∀ t q, empiricalCDF (rowOutcomes perturbedCornerWitness t q) 1 = 1) ∧
  (∀ t x, ¬ContinuousAt (lawCDF cornerLaw t) x →
    Tendsto (fun q => empiricalCDF (rowOutcomes perturbedCornerWitness t q) x)
      atTop (𝓝 (lawCDF cornerLaw t x)))

def PerturbedThresholdFacts : Prop :=
  ∀ q t, 0 < perturbedThreshold q ∧ perturbedThreshold q < 1 ∧
    empiricalCDF (rowOutcomes perturbedCornerWitness t q) (perturbedThreshold q) = 1 ∧
    lawCDF cornerLaw t (perturbedThreshold q) = 1 / 2 ∧
    (1 / 2 : ℝ) ≤ cdfDistance (lawCDF cornerLaw t)
      (empiricalCDF (rowOutcomes perturbedCornerWitness t q)) ∧
    ∀ π, sampledCDF perturbedCornerWitness t q π (perturbedThreshold q) = 1 ∧
      (1 / 2 : ℝ) ≤ cdfDistance (lawCDF cornerLaw t)
        (sampledCDF perturbedCornerWitness t q π)

/-- The printed claim is false: P022-T1; p. 860 (PDF p. 11), proof on pp. 860–861.
The fixed negative-reciprocal witness satisfies conditions 1–4 but has population and
sample CDF error one, certain tails, and a persistent error at the required partition
knot zero. The bounded perturbed four-corner witness satisfies conditions 1–4 with a
nonsingular limit and has CDF error at least one half and certain tails. Thus both
conclusions of printed Lemma 2 fail, even with a nonsingular limiting law.
The usual measure-theoretic conditions are assumed. -/
def T1WholeStatement : Prop :=
  T1Statement ∧ ReciprocalExtraFacts ∧ CertainCDFError reciprocalWitness originLaw (1 / 2) ∧
  (∀ P (s : Fin (P + 1) → EReal) η, 0 < η → η ≤ 2 → OriginPartitionMesh P s η →
    ∃ j, s j = 0 ∧ ∀ q t,
      |empiricalLeftCDF (rowOutcomes reciprocalWitness t q) 0 - lawLeftCDF originLaw t 0| = 1) ∧
  CornerLawFacts ∧ Conditions123 perturbedCornerWitness cornerLaw 1 (1 / 2) ∧
  PerturbedAtomFacts ∧ PerturbedThresholdFacts ∧
  CertainCDFError perturbedCornerWitness cornerLaw (1 / 4) ∧
  (∀ t, scaledProbabilityLimsup perturbedCornerWitness (fun q π => (1 / 4 : ℝ) ≤
    cdfDistance (lawCDF cornerLaw t) (sampledCDF perturbedCornerWitness t q π)) = ⊤) ∧
  ¬Lemma2Conclusions perturbedCornerWitness cornerLaw 1 (1 / 2) ∧
  (∀ K : ℕ, (1 - 1 * (1 / 2 : ℝ)) * K / (1 * (1 / 2) * (1 / 2) ^ 2) = 4 * K ∧
    (1 - 1 * (1 / 2 : ℝ)) * K / (1 * (1 / 2) * (1 / 4) ^ 2) = 16 * K)

def CornerEndpointFacts : Prop :=
  (∀ t x, lawCDF cornerLaw t x = bernoulliHalfCDF x) ∧
  ∀ t, Tendsto (fun q => empiricalCDF (rowOutcomes cornerWitness t q) 0)
    atTop (𝓝 (1 / 2 : ℝ)) ∧
    (∀ q, empiricalCDF (rowOutcomes cornerWitness t q) 1 = 1 ∧
      empiricalLeftCDF (rowOutcomes cornerWitness t q) 0 = 0 ∧
      empiricalLeftCDF (rowOutcomes cornerWitness t q) 1 =
        empiricalCDF (rowOutcomes cornerWitness t q) 0) ∧
    Tendsto (fun q => empiricalLeftCDF (rowOutcomes cornerWitness t q) 1)
      atTop (𝓝 (1 / 2 : ℝ))

def CornerBalancedMoments : Prop :=
  ∀ r, let d := cornerWitness.design (4 * r)
    let a := rowOutcomes cornerWitness true (4 * r)
    let b := rowOutcomes cornerWitness false (4 * r)
    d.m = 2 * (r + 1) ∧ d.k = 2 * (r + 1) ∧
    finiteMean a = 1 / 2 ∧ finiteMean b = 1 / 2 ∧
    finiteVariance a = 1 / 4 ∧ finiteVariance b = 1 / 4 ∧
    finiteMean (fun i => a i * b i) = 1 / 4 ∧ finiteCovariance a b = 0 ∧
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b u) = 1 / 2 ∧
    sharpCovariance a b .H = 1 / 4

def CornerBalancedVariances : Prop :=
  ∀ r, rowTrueVariance cornerWitness (4 * r) =
      1 / (2 * (rowSize cornerWitness (4 * r) - 1)) ∧
    rowBound cornerWitness .H (4 * r) = 1 / (rowSize cornerWitness (4 * r) - 1) ∧
    ∀ π, rowSize cornerWitness (4 * r) *
      (rowEstimate cornerWitness .H (4 * r) π - rowTrueVariance cornerWitness (4 * r)) =
      centeredUpperError cornerWitness (4 * r) π +
        rowSize cornerWitness (4 * r) / (2 * (rowSize cornerWitness (4 * r) - 1))

def CornerBalancedRate : Prop :=
  ∀ r δ, 0 < δ → 64 / δ ≤ rowSize cornerWitness (4 * r) →
    designProbability (cornerWitness.design (4 * r)) (fun π =>
      δ ≤ |centeredUpperError cornerWitness (4 * r) π|) ≤
      51200 / (rowSize cornerWitness (4 * r) * δ ^ 2)

def CornerWrongLimits : Prop :=
  designConvergence (fun r => cornerWitness.design (4 * r))
    (fun r π => wrongUpperError cornerWitness (4 * r) π) (1 / 2) ∧
  ∀ ε, 0 < ε → ε < (1 / 2 : ℝ) →
    Tendsto (fun r => designProbability (cornerWitness.design (4 * r))
      (fun π => ε ≤ wrongUpperError cornerWitness (4 * r) π)) atTop (𝓝 1) ∧
    Tendsto (fun r => rowSize cornerWitness (4 * r) *
      designProbability (cornerWitness.design (4 * r))
        (fun π => ε ≤ wrongUpperError cornerWitness (4 * r) π)) atTop atTop ∧
    (∀ R : ℝ, ∀ᶠ r in atTop, R < rowSize cornerWitness (4 * r) *
      designProbability (cornerWitness.design (4 * r))
        (fun π => ε ≤ wrongUpperError cornerWitness (4 * r) π))

/-- The printed claim is false: P022-T7; p. 868 (PDF p. 19), Proposition 2 on p. 863.
The nested four-corner population satisfies the stated assumptions. The admissible
split (1,1,1) makes (23) a probability-one event. On N=4r the exact moments give a
scaled centering gap tending to one half; the centered error has the stated
51200/(N delta^2) tail bound. The wrongly centered absolute error tends to one half
in probability, its small-threshold probabilities tend to one, and their N-scaled
values diverge, refuting both finite printed bounds. The usual measure-theoretic
conditions are assumed. -/
def T7WholeStatement : Prop :=
  T7Statement ∧ CornerEndpointFacts ∧
  ((0 : ℝ) < 1 ∧ (1 : ℝ) + 1 + 1 = 3) ∧
  (∀ q, designProbability (cornerWitness.design q) (fun π => (1 - 1 : ℝ) ≤
      |lastIntegralTerm (cornerWitness.design q) (rowOutcomes cornerWitness true q)
        (rowOutcomes cornerWitness false q) 1 π|) = 1 ∧
    rowSize cornerWitness q * designProbability (cornerWitness.design q) (fun π =>
      (1 - 1 : ℝ) ≤ |lastIntegralTerm (cornerWitness.design q)
        (rowOutcomes cornerWitness true q) (rowOutcomes cornerWitness false q) 1 π|) =
      rowSize cornerWitness q) ∧
  CornerBalancedMoments ∧ CornerBalancedVariances ∧ CornerBalancedRate ∧
  designConvergence cornerWitness.design (centeredUpperError cornerWitness) 0 ∧
  CornerWrongLimits ∧
  (∀ R : ℝ, ¬scaledProbabilityLimsup cornerWitness (fun q π => (1 - 1 : ℝ) ≤
    |lastIntegralTerm (cornerWitness.design q) (rowOutcomes cornerWitness true q)
      (rowOutcomes cornerWitness false q) 1 π|) ≤ ENNReal.ofReal R)

def CodeExampleDetails : Prop :=
  Nat.choose 4 2 = 6 ∧
  (∀ π : Assignment fourUnitDesign,
    observedTreatment fourUnitDesign (fun _ => (1 : ℝ)) π = (fun _ => 1) ∧
    observedControl fourUnitDesign (fun _ => (1 : ℝ)) π = (fun _ => 1) ∧
    estimatedEffect fourUnitDesign (fun _ => 1) (fun _ => 1) π = 0) ∧
  sampleVariance (fun _ : Fin 2 => (1 : ℝ)) = 0 ∧
  marginalVarianceEstimate 4 (fun _ : Fin 2 => (1 : ℝ)) = 0 ∧
  (∀ B, sharpCovariance (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) B = 0) ∧
  partitionKnots 2 2 = [0, 1 / 2, 1] ∧
  codePoint 2 2 0 = codeEpsilon ∧ codePoint 2 2 1 = 1 / 2 - codeEpsilon ∧
  codePoint 2 2 2 = 1 - codeEpsilon ∧
  (∀ r < 3, empiricalQuantile (fun _ : Fin 2 => (1 : ℝ)) (codePoint 2 2 r) = 1) ∧
  (∀ r < 3, orderStatistic (fun _ : Fin 2 => (1 : ℝ))
    (3 - Nat.ceil (2 * codePoint 2 2 r)) = 1) ∧
  codePoint 2 2 1 - codePoint 2 2 0 = 1 / 2 - 2 * codeEpsilon ∧
  codePoint 2 2 2 - codePoint 2 2 1 = 1 / 2 ∧
  (1 / 2 - 2 * codeEpsilon) + 1 / 2 = (33554431 / 33554432 : ℝ) ∧
  -(4 * codeEpsilon / 3) = -(1 / 50331648 : ℝ) ∧ -(1 / 50331648 : ℝ) < 0

def ShiftedWeightSum : Prop :=
  ∀ m k : ℕ, 2 ≤ m → 2 ≤ k →
    (∑ r ∈ Finset.range (partitionCells m k),
      (codePoint m k (r + 1) - codePoint m k r)) = 1 - 2 * codeEpsilon

def BoundTranslationInvariant : Prop :=
  ∀ {N m k : ℕ}, 2 ≤ m → 2 ≤ k → m + k ≤ N →
    ∀ (a : Fin m → ℝ) (b : Fin k → ℝ) (c : ℝ) (B : BoundSide),
      estimateBound N (fun i => a i + c) (fun i => b i + c) B = estimateBound N a b B

def CodeTranslationFormula : Prop :=
  ∀ {N m k : ℕ}, 2 ≤ m → 2 ≤ k → m + k ≤ N →
    (∀ r < partitionCells m k, 2 * codeEpsilon < cellWidth m k r) →
    ∀ (a : Fin m → ℝ) (b : Fin k → ℝ) (c : ℝ) (B : BoundSide),
      printedCodeBound N (fun i => a i + c) (fun i => b i + c) B -
        printedCodeBound N a b B =
      -4 * codeEpsilon * (c * (orderStatistic a 1 +
        orderStatistic b (if B = .H then 1 else k)) + c ^ 2) / ((N : ℝ) - 1)

/-- The printed claim is false: P022-T9; Appendix B, p. 869 (PDF p. 20), (8)–(9) on p. 854.
In real arithmetic the all-ones four-unit example has constant observed samples,
zero effect, variance and sharp estimates, but the printed routine returns the
negative value -1/50331648. Its shifted weights sum to 1-2e. Under the stated
cell-width condition both endpoint discrepancies and the exact translation defect
hold, while the mathematical sharp estimates are translation invariant.
The usual measure-theoretic conditions are assumed. -/
def T9WholeStatement : Prop :=
  T9Statement ∧ CodeExampleDetails ∧ ShiftedWeightSum ∧ BoundTranslationInvariant ∧
  CodeTranslationFormula ∧
  (∀ B, printedCodeBound 4 (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 2 => (0 : ℝ)) B = 0 ∧
    printedCodeBound 4 (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 2 => (0 : ℝ)) B ≠
      printedCodeBound 4 (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) B)

def allocationFraction (θ ρ : ℝ) (t : Bool) : ℝ :=
  if t then θ * ρ else θ * (1 - ρ)

/-- A universal integer choice; in particular it has no sequence or tolerance-split input. -/
def marginalTailRate (θ ρ : ℝ) (t : Bool) (η : ℝ) : ℝ :=
  (1 - allocationFraction θ ρ t) * correctedPartitionInteger η /
    (allocationFraction θ ρ t * η ^ 2)

def UniversalCDFRates : Prop :=
  (∀ η, 0 < η → 0 < correctedPartitionInteger η) ∧
  (∀ a b, 0 < a → a ≤ b → correctedPartitionInteger b ≤ correctedPartitionInteger a) ∧
  ∀ S H θ ρ, Conditions123 S H θ ρ → Lemma2Conclusions S H θ ρ →
    ∀ t η, 0 < η → scaledProbabilityLimsup S (fun q π =>
      η ≤ cdfDistance (lawCDF H t) (sampledCDF S t q π)) ≤
      ENNReal.ofReal (marginalTailRate θ ρ t η)

def lastTermRate (θ ρ C ε1 ξ : ℝ) : ℝ :=
  marginalTailRate θ ρ true (ε1 / (16 * C ^ 2) - ξ) +
    marginalTailRate θ ρ false (ε1 / (16 * C ^ 2) - ξ)

def coefficientSum (θ ρ : ℝ) (ν : Fin 8 → ℝ) : ℝ :=
  ∑ i, termRateCoefficient θ ρ i / (ν i) ^ 2

def sixTermCoefficient (θ ρ : ℝ) (ν : Fin 8 → ℝ) (j : Fin 6) : ℝ :=
  match j.val with
  | 0 => termRateCoefficient θ ρ 0 / (ν 0) ^ 2
  | 1 => termRateCoefficient θ ρ 1 / (ν 1) ^ 2
  | 2 => termRateCoefficient θ ρ 2 / (ν 2) ^ 2
  | 3 => termRateCoefficient θ ρ 3 / (ν 3) ^ 2
  | 4 => termRateCoefficient θ ρ 4 / (ν 4) ^ 2 + termRateCoefficient θ ρ 5 / (ν 5) ^ 2
  | _ => termRateCoefficient θ ρ 6 / (ν 6) ^ 2 + termRateCoefficient θ ρ 7 / (ν 7) ^ 2

def EarlierSixRates (S : ExperimentSequence) (θ ρ C : ℝ) (ν : Fin 8 → ℝ) : Prop :=
  ∀ j : Fin 6, scaledProbabilityLimsup S (fun q π =>
    correctedAllocation ν 0 ⟨j.val, by omega⟩ ≤ |sevenTerms (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q) C π ⟨j.val, by omega⟩|) ≤
    ENNReal.ofReal (C ^ 4 * sixTermCoefficient θ ρ ν j)

def UpperLastLimit : Prop :=
  ∀ S H θ ρ C, Conditions123 S H θ ρ → 0 < C →
    (∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C) → Lemma2Conclusions S H θ ρ →
    ∀ ε1 ξ, 0 < ε1 → 0 < ξ → ξ < ε1 / (16 * C ^ 2) →
      scaledProbabilityLimsup S (fun q π => ε1 / 2 ≤
        |lastIntegralTerm (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) C π|) ≤
        ENNReal.ofReal (lastTermRate θ ρ C ε1 ξ)

def UpperConditionalConclusion : Prop :=
  ∀ S H θ ρ C, Conditions123 S H θ ρ → 0 < C →
    (∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C) → Lemma2Conclusions S H θ ρ →
    ∀ ε1 ξ (ν : Fin 8 → ℝ), 0 < ε1 → 0 < ξ → ξ < ε1 / (16 * C ^ 2) →
      (∀ i, 0 < ν i) → (∑ i, ν i) = ε1 / 2 → EarlierSixRates S θ ρ C ν →
      ∀ ε, ε1 < ε →
      scaledProbabilityLimsup S (fun q π => ε ≤ |centeredUpperError S q π|) ≤
        scaledProbabilityLimsup S (fun q π => ε1 ≤ |centeredUpperError S q π|) ∧
      scaledProbabilityLimsup S (fun q π => ε1 ≤ |centeredUpperError S q π|) ≤
        ENNReal.ofReal (C ^ 4 * coefficientSum θ ρ ν + lastTermRate θ ρ C ε1 ξ)

def coefficientRoots (θ ρ : ℝ) (i : Fin 8) : ℝ :=
  (termRateCoefficient θ ρ i) ^ (1 / 3 : ℝ)

def rootSum (θ ρ : ℝ) : ℝ := ∑ i, coefficientRoots θ ρ i

def optimalAllocation (θ ρ s : ℝ) (i : Fin 8) : ℝ :=
  s * coefficientRoots θ ρ i / rootSum θ ρ

def AllocationMinimum : Prop :=
  ∀ θ ρ, 0 < θ → θ ≤ 1 → 0 < ρ → ρ < 1 → ∀ s, 0 < s →
    (∀ i, 0 < termRateCoefficient θ ρ i) ∧
    (∀ i, 0 < optimalAllocation θ ρ s i) ∧
    (∑ i, optimalAllocation θ ρ s i) = s ∧
    coefficientSum θ ρ (optimalAllocation θ ρ s) = (rootSum θ ρ) ^ 3 / s ^ 2 ∧
    ∀ ν : Fin 8 → ℝ, (∀ i, 0 < ν i) → (∑ i, ν i) = s →
      (rootSum θ ρ) ^ 3 / s ^ 2 ≤ coefficientSum θ ρ ν

/-- The dependence on C and the allocation parameters is explicit. -/
def optimizedUpperRate (θ ρ C ε1 : ℝ) : ℝ :=
  4 * (rootSum θ ρ) ^ 3 / ε1 ^ 2 +
    lastTermRate θ ρ C ε1 (ε1 / (32 * C ^ 2)) / C ^ 4

def OptimizedUpperConclusion : Prop :=
  ∀ S H θ ρ C, Conditions123 S H θ ρ → 0 < C →
    (∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C) → Lemma2Conclusions S H θ ρ →
    ∀ ε1, 0 < ε1 →
    (∀ ν : Fin 8 → ℝ, (∀ i, 0 < ν i) → (∑ i, ν i) = ε1 / 2 →
      EarlierSixRates S θ ρ C ν) →
    0 < optimizedUpperRate θ ρ C ε1 ∧
    ∀ ε, ε1 < ε → scaledProbabilityLimsup S (fun q π =>
      ε ≤ |centeredUpperError S q π|) ≤ ENNReal.ofReal (C ^ 4 * optimizedUpperRate θ ρ C ε1)

def lowerLastIntegralTerm (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (π : Assignment d) : ℝ :=
  (2 * d.N / ((d.N : ℝ) - 1)) *
    (∫ x in (-C)..C, ∫ y in (-C)..C,
      frechetCDF (empiricalCDF (observedTreatment d y1 π))
        (empiricalCDF (observedControl d y0 π)) .L x y -
      frechetCDF (empiricalCDF y1) (empiricalCDF y0) .L x y)

def lowerSevenTerms (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (π : Assignment d) (j : Fin 7) : ℝ :=
  if j = 6 then lowerLastIntegralTerm d y1 y0 C π else sevenTerms d y1 y0 C π j

def lowerAllocation (ν : Fin 8 → ℝ) (ε2 ε3 : ℝ) (j : Fin 7) : ℝ :=
  if j = 6 then ε2 + ε3 else correctedAllocation ν 0 j

def LowerQuantileRepresentation : Prop :=
  ∀ {m k : ℕ}, 0 < m → 0 < k → ∀ (a : Fin m → ℝ) (b : Fin k → ℝ) C,
    0 ≤ C → (∀ i, |a i| ≤ C) → (∀ i, |b i| ≤ C) →
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b (1 - u)) =
      -C ^ 2 + C * (finiteMean a + finiteMean b) +
        ∫ x in (-C)..C, ∫ y in (-C)..C, frechetCDF (empiricalCDF a) (empiricalCDF b) .L x y

def LowerFiniteFacts : Prop :=
  ∀ d (y1 y0 : Fin d.N → ℝ) C, 0 ≤ C → (∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C) →
    (∀ π, (d.N : ℝ) * (estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L) =
      sevenTotal (lowerSevenTerms d y1 y0 C π)) ∧
    (∀ (a : Fin 7 → ℝ) ε, (∀ j, 0 < a j) → (∑ j, a j) ≤ ε →
      (∀ π, ε ≤ (d.N : ℝ) * |estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L| →
        ∃ j, a j ≤ |lowerSevenTerms d y1 y0 C π j|) ∧
      designProbability d (fun π => ε ≤ (d.N : ℝ) *
        |estimatedVariance d y1 y0 .L π - populationBound d y1 y0 .L|) ≤
        ∑ j, designProbability d (fun π => a j ≤ |lowerSevenTerms d y1 y0 C π j|)) ∧
    (∀ π, |lowerLastIntegralTerm d y1 y0 C π| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) *
        (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) +
         cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))) ∧
    (0 < C → ∀ ε2 ε3, 0 < ε2 → 0 < ε3 → ∀ π,
      ε2 + ε3 ≤ |lowerLastIntegralTerm d y1 y0 C π| →
      ((d.N : ℝ) - 1) * ε2 / (8 * d.N * C ^ 2) ≤
        cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) ∨
      ((d.N : ℝ) - 1) * ε3 / (8 * d.N * C ^ 2) ≤
        cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))

def LowerConditionalConclusion : Prop :=
  ∀ S H θ ρ C, Conditions123 S H θ ρ → 0 < C →
    (∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C) → Lemma2Conclusions S H θ ρ →
    ∀ ε1 ε2 ε3 ξ2 ξ3 (ν : Fin 8 → ℝ),
      0 < ε1 → 0 < ε2 → 0 < ε3 →
      0 < ξ2 → ξ2 < ε2 / (8 * C ^ 2) → 0 < ξ3 → ξ3 < ε3 / (8 * C ^ 2) →
      (∀ i, 0 < ν i) → (∑ i, ν i) = ε1 →
      (scaledProbabilityLimsup S (fun q π => ε2 + ε3 ≤
        |lowerLastIntegralTerm (S.design q) (rowOutcomes S true q)
          (rowOutcomes S false q) C π|) ≤
        ENNReal.ofReal (marginalTailRate θ ρ true (ε2 / (8 * C ^ 2) - ξ2) +
          marginalTailRate θ ρ false (ε3 / (8 * C ^ 2) - ξ3))) ∧
      (EarlierSixRates S θ ρ C ν →
        scaledProbabilityLimsup S (fun q π => ε1 + ε2 + ε3 ≤ rowSize S q *
          |rowEstimate S .L q π - rowBound S .L q|) ≤
          ENNReal.ofReal (C ^ 4 * coefficientSum θ ρ ν +
            marginalTailRate θ ρ true (ε2 / (8 * C ^ 2) - ξ2) +
            marginalTailRate θ ρ false (ε3 / (8 * C ^ 2) - ξ3)))

/-- P022-T6; pp. 865 and 867–868 (PDF pp. 16 and 18–19), Proposition 2 on p. 863.
The corrected upper seven-term budget uses sum nu=epsilon1/2 and last tolerance
epsilon1/2, and is centered at the sharp upper bound. The finite decomposition,
event inclusion, union bound and last-term CDF bound hold. Conditional on the
Lemma 2 conclusions, universal positive nonincreasing integer functions give the
corrected last-term limit; conditional also on (17)–(22), the concluding bounds
hold. The cubic-root allocation attains their minimum and gives a positive rate
function independent of the sequence. The lower endpoint retains sum nu=epsilon1
and last tolerance epsilon2+epsilon3, with its decomposition, finite budget and
conditional limits. The reciprocal thresholds require C>0; at C=0 both last
integrals vanish. The usual measure-theoretic conditions are assumed. -/
def T6WholeStatement : Prop :=
  T6Statement ∧ UniversalCDFRates ∧ UpperLastLimit ∧ UpperConditionalConclusion ∧
  AllocationMinimum ∧ OptimizedUpperConclusion ∧ LowerFiniteFacts ∧
  (∀ (ν : Fin 8 → ℝ) ε1 ε2 ε3, (∑ i, ν i) = ε1 →
    (∑ j, lowerAllocation ν ε2 ε3 j) = ε1 + ε2 + ε3) ∧
  LowerConditionalConclusion ∧
  (∀ d (y1 y0 : Fin d.N → ℝ) π,
    lastIntegralTerm d y1 y0 0 π = 0 ∧ lowerLastIntegralTerm d y1 y0 0 π = 0)

def LawThirdMomentsFinite (H : JointLaw) : Prop :=
  ∀ t : Bool, Integrable (fun p : ℝ × ℝ => |if t then p.1 else p.2| ^ 3)
    (H : Measure (ℝ × ℝ))

def waldCoverage (S : ExperimentSequence)
    (W : (q : ℕ) → Assignment (S.design q) → ℝ) (α : ℝ) (q : ℕ) : ℝ :=
  designProbability (S.design q) (fun π =>
    |effectError S q π| ≤ normalCritical α * Real.sqrt (W q π))

def gaussianWaldCoverage (α v s : ℝ) : ℝ :=
  2 * normalCDF (normalCritical α * Real.sqrt (v / s)) - 1

/-- Assurance concerns all admissible nonsingular joint laws with these marginals,
all nested populations realizing those laws, and consistent nonnegative Wald inputs.
The normal critical value is fixed. Width is compared at its leading N^(-1/2) scale. -/
def AssuredLeadingVariance (H : JointLaw) (θ ρ v : ℝ) : Prop :=
  0 ≤ v ∧ ∀ (J : JointLaw), J ∈ compatibleLaws H →
    ∀ S, Conditions123 S J θ ρ → BoundedThirdMoments S → NonsingularLaw J →
    ∀ W : (q : ℕ) → Assignment (S.design q) → ℝ,
      (∀ q π, 0 ≤ W q π) →
      designConvergence S.design (fun q π => rowSize S q * W q π) v →
      ∀ α, 0 < α → α < 1 → ∃ c : ℝ,
        Tendsto (waldCoverage S W α) atTop (𝓝 c) ∧ 1 - α ≤ c

def CorollaryCore : Prop :=
  ∀ S H θ ρ, Conditions123 S H θ ρ → BoundedThirdMoments S → NonsingularLaw H →
    0 < gamma H θ ρ ∧ gamma H θ ρ ≤ 1 ∧
    Tendsto (fun q => rowSize S q * rowTrueVariance S q) atTop
      (𝓝 (limitingTrueVariance H θ ρ)) ∧
    weakStandardNormal S (fun q π => effectError S q π /
      Real.sqrt (gamma H θ ρ * rowEstimate S .H q π)) ∧
    ∀ α, 0 < α → α < 1 →
      Tendsto (waldCoverage S (rowEstimate S .H) α) atTop
        (𝓝 (2 * normalCDF (normalCritical α / Real.sqrt (gamma H θ ρ)) - 1)) ∧
      1 - α ≤ 2 * normalCDF (normalCritical α / Real.sqrt (gamma H θ ρ)) - 1

def CorollaryMomentFacts : Prop :=
  ∀ S H θ ρ, Conditions123 S H θ ρ → BoundedThirdMoments S → NonsingularLaw H →
    LawFunctionalsDefined H ∧ LawThirdMomentsFinite H ∧
    0 < limitingTrueVariance H θ ρ ∧
    limitingTrueVariance H θ ρ ≤ limitingBound H θ ρ .H ∧
    Tendsto (fun q => rowSize S q * rowBound S .H q) atTop
      (𝓝 (limitingBound H θ ρ .H))

def WaldInputCoverage : Prop :=
  ∀ S H θ ρ, Conditions123 S H θ ρ → BoundedThirdMoments S → NonsingularLaw H →
    ∀ (W : (q : ℕ) → Assignment (S.design q) → ℝ) v,
      (∀ q π, 0 ≤ W q π) → 0 ≤ v →
      designConvergence S.design (fun q π => rowSize S q * W q π) v →
      ∀ α, 0 < α → α < 1 → Tendsto (waldCoverage S W α) atTop
        (𝓝 (gaussianWaldCoverage α v (limitingTrueVariance H θ ρ)))

/-- P022-T17; Corollary 1, p. 856 (PDF p. 7), Remark 4, p. 857 (PDF p. 8).
Conditions 1–3, uniformly bounded third moments and a nonsingular limiting law
give the actual and upper variance limits, gamma in (0,1], the studentized normal
limit, and the stated Wald coverage limit at least nominal. No positivity of
every finite estimate is assumed; division is totalized on exceptional rows.
The sharp upper variance is the least leading variance input assuring nominal
Wald coverage uniformly over admissible joint laws with the given marginals.
Every smaller nonnegative input is defeated by a nonsingular compatible law and
a nested fixed-outcome population realizing it. The usual measure-theoretic
conditions are assumed, and existence of the moments and extrema is concluded. -/
def T17WholeStatement : Prop :=
  CorollaryCore ∧ CorollaryMomentFacts ∧ WaldInputCoverage ∧
  ∀ S H θ ρ, Conditions123 S H θ ρ → BoundedThirdMoments S → NonsingularLaw H →
    (∀ v, 0 ≤ v → (AssuredLeadingVariance H θ ρ v ↔ limitingBound H θ ρ .H ≤ v)) ∧
    (∀ v, 0 ≤ v → v < limitingBound H θ ρ .H →
      ∃ (J : JointLaw) (R : ExperimentSequence),
        J ∈ compatibleLaws H ∧ Conditions123 R J θ ρ ∧ BoundedThirdMoments R ∧
        NonsingularLaw J ∧ v < limitingTrueVariance J θ ρ ∧
        ∀ (W : (q : ℕ) → Assignment (R.design q) → ℝ),
          (∀ q π, 0 ≤ W q π) →
          designConvergence R.design (fun q π => rowSize R q * W q π) v →
          ∀ α, 0 < α → α < 1 →
            Tendsto (waldCoverage R W α) atTop
              (𝓝 (gaussianWaldCoverage α v (limitingTrueVariance J θ ρ))) ∧
            gaussianWaldCoverage α v (limitingTrueVariance J θ ρ) < 1 - α)

end
end SAP.P022
