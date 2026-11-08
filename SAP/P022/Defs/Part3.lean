import Mathlib
import SAP.P022.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
noncomputable section

-- SAP version of AronowAudit/P022/P022_Variance.lean:Lemma2Conclusions
def Lemma2Conclusions (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ) : Prop :=
  (∀ t, Tendsto (fun q => cdfDistance (lawCDF H t)
      (empiricalCDF (rowOutcomes S t q))) atTop (𝓝 0)) ∧
  ∃ K1 K0 : ℝ → ℕ,
    (∀ η, 0 < η → 0 < K1 η ∧ 0 < K0 η) ∧
    (∀ a b, 0 < a → a ≤ b → K1 b ≤ K1 a ∧ K0 b ≤ K0 a) ∧
    (∀ η, 0 < η →
      scaledProbabilityLimsup S (fun q π =>
        η ≤ cdfDistance (lawCDF H true) (sampledCDF S true q π)) ≤
        ENNReal.ofReal ((1 - θ * ρ) * K1 η / (θ * ρ * η ^ 2))) ∧
    (∀ η, 0 < η →
      scaledProbabilityLimsup S (fun q π =>
        η ≤ cdfDistance (lawCDF H false) (sampledCDF S false q π)) ≤
        ENNReal.ofReal ((1 - θ * (1 - ρ)) * K0 η / (θ * (1 - ρ) * η ^ 2)))

-- SAP version of AronowAudit/P022/P022_Variance.lean:reciprocalWitness
def reciprocalWitness : ExperimentSequence where
  design q := {
    N := q + 4
    m := (q + 4) / 2
    k := q + 4 - (q + 4) / 2
    population_min := by omega
    treatment_min := by omega
    control_min := by omega
    sample_le := by omega }
  size q := rfl
  y1 i := -(1 / ((i : ℝ) + 1))
  y0 i := -(1 / ((i : ℝ) + 1))

-- SAP version of AronowAudit/P022/P022_Variance.lean:originLaw
def originLaw : JointLaw := ⟨Measure.dirac (0, 0), by infer_instance⟩

-- SAP version of AronowAudit/P022/P022_Variance.lean:integratedCDFError
def integratedCDFError {N s : ℕ} (C : ℝ) (y : Fin N → ℝ) (a : Fin s → ℝ) : ℝ :=
  ∫ x in (-C)..C, |empiricalCDF a x - empiricalCDF y x|

-- SAP version of AronowAudit/P022/P022_Variance.lean:fourUnitDesign
def fourUnitDesign : Design := ⟨4, 2, 2, by omega, by omega, by omega, by omega⟩

-- SAP version of AronowAudit/P022/P022_Variance.lean:partitionKnots
def partitionKnots (m k : ℕ) : List ℝ :=
  (((Finset.range (m + 1)).image (fun i : ℕ => (i : ℝ) / m)) ∪
   ((Finset.range (k + 1)).image (fun j : ℕ => (j : ℝ) / k))).sort (· ≤ ·)

-- SAP version of AronowAudit/P022/P022_Variance.lean:partitionPoint
def partitionPoint (m k r : ℕ) : ℝ := (partitionKnots m k).getD r 0

-- SAP version of AronowAudit/P022/P022_Variance.lean:partitionCells
def partitionCells (m k : ℕ) : ℕ := (partitionKnots m k).length - 1

-- SAP version of AronowAudit/P022/P022_Variance.lean:cellWidth
def cellWidth (m k r : ℕ) : ℝ := partitionPoint m k (r + 1) - partitionPoint m k r

-- SAP version of AronowAudit/P022/P022_Variance.lean:cellMidpoint
def cellMidpoint (m k r : ℕ) : ℝ :=
  (partitionPoint m k r + partitionPoint m k (r + 1)) / 2

-- SAP version of AronowAudit/P022/P022_Variance.lean:midpointCovariance
def midpointCovariance {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (B : BoundSide) : ℝ :=
  ∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r *
    (empiricalQuantile a (cellMidpoint m k r) - finiteMean a) *
    (empiricalQuantile b (if B = .H then cellMidpoint m k r else
      1 - cellMidpoint m k r) - finiteMean b)

-- SAP version of AronowAudit/P022/P022_Variance.lean:overlapWeight
def overlapWeight (m k : ℕ) (i : Fin m) (j : Fin k) : ℝ :=
  max 0 (min (((i.val : ℝ) + 1) * k) (((j.val : ℝ) + 1) * m) -
    max ((i.val : ℝ) * k) ((j.val : ℝ) * m)) / ((m : ℝ) * k)

-- SAP version of AronowAudit/P022/P022_Variance.lean:codeEpsilon
def codeEpsilon : ℝ := 1 / 67108864

-- SAP version of AronowAudit/P022/P022_Variance.lean:codePoint
def codePoint (m k r : ℕ) : ℝ :=
  if r = 0 then codeEpsilon else partitionPoint m k r - codeEpsilon

-- SAP version of AronowAudit/P022/P022_Variance.lean:printedCodeBound
def printedCodeBound {m k : ℕ} (N : ℕ) (a : Fin m → ℝ) (b : Fin k → ℝ)
    (B : BoundSide) : ℝ :=
  varianceExpression N m k (marginalVarianceEstimate N a)
    (marginalVarianceEstimate N b)
    ((∑ r ∈ Finset.range (partitionCells m k),
      (codePoint m k (r + 1) - codePoint m k r) *
      empiricalQuantile a (codePoint m k (r + 1)) *
      (if B = .H then orderStatistic b (Nat.ceil ((k : ℝ) * codePoint m k (r + 1)))
       else orderStatistic b (k + 1 - Nat.ceil ((k : ℝ) * codePoint m k (r + 1))))) -
      finiteMean a * finiteMean b)

-- SAP version of AronowAudit/P022/P022_Variance.lean:sortedValues
def sortedValues {N : ℕ} (y : Fin N → ℝ) : Fin N → ℝ :=
  fun i => (sortedOutcomes y).getD i.val 0

-- SAP version of AronowAudit/P022/P022_Variance.lean:lawMean
def lawMean (H : JointLaw) (t : Bool) : ℝ :=
  ∫ p, (if t then p.1 else p.2) ∂(H : Measure (ℝ × ℝ))

-- SAP version of AronowAudit/P022/P022_Variance.lean:lawVariance
def lawVariance (H : JointLaw) (t : Bool) : ℝ :=
  ∫ p, ((if t then p.1 else p.2) - lawMean H t) ^ 2 ∂(H : Measure (ℝ × ℝ))

-- SAP version of AronowAudit/P022/P022_Variance.lean:lawCovariance
def lawCovariance (H : JointLaw) : ℝ :=
  ∫ p, (p.1 - lawMean H true) * (p.2 - lawMean H false) ∂(H : Measure (ℝ × ℝ))

-- SAP version of AronowAudit/P022/P022_Variance.lean:compatibleLaws
def compatibleLaws (H : JointLaw) : Set JointLaw :=
  {h | ∀ t x, lawCDF h t x = lawCDF H t x}

-- SAP version of AronowAudit/P022/P022_Variance.lean:limitingBound
def limitingBound (H : JointLaw) (θ ρ : ℝ) (B : BoundSide) : ℝ :=
  (1 - θ * ρ) / (θ * ρ) * lawVariance H true +
  (1 - θ * (1 - ρ)) / (θ * (1 - ρ)) * lawVariance H false +
  2 * (if B = .H then sSup (lawCovariance '' compatibleLaws H)
       else sInf (lawCovariance '' compatibleLaws H))

-- SAP version of AronowAudit/P022/P022_Variance.lean:boundConsistency
def boundConsistency (S : ExperimentSequence) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun q => designProbability (S.design q) (fun π =>
    ε ≤ max
      (((S.design q).N : ℝ) * |estimatedVariance (S.design q)
        (rowOutcomes S true q) (rowOutcomes S false q) .H π -
        populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|)
      (((S.design q).N : ℝ) * |estimatedVariance (S.design q)
        (rowOutcomes S true q) (rowOutcomes S false q) .L π -
        populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .L|)))
    atTop (𝓝 0)

-- SAP version of AronowAudit/P022/P022_Variance.lean:BoundedThirdMoments
def BoundedThirdMoments (S : ExperimentSequence) : Prop :=
  ∃ M : ℝ, ∀ q (t : Bool), finiteMean (fun i : Fin (S.design q).N =>
    |(if t then S.y1 else S.y0) i.val| ^ 3) ≤ M

-- SAP version of AronowAudit/P022/P022_Variance.lean:NonsingularLaw
def NonsingularLaw (H : JointLaw) : Prop :=
  ∀ a b c : ℝ, a ≠ 0 ∨ b ≠ 0 →
    ¬(∀ᵐ p ∂(H : Measure (ℝ × ℝ)), a * p.1 + b * p.2 = c)

-- SAP version of AronowAudit/P022/P022_Variance.lean:limitingTrueVariance
def limitingTrueVariance (H : JointLaw) (θ ρ : ℝ) : ℝ :=
  (1 - θ * ρ) / (θ * ρ) * lawVariance H true +
  (1 - θ * (1 - ρ)) / (θ * (1 - ρ)) * lawVariance H false + 2 * lawCovariance H

-- SAP version of AronowAudit/P022/P022_Variance.lean:gamma
def gamma (H : JointLaw) (θ ρ : ℝ) : ℝ :=
  limitingTrueVariance H θ ρ / limitingBound H θ ρ .H

-- SAP version of AronowAudit/P022/P022_Variance.lean:normalCDF
def normalCDF (x : ℝ) : ℝ :=
  (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal

-- SAP version of AronowAudit/P022/P022_Variance.lean:normalCritical
def normalCritical (α : ℝ) : ℝ := sInf {x | 1 - α / 2 ≤ normalCDF x}

-- SAP version of AronowAudit/P022/P022_Variance.lean:weakStandardNormal
def weakStandardNormal (S : ExperimentSequence)
    (Z : (q : ℕ) → Assignment (S.design q) → ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun q => designExpectation (S.design q) (fun π => f (Z q π))) atTop
      (𝓝 (∫ x, f x ∂ProbabilityTheory.gaussianReal 0 1))

-- SAP version of AronowAudit/P022/P022_Variance.lean:reciprocalThreshold
def reciprocalThreshold (q : ℕ) : ℝ := -(1 / (2 * ((q : ℝ) + 4)))

-- SAP version of AronowAudit/P022/P022_Variance.lean:correctedPartitionInteger
def correctedPartitionInteger (η : ℝ) : ℕ := 2 * Nat.ceil (4 / min η 1)

-- SAP version of AronowAudit/P022/P022_Variance.lean:frechetCDF
def frechetCDF (G F : ℝ → ℝ) (B : BoundSide) (x y : ℝ) : ℝ :=
  if B = .H then min (G x) (F y) else max 0 (G x + F y - 1)

-- SAP version of AronowAudit/P022/P022_Variance.lean:lastIntegralTerm
def lastIntegralTerm (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (π : Assignment d) : ℝ :=
  (2 * d.N / ((d.N : ℝ) - 1)) *
    (∫ x in (-C)..C, ∫ y in (-C)..C,
      frechetCDF (empiricalCDF (observedTreatment d y1 π))
        (empiricalCDF (observedControl d y0 π)) .H x y -
      frechetCDF (empiricalCDF y1) (empiricalCDF y0) .H x y)

-- SAP version of AronowAudit/P022/P022_Variance.lean:sevenTerms
def sevenTerms (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (π : Assignment d) : Fin 7 → ℝ :=
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  let β1 := (d.N : ℝ) * ((d.m : ℝ) - 1) / (d.m * ((d.N : ℝ) - 1))
  let β0 := (d.N : ℝ) * ((d.k : ℝ) - 1) / (((d.N : ℝ) - 1) * d.k)
  fun j => match j.val with
  | 0 => ((d.N : ℝ) - d.m) / ((d.m : ℝ) - 1) *
      (finiteMean (fun i => a i ^ 2) - β1 * finiteMean (fun i => y1 i ^ 2))
  | 1 => ((d.N : ℝ) - d.m) / ((d.m : ℝ) - 1) *
      (finiteMean a ^ 2 - β1 * finiteMean y1 ^ 2)
  | 2 => ((d.N : ℝ) - d.k) / ((d.k : ℝ) - 1) *
      (finiteMean (fun i => b i ^ 2) - β0 * finiteMean (fun i => y0 i ^ 2))
  | 3 => ((d.N : ℝ) - d.k) / ((d.k : ℝ) - 1) *
      (finiteMean b ^ 2 - β0 * finiteMean y0 ^ 2)
  | 4 => (2 * d.N / ((d.N : ℝ) - 1)) * C *
      (finiteMean a - finiteMean y1 + finiteMean b - finiteMean y0)
  | 5 => (2 * d.N / ((d.N : ℝ) - 1)) *
      (finiteMean a * finiteMean b - finiteMean y1 * finiteMean y0)
  | _ => lastIntegralTerm d y1 y0 C π

-- SAP version of AronowAudit/P022/P022_Variance.lean:sevenTotal
def sevenTotal (T : Fin 7 → ℝ) : ℝ :=
  T 0 - T 1 + T 2 - T 3 + T 4 - T 5 + T 6

-- SAP version of AronowAudit/P022/P022_Variance.lean:correctedAllocation
def correctedAllocation (ν : Fin 8 → ℝ) (ε1 : ℝ) : Fin 7 → ℝ :=
  fun j => match j.val with
  | 0 => ν 0 | 1 => ν 1 | 2 => ν 2 | 3 => ν 3
  | 4 => ν 4 + ν 5 | 5 => ν 6 + ν 7 | _ => ε1 / 2

end
end SAP.P022
