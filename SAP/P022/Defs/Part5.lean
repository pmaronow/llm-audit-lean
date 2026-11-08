import Mathlib
import SAP.P022.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option linter.unusedVariables false
noncomputable section

/-- The preserved P022-T1 statement over the shared SAP definitions. -/
def T1Statement : Prop :=
  Conditions123 reciprocalWitness originLaw 1 (1 / 2) ∧
    (∀ q t, cdfDistance (lawCDF originLaw t)
      (empiricalCDF (rowOutcomes reciprocalWitness t q)) = 1) ∧
    (∀ q t π, cdfDistance (lawCDF originLaw t)
      (sampledCDF reciprocalWitness t q π) = 1) ∧
    (∀ t, scaledProbabilityLimsup reciprocalWitness (fun q π =>
      (1 / 2 : ℝ) ≤ cdfDistance (lawCDF originLaw t)
        (sampledCDF reciprocalWitness t q π)) = ⊤) ∧
    ¬Lemma2Conclusions reciprocalWitness originLaw 1 (1 / 2)

/-- The preserved P022-T2 statement over the shared SAP definitions. -/
def T2Statement : Prop :=
  ∀ (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hleft : AtomLeftConvergence S H),
(∀ η, 0 < η → 0 < correctedPartitionInteger η) ∧
    (∀ a b, 0 < a → a ≤ b → correctedPartitionInteger b ≤ correctedPartitionInteger a) ∧
    (∀ t, Tendsto (fun q => cdfDistance (lawCDF H t)
      (empiricalCDF (rowOutcomes S t q))) atTop (𝓝 0)) ∧
    (∀ η, 0 < η →
      scaledProbabilityLimsup S (fun q π => η ≤
        cdfDistance (lawCDF H true) (sampledCDF S true q π)) ≤
        ENNReal.ofReal ((1 - θ * ρ) * correctedPartitionInteger η / (θ * ρ * η ^ 2)) ∧
      scaledProbabilityLimsup S (fun q π => η ≤
        cdfDistance (lawCDF H false) (sampledCDF S false q π)) ≤
        ENNReal.ofReal ((1 - θ * (1 - ρ)) * correctedPartitionInteger η /
          (θ * (1 - ρ) * η ^ 2)))

/-- The preserved P022-T3 statement over the shared SAP definitions. -/
def T3Statement : Prop :=
  (∀ (d : Design) (y1 y0 : Fin d.N → ℝ) (C c : ℝ)
    (hC : 0 ≤ C) (hy : ∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C)
    (hc : 0 < c) (hm : c * d.N ≤ d.m) (hk : c * d.N ≤ d.k)
    (hN : 2 / c ≤ (d.N : ℝ)),
let D1 := fun π => integratedCDFError C y1 (observedTreatment d y1 π)
    let D0 := fun π => integratedCDFError C y0 (observedControl d y0 π)
    designExpectation d (fun π => D1 π ^ 2) ≤ C ^ 2 * ((d.N : ℝ) - d.m) /
      (((d.N : ℝ) - 1) * d.m) ∧
    C ^ 2 * ((d.N : ℝ) - d.m) / (((d.N : ℝ) - 1) * d.m) ≤ C ^ 2 / (c * d.N) ∧
    designExpectation d (fun π => D0 π ^ 2) ≤ C ^ 2 * ((d.N : ℝ) - d.k) /
      (((d.N : ℝ) - 1) * d.k) ∧
    C ^ 2 * ((d.N : ℝ) - d.k) / (((d.N : ℝ) - 1) * d.k) ≤ C ^ 2 / (c * d.N) ∧
    designExpectation d (fun π => (D1 π + D0 π) ^ 2) ≤ 4 * C ^ 2 / (c * d.N) ∧
    (∀ B π, (d.N : ℝ) * |estimatedVariance d y1 y0 B π - populationBound d y1 y0 B| ≤
      (16 / c + 8) * C * (D1 π + D0 π) + 8 * C ^ 2 / (c ^ 2 * d.N)) ∧
    (∀ ε, 0 < ε → 16 * C ^ 2 / (c ^ 2 * ε) ≤ (d.N : ℝ) → ∀ B,
      designProbability d (fun π => ε ≤ (d.N : ℝ) *
        |estimatedVariance d y1 y0 B π - populationBound d y1 y0 B|) ≤
          16 * (16 / c + 8) ^ 2 * C ^ 4 / (c * d.N * ε ^ 2))) ∧
(∀ (S : ExperimentSequence) (θ ρ C : ℝ)
    (hθ : 0 < θ ∧ θ ≤ 1) (hρ : 0 < ρ ∧ ρ < 1)
    (hm : Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N)
      atTop (𝓝 (θ * ρ)))
    (hn : Tendsto (fun q => (((S.design q).m : ℝ) + (S.design q).k) / (S.design q).N)
      atTop (𝓝 θ))
    (hC : 0 ≤ C) (hy : ∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C),
∀ ε c, 0 < ε → 0 < c → c < min (θ * ρ) (θ * (1 - ρ)) → ∀ B,
      scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
        |estimatedVariance (S.design q) (rowOutcomes S true q)
          (rowOutcomes S false q) B π - populationBound (S.design q)
            (rowOutcomes S true q) (rowOutcomes S false q) B|) ≤
        ENNReal.ofReal (16 * (16 / c + 8) ^ 2 * C ^ 4 / (c * ε ^ 2)))

/-- The preserved P022-T4 statement over the shared SAP definitions. -/
def T4Statement : Prop :=
  ∀ (d : Design) (y1 y0 : Fin d.N → ℝ) (x : ℝ),
let G := empiricalCDF y1 x
    let F := empiricalCDF y0 x
    let Gh := fun π => empiricalCDF (observedTreatment d y1 π) x
    let Fh := fun π => empiricalCDF (observedControl d y0 π) x
    designExpectation d Gh = G ∧ designExpectation d Fh = F ∧
    designVariance d Gh = ((d.N : ℝ) - d.m) / (((d.N : ℝ) - 1) * d.m) * G * (1 - G) ∧
    designVariance d Fh = ((d.N : ℝ) - d.k) / (((d.N : ℝ) - 1) * d.k) * F * (1 - F) ∧
    designVariance d Gh ≤ ((d.N : ℝ) - d.m) / (4 * ((d.N : ℝ) - 1) * d.m) ∧
    designVariance d Fh ≤ ((d.N : ℝ) - d.k) / (4 * ((d.N : ℝ) - 1) * d.k) ∧
    finiteVariance (fun i => if y1 i ≤ x then 1 else 0) = G * (1 - G) ∧
    finiteVariance (fun i => if y0 i ≤ x then 1 else 0) = F * (1 - F)

/-- The preserved P022-T5 statement over the shared SAP definitions. -/
def T5Statement : Prop :=
  (empiricalCDF (fun _ : Fin 4 => (1 : ℝ)) 0 = 0 ∧
    finiteVariance (fun _ : Fin 4 => (if (1 : ℝ) ≤ 0 then 1 else 0)) = 0 ∧
    (∀ π : Assignment fourUnitDesign,
      empiricalCDF (observedTreatment fourUnitDesign (fun _ => 1) π) 0 = 0) ∧
    designVariance fourUnitDesign (fun π =>
      empiricalCDF (observedTreatment fourUnitDesign (fun _ => 1) π) 0) = 0 ∧
    ((4 - 2 : ℝ) / (4 * (4 - 1) * 2) = 1 / 12) ∧ (0 : ℝ) ≠ 1 / 12) ∧
(Nat.choose 4 2 = 6) ∧
(∀ (d : Design) (y : Fin d.N → ℝ) (x : ℝ),
    (designVariance d (fun π => empiricalCDF (observedTreatment d y π) x) =
      ((d.N : ℝ) - d.m) / (4 * ((d.N : ℝ) - 1) * d.m)) ↔
      empiricalCDF y x = 1 / 2)

/-- The preserved P022-T6 statement over the shared SAP definitions. -/
def T6Statement : Prop :=
  (∀ (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hy : ∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C),
(∀ π, ((d.N : ℝ) * (estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H)) =
      sevenTotal (sevenTerms d y1 y0 C π)) ∧
    (∀ a : Fin 7 → ℝ, ∀ ε, (∀ j, 0 < a j) → (∑ j, a j) ≤ ε →
      designProbability d (fun π => ε ≤ (d.N : ℝ) *
        |estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H|) ≤
      ∑ j, designProbability d (fun π => a j ≤ |sevenTerms d y1 y0 C π j|)) ∧
    (∀ π, |lastIntegralTerm d y1 y0 C π| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) *
        max (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
          (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))) ∧
    (0 < C → ∀ x, 0 < x → ∀ π, x ≤ |lastIntegralTerm d y1 y0 C π| →
      ((d.N : ℝ) - 1) * x / (8 * d.N * C ^ 2) ≤
        cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1) ∨
      ((d.N : ℝ) - 1) * x / (8 * d.N * C ^ 2) ≤
        cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0))) ∧
(∀ (d : Design) (y1 y0 : Fin d.N → ℝ) (C : ℝ),
      0 ≤ C → (∀ i, |y1 i| ≤ C ∧ |y0 i| ≤ C) →
      ∀ (a : Fin 7 → ℝ) (ε : ℝ), (∀ j, 0 < a j) → (∑ j, a j) ≤ ε →
      ∀ π, ε ≤ (d.N : ℝ) * |estimatedVariance d y1 y0 .H π - populationBound d y1 y0 .H| →
        ∃ j, a j ≤ |sevenTerms d y1 y0 C π j|) ∧
(∀ (ν : Fin 8 → ℝ) (ε1 : ℝ)
    (hν : (∑ i, ν i) = ε1 / 2),
(∑ j, correctedAllocation ν ε1 j) = ε1) ∧
(∀ (ν : Fin 8 → ℝ) (ε1 : ℝ), (∑ i, ν i) = ε1 →
      ν 0 + ν 1 + ν 2 + ν 3 + (ν 4 + ν 5) + (ν 6 + ν 7) + (1 - ε1) = 1) ∧
(∀ (S : ExperimentSequence) (H : JointLaw) (θ ρ C : ℝ)
    (h : Conditions123 S H θ ρ) (hC : 0 < C)
    (hy : ∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C)
    (hLemma : Lemma2Conclusions S H θ ρ) (ε1 ξ : ℝ)
    (hε1 : 0 < ε1) (hξ : 0 < ξ ∧ ξ < ε1 / (16 * C ^ 2)),
∃ K1 K0 : ℝ → ℕ, ∃ κ : ℝ,
      (∀ η, 0 < η →
        scaledProbabilityLimsup S (fun q π => η ≤
          cdfDistance (lawCDF H true) (sampledCDF S true q π)) ≤
          ENNReal.ofReal ((1 - θ * ρ) * K1 η / (θ * ρ * η ^ 2)) ∧
        scaledProbabilityLimsup S (fun q π => η ≤
          cdfDistance (lawCDF H false) (sampledCDF S false q π)) ≤
          ENNReal.ofReal ((1 - θ * (1 - ρ)) * K0 η / (θ * (1 - ρ) * η ^ 2))) ∧
      (let η := ε1 / (16 * C ^ 2) - ξ
       C ^ 4 * κ = (1 - θ * ρ) * K1 η / (θ * ρ * η ^ 2) +
         (1 - θ * (1 - ρ)) * K0 η / (θ * (1 - ρ) * η ^ 2)) ∧
      scaledProbabilityLimsup S (fun q π => ε1 / 2 ≤
        |lastIntegralTerm (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) C π|) ≤
          ENNReal.ofReal (C ^ 4 * κ) ∧
      (∀ ν : Fin 8 → ℝ, (∀ i, 0 < ν i) → (∑ i, ν i) = ε1 / 2 →
        (∀ j : Fin 6,
          scaledProbabilityLimsup S (fun q π => correctedAllocation ν ε1
            ⟨j.val, by omega⟩ ≤ |sevenTerms (S.design q)
              (rowOutcomes S true q) (rowOutcomes S false q) C π ⟨j.val, by omega⟩|) ≤
            ENNReal.ofReal (C ^ 4 * (match j.val with
              | 0 => termRateCoefficient θ ρ 0 / (ν 0) ^ 2
              | 1 => termRateCoefficient θ ρ 1 / (ν 1) ^ 2
              | 2 => termRateCoefficient θ ρ 2 / (ν 2) ^ 2
              | 3 => termRateCoefficient θ ρ 3 / (ν 3) ^ 2
              | 4 => termRateCoefficient θ ρ 4 / (ν 4) ^ 2 + termRateCoefficient θ ρ 5 / (ν 5) ^ 2
              | _ => termRateCoefficient θ ρ 6 / (ν 6) ^ 2 + termRateCoefficient θ ρ 7 / (ν 7) ^ 2))) →
        ∀ ε, ε1 < ε →
        scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
          |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π -
            populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|) ≤
        scaledProbabilityLimsup S (fun q π => ε1 ≤ ((S.design q).N : ℝ) *
          |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π -
            populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|) ∧
        scaledProbabilityLimsup S (fun q π => ε1 ≤ ((S.design q).N : ℝ) *
          |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π -
            populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|) ≤
          ENNReal.ofReal (C ^ 4 * ((∑ i, termRateCoefficient θ ρ i / (ν i) ^ 2) + κ))))

/-- The preserved P022-T7 statement over the shared SAP definitions. -/
def T7Statement : Prop :=
  Conditions123 cornerWitness cornerLaw 1 (1 / 2) ∧
    AtomLeftConvergence cornerWitness cornerLaw ∧
    (∀ i, |cornerWitness.y1 i| ≤ 1 ∧ |cornerWitness.y0 i| ≤ 1) ∧
    scaledProbabilityLimsup cornerWitness (fun q π => (1 - 1 : ℝ) ≤
      |lastIntegralTerm (cornerWitness.design q) (rowOutcomes cornerWitness true q)
        (rowOutcomes cornerWitness false q) 1 π|) = ⊤ ∧
    (∀ ε, 0 < ε → ε < (1 / 2 : ℝ) →
      Filter.limsup (fun r => ENNReal.ofReal
        (((cornerWitness.design (4 * r)).N : ℝ) *
          designProbability (cornerWitness.design (4 * r)) (fun π => ε ≤
            ((cornerWitness.design (4 * r)).N : ℝ) *
            |estimatedVariance (cornerWitness.design (4 * r))
              (rowOutcomes cornerWitness true (4 * r))
              (rowOutcomes cornerWitness false (4 * r)) .H π -
             trueVariance (cornerWitness.design (4 * r))
              (rowOutcomes cornerWitness true (4 * r))
              (rowOutcomes cornerWitness false (4 * r))|))) atTop = ⊤)

/-- The preserved P022-T8 statement over the shared SAP definitions. -/
def T8Statement : Prop :=
  ∀ {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (a : Fin m → ℝ) (b : Fin k → ℝ),
(∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r) = 1 ∧
    (∀ r < partitionCells m k, ∀ u,
      partitionPoint m k r < u → u < partitionPoint m k (r + 1) →
      Nat.ceil ((m : ℝ) * u) = Nat.ceil ((m : ℝ) * partitionPoint m k (r + 1)) ∧
      Nat.ceil ((k : ℝ) * u) = Nat.ceil ((k : ℝ) * partitionPoint m k (r + 1)) ∧
      k + 1 - Nat.ceil ((k : ℝ) * u) =
        Nat.ceil ((k : ℝ) * partitionPoint m k (partitionCells m k - r))) ∧
    (∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r *
      empiricalQuantile a (cellMidpoint m k r)) = finiteMean a ∧
    (∀ B, (∑ r ∈ Finset.range (partitionCells m k), cellWidth m k r *
      empiricalQuantile b (if B = BoundSide.H then cellMidpoint m k r else
        1 - cellMidpoint m k r)) = finiteMean b) ∧
    (∀ B, midpointCovariance a b B = sharpCovariance a b B) ∧
    (∀ N, m + k ≤ N → ∀ B, varianceExpression N m k (marginalVarianceEstimate N a)
      (marginalVarianceEstimate N b) (midpointCovariance a b B) = estimateBound N a b B) ∧
    (∀ i, (∑ j, overlapWeight m k i j) = 1 / (m : ℝ)) ∧
    (∀ j, (∑ i, overlapWeight m k i j) = 1 / (k : ℝ)) ∧
    (∀ B, sharpCovariance a b B = ∑ i, ∑ j, overlapWeight m k i j *
      (orderStatistic a (i.val + 1) - finiteMean a) *
      (orderStatistic b (if B = BoundSide.H then j.val + 1 else k - j.val) - finiteMean b))

/-- The preserved P022-T9 statement over the shared SAP definitions. -/
def T9Statement : Prop :=
  (trueVariance fourUnitDesign (fun _ => 1) (fun _ => 1) = 0 ∧
    (∀ B, estimateBound 4 (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) B = 0 ∧
      printedCodeBound 4 (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) B =
        -(1 / 50331648 : ℝ))) ∧
(∀ {N m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hN : m + k ≤ N) (a : Fin m → ℝ) (b : Fin k → ℝ)
    (hw : ∀ r < partitionCells m k, 2 * codeEpsilon < cellWidth m k r),
printedCodeBound N a b .H - estimateBound N a b .H =
      -4 * codeEpsilon * orderStatistic a 1 * orderStatistic b 1 / ((N : ℝ) - 1) ∧
    printedCodeBound N a b .L - estimateBound N a b .L =
      -4 * codeEpsilon * orderStatistic a 1 * orderStatistic b k / ((N : ℝ) - 1))

end
end SAP.P022
