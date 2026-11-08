import Mathlib
import SAP.P022.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option linter.unusedVariables false
noncomputable section

/-- The preserved P022-T10 statement over the shared SAP definitions. -/
def T10Statement : Prop :=
  (∀ {m k N : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (hN : m + k ≤ N) (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide),
estimateBound N a b B =
      (1 / (m : ℝ) - 1 / (N : ℝ)) * sampleVariance a +
      (1 / (k : ℝ) - 1 / (N : ℝ)) * sampleVariance b +
      2 * sharpCovariance a b B / ((N : ℝ) - 1)) ∧
(∀ {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide),
Tendsto (fun r : ℕ => estimateBound (r + (m + k)) a b B) atTop
      (𝓝 (sampleVariance a / m + sampleVariance b / k))) ∧
(∀ (S : ExperimentSequence) (m k : ℕ), 2 ≤ m → 2 ≤ k →
    (∀ᶠ q : ℕ in atTop, (S.design q).m = m) →
    (∀ᶠ q : ℕ in atTop, (S.design q).k = k) →
    (∃ M : ℝ, ∀ q, finiteVariance (rowOutcomes S true q) ≤ M ∧
      finiteVariance (rowOutcomes S false q) ≤ M) →
    Tendsto (fun q => trueVariance (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q) -
      (finiteVariance (rowOutcomes S true q) / m +
       finiteVariance (rowOutcomes S false q) / k)) atTop (𝓝 0))

/-- The preserved P022-T12 statement over the shared SAP definitions. -/
def T12Statement.{u} : Prop :=
  (∀ (d : Design) (hn : d.m + d.k = d.N)
    (y : Fin d.N → ℝ),
designExpectation d (neymanEstimate d y y .H) ≤ trueVariance d y y) ∧
(∀ {ι : Type u} (s : Finset ι)
    (hs : s.Nonempty) (v : ι → ℝ) (hv : ∀ i ∈ s, 0 ≤ v i) (c : ℝ),
(𝔼 i ∈ s, c * Real.sqrt (v i)) ^ 2 ≤ c ^ 2 * (𝔼 i ∈ s, v i)) ∧
(∀ (c q d : ℝ)
    (hq : 391 / 2000 ≤ q) (hd0 : 0 ≤ d) (hd : d ≤ 867 / 500)
    (hwidth : d ^ 2 = c ^ 2 * q),
c ^ 2 ≤ 44217 / 2875) ∧
(∀ (c meanWidth meanVariance trueVariance bias : ℝ)
    (hc : c ^ 2 ≤ 44217 / 2875)
    (hmu : 0 ≤ meanVariance)
    (hw : 3447 / 2000 ≤ meanWidth)
    (hcs : meanWidth ^ 2 ≤ c ^ 2 * meanVariance)
    (ht : trueVariance ≤ 399 / 2000)
    (hb : bias ≤ -(13 / 2000))
    (hdef : meanVariance = trueVariance + bias),
False) ∧
(∀ (w v : ℝ)
    (hw : 3447 / 2000 ≤ w) (h : w ^ 2 ≤ (98 / 25 : ℝ) ^ 2 * v),
(11881809 / 61465600 : ℝ) ≤ v ∧ (193 / 1000 : ℝ) < v) ∧
    (∀ V b : ℝ, V ≤ 399 / 2000 → b ≤ -(13 / 2000) → V + b ≤ 193 / 1000)

/-- The preserved P022-T13 statement over the shared SAP definitions. -/
def T13Statement : Prop :=
  ∀ (d : Design) (y1 y0 : Fin d.N → ℝ),
    designExpectation d (estimatedEffect d y1 y0) = averageEffect d y1 y0 ∧
    trueVariance d y1 y0 = varianceExpression d.N d.m d.k
      (finiteVariance y1) (finiteVariance y0) (finiteCovariance y1 y0) ∧
    (∀ z1 z0 : Fin d.N → ℝ,
      List.Perm (List.ofFn z1) (List.ofFn y1) →
      List.Perm (List.ofFn z0) (List.ofFn y0) →
      sharpCovariance y1 y0 .L ≤ finiteCovariance z1 z0 ∧
      finiteCovariance z1 z0 ≤ sharpCovariance y1 y0 .H ∧
      populationBound d y1 y0 .L ≤ trueVariance d z1 z0 ∧
      trueVariance d z1 z0 ≤ populationBound d y1 y0 .H) ∧
    trueVariance d (sortedValues y1) (sortedValues y0) =
      populationBound d y1 y0 .H ∧
    trueVariance d (sortedValues y1) (fun i => sortedValues y0 i.rev) =
      populationBound d y1 y0 .L ∧
    (∀ J ∈ empiricalCompatibleLaws y1 y0,
      Integrable (fun p : ℝ × ℝ => p.1 * p.2) (J : Measure (ℝ × ℝ)) ∧
      sharpCovariance y1 y0 .L ≤ lawCovariance J ∧
      lawCovariance J ≤ sharpCovariance y1 y0 .H) ∧
    (∀ B, ∃ J ∈ empiricalCompatibleLaws y1 y0,
      lawCovariance J = sharpCovariance y1 y0 B ∧
      ∀ f : BoundedContinuousFunction (ℝ × ℝ) ℝ,
        (∫ p, f p ∂(J : Measure (ℝ × ℝ))) =
          ∫ u in (0 : ℝ)..1,
            f (empiricalQuantile y1 u, empiricalQuantile y0
              (if B = BoundSide.H then u else 1 - u)))

/-- The preserved P022-T14 statement over the shared SAP definitions. -/
def T14Statement : Prop :=
  ∀ (d : Design) (hn : d.m + d.k = d.N)
    (y1 y0 : Fin d.N → ℝ) (π : Assignment d),
neymanEstimate d y1 y0 .L π ≤ estimatedVariance d y1 y0 .L π ∧
    estimatedVariance d y1 y0 .L π ≤ estimatedVariance d y1 y0 .H π ∧
    estimatedVariance d y1 y0 .H π ≤ neymanEstimate d y1 y0 .H π ∧
    neymanEstimate d y1 y0 .H π ≤ conventionalEstimate d y1 y0 π

/-- The preserved P022-T15 statement over the shared SAP definitions. -/
def T15Statement : Prop :=
  ∀ (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S),
(∀ h ∈ compatibleLaws H, ∀ t : Bool, ∀ j : ℕ, j ≤ 2 →
      Integrable (fun p : ℝ × ℝ => (if t then p.1 else p.2) ^ j)
        (h : Measure (ℝ × ℝ))) ∧
    (∀ h ∈ compatibleLaws H, Integrable (fun p : ℝ × ℝ => p.1 * p.2)
      (h : Measure (ℝ × ℝ))) ∧
    (∀ B, Tendsto (fun q => ((S.design q).N : ℝ) * populationBound (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q) B) atTop (𝓝 (limitingBound H θ ρ B))) ∧
    boundConsistency S

/-- The preserved P022-T16 statement over the shared SAP definitions. -/
def T16Statement : Prop :=
  ∀ (H : JointLaw) (θ ρ C : ℝ) (hC : 0 ≤ C),
∃ κ1 κ2 κ3 : ℝ → ℝ, (∀ ε, 0 < ε → 0 ≤ κ1 ε ∧ 0 ≤ κ2 ε ∧ 0 ≤ κ3 ε) ∧
    ∀ S : ExperimentSequence, Conditions123 S H θ ρ →
    (∀ i, |S.y1 i| ≤ C ∧ |S.y0 i| ≤ C) →
    ∀ ε ε1 ε2 ε3, 0 < ε1 → 0 < ε2 → 0 < ε3 → ε1 + ε2 + ε3 = ε →
    scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
      |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H π -
        populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .H|) ≤
      ENNReal.ofReal (C ^ 4 * κ1 ε1) ∧
    scaledProbabilityLimsup S (fun q π => ε ≤ ((S.design q).N : ℝ) *
      |estimatedVariance (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .L π -
        populationBound (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) .L|) ≤
      ENNReal.ofReal (C ^ 4 * (1 / ε1 ^ 2 + κ2 ε2 + κ3 ε3))

/-- The preserved P022-T17 statement over the shared SAP definitions. -/
def T17Statement : Prop :=
  ∀ (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (h3 : BoundedThirdMoments S)
    (hns : NonsingularLaw H)
    (hDefined : LawFunctionalsDefined H)
    (hLimit : 0 < limitingBound H θ ρ .H)
    (hEstimates : ∀ q π, 0 < estimatedVariance (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q) .H π),
0 < gamma H θ ρ ∧ gamma H θ ρ ≤ 1 ∧
    Tendsto (fun q => ((S.design q).N : ℝ) * trueVariance (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q)) atTop (𝓝 (limitingTrueVariance H θ ρ)) ∧
    weakStandardNormal S (fun q π =>
      (estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π -
        averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)) /
          Real.sqrt (gamma H θ ρ * estimatedVariance (S.design q)
            (rowOutcomes S true q) (rowOutcomes S false q) .H π)) ∧
    (∀ α, 0 < α → α < 1 → NormalCriticalDefined α →
      Tendsto (fun q => designProbability (S.design q) (fun π =>
        |estimatedEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q) π -
          averageEffect (S.design q) (rowOutcomes S true q) (rowOutcomes S false q)| ≤
            normalCritical α * Real.sqrt (estimatedVariance (S.design q)
              (rowOutcomes S true q) (rowOutcomes S false q) .H π))) atTop
        (𝓝 (2 * normalCDF (normalCritical α / Real.sqrt (gamma H θ ρ)) - 1)) ∧
      1 - α ≤ 2 * normalCDF (normalCritical α / Real.sqrt (gamma H θ ρ)) - 1)

/-- P022-T18: a sequence-specific counterexample to printed Lemma 2. -/
def T18Statement : Prop :=
  ∃ (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ),
    Conditions123 S H θ ρ ∧ ¬ Lemma2Conclusions S H θ ρ

end
end SAP.P022
