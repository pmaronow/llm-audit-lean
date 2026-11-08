import SAP.P009a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P009a

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

/-- Mathematical content retained for target P009-T1. -/
def T1Statement : Prop :=
  (SequenceRegularity sparseSequence 2 4 1 ∧
    (∀ t, ProductDesign (sparseSequence.experiment t) ∧
      NoSpillovers (sparseSequence.experiment t) ∧
      averageDependence (sparseSequence.experiment t) = 1 ∧ maximumDependence (sparseSequence.experiment t) = 1 ∧
      rmsDependence (sparseSequence.experiment t) = 1 ∧ spectralRadius (sparseSequence.experiment t) = 1) ∧
    SparseDependence sparseSequence ∧
    (∀ t, let E := sparseSequence.experiment t
      expectedATE E = 1 / sampleSize sparseSequence t ∧ distributionalEffect E = 1 / sampleSize sparseSequence t ∧
      meanSquaredEffect E = 1 / sampleSize sparseSequence t ∧
      variance E.design (htEstimate E) = 1 / sampleSize sparseSequence t ^ 2 ∧
      expectation E.design (bernoulliVarianceEstimate E) = 2 / sampleSize sparseSequence t ^ 2 ∧
      variance E.design (htEstimate E) < expectation E.design (bernoulliVarianceEstimate E) ∧
      (∀ z, htEstimate E z = 2 * treatmentValue (z ⟨0, by simp [sparseSequence]⟩) / sampleSize sparseSequence t ∧
        bernoulliVarianceEstimate E z = 4 * treatmentValue (z ⟨0, by simp [sparseSequence]⟩) / sampleSize sparseSequence t ^ 2 ∧
        averageVarianceEstimate E z = bernoulliVarianceEstimate E z ∧ maximumVarianceEstimate E z = bernoulliVarianceEstimate E z ∧ spectralVarianceEstimate E z = bernoulliVarianceEstimate E z) ∧
      dispersionOfVariances E ^ 2 = (sampleSize sparseSequence t - 1) / sampleSize sparseSequence t ^ 2) ∧
    VarianceConservative sparseSequence (fun t => bernoulliVarianceEstimate (sparseSequence.experiment t)) ∧
    VarianceConservative sparseSequence (fun t => averageVarianceEstimate (sparseSequence.experiment t)) ∧
    VarianceConservative sparseSequence (fun t => maximumVarianceEstimate (sparseSequence.experiment t)) ∧
    VarianceConservative sparseSequence (fun t => spectralVarianceEstimate (sparseSequence.experiment t)) ∧
    ConvergesInProbability sparseSequence (fun t z => let E := sparseSequence.experiment t
      sampleSize sparseSequence t * (bernoulliVarianceEstimate E z - variance E.design (htEstimate E)) - meanSquaredEffect E) ∧
    (∀ t, probability (sparseSequence.experiment t).design (fun z =>
      IntervalCovers (htEstimate (sparseSequence.experiment t) z) (expectedATE (sparseSequence.experiment t))
        (bernoulliVarianceEstimate (sparseSequence.experiment t) z) (1/20)) = 1/2) ∧
    (1/2 : ℝ) < 1 - 1/20) ∧
  (∀ t, expectation (sparseSequence.experiment t).design
    (htEstimate (sparseSequence.experiment t)) = 1 / sampleSize sparseSequence t)

/-- Mathematical content retained for target P009-T2. -/
def T2Statement : Prop :=
  (∀ (Ω : ℕ → Type) [∀ t, MeasurableSpace (Ω t)]
    (P : (t : ℕ) → MeasureTheory.Measure (Ω t))
    [∀ t, MeasureTheory.IsProbabilityMeasure (P t)]
    (T Vhat : (t : ℕ) → Ω t → ℝ) (θ V δ : ℕ → ℝ)
    (hT : ∀ t, MeasureTheory.Integrable (T t) (P t))
    (hT2 : ∀ t, MeasureTheory.Integrable (fun ω => T t ω ^ 2) (P t))
    (hMeas : ∀ t, Measurable (T t) ∧ Measurable (Vhat t))
    (hMean : ∀ t, (∫ ω, T t ω ∂P t) = θ t)
    (hVar : ∀ t, V t = ∫ ω, (T t ω - θ t) ^ 2 ∂P t)
    (hV : ∀ t, 0 < V t) (hVhat : ∀ t ω, 0 ≤ Vhat t ω)
    (hδ : ∀ t, 0 < δ t) (α : ℝ) (hα : 0 < α ∧ α < 1),
    (∀ t η, 0 < η → η < 1 →
      ((P t) {ω | ¬ IntervalCovers (T t ω) (θ t) (Vhat t ω) α}).toReal ≤
      ((P t) {ω | Vhat t ω < (1-η) * V t}).toReal + α/(1-η)) ∧
    ((∀ η, 0 < η → η < 1 → Tendsto
      (fun t => ((P t) {ω | Vhat t ω < (1-η) * V t}).toReal) atTop (nhds 0)) →
      1-α ≤ Filter.liminf (fun t =>
        ((P t) {ω | IntervalCovers (T t ω) (θ t) (Vhat t ω) α}).toReal) atTop) ∧
    ((∀ ε > 0, Tendsto (fun t => ((P t) {ω |
      ((t+1 : ℕ) : ℝ) / δ t * (Vhat t ω - V t) ≤ -ε}).toReal) atTop (nhds 0)) →
      EventuallyPositiveLowerBound (fun t => ((t+1 : ℕ) : ℝ) / δ t * V t) →
      ∀ η, 0 < η → η < 1 → Tendsto
        (fun t => ((P t) {ω | Vhat t ω < (1-η) * V t}).toReal) atTop (nhds 0))) ∧
  (∀ (a V Vhat η c : ℝ)
    (ha : 0 < a) (hη : 0 < η) (hc : c ≤ a * V)
    (hunder : Vhat < (1-η) * V),
    a * (Vhat - V) ≤ -η*c) ∧
  (∀ (S : ExperimentSequence) (k q s α : ℝ)
    (hReg : SequenceRegularity S k q s) (hBER : ∀ t, ProductDesign (S.experiment t))
    (Vhat : (t : ℕ) → TreatmentVector (S.N t) → ℝ)
    (hVhat : ∀ t z, 0 ≤ Vhat t z) (hα : 0 < α ∧ α < 1)
    (hCons : VarianceConservative S Vhat)
    (hScale : EventuallyPositiveLowerBound (fun t => sampleSize S t/averageDependence (S.experiment t)*
      variance (S.experiment t).design (htEstimate (S.experiment t)))),
    (∀ η, 0 < η → η < 1 → Tendsto (fun t => probability (S.experiment t).design
      (fun z => Vhat t z < (1-η)*variance (S.experiment t).design (htEstimate (S.experiment t))))
      atTop (nhds 0)) ∧
    1-α ≤ Filter.liminf (fun t => probability (S.experiment t).design
      (fun z => IntervalCovers (htEstimate (S.experiment t) z) (expectedATE (S.experiment t)) (Vhat t z) α)) atTop) ∧
  (∀ {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) (k q s : ℝ),
    Regularity E k q s → ProductDesign E → expectation E.design (htEstimate E) = expectedATE E)

/-- Mathematical content retained for target P009-T3. -/
def T3Statement : Prop :=
  ∃ E F G : FiniteExperiment 2,
    (∀ z, E.design.mass z =
      (if z 0 then 1/4 else 3/4) * (if z 1 then 3/4 else 1/4)) ∧
    (∀ i z, E.outcome i z = if i = 0 then treatmentValue (z 1) else -treatmentValue (z 0)) ∧
    (∀ z, F.design.mass z =
      if z 0 ∧ ¬ z 1 then 1/4 else if ¬ z 0 ∧ z 1 then 3/4 else 0) ∧
    (∀ i z, F.outcome i z = 1) ∧
    (∀ z, G.design.mass z =
      (if z 0 then 1/4 else 3/4) * (if z 1 then 3/4 else 1/4)) ∧
    (∀ i z, G.outcome i z = if i = 0 then 1 else 1-treatmentValue (z 0)) ∧
    Regularity E 4 4 1 ∧ ProductDesign E ∧ Regularity F 4 4 1 ∧
    Regularity G 4 4 1 ∧ ProductDesign G ∧
    variance E.design (estimatedArmMean E true) = 13/48 ∧
    (∑ i, ∑ j, covariance E.design (armResponse E true 1 i) (armResponse E true 1 j)) = 0 ∧
    variance F.design (fun z => estimatedArmSize F true z / 2) = 1/3 ∧
    (∑ i, ∑ j, covariance F.design
      (fun z => treatmentValue (z i)) (fun z => treatmentValue (z j))) = 0 ∧
    variance G.design (fun z => ∑ i,
      armResponse G true 2 i z / armProbability G i true ^ 2) = 367/9 ∧
    (4:ℝ)^4 * (∑ i, ∑ j, covariance G.design
      (armResponse G true 2 i) (armResponse G true 2 j)) = 39 ∧
    (0:ℝ) < 13/48 ∧ (0:ℝ) < 1/3 ∧ (39:ℝ) < 367/9

/-- Mathematical content retained for target P009-T4. -/
def T4Statement : Prop :=
  (∀ {Ω U : Type*} [Fintype Ω] [Fintype U]
    (P : FiniteDistribution Ω) (X : U → Ω → ℝ) (w : U → ℝ) (K : ℝ)
    (hw : ∀ i, 0 < w i ∧ w i ≤ K),
    variance P (fun ω => ∑ i, w i * X i ω) =
      ∑ i, ∑ j, w i * w j * covariance P (X i) (X j) ∧
    variance P (fun ω => ∑ i, w i * X i ω) ≤
      K^2 * (∑ i, ∑ j, |covariance P (X i) (X j)|)) ∧
  (∀ {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n)
    (k q s : ℝ) (hReg : Regularity E k q s),
    (∀ b, variance E.design (estimatedArmMean E b) ≤ k^2/(n:ℝ)^2 *
      (∑ i, ∑ j, |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)|)) ∧
    (ProductDesign E → ∀ b,
      (∑ i, ∑ j, |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)|) =
        ∑ i, ∑ j, dependenceIndicator E i j * |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)| ∧
      variance E.design (estimatedArmMean E b) ≤ k^4/(n:ℝ) * averageDependence E) ∧
    (∀ b, variance E.design (estimatedArmMean E b) ≤ k^4/(n:ℝ)*averageDependence E +
      10*k^4/(n:ℝ)*externalMixing E ((q-2)/q)) ∧
    (∀ b, variance E.design (fun z => estimatedArmSize E b z / n) ≤ k^2/(n:ℝ)^2 *
      (∑ i, ∑ j, |covariance E.design
        (fun z => if z i = b then 1 else 0) (fun z => if z j = b then 1 else 0)|) ∧
      variance E.design (fun z => estimatedArmSize E b z / n) ≤
        k^2/(n:ℝ)*averageDependence E + k^2/(n:ℝ)*externalMixing E ((q-2)/q)) ∧
    (4 ≤ q → ProductDesign E →
      (∀ b, variance E.design (fun z => ∑ i, armResponse E b 2 i z / armProbability E i b ^ 2) ≤
        k^4 * (∑ i, ∑ j, |covariance E.design (armResponse E b 2 i) (armResponse E b 2 j)|) ∧
        (∑ i, ∑ j, |covariance E.design (armResponse E b 2 i) (armResponse E b 2 j)|) =
          ∑ i, ∑ j, dependenceIndicator E i j * |covariance E.design (armResponse E b 2 i) (armResponse E b 2 j)| ∧
        variance E.design (fun z => ∑ i, armResponse E b 2 i z / armProbability E i b ^ 2) ≤
          k^8*(n:ℝ)*averageDependence E) ∧
      variance E.design (fun z => (n:ℝ)*bernoulliVarianceEstimate E z) ≤ 4*k^8*averageDependence E/(n:ℝ))) ∧
  (∀ {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) (k q s : ℝ)
    (hReg : Regularity E k q s) (a : ℕ) (ha : a = 1 ∨ a = 2) (hqa : 2*a ≤ q)
    (i j : Fin n) (b : Bool),
    |covariance E.design (armResponse E b a i) (armResponse E b a j)| ≤ k^(2*a))

/-- Mathematical content retained for target P009-T5. -/
def T5Statement : Prop :=
  (SequenceRegularity clusterSequence 3 2 1 ∧
    (∀ t, ProductDesign (clusterSequence.experiment t) ∧
      averageDependence (clusterSequence.experiment t)/sampleSize clusterSequence t = clusterDensity (t+1)) ∧
    Tendsto (fun t => averageDependence (clusterSequence.experiment t)/sampleSize clusterSequence t)
      atTop (nhds (1/4)) ∧
    (∀ t, 1/4 ≤ averageDependence (clusterSequence.experiment t)/sampleSize clusterSequence t ↔ t+1 ≤ 4)) ∧
  (Tendsto (fun t => clusterDensity (t+1)) atTop (nhds (1/4)) ∧
    (∀ n, 0 < n → (1/4 ≤ clusterDensity n ↔ n ≤ 4)) ∧
    (∀ m, 3 ≤ m → 1/4-clusterDensity (2*m) = ((m:ℝ)-2)/(4*(m:ℝ)^2)) ∧
    (∀ m, 2 ≤ m → 1/4-clusterDensity (2*m+1) =
      (8*(m:ℝ)-11)/(4*(2*(m:ℝ)+1)^2)))

/-- Mathematical content retained for target P009-T6. -/
def T6Statement : Prop :=
  (∀ (a : ℕ → ℝ) (L c : ℝ)
    (hL : FiniteLimsup a L) (hc : 0 < c) (hcL : c < L),
    Set.Infinite {t | c ≤ a t}) ∧
  (∀ {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) (k q s L : ℝ),
    Regularity E k q s → 0 < L ∧ L ≤ 1 →
    let M := ⌈Real.sqrt L*(n:ℝ)⌉₊
    let F : FiniteExperiment n := {E with outcome := subsequenceResponse hn E M}
    averageDependence F = (M:ℝ)^2/(n:ℝ)+((n:ℝ)-M)/(n:ℝ) ∧
    L*(n:ℝ) ≤ averageDependence F ∧
    (∀ i z, |F.outcome i z| ≤ 1/Real.sqrt L) ∧
    expectedATE F = armProbability E ⟨0,hn⟩ true ∧
    (∀ z, htEstimate F z = treatmentValue (z ⟨0,hn⟩) ∧
      k⁻¹ ≤ |htEstimate F z-expectedATE F|))

/-- Mathematical content retained for target P009-T7. -/
def T7Statement : Prop :=
  SequenceRegularity sparseSequence 2 4 1 ∧
    SparseDependence sparseSequence ∧
    (∀ t, ProductDesign (sparseSequence.experiment t) ∧
      NoSpillovers (sparseSequence.experiment t) ∧ averageDependence (sparseSequence.experiment t) = 1 ∧
      maximumDependence (sparseSequence.experiment t) = 1 ∧
      variance (sparseSequence.experiment t).design (htEstimate (sparseSequence.experiment t)) > 0) ∧
    Tendsto (fun t => sampleSize sparseSequence t *
      variance (sparseSequence.experiment t).design (htEstimate (sparseSequence.experiment t))) atTop (nhds 0) ∧
    (∀ t b, probability (sparseSequence.experiment t).design (fun z =>
      (htEstimate (sparseSequence.experiment t) z - expectedATE (sparseSequence.experiment t)) /
        Real.sqrt (variance (sparseSequence.experiment t).design (htEstimate (sparseSequence.experiment t))) =
        (if b then 1 else -1)) = 1/2) ∧
    ¬ ConvergesInLaw sparseSequence (fun t z =>
      (htEstimate (sparseSequence.experiment t) z - expectedATE (sparseSequence.experiment t)) /
        Real.sqrt (variance (sparseSequence.experiment t).design (htEstimate (sparseSequence.experiment t)))) standardNormalCDF

/-- Mathematical content retained for target P009-T8. -/
def T8Statement : Prop :=
  ∀ (S : ExperimentSequence) (k q s : ℝ)
    (hReg : SequenceRegularity S k q s) (hBER : ∀ t, ProductDesign (S.experiment t))
    (hDegree : ∃ D, ∀ t, maximumDependence (S.experiment t) ≤ D)
    (hPositive : ∀ t, 0 < variance (S.experiment t).design (htEstimate (S.experiment t)))
    (hVariance : EventuallyPositiveLowerBound (fun t => sampleSize S t *
      variance (S.experiment t).design (htEstimate (S.experiment t)))),
    ConvergesInLaw S (fun t z => (htEstimate (S.experiment t) z - expectedATE (S.experiment t)) /
      Real.sqrt (variance (S.experiment t).design (htEstimate (S.experiment t)))) standardNormalCDF

/-- Mathematical content retained for target P009-T9. -/
def T9Statement : Prop :=
  ∀ (r : ℕ) (hr : 1 ≤ r),
    ∃ E : FiniteExperiment (4*r+2), FixedSizeDesign E (2*r+1) ∧ E.outcome = halfPopulationResponse r ∧
      Regularity E 2 4 1 ∧ dependenceIndicator E 0 1 = 0 ∧
      averageDependence E = 3 - 4/(4*r+2:ℕ) ∧ averageDependence E < 3 ∧
      averageOutgoing E = 2 - 2/(4*r+2:ℕ) ∧ maximumOutgoing E = 2 ∧
      mixingCoefficient E.design (relevantTreatments E 0) (relevantTreatments E 1) = 1/4

/-- Mathematical content retained for target P009-T10. -/
def T10Statement : Prop :=
  ∀ (S : ExperimentSequence)
    (hCR : ∀ t, ∃ m, FixedSizeDesign (S.experiment t) m)
    (hBound : ∃ D, ∀ᶠ t in atTop, averageDependence (S.experiment t) ≤ D)
    (hPairs : ∀ t, 0 < (Finset.univ.filter
      (fun ij : Fin (S.N t) × Fin (S.N t) =>
        dependenceIndicator (S.experiment t) ij.1 ij.2 = 0)).card),
    ∃ exceptions : (t : ℕ) → Finset (Fin (S.N t) × Fin (S.N t)),
      (∀ t, ∀ ij ∈ exceptions t, dependenceIndicator (S.experiment t) ij.1 ij.2 = 0) ∧
      Tendsto (fun t => (exceptions t).card / ((Finset.univ.filter
        (fun ij : Fin (S.N t) × Fin (S.N t) => dependenceIndicator (S.experiment t) ij.1 ij.2 = 0)).card : ℝ))
        atTop (nhds 0) ∧
      (∀ ε > 0, ∀ᶠ t in atTop, ∀ i j, dependenceIndicator (S.experiment t) i j = 0 →
        (i,j) ∉ exceptions t →
        mixingCoefficient (S.experiment t).design (relevantTreatments (S.experiment t) i) (relevantTreatments (S.experiment t) j) < ε)

/-- Mathematical content retained for target P009-T11. -/
def T11Statement : Prop :=
  (∀ m (hm : 2 ≤ m), let E := fairPopulation (m*m) (starPopulationResponse m hm)
      ProductDesign E ∧ Regularity E 2 4 1 ∧ averageOutgoing E = 2 ∧ averageDependence E = m ∧
      meanSquaredEffect E = 1 ∧ directBias E = 2/(m:ℝ)^2 ∧ indirectBias E = 0 ∧
      0 < directBias E ∧ directBias E ≤ meanSquaredEffect E / averageDependence E) ∧
    Tendsto (fun t =>
      let E := fairPopulation ((t+2)*(t+2)) (starPopulationResponse (t+2) (by omega))
      averageDependence E / averageOutgoing E) atTop atTop

/-- Mathematical content retained for target P009-T12. -/
def T12Statement : Prop :=
  (∀ {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n)
    (k q s : ℝ) (hReg : Regularity E k q s) (hQ : 4 ≤ q) (hBER : ProductDesign E),
    |directBias E| ≤ 12*k^4*(averageOutgoing E-1)/averageDependence E ∧
    |indirectBias E| ≤ 4*k^4*(averageDependence E-1)/averageDependence E ∧ |indirectBias E| ≤ 4*k^4 ∧
    0 ≤ meanSquaredEffect E ∧ meanSquaredEffect E ≤ 4*k^4) ∧
  (∀ (S : ExperimentSequence) (k q s : ℝ)
    (hReg : SequenceRegularity S k q s) (hQ : 4 ≤ q)
    (hBER : ∀ t, ProductDesign (S.experiment t))
    (hRatio : Tendsto (fun t => averageDependence (S.experiment t)/averageOutgoing (S.experiment t)) atTop atTop),
    Tendsto (fun t => meanSquaredEffect (S.experiment t)/averageDependence (S.experiment t)) atTop (nhds 0) ∧
    Tendsto (fun t => directBias (S.experiment t)) atTop (nhds 0) ∧
    boundedRelativeTo (fun t => indirectBias (S.experiment t)) (fun _ => 1) ∧
    (Tendsto (fun t => averageOutgoing (S.experiment t)/
      (averageDependence (S.experiment t)*|indirectBias (S.experiment t)|)) atTop (nhds 0) →
      (∀ᶠ t in atTop, indirectBias (S.experiment t) ≠ 0) →
      vanishingRelativeTo (fun t => meanSquaredEffect (S.experiment t)/averageDependence (S.experiment t))
        (fun t => |indirectBias (S.experiment t)|) ∧
      vanishingRelativeTo (fun t => directBias (S.experiment t)) (fun t => |indirectBias (S.experiment t)|)))

end
end SAP.P009a
