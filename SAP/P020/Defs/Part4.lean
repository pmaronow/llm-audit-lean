import SAP.P020.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020
open scoped BigOperators
open Filter
noncomputable section

/-- Mathematical content retained for P020-T9; see the Challenge docstring. -/
def T9Statement : Prop :=
  (({0} : Finset (Fin 2)) ∈ assignments subscriptPopulation ∧
    desRaj (affinePopulation subscriptPopulation 0 1) 0 {0} = (2 : ℝ) / 3 ∧
    (subscriptPopulation.M : ℝ) / populationSize subscriptPopulation *
      (armSum subscriptPopulation true (rajPotential subscriptPopulation true 0) {0} /
          subscriptPopulation.mt -
       armSum subscriptPopulation false (rajPotential subscriptPopulation true 0) {0} /
          controlCount subscriptPopulation) = -(2 : ℝ) / 3 ∧
    desRaj (affinePopulation subscriptPopulation 0 1) 0 {0} ≠
      (subscriptPopulation.M : ℝ) / populationSize subscriptPopulation *
        (armSum subscriptPopulation true (rajPotential subscriptPopulation true 0) {0} /
          subscriptPopulation.mt -
         armSum subscriptPopulation false (rajPotential subscriptPopulation true 0) {0} /
          controlCount subscriptPopulation)) ∧
  (({0} : Finset (Fin 2)) ∈ assignments bracketPopulation ∧
    clusterCovariance bracketPopulation.y0 bracketPopulation.y1 = 1 ∧
    clusterMean bracketPopulation.y0 * bracketPopulation.y1 0 -
      clusterMean bracketPopulation.y0 * clusterMean bracketPopulation.y1 = -1 ∧
    clusterCovariance bracketPopulation.y0 bracketPopulation.y1 ≠
      clusterMean bracketPopulation.y0 * bracketPopulation.y1 0 -
        clusterMean bracketPopulation.y0 * clusterMean bracketPopulation.y1) ∧
  (clusterCovariance (![0, 2] : Fin 2 → ℝ) ![0, 2] = 1 ∧
    clusterMean (![0, 2] : Fin 2 → ℝ) * (![0, 2] : Fin 2 → ℝ) 0 -
      clusterMean (![0, 2] : Fin 2 → ℝ) * clusterMean (![0, 2] : Fin 2 → ℝ) = -1 ∧
    clusterMean (![0, 2] : Fin 2 → ℝ) * (![0, 2] : Fin 2 → ℝ) 1 -
      clusterMean (![0, 2] : Fin 2 → ℝ) * clusterMean (![0, 2] : Fin 2 → ℝ) = 1 ∧
    clusterCovariance (![0, 2] : Fin 2 → ℝ) ![0, 2] ≠
      clusterMean (![0, 2] : Fin 2 → ℝ) * (![0, 2] : Fin 2 → ℝ) 0 -
        clusterMean (![0, 2] : Fin 2 → ℝ) * clusterMean (![0, 2] : Fin 2 → ℝ)) ∧
  (desRaj subscriptPopulation 0 {0} = (2 : ℝ) / 3)

/-- Mathematical content retained for P020-T10; see the Challenge docstring. -/
def T10Statement : Prop :=
  (∀ (P : ClusterPopulation)
    (I : IndividualPotentialOutcomes P) (hnull : IndividualSharpNull I)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P),
  (∀ j i, I.Y0 j i = observedIndividual I s j i ∧
      I.Y1 j i = observedIndividual I s j i) ∧ (∀ j, P.y0 j = P.y1 j)) ∧
  (∀ (P : ClusterPopulation)
    (I : IndividualPotentialOutcomes P) (hnull : IndividualSharpNull I)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P),
  (∀ j, P.y0 j = observedTotal P s j ∧ P.y1 j = observedTotal P s j) ∧
    clusterVariance P.y0 = clusterVariance P.y1 ∧
    clusterVariance P.y1 = clusterVariance (observedTotal P s) ∧
    clusterCovariance P.y0 P.y1 = clusterVariance (observedTotal P s) ∧
    designVariance (clusterLaw P) (horvitzThompson P) = htVarianceFormula P ∧
    htVarianceFormula P = sharpNullVarianceEstimator P s)

/-- Mathematical content retained for P020-T11; see the Challenge docstring. -/
def T11Statement : Prop :=
  (∀ {Ω : Type*} (L : FiniteLaw Ω) (u v : Ω → ℝ)
    (hv : ∀ ω ∈ L.support, 0 < v ω),
  expectation L (fun ω => u ω / v ω) =
      (expectation L u - designCovariance L (fun ω => u ω / v ω) v) /
        expectation L v) ∧
  (∀ (P : ClusterPopulation),
  expectation (clusterLaw P) (differenceInMeans P) = averageTreatmentEffect P -
      (P.M : ℝ) / populationSize P *
        (designCovariance (clusterLaw P)
          (fun s => armSum P true P.y1 s / armSize P true s) (armSize P true) / P.mt -
         designCovariance (clusterLaw P)
          (fun s => armSum P false P.y0 s / armSize P false s) (armSize P false) / controlCount P) ∧
    designBias (clusterLaw P) (differenceInMeans P) (averageTreatmentEffect P) =
      -((P.M : ℝ) / populationSize P) *
        (designCovariance (clusterLaw P)
          (fun s => armSum P true P.y1 s / armSize P true s) (armSize P true) / P.mt -
         designCovariance (clusterLaw P)
          (fun s => armSum P false P.y0 s / armSize P false s) (armSize P false) / controlCount P))

/-- Mathematical content retained for P020-T12; see the Challenge docstring. -/
def T12Statement : Prop :=
  (∀ (n : ℕ) (Y : Fin n → ℝ) (b0 b1 : ℝ),
  clusterTotal (fun i => b0 + b1 * Y i) = (n : ℝ) * b0 + b1 * clusterTotal Y) ∧
  (∀ (P : ClusterPopulation),
  expectation (clusterLaw P) (htTotal P false) = ∑ j, P.y0 j ∧
    expectation (clusterLaw P) (htTotal P true) = ∑ j, P.y1 j ∧
    expectation (clusterLaw P) (horvitzThompson P) = averageTreatmentEffect P) ∧
  (∀ (P : ClusterPopulation) (b0 b1 : ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P),
  horvitzThompson (affinePopulation P b0 b1) s =
      b0 * (P.M : ℝ) / populationSize P *
        (armMeanSize P true s - armMeanSize P false s) + b1 * horvitzThompson P s) ∧
  (∀ (P : ClusterPopulation) (b0 b1 : ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) (hb0 : b0 ≠ 0)
    (hsizes : armMeanSize P true s ≠ armMeanSize P false s),
  horvitzThompson (affinePopulation P b0 b1) s ≠ b1 * horvitzThompson P s) ∧
  (∃ (P : ClusterPopulation) (b0 b1 : ℝ) (s : Finset (Fin P.M)),
    s ∈ assignments P ∧ horvitzThompson (affinePopulation P b0 b1) s ≠ b1 * horvitzThompson P s)

/-- Mathematical content retained for P020-T13; see the Challenge docstring. -/
def T13Statement : Prop :=
  (∀ (P : ClusterPopulation) (k : ℝ),
  expectation (clusterLaw P) (rajTotal P false k) = ∑ j, P.y0 j ∧
    expectation (clusterLaw P) (rajTotal P true k) = ∑ j, P.y1 j ∧
    expectation (clusterLaw P) (desRaj P k) = averageTreatmentEffect P) ∧
  (∀ (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ),
  expectation (clusterLaw P) (rajCovariateTotal P X ks ka false) = ∑ j, P.y0 j ∧
    expectation (clusterLaw P) (rajCovariateTotal P X ks ka true) = ∑ j, P.y1 j ∧
    expectation (clusterLaw P) (desRajCovariates P X ks ka) = averageTreatmentEffect P)

/-- Mathematical content retained for P020-T14; see the Challenge docstring. -/
def T14Statement : Prop :=
  (∀ (P : ClusterPopulation) (a : Bool)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) (k : ℝ),
  clusterVariance (rajPotential P a k) =
      clusterVariance (rajPotential P a (armOptimalCoefficient P a)) +
        clusterVariance (fun j => (P.n j : ℝ)) * (k - armOptimalCoefficient P a)^2) ∧
  (∀ (P : ClusterPopulation)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) (a : Bool) (k : ℝ),
  clusterVariance (rajPotential P a (armOptimalCoefficient P a)) ≤
      clusterVariance (rajPotential P a k) ∧
    (clusterVariance (rajPotential P a (armOptimalCoefficient P a)) =
      clusterVariance (rajPotential P a k) ↔ k = armOptimalCoefficient P a)) ∧
  (∀ (P : ClusterPopulation) (k : ℝ),
  designVariance (clusterLaw P) (desRaj P k) =
      (P.M : ℝ)^2 / ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1)) *
        rajMomentObjective P k) ∧
  (∀ (P : ClusterPopulation) (k : ℝ)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))),
  designVariance (clusterLaw P) (desRaj P k) =
      designVariance (clusterLaw P) (desRaj P (optimalCoefficient P)) +
        rajVarianceCurvature P * (k - optimalCoefficient P)^2) ∧
  (∀ (P : ClusterPopulation) (k : ℝ)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))),
  designVariance (clusterLaw P) (desRaj P k) -
      designVariance (clusterLaw P) (horvitzThompson P) =
      rajVarianceCurvature P * k * (k - 2 * optimalCoefficient P)) ∧
  (∀ (P : ClusterPopulation)
    (hsize : 0 < clusterVariance (fun j => (P.n j : ℝ))) (k : ℝ),
  designVariance (clusterLaw P) (desRaj P (optimalCoefficient P)) ≤
      designVariance (clusterLaw P) (desRaj P k) ∧
    (designVariance (clusterLaw P) (desRaj P (optimalCoefficient P)) =
      designVariance (clusterLaw P) (desRaj P k) ↔ k = optimalCoefficient P) ∧
    (designVariance (clusterLaw P) (desRaj P k) <
      designVariance (clusterLaw P) (horvitzThompson P) ↔ k^2 < 2 * k * optimalCoefficient P) ∧
    (designVariance (clusterLaw P) (desRaj P k) =
      designVariance (clusterLaw P) (horvitzThompson P) ↔ k = 0 ∨ k = 2 * optimalCoefficient P)) ∧
  (∀ (k star : ℝ),
  (k^2 < 2 * k * star ↔
      (0 < star ∧ 0 < k ∧ k < 2 * star) ∨ (star < 0 ∧ 2 * star < k ∧ k < 0)))

/-- Mathematical content retained for P020-T15; see the Challenge docstring. -/
def T15Statement : Prop :=
  (∀ (P : ClusterPopulation),
  designVariance (clusterLaw P) (horvitzThompson P) =
      (designVariance (clusterLaw P) (htTotal P false) +
       designVariance (clusterLaw P) (htTotal P true) -
       2 * designCovariance (clusterLaw P) (htTotal P false) (htTotal P true)) /
        (populationSize P : ℝ)^2 ∧
    designVariance (clusterLaw P) (htTotal P false) =
      (P.M : ℝ)^2 / controlCount P *
        (((P.M : ℝ) - controlCount P) / ((P.M : ℝ) - 1)) * clusterVariance P.y0 ∧
    designVariance (clusterLaw P) (htTotal P true) =
      (P.M : ℝ)^2 / P.mt *
        (((P.M : ℝ) - P.mt) / ((P.M : ℝ) - 1)) * clusterVariance P.y1 ∧
    designCovariance (clusterLaw P) (htTotal P false) (htTotal P true) =
      -((P.M : ℝ)^2 / ((P.M : ℝ) - 1)) * clusterCovariance P.y0 P.y1) ∧
  (∀ (P : ClusterPopulation),
  designVariance (clusterLaw P) (horvitzThompson P) = htVarianceFormula P ∧
    designVariance (clusterLaw P) (horvitzThompson P) ≤ approximateVariance P P.y0 P.y1) ∧
  (∀ (P : ClusterPopulation), 2 * clusterCovariance P.y0 P.y1 - clusterVariance P.y0 - clusterVariance P.y1 ≤ 0) ∧
  (∀ (P : ClusterPopulation)
    (ht : 2 ≤ P.mt) (hc : 2 ≤ controlCount P),
  expectation (clusterLaw P) (combinedVarianceEstimator P P.y0 P.y1) =
      approximateVariance P P.y0 P.y1 ∧
    designVariance (clusterLaw P) (horvitzThompson P) ≤
      expectation (clusterLaw P) (combinedVarianceEstimator P P.y0 P.y1)) ∧
  (∀ (P : ClusterPopulation) (k : ℝ)
    (ht : 2 ≤ P.mt) (hc : 2 ≤ controlCount P),
  expectation (clusterLaw P)
      (combinedVarianceEstimator P (rajPotential P false k) (rajPotential P true k)) =
      approximateVariance P (rajPotential P false k) (rajPotential P true k) ∧
    designVariance (clusterLaw P) (desRaj P k) ≤
      expectation (clusterLaw P)
        (combinedVarianceEstimator P (rajPotential P false k) (rajPotential P true k))) ∧
  (∀ {B : ℕ} (hB : 0 < B)
    (P : Fin B → ClusterPopulation),
  expectation (blockLaw P) (blockedHT P) = blockedATE P ∧
    designVariance (blockLaw P) (blockedHT P) =
      ∑ b, ((populationSize (P b) : ℝ) / blockedSize P)^2 *
        designVariance (clusterLaw (P b)) (horvitzThompson (P b))) ∧
  (∀ {B : ℕ} (hB : 0 < B)
    (P : Fin B → ClusterPopulation)
    (Vhat : (b : Fin B) → Finset (Fin (P b).M) → ℝ)
    (hVhat : ∀ b, designVariance (clusterLaw (P b)) (horvitzThompson (P b)) ≤
      expectation (clusterLaw (P b)) (Vhat b)),
  designVariance (blockLaw P) (blockedHT P) ≤
      expectation (blockLaw P) (fun s => ∑ b,
        ((populationSize (P b) : ℝ) / blockedSize P)^2 * Vhat b (s b).val))

/-- Mathematical content retained for P020-T16; see the Challenge docstring. -/
def T16Statement : Prop :=
  ∀ (P : ClusterPopulation)
    (hcondition : (∃ τ : ℝ, ∀ j, P.y1 j - P.y0 j = τ) ∨ controlCount P = P.mt),
  designVariance (clusterLaw P) (horvitzThompson P) ≤
      expectation (clusterLaw P) (sharpNullVarianceEstimator P)

/-- Mathematical content retained for P020-T17; see the Challenge docstring. -/
def T17Statement : Prop :=
  (∀ (P : ClusterPopulation),
  DesignConsistent (fun h => copyLaw P (h + 1)) (fun h => copyAverage P true P.y1 (h + 1))
      (fun _ => (P.mt : ℝ) / P.M * ∑ j, P.y1 j) ∧
    DesignConsistent (fun h => copyLaw P (h + 1)) (fun h => copyAverage P false P.y0 (h + 1))
      (fun _ => (controlCount P : ℝ) / P.M * ∑ j, P.y0 j) ∧
    DesignConsistent (fun h => copyLaw P (h + 1)) (fun h => copyAverage P true (fun j => (P.n j : ℝ)) (h + 1))
      (fun _ => (P.mt : ℝ) / P.M * populationSize P) ∧
    DesignConsistent (fun h => copyLaw P (h + 1)) (fun h => copyAverage P false (fun j => (P.n j : ℝ)) (h + 1))
      (fun _ => (controlCount P : ℝ) / P.M * populationSize P) ∧
    DesignConsistent (fun h => copyLaw P (h + 1)) (fun h => copiedDifferenceInMeans P (h + 1))
      (fun _ => averageTreatmentEffect P)) ∧
  (∀ (P : ClusterPopulation),
  ((∑ j, P.y1 j) * ((P.mt : ℝ) / P.M)) /
        ((populationSize P : ℝ) * ((P.mt : ℝ) / P.M)) -
    ((∑ j, P.y0 j) * ((controlCount P : ℝ) / P.M)) /
        ((populationSize P : ℝ) * ((controlCount P : ℝ) / P.M)) = averageTreatmentEffect P) ∧
  (∀ (P : ClusterPopulation) (h : ℕ) (hh : 0 < h),
  populationSize (replicateWithin P h hh) = h * populationSize P) ∧
  (∀ (P : ClusterPopulation) (h : ℕ) (hh : 0 < h)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P) (k : ℝ),
  averageTreatmentEffect (replicateWithin P h hh) = averageTreatmentEffect P ∧
    differenceInMeans (replicateWithin P h hh) s = differenceInMeans P s ∧
    horvitzThompson (replicateWithin P h hh) s = horvitzThompson P s ∧
    desRaj (replicateWithin P h hh) k s = desRaj P k s) ∧
  (∀ (P : ClusterPopulation)
    (hbias : designBias (clusterLaw P) (differenceInMeans P) (averageTreatmentEffect P) ≠ 0),
  (∀ h (hh : 0 < h),
      designBias (clusterLaw (replicateWithin P h hh))
        (differenceInMeans (replicateWithin P h hh))
        (averageTreatmentEffect (replicateWithin P h hh)) =
        designBias (clusterLaw P) (differenceInMeans P) (averageTreatmentEffect P)) ∧
    ¬ DesignConsistent (fun _ : ℕ => clusterLaw P)
        (fun _ : ℕ => differenceInMeans P) (fun _ : ℕ => averageTreatmentEffect P)) ∧
  (¬ DesignConsistent (fun _ : ℕ => clusterLaw efficiencyPopulation)
      (fun _ : ℕ => differenceInMeans efficiencyPopulation)
      (fun _ : ℕ => averageTreatmentEffect efficiencyPopulation)) ∧
  (Tendsto (fun h : ℕ => 7 * h) atTop atTop) ∧
  (∀ h (hh : 0 < h), clusterLaw (replicateWithin efficiencyPopulation h hh) = clusterLaw efficiencyPopulation) ∧
  (¬ WithinReplicationConsistent efficiencyPopulation) ∧
  (∀ h (hh : 0 < h), designBias (clusterLaw (replicateWithin efficiencyPopulation h hh)) (differenceInMeans (replicateWithin efficiencyPopulation h hh)) (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) = -(1 : ℝ) / 315)

end
end SAP.P020
