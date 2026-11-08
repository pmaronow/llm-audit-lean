import SAP.P020.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020
open scoped BigOperators
open Filter
noncomputable section

/-- Mathematical content retained for P020-T1; see the Challenge docstring. -/
def T1Statement : Prop :=
  (∀ (j : Fin 3),
  clusterTotal (fun i : Fin (efficiencyPopulation.n j) =>
      if j = 0 then (0 : ℝ) else if i.val = 0 then 1 else 0) = efficiencyPopulation.y0 j ∧
    clusterTotal (fun _ : Fin (efficiencyPopulation.n j) => (0 : ℝ)) = efficiencyPopulation.y1 j) ∧
  (populationSize efficiencyPopulation = 7 ∧
    averageTreatmentEffect efficiencyPopulation = -(2 : ℝ) / 7 ∧
    differenceInMeans efficiencyPopulation {0} = -(1 : ℝ) / 3 ∧
    differenceInMeans efficiencyPopulation {1} = -(1 : ℝ) / 5 ∧
    differenceInMeans efficiencyPopulation {2} = -(1 : ℝ) / 3 ∧
    horvitzThompson efficiencyPopulation {0} = -(3 : ℝ) / 7 ∧
    horvitzThompson efficiencyPopulation {1} = -(3 : ℝ) / 14 ∧
    horvitzThompson efficiencyPopulation {2} = -(3 : ℝ) / 14 ∧
    expectation (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation) = -(13 : ℝ) / 45 ∧
    designBias (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) = -(1 : ℝ) / 315 ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) = (131 : ℝ) / 33075 ∧
    expectation (clusterLaw efficiencyPopulation) (horvitzThompson efficiencyPopulation) =
      averageTreatmentEffect efficiencyPopulation ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (horvitzThompson efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) = (1 : ℝ) / 98) ∧
  (∀ k : ℝ,
  (desRaj efficiencyPopulation k {0} = -3 / 7 + 6 / 7 * k ∧
    desRaj efficiencyPopulation k {1} = -3 / 14 + 3 / 14 * k ∧
    desRaj efficiencyPopulation k {2} = -3 / 14 - 15 / 14 * k ∧
    expectation (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k) =
      averageTreatmentEffect efficiencyPopulation ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k)
      (averageTreatmentEffect efficiencyPopulation) = 1 / 98 - 6 / 49 * k + 9 / 14 * k^2 ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k)
      (averageTreatmentEffect efficiencyPopulation) = 3 / 686 + 9 / 14 * (k - 2 / 21)^2 ∧
    (meanSquaredError (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k)
      (averageTreatmentEffect efficiencyPopulation) = 3 / 686 ↔ k = 2 / 21)) ∧
  (3 / 686 ≤ meanSquaredError (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k) (averageTreatmentEffect efficiencyPopulation)) ∧
  ((131 : ℝ) / 33075 < 3 / 686 ∧ (3 : ℝ) / 686 < 1 / 98 ∧
    meanSquaredError (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) <
    meanSquaredError (clusterLaw efficiencyPopulation) (desRaj efficiencyPopulation k)
      (averageTreatmentEffect efficiencyPopulation))) ∧
  (clusterVariance (fun j => (efficiencyPopulation.n j : ℝ)) = 14 / 9 ∧
    clusterCovariance (fun j => (efficiencyPopulation.n j : ℝ)) efficiencyPopulation.y0 = 4 / 9 ∧
    clusterCovariance (fun j => (efficiencyPopulation.n j : ℝ)) efficiencyPopulation.y1 = 0 ∧
    optimalCoefficient efficiencyPopulation = 2 / 21) ∧
  (errorProbability (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation)
      (averageTreatmentEffect efficiencyPopulation) (1 / 25) = 1) ∧
  (∀ (h : ℕ) (hh : 0 < h) (k : ℝ),
  populationSize (replicateWithin efficiencyPopulation h hh) = 7 * h ∧
    averageTreatmentEffect (replicateWithin efficiencyPopulation h hh) = -(2 : ℝ) / 7 ∧
    (∀ s ∈ assignments efficiencyPopulation, differenceInMeans (replicateWithin efficiencyPopulation h hh) s =
      differenceInMeans efficiencyPopulation s ∧
      horvitzThompson (replicateWithin efficiencyPopulation h hh) s = horvitzThompson efficiencyPopulation s ∧
      desRaj (replicateWithin efficiencyPopulation h hh) k s = desRaj efficiencyPopulation k s) ∧
    designBias (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (differenceInMeans (replicateWithin efficiencyPopulation h hh))
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) = -(1 : ℝ) / 315 ∧
    errorProbability (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (differenceInMeans (replicateWithin efficiencyPopulation h hh))
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) (1 / 25) = 1 ∧
    meanSquaredError (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (differenceInMeans (replicateWithin efficiencyPopulation h hh))
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) <
    meanSquaredError (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (desRaj (replicateWithin efficiencyPopulation h hh) k)
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh))) ∧
  (Tendsto (fun h : ℕ => 7 * h) atTop atTop) ∧
  (¬ DesignConsistent (fun _ : ℕ => clusterLaw efficiencyPopulation)
      (fun _ : ℕ => differenceInMeans efficiencyPopulation)
      (fun _ : ℕ => averageTreatmentEffect efficiencyPopulation)) ∧
  (¬ WithinReplicationConsistent efficiencyPopulation) ∧
  (designBias (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation) (averageTreatmentEffect efficiencyPopulation) ≠ 0) ∧
  (meanSquaredError (clusterLaw efficiencyPopulation) (differenceInMeans efficiencyPopulation) (averageTreatmentEffect efficiencyPopulation) < meanSquaredError (clusterLaw efficiencyPopulation) (horvitzThompson efficiencyPopulation) (averageTreatmentEffect efficiencyPopulation))

/-- Mathematical content retained for P020-T2; see the Challenge docstring. -/
def T2Statement : Prop :=
  (∀ {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d : ℝ),
  (meanSquaredError L T d = designVariance L T + (designBias L T d)^2) ∧
  ((designBias L T d)^2 ≤ meanSquaredError L T d)) ∧
  (∀ {Ω : ℕ → Type*}
    (L : ∀ h, FiniteLaw (Ω h)) (T U : ∀ h, Ω h → ℝ) (d : ℕ → ℝ)
    (b : ℝ) (hb : b ≠ 0)
    (hBias : Tendsto (fun h => designBias (L h) (T h) (d h)) atTop (nhds b))
    (hMSE : Tendsto (fun h => meanSquaredError (L h) (U h) (d h)) atTop (nhds 0)),
  ∃ h₀ : ℕ, ∀ h ≥ h₀, meanSquaredError (L h) (U h) (d h) <
      meanSquaredError (L h) (T h) (d h)) ∧
  (∀ {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ)
    (d ε : ℝ) (hε : 0 < ε),
  errorProbability L T d ε ≤ meanSquaredError L T d / ε^2) ∧
  (∀ {Ω : ℕ → Type*}
    (L : ∀ h, FiniteLaw (Ω h)) (U : ∀ h, Ω h → ℝ) (d : ℕ → ℝ)
    (hMSE : Tendsto (fun h => meanSquaredError (L h) (U h) (d h)) atTop (nhds 0)),
  DesignConsistent L U d) ∧
  (∀ h (hh : 0 < h),
    designBias (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (differenceInMeans (replicateWithin efficiencyPopulation h hh))
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) = -(1 : ℝ) / 315 ∧
    meanSquaredError (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (differenceInMeans (replicateWithin efficiencyPopulation h hh))
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) <
    meanSquaredError (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (desRaj (replicateWithin efficiencyPopulation h hh) 0)
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh))) ∧
  (Tendsto (fun h : ℕ => 7 * h) atTop atTop)

/-- Mathematical content retained for P020-T3; see the Challenge docstring. -/
def T3Statement : Prop :=
  (StrictMono logistic) ∧
  (∀ (n : ℝ) (hn : 1 ≤ n),
  (2 : ℝ) / 5 - (9 : ℝ) / 10 * n ≤ -(1 : ℝ) / 2) ∧
  (∀ (base n : ℝ) (hn : 1 ≤ n),
  logistic (base + (2 : ℝ) / 5 - (9 : ℝ) / 10 * n) - logistic base < 0) ∧
  (∀ (N : ℕ) (hN : 0 < N) (base size : Fin N → ℝ)
    (hsize : ∀ i, 1 ≤ size i),
  (∑ i : Fin N, (logistic (base i + 2 / 5 - 9 / 10 * size i) -
      logistic (base i))) / (N : ℝ) < 0) ∧
  (∀ (N : ℕ) (hN : 0 < N) (base size : Fin N → ℝ)
    (hsize : ∀ i, 1 ≤ size i),
  (∑ i : Fin N, (logistic (base i + 2 / 5 - 9 / 10 * size i) -
      logistic (base i))) / (N : ℝ) ≠ (7 : ℝ) / 1000)

/-- Mathematical content retained for P020-T4; see the Challenge docstring. -/
def T4Statement : Prop :=
  (∀ (alpha block n t : ℝ),
  alpha + 2 / 5 * t + 7 / 5 * (n / 1000) - 9 / 10 * (n / 1000) * t + block =
    alpha + 2 / 5 * t + 7 / 5000 * n - 9 / 10000 * n * t + block) ∧
  (∀ (n : ℝ),
  (0 < repairedContrast n ↔ n < 4000 / 9) ∧
    (repairedContrast n < 0 ↔ 4000 / 9 < n)) ∧
  (∀ (n : ℕ),
  (0 < repairedContrast (n : ℝ) ↔ n ≤ 444) ∧
    (repairedContrast (n : ℝ) < 0 ↔ 445 ≤ n)) ∧
  (∀ (base : ℝ) (n : ℕ),
  (logistic base < logistic (base + repairedContrast n) ↔ n ≤ 444) ∧
    (logistic (base + repairedContrast n) < logistic base ↔ 445 ≤ n)) ∧
  (∀ (N : ℕ) (hN : 0 < N)
    (base : Fin N → ℝ) (size : Fin N → ℕ) (hsize : ∀ i, 1 ≤ size i),
  ((∀ i, size i ≤ 444) →
      0 < (∑ i, (logistic (base i + repairedContrast (size i)) - logistic (base i))) / N) ∧
    ((∀ i, 445 ≤ size i) →
      (∑ i, (logistic (base i + repairedContrast (size i)) - logistic (base i))) / N < 0))

/-- Mathematical content retained for P020-T5; see the Challenge docstring. -/
def T5Statement : Prop :=
  (∀ (P : ClusterPopulation)
    (khat : Finset (Fin P.M) → ℝ),
  expectation (clusterLaw P) (fun s => rajTotal P true (khat s) s) =
      (∑ j, P.y1 j) - (P.M : ℝ) *
        designCovariance (clusterLaw P) khat (armMeanSize P true) ∧
    expectation (clusterLaw P) (fun s => rajTotal P false (khat s) s) =
      (∑ j, P.y0 j) - (P.M : ℝ) *
        designCovariance (clusterLaw P) khat (armMeanSize P false) ∧
    expectation (clusterLaw P) (fun s => desRaj P (khat s) s) =
      averageTreatmentEffect P + (P.M : ℝ) / populationSize P *
        (designCovariance (clusterLaw P) khat (armMeanSize P false) -
         designCovariance (clusterLaw P) khat (armMeanSize P true))) ∧
  (∀ (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ),
    designBias (clusterLaw P) (fun s => desRaj P (khat s) s) (averageTreatmentEffect P) =
      (P.M : ℝ) / populationSize P *
        (designCovariance (clusterLaw P) khat (armMeanSize P false) -
         designCovariance (clusterLaw P) khat (armMeanSize P true)))

/-- Mathematical content retained for P020-T6; see the Challenge docstring. -/
def T6Statement : Prop :=
  (averageTreatmentEffect slopePopulation = (1 : ℝ) / 2 ∧
    observedSlope slopePopulation {0} = 0 ∧
    observedSlope slopePopulation {1} = 0 ∧
    observedSlope slopePopulation {2} = 3 / 2 ∧
    desRaj slopePopulation (observedSlope slopePopulation {0}) {0} = 0 ∧
    desRaj slopePopulation (observedSlope slopePopulation {1}) {1} = 0 ∧
    desRaj slopePopulation (observedSlope slopePopulation {2}) {2} = 3 / 8 ∧
    expectation (clusterLaw slopePopulation)
      (fun s => desRaj slopePopulation (observedSlope slopePopulation s) s) = 1 / 8 ∧
    expectation (clusterLaw slopePopulation)
      (fun s => desRaj slopePopulation (observedSlope slopePopulation s) s) ≠
      averageTreatmentEffect slopePopulation ∧
    designBias (clusterLaw slopePopulation)
      (fun s => desRaj slopePopulation (observedSlope slopePopulation s) s)
      (averageTreatmentEffect slopePopulation) = -3 / 8 ∧
    designCovariance (clusterLaw slopePopulation) (observedSlope slopePopulation)
      (armMeanSize slopePopulation true) = 1 / 2 ∧
    designCovariance (clusterLaw slopePopulation) (observedSlope slopePopulation)
      (armMeanSize slopePopulation false) = -1 / 4) ∧
  (populationSize slopePopulation = 6) ∧
  (clusterVariance (fun j => (slopePopulation.n j : ℝ)) = 2 / 3) ∧
  (armMeanSize slopePopulation true {0} = 1 ∧ armMeanSize slopePopulation true {1} = 2 ∧ armMeanSize slopePopulation true {2} = 3) ∧
  (armMeanSize slopePopulation false {0} = 5 / 2 ∧ armMeanSize slopePopulation false {1} = 2 ∧ armMeanSize slopePopulation false {2} = 3 / 2) ∧
  (designBias (clusterLaw slopePopulation)
      (fun s => desRaj slopePopulation (observedSlope slopePopulation s) s)
      (averageTreatmentEffect slopePopulation) =
      (slopePopulation.M : ℝ) / populationSize slopePopulation *
        (designCovariance (clusterLaw slopePopulation) (observedSlope slopePopulation) (armMeanSize slopePopulation false) -
         designCovariance (clusterLaw slopePopulation) (observedSlope slopePopulation) (armMeanSize slopePopulation true)))

/-- Mathematical content retained for P020-T7; see the Challenge docstring. -/
def T7Statement : Prop :=
  (∀ (n : ℕ) (Y : Fin n → ℝ) (b0 b1 : ℝ),
  clusterTotal (fun i => b0 + b1 * Y i) = (n : ℝ) * b0 + b1 * clusterTotal Y) ∧
  (∀ (P : ClusterPopulation) (a : Bool) (b0 b1 k : ℝ)
    (j : Fin P.M),
  rajPotential (affinePopulation P b0 b1) a (b0 + b1 * k) j =
      b0 * ((populationSize P : ℝ) / P.M) + b1 * rajPotential P a k j) ∧
  (∀ (P : ClusterPopulation) (b0 b1 k : ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P),
  desRaj (affinePopulation P b0 b1) (b0 + b1 * k) s =
      (P.M : ℝ) / populationSize P *
        ((∑ j ∈ s, (b0 * ((populationSize P : ℝ) / P.M) + b1 * rajPotential P true k j)) / P.mt -
         (∑ j ∈ controls s, (b0 * ((populationSize P : ℝ) / P.M) + b1 * rajPotential P false k j)) /
           controlCount P) ∧
    desRaj (affinePopulation P b0 b1) (b0 + b1 * k) s = b1 * desRaj P k s) ∧
  (∀ (P : ClusterPopulation) (b0 b1 k : ℝ)
    (s : Finset (Fin P.M)) (hs : s ∈ assignments P),
  desRaj (affinePopulation P b0 b1) (b0 + b1 * k) s =
      (P.M : ℝ) / populationSize P *
        (b1 * armSum P true (rajPotential P true k) s / P.mt -
         b1 * armSum P false (rajPotential P false k) s / controlCount P) ∧
    (P.M : ℝ) / populationSize P *
        (b1 * armSum P true (rajPotential P true k) s / P.mt -
         b1 * armSum P false (rajPotential P false k) s / controlCount P) =
      b1 * desRaj P k s)

/-- Mathematical content retained for P020-T8; see the Challenge docstring. -/
def T8Statement : Prop :=
  (∀ {M : ℕ} (hM : 0 < M) (v size : Fin M → ℝ) (k : ℝ),
  clusterMean (differenced v size k) = clusterMean v) ∧
  (∀ {M : ℕ} (hM : 0 < M) (v size : Fin M → ℝ) (k : ℝ),
  clusterVariance (differenced v size k) = clusterVariance v +
      k^2 * clusterVariance size - 2 * k * clusterCovariance v size) ∧
  (∀ {M : ℕ} (hM : 0 < M) (v w size : Fin M → ℝ) (k : ℝ),
    let δ := fun j => size j - clusterMean size
    let C := clusterCovariance (differenced v size k) (differenced w size k)
    C = clusterMean (fun j => differenced v size k j * differenced w size k j) -
      clusterMean (differenced v size k) * clusterMean (differenced w size k) ∧
    C = clusterMean (fun j => (v j - k * δ j) * (w j - k * δ j)) - clusterMean v * clusterMean w ∧
    C = clusterMean (fun j => v j * w j - v j * k * δ j - w j * k * δ j + k^2 * δ j^2) -
      clusterMean v * clusterMean w ∧
    C = clusterMean (fun j => v j * w j) - clusterMean v * clusterMean w -
      clusterMean (fun j => v j * k * δ j) - clusterMean (fun j => w j * k * δ j) +
      clusterMean (fun j => k^2 * δ j^2) ∧
    C = clusterCovariance v w - k * (clusterCovariance v size + clusterMean v * clusterMean δ) -
      k * (clusterCovariance w size + clusterMean w * clusterMean δ) + k^2 * clusterVariance size ∧
    C = clusterCovariance v w - k * (clusterCovariance v size + clusterMean v * 0) -
      k * (clusterCovariance w size + clusterMean w * 0) + k^2 * clusterVariance size ∧
    C = clusterCovariance v w - k * clusterCovariance v size -
      k * clusterCovariance w size + k^2 * clusterVariance size)

end
end SAP.P020
