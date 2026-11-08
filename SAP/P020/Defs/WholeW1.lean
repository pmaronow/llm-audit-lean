import Mathlib
import SAP.P020.Defs
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P020
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
noncomputable section
/-- P020-T3; p. 61 (PDF p. 23); cluster counts on p. 44 (PDF p. 6). The printed claim is false: the printed logistic coefficients force every individual contrast and every nonempty population average to be negative, excluding +0.007. The scalar calculation at size one is valid, but no one-person cluster experiment satisfies the standing positive-arm and positive-cluster-size assumptions. -/
def T3WholeStatement : Prop := T3Statement ∧ (logistic 0 = (1 : ℝ) / 2 ∧ logistic (-(1 : ℝ) / 2) < 1 / 2 ∧ logistic (-(1 : ℝ) / 2) - logistic 0 ≠ 7 / 1000) ∧ (∀ P : ClusterPopulation, P.M ≤ populationSize P ∧ 2 ≤ populationSize P) ∧ ¬ (∃ P : ClusterPopulation, populationSize P = 1)
/-- Fixed arm cluster count, as a real number. Both choices are positive. -/
def W1ArmCount (P : ClusterPopulation) (a : Bool) : ℝ := if a then P.mt else controlCount P
/-- The arm's cluster labels under a given assignment. -/
def W1ArmSet {M : ℕ} (a : Bool) (s : Finset (Fin M)) : Finset (Fin M) := if a then s else controls s
/-- The observed mean of cluster totals in an arm. -/
def W1ObservedArmMean (P : ClusterPopulation) (a : Bool) (s : Finset (Fin P.M)) : ℝ := (∑ j ∈ W1ArmSet a s, observedTotal P s j) / W1ArmCount P a
/-- Equations (20)-(21) using observed, rather than potential, totals. -/
def W1ObservedRajTotal (P : ClusterPopulation) (a : Bool) (khat : Finset (Fin P.M) → ℝ) (s : Finset (Fin P.M)) : ℝ := (P.M : ℝ) / W1ArmCount P a * ∑ j ∈ W1ArmSet a s,
      (observedTotal P s j - khat s * ((P.n j : ℝ) - (populationSize P : ℝ) / P.M))
/-- All intermediate lines of Appendix B (29), for either arm; (30) is its control-arm specialization. No independence or moment condition on the fitted coefficient is imposed: the assignment space is finite. -/
def W1RajExpectationChain (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool) : Prop :=
  let E := expectation (clusterLaw P)
  let R := fun s => rajTotal P a (khat s) s
  let O := W1ObservedRajTotal P a khat
  let m := W1ArmCount P a
  let y := if a then P.y1 else P.y0
  let B := (P.M : ℝ) / m * (E (fun s => ∑ j ∈ W1ArmSet a s, observedTotal P s j) - E (fun s => ∑ j ∈ W1ArmSet a s, khat s * (P.n j : ℝ)) + E (fun s => ∑ _j ∈ W1ArmSet a s, khat s * (populationSize P : ℝ) / P.M))
  let C := (P.M : ℝ) / m * (E (fun s => m * W1ObservedArmMean P a s) -
     E (fun s => khat s * m * armMeanSize P a s) +
     E (fun s => khat s * m * (populationSize P : ℝ) / P.M))
  let D := (∑ j, y j) - (P.M : ℝ) *
    (E (fun s => khat s * armMeanSize P a s) - E khat * E (armMeanSize P a))
  (∀ s ∈ assignments P, R s = O s) ∧
  E (armMeanSize P a) = (populationSize P : ℝ) / P.M ∧
  E (fun s => m * W1ObservedArmMean P a s) = m / P.M * ∑ j, y j ∧
  E R = E O ∧ E O = B ∧ B = C ∧ C = D ∧
  D = (∑ j, y j) - (P.M : ℝ) * designCovariance (clusterLaw P) khat (armMeanSize P a)
/-- P020-T5; Appendix B, pp. 70-71 (PDF pp. 32-33); pp. 57-58 (PDF pp. 19-20). For every coefficient estimated from the same experiment, both complete arm-total expectation calculations (29)-(30) hold, and the corrected ATE expectation is Delta plus M/N times (control covariance minus treatment covariance), while the bias equals that covariance correction. -/
def T5WholeStatement : Prop :=
  T5Statement ∧
  ∀ (P : ClusterPopulation) (khat : Finset (Fin P.M) → ℝ) (a : Bool),
    W1RajExpectationChain P khat a
/-- P020-T13; p. 54 (PDF p. 16); pp. 58-59 (PDF pp. 20-21). The printed claim is false: under design expectation a fixed cluster's centered size is a constant, not a mean-zero random variable. In the admissible two-cluster population of sizes (1,2), k=1 and the size-one cluster give expectation -1/2. Both fixed-size-adjusted and fixed-covariate-adjusted Des Raj estimators nevertheless estimate both potential totals and the ATE without bias. The arm-mean centering calculation is explicitly recorded as a valid correction of (22). -/
def T13WholeStatement : Prop :=
  T13Statement ∧
  (∀ (P : ClusterPopulation) (k : ℝ) (j : Fin P.M),
    expectation (clusterLaw P) (fun _ => k * ((P.n j : ℝ) - (populationSize P : ℝ) / P.M)) =
      k * expectation (clusterLaw P) (fun _ => (P.n j : ℝ) - (populationSize P : ℝ) / P.M) ∧
    expectation (clusterLaw P) (fun _ => k * ((P.n j : ℝ) - (populationSize P : ℝ) / P.M)) =
      k * ((P.n j : ℝ) - (populationSize P : ℝ) / P.M) ∧
    (expectation (clusterLaw P) (fun _ => k * ((P.n j : ℝ) - (populationSize P : ℝ) / P.M)) = 0 ↔
      k = 0 ∨ (P.n j : ℝ) = (populationSize P : ℝ) / P.M)) ∧
  (populationSize subscriptPopulation = 3 ∧
    expectation (clusterLaw subscriptPopulation)
      (fun _ => (1 : ℝ) * ((subscriptPopulation.n 0 : ℝ) -
        (populationSize subscriptPopulation : ℝ) / subscriptPopulation.M)) = -(1 : ℝ) / 2) ∧
  (¬ ∀ (P : ClusterPopulation) (k : ℝ) (j : Fin P.M),
    expectation (clusterLaw P) (fun _ => k * ((P.n j : ℝ) - (populationSize P : ℝ) / P.M)) = 0) ∧
  (∀ (P : ClusterPopulation) (k : ℝ) (a : Bool),
    expectation (clusterLaw P) (fun s => k * (armMeanSize P a s - (populationSize P : ℝ) / P.M)) =
      k * expectation (clusterLaw P) (fun s => armMeanSize P a s - (populationSize P : ℝ) / P.M) ∧
    expectation (clusterLaw P) (fun s => k * (armMeanSize P a s - (populationSize P : ℝ) / P.M)) = 0)
/-- The fixed real cluster-size vector. -/
def W1Sizes (P : ClusterPopulation) : Fin P.M → ℝ := fun j => P.n j
/-- Population size variance, with divisor M. -/
def W1SizeVariance (P : ClusterPopulation) : ℝ := clusterVariance (W1Sizes P)
/-- Covariance of size with an arm's potential total, with divisor M. -/
def W1SizeCovariance (P : ClusterPopulation) (a : Bool) : ℝ :=
  clusterCovariance (W1Sizes P) (if a then P.y1 else P.y0)
/-- The control variance multiplier in Appendix C. -/
def W1c (P : ClusterPopulation) : ℝ := ((P.M : ℝ) - controlCount P) / controlCount P
/-- The treatment variance multiplier in Appendix C. -/
def W1t (P : ClusterPopulation) : ℝ := ((P.M : ℝ) - P.mt) / P.mt
/-- The positive scaling v in equation (32). -/
def W1v (P : ClusterPopulation) : ℝ := ((P.M : ℝ) - 1) * (populationSize P : ℝ)^2 / (P.M : ℝ)^2
/-- An arm's differenced population variance as a function of k. -/
def W1ArmVariance (P : ClusterPopulation) (a : Bool) (k : ℝ) : ℝ :=
  clusterVariance (rajPotential P a k)
/-- The mean preservation and two variance displays preceding equation (26), including the explicit sum centered at the original outcome mean. -/
def W1ArmExpansion (P : ClusterPopulation) (a : Bool) : Prop :=
  ∀ k : ℝ,
    clusterMean (rajPotential P a k) = clusterMean (if a then P.y1 else P.y0) ∧
    W1ArmVariance P a k =
      (∑ j, ((if a then P.y1 else P.y0) j -
        k * ((P.n j : ℝ) - (populationSize P : ℝ) / P.M) -
        clusterMean (if a then P.y1 else P.y0))^2) / P.M ∧
    W1ArmVariance P a k = clusterVariance (if a then P.y1 else P.y0) +
      k^2 * W1SizeVariance P - 2 * k * W1SizeCovariance P a
/-- The complete substituted quadratic in equation (32), with the actual design variance identified before any division by the size variance. -/
def W1ObjectiveExpansion (P : ClusterPopulation) : Prop :=
  ∀ k : ℝ,
    W1v P * designVariance (clusterLaw P) (desRaj P k) = rajMomentObjective P k ∧
    rajMomentObjective P k =
      W1c P * (clusterVariance P.y0 + k^2 * W1SizeVariance P - 2*k*W1SizeCovariance P false) +
      W1t P * (clusterVariance P.y1 + k^2 * W1SizeVariance P - 2*k*W1SizeCovariance P true) +
      2 * (clusterCovariance P.y0 P.y1 - k*W1SizeCovariance P false -
        k*W1SizeCovariance P true + k^2 * W1SizeVariance P)
/-- First and second derivatives of the two arm quadratics and the common moment objective. The second derivatives are derivatives of the actual first derivative functions, not of an unrelated polynomial. -/
def W1VarianceDerivatives (P : ClusterPopulation) : Prop :=
  (∀ (a : Bool) (k : ℝ),
    HasDerivAt (W1ArmVariance P a) (2*k*W1SizeVariance P - 2*W1SizeCovariance P a) k ∧
    HasDerivAt (deriv (W1ArmVariance P a)) (2*W1SizeVariance P) k) ∧
  (∀ k : ℝ,
    HasDerivAt (rajMomentObjective P)
      (W1c P * (2*k*W1SizeVariance P - 2*W1SizeCovariance P false) +
       W1t P * (2*k*W1SizeVariance P - 2*W1SizeCovariance P true) +
       2 * (-W1SizeCovariance P false - W1SizeCovariance P true + 2*k*W1SizeVariance P)) k ∧
    deriv (rajMomentObjective P) k =
      2*(W1c P + W1t P + 2)*k*W1SizeVariance P -
        2*((W1c P + 1)*W1SizeCovariance P false + (W1t P + 1)*W1SizeCovariance P true) ∧
    HasDerivAt (deriv (rajMomentObjective P))
      (2*(W1c P + W1t P + 2)*W1SizeVariance P) k)
/-- Appendix C's full first-order and coefficient-rearrangement chain. This property is asserted only when the size variance is nonzero. -/
def W1OptimalAlgebra (P : ClusterPopulation) : Prop :=
  let s := W1SizeVariance P
  let q0 := W1SizeCovariance P false
  let q1 := W1SizeCovariance P true
  let c := W1c P
  let t := W1t P
  let mc : ℝ := controlCount P
  let mt : ℝ := P.mt
  let M : ℝ := P.M
  let κ := optimalCoefficient P
  0 < s ∧ 0 < W1v P ∧ 0 < c+t+2 ∧
  (∀ a : Bool, 0 < 2*s ∧ ∀ k : ℝ,
    (deriv (W1ArmVariance P a) k = 0 ↔ k = armOptimalCoefficient P a)) ∧
  (∀ k : ℝ, deriv (rajMomentObjective P) k = 0 ↔ k = κ) ∧
  0 < 2*(c+t+2)*s ∧
  0 = c*(2*κ*s-2*q0) + t*(2*κ*s-2*q1) + 2*(-q0-q1+2*κ*s) ∧
  c*κ*s+t*κ*s+2*κ*s = c*q0+t*q1+q0+q1 ∧
  (c+t+2)*κ*s = (c+1)*q0+(t+1)*q1 ∧
  ((M-mc)/mc+(M-mt)/mt+mc/mc+mt/mt)*κ*s =
    ((M-mc)/mc+mc/mc)*q0+((M-mt)/mt+mt/mt)*q1 ∧
  (M/mc+M/mt)*κ*s = (M/mc)*q0+(M/mt)*q1 ∧
  κ = (1/mc+1/mt)⁻¹ * ((1/mc)*(q0/s)+(1/mt)*(q1/s)) ∧
  κ = (1/mc+1/mt)⁻¹ * (armOptimalCoefficient P false/mc+armOptimalCoefficient P true/mt) ∧
  κ = mt/M*armOptimalCoefficient P false+mc/M*armOptimalCoefficient P true ∧
  (∀ k : ℝ, rajMomentObjective P κ ≤ rajMomentObjective P k ∧
    (rajMomentObjective P κ = rajMomentObjective P k ↔ k = κ))
/-- Every efficiency inequality in Appendix C, including the steps dividing by size variance and the multiplier c+t+2. -/
def W1EfficiencyChain (P : ClusterPopulation) : Prop :=
  let s := W1SizeVariance P
  let q0 := W1SizeCovariance P false
  let q1 := W1SizeCovariance P true
  let c := W1c P
  let t := W1t P
  let k0 := armOptimalCoefficient P false
  let k1 := armOptimalCoefficient P true
  let κ := optimalCoefficient P
  ∀ k : ℝ,
    (designVariance (clusterLaw P) (desRaj P k) < designVariance (clusterLaw P) (horvitzThompson P) ↔
      (c+t+2)*k^2*s < 2*k*((c+1)*q0+(t+1)*q1)) ∧
    ((c+t+2)*k^2*s < 2*k*((c+1)*q0+(t+1)*q1) ↔
      (c+t+2)*k^2 < 2*k*((c+1)*(q0/s)+(t+1)*(q1/s))) ∧
    ((c+t+2)*k^2 < 2*k*((c+1)*(q0/s)+(t+1)*(q1/s)) ↔
      (c+t+2)*k^2 < 2*k*((c+1)*k0+(t+1)*k1)) ∧
    ((c+t+2)*k^2 < 2*k*((c+1)*k0+(t+1)*k1) ↔
      k^2 < 2*k*((P.mt : ℝ)/P.M*k0+(controlCount P : ℝ)/P.M*k1)) ∧
    (k^2 < 2*k*((P.mt : ℝ)/P.M*k0+(controlCount P : ℝ)/P.M*k1) ↔ k^2 < 2*k*κ) ∧
    (k^2 < 2*k*κ ↔ (0 < κ ∧ 0 < k ∧ k < 2*κ) ∨ (κ < 0 ∧ 2*κ < k ∧ k < 0))
/-- P020-T14; pp. 56-57 (PDF pp. 18-19); Appendix C, pp. 71-73 (PDF pp. 33-35). The differenced means, explicit variance expansions, first and second derivatives, and scaled design-variance quadratic hold. When the size variance is nonzero, the arm and common coefficients are unique stationary minima, all first-order rearrangements and coefficient formulas hold, and every efficiency inequality is equivalent to the stated sign intervals. Equal cluster sizes give HT for every k. -/
def T14WholeStatement : Prop :=
  T14Statement ∧
  (∀ (P : ClusterPopulation) (a : Bool), W1ArmExpansion P a) ∧
  (∀ P : ClusterPopulation, W1ObjectiveExpansion P) ∧
  (∀ P : ClusterPopulation, W1VarianceDerivatives P) ∧
  (∀ (P : ClusterPopulation), W1SizeVariance P ≠ 0 → W1OptimalAlgebra P ∧ W1EfficiencyChain P) ∧
  (∀ (P : ClusterPopulation) (n : ℕ), (∀ j, P.n j = n) →
    ∀ (k : ℝ) (s : Finset (Fin P.M)), desRaj P k s = horvitzThompson P s)
/-- A supported one-copy assignment, with its validity certificate. -/
abbrev W1Assignment (P : ClusterPopulation) := {s : Finset (Fin P.M) // s ∈ assignments P}
instance W1AssignmentNonempty (P : ClusterPopulation) : Nonempty (W1Assignment P) :=
  ⟨⟨(assignments_nonempty P).choose, (assignments_nonempty P).choose_spec⟩⟩
instance W1AssignmentMeasurableSpace (P : ClusterPopulation) : MeasurableSpace (W1Assignment P) := ⊤
instance W1AssignmentDiscrete (P : ClusterPopulation) : DiscreteMeasurableSpace (W1Assignment P) := ⟨fun _ => trivial⟩
/-- A single uniform complete cluster randomization. -/
def W1AssignmentMeasure (P : ClusterPopulation) : Measure (W1Assignment P) :=
  uniformOn Set.univ
instance W1AssignmentProbability (P : ClusterPopulation) : IsProbabilityMeasure (W1AssignmentMeasure P) :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn (Set.univ : Set (W1Assignment P))))
/-- One infinite path of valid independent-copy assignments. -/
abbrev W1Path (P : ClusterPopulation) := ℕ → W1Assignment P
/-- The countable product law, used to retain earlier assignments as h grows. -/
def W1CopyMeasure (P : ClusterPopulation) : Measure (W1Path P) :=
  Measure.infinitePi (fun _ : ℕ => W1AssignmentMeasure P)
instance W1CopyProbability (P : ClusterPopulation) : IsProbabilityMeasure (W1CopyMeasure P) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => W1AssignmentMeasure P)))
/-- The first h copies of a path. -/
def W1Prefix (P : ClusterPopulation) (h : ℕ) (ω : W1Path P) : CopyAssignments P h :=
  fun i => ω i.val
/-- Convergence in probability, with a probability certificate so that every real-valued event probability is the real value of a finite measure. -/
def W1InProbability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) (d : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ ε : ℝ, 0 < ε →
    Tendsto (fun r => μ.real {ω | ε < |X r ω - d|}) atTop (nhds 0)
/-- The actual population size on the product cluster set Fin h × Fin M. -/
def W1CopiedN (P : ClusterPopulation) (h : ℕ) : ℕ :=
  ∑ c : Fin h × Fin P.M, P.n c.2
/-- The ATE of the copied population, using its potential totals and size. -/
def W1CopiedATE (P : ClusterPopulation) (h : ℕ) : ℝ :=
  ((∑ c : Fin h × Fin P.M, P.y1 c.2) - ∑ c : Fin h × Fin P.M, P.y0 c.2) / W1CopiedN P h
/-- Treated or control clusters of a finite copy assignment on the product set. -/
def W1CopiedArm (P : ClusterPopulation) (h : ℕ) (a : Bool) (s : CopyAssignments P h) : Finset (Fin h × Fin P.M) :=
  Finset.univ.filter (fun c => c.2 ∈ W1ArmSet a (s c.1).val)
/-- The pooled observed difference in means on the product cluster set. -/
def W1CopiedEstimator (P : ClusterPopulation) (h : ℕ) (s : CopyAssignments P h) : ℝ :=
  (∑ c ∈ W1CopiedArm P h true s, P.y1 c.2) /
    (∑ c ∈ W1CopiedArm P h true s, (P.n c.2 : ℝ)) -
  (∑ c ∈ W1CopiedArm P h false s, P.y0 c.2) /
    (∑ c ∈ W1CopiedArm P h false s, (P.n c.2 : ℝ))
/-- The finite population, cluster counts, unchanged target, and the connection between product-cluster sums and the existing independent-copy estimator. -/
def W1CopyPopulationFacts (P : ClusterPopulation) (h : ℕ) (s : CopyAssignments P h) : Prop :=
  Fintype.card (Fin h × Fin P.M) = h * P.M ∧
  (W1CopiedArm P h true s).card = h * P.mt ∧
  (W1CopiedArm P h false s).card = h * controlCount P ∧
  W1CopiedN P h = h * populationSize P ∧
  W1CopiedATE P h = averageTreatmentEffect P ∧
  (∀ a : Bool,
    (∑ c ∈ W1CopiedArm P h a s, (P.n c.2 : ℝ)) = ∑ r, armSize P a (s r).val ∧
    0 < ∑ r, armSize P a (s r).val) ∧
  W1CopiedEstimator P h s = copiedDifferenceInMeans P h s
/-- The independent uniform coordinate laws and all finite prefix laws. The zero prefix is permitted here; population ratios use only positive prefixes. -/
def W1CopyMarginals (P : ClusterPopulation) : Prop :=
  IsProbabilityMeasure (W1CopyMeasure P) ∧
  iIndepFun (fun r (ω : W1Path P) => ω r) (W1CopyMeasure P) ∧
  (∀ r : ℕ, (W1CopyMeasure P).map (fun ω => ω r) = W1AssignmentMeasure P) ∧
  (∀ h : ℕ, (W1CopyMeasure P).map (W1Prefix P h) =
    (uniformOn Set.univ : Measure (CopyAssignments P h)))
/-- The finite-law error probabilities equal those on the common realization. -/
def W1CopyCoupling (P : ClusterPopulation) : Prop :=
  W1CopyMarginals P ∧ ∀ (h : ℕ) (T : CopyAssignments P h → ℝ) (d ε : ℝ),
    (W1CopyMeasure P).real {ω | ε < |T (W1Prefix P h ω) - d|} =
      errorProbability (copyLaw P h) T d ε
/-- Total size and both realized arm sizes strictly increase along the positive prefix sequence, and along within-cluster replication with the same draw. -/
def W1ReplicationGrowth (P : ClusterPopulation) : Prop :=
  StrictMono (fun r : ℕ => W1CopiedN P (r+1)) ∧
  (∀ (ω : W1Path P) (a : Bool),
    StrictMono (fun r : ℕ => ∑ i : Fin (r+1), armSize P a (ω i.val).val)) ∧
  StrictMono (fun r : ℕ => populationSize (replicateWithin P (r+1) (Nat.succ_pos r))) ∧
  (∀ (s : W1Assignment P) (a : Bool),
    StrictMono (fun r : ℕ => armSize (replicateWithin P (r+1) (Nat.succ_pos r)) a s.val))
/-- The four weak laws and the pooled ratio limit on the shared path space. -/
def W1CoupledLimits (P : ClusterPopulation) : Prop :=
  W1InProbability (W1CopyMeasure P)
    (fun r ω => copyAverage P true P.y1 (r+1) (W1Prefix P (r+1) ω))
    ((P.mt : ℝ)/P.M * ∑ j, P.y1 j) ∧
  W1InProbability (W1CopyMeasure P)
    (fun r ω => copyAverage P false P.y0 (r+1) (W1Prefix P (r+1) ω))
    ((controlCount P : ℝ)/P.M * ∑ j, P.y0 j) ∧
  W1InProbability (W1CopyMeasure P)
    (fun r ω => copyAverage P true (W1Sizes P) (r+1) (W1Prefix P (r+1) ω))
    ((P.mt : ℝ)/P.M * populationSize P) ∧
  W1InProbability (W1CopyMeasure P)
    (fun r ω => copyAverage P false (W1Sizes P) (r+1) (W1Prefix P (r+1) ω))
    ((controlCount P : ℝ)/P.M * populationSize P) ∧
  W1InProbability (W1CopyMeasure P)
    (fun r ω => copiedDifferenceInMeans P (r+1) (W1Prefix P (r+1) ω)) (averageTreatmentEffect P)
/-- Further within-cluster replication facts, including the law and bias for all base populations, and the event-law bridge for a single reused draw. -/
def W1WithinDetails (P : ClusterPopulation) : Prop :=
  ∀ (h : ℕ) (hh : 0 < h),
    (∀ (a : Bool) (s : Finset (Fin P.M)),
      armSize (replicateWithin P h hh) a s = (h : ℝ) * armSize P a s) ∧
    clusterLaw (replicateWithin P h hh) = clusterLaw P ∧
    designBias (clusterLaw (replicateWithin P h hh)) (differenceInMeans (replicateWithin P h hh))
      (averageTreatmentEffect (replicateWithin P h hh)) =
      designBias (clusterLaw P) (differenceInMeans P) (averageTreatmentEffect P) ∧
    (∀ ε : ℝ, (W1AssignmentMeasure P).real
      {s | ε < |differenceInMeans (replicateWithin P h hh) s.val - averageTreatmentEffect P|} =
        errorProbability (clusterLaw (replicateWithin P h hh))
          (differenceInMeans (replicateWithin P h hh))
          (averageTreatmentEffect (replicateWithin P h hh)) ε)
/-- P020-T17; pp. 45-47 (PDF pp. 7-9); Figure 1 on p. 46 (PDF p. 8). Consistency means convergence in probability along populations whose total and both realized arm counts strictly increase. Independent exact copies have a common path realization with the stipulated uniform prefix laws, all growth certificates, all four weak laws, positive denominators and pooled consistency. Within-cluster replication with a common draw has the same strict growth but preserves the target, estimates, law and bias; nonzero bias implies inconsistency. The sizes (1,2,4), control totals (0,1,1), treatment totals (0,0,0) give N_h=7h, ATE=-2/7, bias=-1/315 and error probability one at tolerance 1/25 for every h. -/
def T17WholeStatement : Prop :=
  T17Statement ∧
  (∀ (P : ClusterPopulation) (h : ℕ), 0 < h → ∀ s : CopyAssignments P h, W1CopyPopulationFacts P h s) ∧
  (∀ (P : ClusterPopulation) (h : ℕ), h * controlCount P = h * P.M - h * P.mt) ∧
  (∀ P : ClusterPopulation, W1CopyCoupling P) ∧
  (∀ P : ClusterPopulation, W1ReplicationGrowth P) ∧
  (∀ P : ClusterPopulation, W1CoupledLimits P) ∧
  (∀ P : ClusterPopulation, W1WithinDetails P) ∧
  (∀ (P : ClusterPopulation),
    0 < (P.mt : ℝ)/P.M * populationSize P ∧
    0 < (controlCount P : ℝ)/P.M * populationSize P) ∧
  (∀ (P : ClusterPopulation),
    designBias (clusterLaw P) (differenceInMeans P) (averageTreatmentEffect P) ≠ 0 →
    ¬ WithinReplicationConsistent P ∧
    ¬ W1InProbability (W1AssignmentMeasure P)
      (fun r s => differenceInMeans (replicateWithin P (r+1) (Nat.succ_pos r)) s.val)
      (averageTreatmentEffect P)) ∧
  (∀ (h : ℕ) (hh : 0 < h),
    populationSize (replicateWithin efficiencyPopulation h hh) = 7*h ∧
    averageTreatmentEffect (replicateWithin efficiencyPopulation h hh) = -(2 : ℝ)/7 ∧
    errorProbability (clusterLaw (replicateWithin efficiencyPopulation h hh))
      (differenceInMeans (replicateWithin efficiencyPopulation h hh))
      (averageTreatmentEffect (replicateWithin efficiencyPopulation h hh)) (1/25) = 1)
end
end SAP.P020
