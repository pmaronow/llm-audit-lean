import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P020
open scoped BigOperators
open Filter
noncomputable section

/-- A finite randomization distribution with normalized nonnegative weights. -/
structure FiniteLaw (Ω : Type*) where
  support : Finset Ω
  weight : Ω → ℝ
  nonneg : ∀ ω ∈ support, 0 ≤ weight ω
  total : ∑ ω ∈ support, weight ω = 1

/-- The paper quantity expectation, expressed using finite sums and ordinary real arithmetic. -/
def expectation {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) : ℝ :=
  ∑ ω ∈ L.support, L.weight ω * T ω

/-- The paper quantity designBias, expressed using finite sums and ordinary real arithmetic. -/
def designBias {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d : ℝ) : ℝ :=
  expectation L T - d

/-- The paper quantity designVariance, expressed using finite sums and ordinary real arithmetic. -/
def designVariance {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) : ℝ :=
  expectation L (fun ω => (T ω - expectation L T)^2)

/-- The paper quantity designCovariance, expressed using finite sums and ordinary real arithmetic. -/
def designCovariance {Ω : Type*} (L : FiniteLaw Ω) (T U : Ω → ℝ) : ℝ :=
  expectation L (fun ω => (T ω - expectation L T) * (U ω - expectation L U))

/-- The paper quantity meanSquaredError, expressed using finite sums and ordinary real arithmetic. -/
def meanSquaredError {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d : ℝ) : ℝ :=
  expectation L (fun ω => (T ω - d)^2)

/-- The paper quantity errorProbability, expressed using finite sums and ordinary real arithmetic. -/
def errorProbability {Ω : Type*} (L : FiniteLaw Ω) (T : Ω → ℝ) (d ε : ℝ) : ℝ := by
  classical
  exact ∑ ω ∈ L.support, if ε < |T ω - d| then L.weight ω else 0

/-- Convergence in probability for finite laws, allowing the assignment space to vary. -/
def DesignConsistent {Ω : ℕ → Type*} (L : ∀ h, FiniteLaw (Ω h))
    (T : ∀ h, Ω h → ℝ) (d : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun h => errorProbability (L h) (T h) (d h) ε) atTop (nhds 0)

/-- The uniform distribution on a nonempty finite support. -/
def uniformLaw {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) : FiniteLaw Ω where
  support := s
  weight := fun _ => 1 / (s.card : ℝ)
  nonneg := by intros; positivity
  total := by
    have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hs)
    simp [Finset.sum_const, nsmul_eq_mul, hc]

/-- Fixed positive cluster sizes and potential totals; both arms are nonempty. -/
structure ClusterPopulation where
  M : ℕ
  mt : ℕ
  mt_pos : 0 < mt
  mt_lt : mt < M
  n : Fin M → ℕ
  n_pos : ∀ j, 0 < n j
  y0 : Fin M → ℝ
  y1 : Fin M → ℝ

/-- The paper quantity clusterTotal, expressed using finite sums and ordinary real arithmetic. -/
def clusterTotal {n : ℕ} (Y : Fin n → ℝ) : ℝ := ∑ i, Y i

/-- The paper quantity populationSize, expressed using finite sums and ordinary real arithmetic. -/
def populationSize (P : ClusterPopulation) : ℕ := ∑ j, P.n j

/-- The paper quantity controlCount, expressed using finite sums and ordinary real arithmetic. -/
def controlCount (P : ClusterPopulation) : ℕ := P.M - P.mt

/-- The paper quantity assignments, expressed using finite sums and ordinary real arithmetic. -/
def assignments (P : ClusterPopulation) : Finset (Finset (Fin P.M)) :=
  Finset.univ.powersetCard P.mt

/-- The treatment-assignment support is nonempty by the fixed arm counts. -/
def assignments_nonempty (P : ClusterPopulation) : (assignments P).Nonempty :=
  Finset.powersetCard_nonempty.mpr (by simpa using Nat.le_of_lt P.mt_lt)

/-- Complete randomization of the fixed number of treated clusters. -/
def clusterLaw (P : ClusterPopulation) : FiniteLaw (Finset (Fin P.M)) :=
  uniformLaw (assignments P) (assignments_nonempty P)

/-- The paper quantity controls, expressed using finite sums and ordinary real arithmetic. -/
def controls {M : ℕ} (s : Finset (Fin M)) : Finset (Fin M) := Finset.univ \ s

/-- The paper quantity observedTotal, expressed using finite sums and ordinary real arithmetic. -/
def observedTotal (P : ClusterPopulation) (s : Finset (Fin P.M)) (j : Fin P.M) : ℝ :=
  if j ∈ s then P.y1 j else P.y0 j

/-- The paper quantity averageTreatmentEffect, expressed using finite sums and ordinary real arithmetic. -/
def averageTreatmentEffect (P : ClusterPopulation) : ℝ :=
  ((∑ j, P.y1 j) - ∑ j, P.y0 j) / populationSize P

/-- The paper quantity armSum, expressed using finite sums and ordinary real arithmetic. -/
def armSum (P : ClusterPopulation) (treatment : Bool) (v : Fin P.M → ℝ)
    (s : Finset (Fin P.M)) : ℝ :=
  ∑ j ∈ (if treatment then s else controls s), v j

/-- The paper quantity armSize, expressed using finite sums and ordinary real arithmetic. -/
def armSize (P : ClusterPopulation) (treatment : Bool) (s : Finset (Fin P.M)) : ℝ :=
  armSum P treatment (fun j => (P.n j : ℝ)) s

/-- The paper quantity armMeanSize, expressed using finite sums and ordinary real arithmetic. -/
def armMeanSize (P : ClusterPopulation) (treatment : Bool) (s : Finset (Fin P.M)) : ℝ :=
  armSize P treatment s / (if treatment then P.mt else controlCount P)

/-- The paper quantity differenceInMeans, expressed using finite sums and ordinary real arithmetic. -/
def differenceInMeans (P : ClusterPopulation) (s : Finset (Fin P.M)) : ℝ :=
  armSum P true P.y1 s / armSize P true s -
  armSum P false P.y0 s / armSize P false s

/-- The paper quantity htTotal, expressed using finite sums and ordinary real arithmetic. -/
def htTotal (P : ClusterPopulation) (treatment : Bool) (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ) / (if treatment then P.mt else controlCount P) *
    armSum P treatment (if treatment then P.y1 else P.y0) s

/-- The paper quantity horvitzThompson, expressed using finite sums and ordinary real arithmetic. -/
def horvitzThompson (P : ClusterPopulation) (s : Finset (Fin P.M)) : ℝ :=
  (htTotal P true s - htTotal P false s) / populationSize P

/-- The paper quantity clusterMean, expressed using finite sums and ordinary real arithmetic. -/
def clusterMean {M : ℕ} (v : Fin M → ℝ) : ℝ := (∑ j, v j) / M

/-- The paper quantity clusterCovariance, expressed using finite sums and ordinary real arithmetic. -/
def clusterCovariance {M : ℕ} (v w : Fin M → ℝ) : ℝ :=
  clusterMean (fun j => (v j - clusterMean v) * (w j - clusterMean w))

/-- The paper quantity clusterVariance, expressed using finite sums and ordinary real arithmetic. -/
def clusterVariance {M : ℕ} (v : Fin M → ℝ) : ℝ :=
  clusterMean (fun j => (v j - clusterMean v)^2)

/-- The paper quantity differenced, expressed using finite sums and ordinary real arithmetic. -/
def differenced {M : ℕ} (v size : Fin M → ℝ) (k : ℝ) : Fin M → ℝ :=
  fun j => v j - k * (size j - clusterMean size)

/-- The paper quantity rajPotential, expressed using finite sums and ordinary real arithmetic. -/
def rajPotential (P : ClusterPopulation) (treatment : Bool) (k : ℝ) : Fin P.M → ℝ :=
  differenced (if treatment then P.y1 else P.y0) (fun j => (P.n j : ℝ)) k

/-- The paper quantity rajTotal, expressed using finite sums and ordinary real arithmetic. -/
def rajTotal (P : ClusterPopulation) (treatment : Bool) (k : ℝ)
    (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ) / (if treatment then P.mt else controlCount P) *
    armSum P treatment (rajPotential P treatment k) s

/-- The paper quantity desRaj, expressed using finite sums and ordinary real arithmetic. -/
def desRaj (P : ClusterPopulation) (k : ℝ) (s : Finset (Fin P.M)) : ℝ :=
  (rajTotal P true k s - rajTotal P false k s) / populationSize P

/-- The paper quantity observedSlope, expressed using finite sums and ordinary real arithmetic. -/
def observedSlope (P : ClusterPopulation) (s : Finset (Fin P.M)) : ℝ :=
  clusterCovariance (fun j => (P.n j : ℝ)) (observedTotal P s) /
    clusterVariance (fun j => (P.n j : ℝ))

/-- The paper quantity affinePopulation, expressed using finite sums and ordinary real arithmetic. -/
abbrev affinePopulation (P : ClusterPopulation) (b0 b1 : ℝ) : ClusterPopulation :=
  {P with y0 := fun j => (P.n j : ℝ) * b0 + b1 * P.y0 j,
          y1 := fun j => (P.n j : ℝ) * b0 + b1 * P.y1 j}

/-- The paper quantity rajCovariatePotential, expressed using finite sums and ordinary real arithmetic. -/
def rajCovariatePotential (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ)
    (a : Bool) : Fin P.M → ℝ := fun j =>
  rajPotential P a ks j - ∑ cov, ka cov * (X cov j - clusterMean (X cov))

/-- The paper quantity rajCovariateTotal, expressed using finite sums and ordinary real arithmetic. -/
def rajCovariateTotal (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ)
    (a : Bool) (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ) / (if a then P.mt else controlCount P) *
    armSum P a (rajCovariatePotential P X ks ka a) s

/-- The paper quantity desRajCovariates, expressed using finite sums and ordinary real arithmetic. -/
def desRajCovariates (P : ClusterPopulation) {A : ℕ}
    (X : Fin A → Fin P.M → ℝ) (ks : ℝ) (ka : Fin A → ℝ)
    (s : Finset (Fin P.M)) : ℝ :=
  (rajCovariateTotal P X ks ka true s - rajCovariateTotal P X ks ka false s) / populationSize P

/-- The paper quantity htVarianceFormula, expressed using finite sums and ordinary real arithmetic. -/
def htVarianceFormula (P : ClusterPopulation) : ℝ :=
  (P.M : ℝ)^2 / (populationSize P : ℝ)^2 *
    ((P.M : ℝ) / ((P.M : ℝ) - 1) *
      (clusterVariance P.y0 / controlCount P + clusterVariance P.y1 / P.mt) +
     1 / ((P.M : ℝ) - 1) *
      (2 * clusterCovariance P.y0 P.y1 - clusterVariance P.y0 - clusterVariance P.y1))

/-- The paper quantity approximateVariance, expressed using finite sums and ordinary real arithmetic. -/
def approximateVariance (P : ClusterPopulation) (v0 v1 : Fin P.M → ℝ) : ℝ :=
  (P.M : ℝ)^3 / ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1)) *
    (clusterVariance v0 / controlCount P + clusterVariance v1 / P.mt)

/-- The paper quantity combinedVarianceEstimator, expressed using finite sums and ordinary real arithmetic. -/
def combinedVarianceEstimator (P : ClusterPopulation) (v0 v1 : Fin P.M → ℝ)
    (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ)^2 / (populationSize P : ℝ)^2 *
    ((∑ j ∈ controls s, (v0 j - armSum P false v0 s / controlCount P)^2) /
      ((controlCount P : ℝ) * ((controlCount P : ℝ) - 1)) +
     (∑ j ∈ s, (v1 j - armSum P true v1 s / P.mt)^2) /
      ((P.mt : ℝ) * ((P.mt : ℝ) - 1)))

/-- The paper quantity sharpNullVarianceEstimator, expressed using finite sums and ordinary real arithmetic. -/
def sharpNullVarianceEstimator (P : ClusterPopulation) (s : Finset (Fin P.M)) : ℝ :=
  (P.M : ℝ)^4 * clusterVariance (observedTotal P s) /
    ((populationSize P : ℝ)^2 * ((P.M : ℝ) - 1) * controlCount P * P.mt)

/-- Individual potential outcomes together with their aggregation certificates. -/
structure IndividualPotentialOutcomes (P : ClusterPopulation) where
  Y0 : (j : Fin P.M) → Fin (P.n j) → ℝ
  Y1 : (j : Fin P.M) → Fin (P.n j) → ℝ
  total0 : ∀ j, clusterTotal (Y0 j) = P.y0 j
  total1 : ∀ j, clusterTotal (Y1 j) = P.y1 j

/-- The paper quantity IndividualSharpNull, expressed using finite sums and ordinary real arithmetic. -/
def IndividualSharpNull {P : ClusterPopulation} (I : IndividualPotentialOutcomes P) : Prop :=
  ∀ j i, I.Y0 j i = I.Y1 j i

/-- The paper quantity observedIndividual, expressed using finite sums and ordinary real arithmetic. -/
def observedIndividual {P : ClusterPopulation} (I : IndividualPotentialOutcomes P)
    (s : Finset (Fin P.M)) (j : Fin P.M) (i : Fin (P.n j)) : ℝ :=
  if j ∈ s then I.Y1 j i else I.Y0 j i

/-- The paper quantity armOptimalCoefficient, expressed using finite sums and ordinary real arithmetic. -/
def armOptimalCoefficient (P : ClusterPopulation) (a : Bool) : ℝ :=
  clusterCovariance (fun j => (P.n j : ℝ)) (if a then P.y1 else P.y0) /
    clusterVariance (fun j => (P.n j : ℝ))

/-- The paper quantity optimalCoefficient, expressed using finite sums and ordinary real arithmetic. -/
def optimalCoefficient (P : ClusterPopulation) : ℝ :=
  (P.mt : ℝ) / P.M * armOptimalCoefficient P false +
    (controlCount P : ℝ) / P.M * armOptimalCoefficient P true

/-- The paper quantity BlockAssignments, expressed using finite sums and ordinary real arithmetic. -/
abbrev BlockAssignments {B : ℕ} (P : Fin B → ClusterPopulation) :=
  (b : Fin B) → {s : Finset (Fin (P b).M) // s ∈ assignments (P b)}

/-- The paper quantity blockLaw, expressed using finite sums and ordinary real arithmetic. -/
def blockLaw {B : ℕ} (P : Fin B → ClusterPopulation) : FiniteLaw (BlockAssignments P) :=
  uniformLaw Finset.univ ⟨(fun b =>
    ⟨(assignments_nonempty (P b)).choose, (assignments_nonempty (P b)).choose_spec⟩),
    Finset.mem_univ _⟩

/-- The paper quantity blockedSize, expressed using finite sums and ordinary real arithmetic. -/
def blockedSize {B : ℕ} (P : Fin B → ClusterPopulation) : ℕ :=
  ∑ b, populationSize (P b)

/-- The paper quantity blockedHT, expressed using finite sums and ordinary real arithmetic. -/
def blockedHT {B : ℕ} (P : Fin B → ClusterPopulation) (s : BlockAssignments P) : ℝ :=
  ∑ b, (populationSize (P b) : ℝ) / blockedSize P * horvitzThompson (P b) (s b).val

/-- The paper quantity blockedATE, expressed using finite sums and ordinary real arithmetic. -/
def blockedATE {B : ℕ} (P : Fin B → ClusterPopulation) : ℝ :=
  (∑ b, ((∑ j, (P b).y1 j) - ∑ j, (P b).y0 j)) / blockedSize P

/-- The paper quantity CopyAssignments, expressed using finite sums and ordinary real arithmetic. -/
abbrev CopyAssignments (P : ClusterPopulation) (h : ℕ) :=
  Fin h → {s : Finset (Fin P.M) // s ∈ assignments P}

/-- The paper quantity copyLaw, expressed using finite sums and ordinary real arithmetic. -/
def copyLaw (P : ClusterPopulation) (h : ℕ) : FiniteLaw (CopyAssignments P h) :=
  uniformLaw Finset.univ ⟨(fun _ =>
    ⟨(assignments_nonempty P).choose, (assignments_nonempty P).choose_spec⟩),
    Finset.mem_univ _⟩

/-- The paper quantity copiedDifferenceInMeans, expressed using finite sums and ordinary real arithmetic. -/
def copiedDifferenceInMeans (P : ClusterPopulation) (h : ℕ)
    (s : CopyAssignments P h) : ℝ :=
  (∑ r, armSum P true P.y1 (s r).val) / (∑ r, armSize P true (s r).val) -
  (∑ r, armSum P false P.y0 (s r).val) / (∑ r, armSize P false (s r).val)

/-- The paper quantity copyAverage, expressed using finite sums and ordinary real arithmetic. -/
def copyAverage (P : ClusterPopulation) (a : Bool) (v : Fin P.M → ℝ) (h : ℕ)
    (s : CopyAssignments P h) : ℝ := (∑ r, armSum P a v (s r).val) / h

end
end SAP.P020
