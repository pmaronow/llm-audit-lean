import Mathlib
import SAP.P009a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a

open Filter
open scoped BigOperators Topology Classical

noncomputable section

/-- Assumption 1A alone, without assumptions about the reference outcomes. -/
def AssignmentBounds {n : ℕ} (E : FiniteExperiment n) (k : ℝ) : Prop :=
  0 < k ∧ ∀ i, k⁻¹ ≤ armProbability E i true ∧
    armProbability E i true ≤ 1 - k⁻¹

def interferenceDensity (S : ExperimentSequence) (t : ℕ) : ℝ :=
  averageDependence (S.experiment t) / sampleSize S t

def interferenceDensityLimsup (S : ExperimentSequence) : ℝ :=
  Filter.limsup (interferenceDensity S) atTop

/-- The finite construction in the proof of Proposition 1. -/
def limsupPopulation {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n)
    (L : ℝ) : FiniteExperiment n :=
  { E with outcome := subsequenceResponse hn E ⌈Real.sqrt L * (n : ℝ)⌉₊ }

/-- Keep the original designs, construct outcomes at the selected indices, and use zero elsewhere. -/
def selectedLimsupSequence (S : ExperimentSequence) (L c : ℝ) : ExperimentSequence :=
  { S with experiment := fun t =>
      if c ≤ interferenceDensity S t then
        limsupPopulation (S.positive t) (S.experiment t) L
      else { S.experiment t with outcome := fun _ _ => 0 } }

/-- Exact finite conclusions; all expectations are sums over a finite assignment cube. -/
def LimsupFiniteFacts {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n)
    (k L : ℝ) : Prop :=
  let M := ⌈Real.sqrt L * (n : ℝ)⌉₊
  let F := limsupPopulation hn E L
  averageDependence F = (M : ℝ)^2 / n + ((n : ℝ) - M) / n ∧
  L * n ≤ averageDependence F ∧
  (∀ i z, |F.outcome i z| ≤ 1 / Real.sqrt L) ∧
  expectedATE F = armProbability E ⟨0, hn⟩ true ∧
  (∀ z, htEstimate F z = treatmentValue (z ⟨0, hn⟩) ∧
    |htEstimate F z - expectedATE F| =
      |treatmentValue (z ⟨0, hn⟩) - armProbability E ⟨0, hn⟩ true| ∧
    k⁻¹ ≤ |htEstimate F z - expectedATE F|)

/--
P009-T6. Supplement A, pp. 6–7, proof of Proposition 1.
Every threshold strictly below a positive finite limsup is met infinitely often; the threshold
at the limsup need not be met. Failure of restricted interference supplies a limsup in (0,1].
Retaining the designs and using the displayed outcomes with lambda equal to that limsup on the
selected indices, and zero elsewhere, gives uniform regularity and an HT error bounded away
from zero with probability one infinitely often. Consequently HT is inconsistent for EATE.
-/
def T6WholeStatement : Prop :=
  (∀ (a : ℕ → ℝ) (L c : ℝ), FiniteLimsup a L → 0 < c → c < L →
    Set.Infinite {t | c ≤ a t}) ∧
  (∃ a : ℕ → ℝ, FiniteLimsup a 1 ∧ ∀ t, a t < 1) ∧
  (∀ {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) (k L : ℝ),
    AssignmentBounds E k → 0 < L ∧ L ≤ 1 → LimsupFiniteFacts hn E k L) ∧
  (∀ (S : ExperimentSequence) (k : ℝ),
    (∀ t, AssignmentBounds (S.experiment t) k) → ¬ SparseDependence S →
    let L := interferenceDensityLimsup S
    FiniteLimsup (interferenceDensity S) L ∧ 0 < L ∧ L ≤ 1 ∧
    ∀ c, 0 < c → c < L →
      let H := {t | c ≤ interferenceDensity S t}
      let F := selectedLimsupSequence S L c
      Set.Infinite H ∧
      (∀ t, (F.experiment t).design = (S.experiment t).design) ∧
      (∀ t i z, |(F.experiment t).outcome i z| ≤ 1 / Real.sqrt L) ∧
      (∀ q s : ℝ, 2 ≤ q → 1 ≤ s → ∃ K, 0 < K ∧ SequenceRegularity F K q s) ∧
      (∀ t ∈ H, LimsupFiniteFacts (S.positive t) (S.experiment t) k L ∧
        F.experiment t = limsupPopulation (S.positive t) (S.experiment t) L) ∧
      (∀ t, t ∉ H → (∀ i z, (F.experiment t).outcome i z = 0) ∧
        expectedATE (F.experiment t) = 0 ∧ ∀ z, htEstimate (F.experiment t) z = 0) ∧
      Set.Infinite {t | probability (F.experiment t).design
        (fun z => 1 / (2*k) < |htEstimate (F.experiment t) z -
          expectedATE (F.experiment t)|) = 1} ∧
      ¬ ConvergesInProbability F
        (fun t z => htEstimate (F.experiment t) z - expectedATE (F.experiment t)))

/-- True-standard-deviation normalization. Used only on positive-variance indices;
the T8 statement permits arbitrary values at the finitely many remaining indices. -/
def standardizedHT {n : ℕ} (E : FiniteExperiment n) (z : TreatmentVector n) : ℝ :=
  (htEstimate E z - expectedATE E) / Real.sqrt (variance E.design (htEstimate E))

/-- The second counterexample has a constant, nonzero EATE. -/
def nonshrinkingPopulation (n : ℕ) : FiniteExperiment n :=
  fairPopulation n (fun i z =>
    if i.val = 0 then treatmentValue (z i) else treatmentValue (z i) - 1/2)

def nonshrinkingSequence : ExperimentSequence :=
  { sparseSequence with experiment := fun t => nonshrinkingPopulation (t+1) }

def finiteCDF {Ω : Type*} [Fintype Ω] (P : FiniteDistribution Ω)
    (X : Ω → ℝ) (x : ℝ) : ℝ := probability P (fun ω => X ω ≤ x)

/-- The ordinary continuous CDF domain, with explicit bounds to certify the finite supremum. -/
def ContinuousDistributionFunction (G : ℝ → ℝ) : Prop :=
  Continuous G ∧ Monotone G ∧ (∀ x, 0 ≤ G x ∧ G x ≤ 1) ∧
    Tendsto G atBot (nhds 0) ∧ Tendsto G atTop (nhds 1)

def kolmogorovDistance (F G : ℝ → ℝ) : ℝ :=
  sSup (Set.range (fun x => |F x - G x|))

def rademacherCDF (x : ℝ) : ℝ :=
  if x < -1 then 0 else if x < 1 then 1/2 else 1

/--
P009-T7. Section 6.3, p. 693.
The printed normal-approximation sufficiency fails: both explicit fair Bernoulli families
have all finite regularity orders and diagonal interference dependence, but their standardized
HT statistic is exactly 2 Z1 - 1. Its distance from every continuous distribution function is
at least one quarter. The first family's EATE is 1/n; the second family's EATE is one.
Both have true variance 1/n squared and fail standard normal convergence.
-/
def T7WholeStatement : Prop :=
  T7Statement ∧
  (∀ q s : ℝ, 2 ≤ q → 1 ≤ s →
    SequenceRegularity sparseSequence 2 q s ∧
    SequenceRegularity nonshrinkingSequence 2 q s) ∧
  (∀ t, let E := sparseSequence.experiment t
    let n := sampleSize sparseSequence t
    (∀ i z, |E.outcome i z| ≤ 1) ∧
    (∀ i j, interferenceIndicator E i j = if i = j then 1 else 0) ∧
    (∀ i j, dependenceIndicator E i j = if i = j then 1 else 0) ∧
    expectedATE E = 1/n ∧ expectation E.design (htEstimate E) = 1/n ∧
    variance E.design (htEstimate E) = 1/n^2 ∧
    (∀ z, htEstimate E z = 2*treatmentValue (z ⟨0, sparseSequence.positive t⟩)/n ∧
      standardizedHT E z = 2*treatmentValue (z ⟨0, sparseSequence.positive t⟩)-1)) ∧
  (∀ t, let E := nonshrinkingSequence.experiment t
    let n := sampleSize nonshrinkingSequence t
    ProductDesign E ∧ NoSpillovers E ∧
    (∀ i z, |E.outcome i z| ≤ 1) ∧
    (∀ i j, interferenceIndicator E i j = if i = j then 1 else 0) ∧
    (∀ i j, dependenceIndicator E i j = if i = j then 1 else 0) ∧
    averageDependence E = 1 ∧ maximumDependence E = 1 ∧
    expectedATE E = 1 ∧ expectation E.design (htEstimate E) = 1 ∧
    variance E.design (htEstimate E) = 1/n^2 ∧ 0 < variance E.design (htEstimate E) ∧
    (∀ z, htEstimate E z = (n-1+2*treatmentValue (z ⟨0, nonshrinkingSequence.positive t⟩))/n ∧
      standardizedHT E z = 2*treatmentValue (z ⟨0, nonshrinkingSequence.positive t⟩)-1)) ∧
  (∀ S ∈ ({sparseSequence, nonshrinkingSequence} : Set ExperimentSequence),
    (∀ (t : ℕ) (b : Bool), probability (S.experiment t).design
      (fun z => standardizedHT (S.experiment t) z = if b then 1 else -1) = 1/2) ∧
    (∀ t x, finiteCDF (S.experiment t).design (standardizedHT (S.experiment t)) x =
      rademacherCDF x) ∧
    (∀ (G : ℝ → ℝ), ContinuousDistributionFunction G → ∀ t,
      1/4 ≤ kolmogorovDistance
        (finiteCDF (S.experiment t).design (standardizedHT (S.experiment t))) G) ∧
    Tendsto (fun t => sampleSize S t * variance (S.experiment t).design
      (htEstimate (S.experiment t))) atTop (nhds 0) ∧
    ¬ ConvergesInLaw S (fun t => standardizedHT (S.experiment t)) standardNormalCDF)

/--
P009-T8. Section 6.3, p. 693.
Under Assumption 1, Bernoulli assignment, uniformly bounded maximum dependence, and an
eventually positive lower bound on n times the true HT variance, the variance is eventually
positive and HT centered at EATE and scaled by its true standard deviation is asymptotically
standard normal. Any values at the earlier zero-variance indices give the same limit.
Without the variance lower bound the sparse Bernoulli counterexample fails normal convergence.
-/
def T8WholeStatement : Prop :=
  (∀ (S : ExperimentSequence) (k q s : ℝ),
    SequenceRegularity S k q s → (∀ t, ProductDesign (S.experiment t)) →
    (∃ D, ∀ t, maximumDependence (S.experiment t) ≤ D) →
    EventuallyPositiveLowerBound (fun t => sampleSize S t *
      variance (S.experiment t).design (htEstimate (S.experiment t))) →
    (∀ᶠ t in atTop, 0 < variance (S.experiment t).design (htEstimate (S.experiment t))) ∧
    ∀ X : (t : ℕ) → TreatmentVector (S.N t) → ℝ,
      (∀ t, 0 < variance (S.experiment t).design (htEstimate (S.experiment t)) →
        ∀ z, X t z = standardizedHT (S.experiment t) z) →
      ConvergesInLaw S X standardNormalCDF) ∧
  T7Statement

/--
P009-T14. Section 6.1, p. 691, discussion of Proposition 7.
Absence of direct interference forces pointwise and expected spillovers to vanish, and a
nonzero expected weighted spillover implies interference. The converse fails in the explicit
three-unit cancellation design. With no interference all off-diagonal expected spillovers and
B1 vanish, on the positive-size and positive-arm-probability domain of its conditional means.
-/
def T14WholeStatement : Prop := T14Statement

def assignmentCovariance {n : ℕ} (E : FiniteExperiment n) (i j : Fin n) : ℝ :=
  probability E.design (fun z => z i = true ∧ z j = true) -
    armProbability E i true * armProbability E j true

def fullAssignmentSum {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  4/(n : ℝ)^2 * (∑ i, ∑ j, assignmentCovariance E i j)

def offDiagonalMixingSum {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  4/(n : ℝ)^2 * (∑ i, ∑ j, if j = i then 0 else
    mixingCoefficient E.design (fun z => z i) (fun z => z j))

/--
P009-T15. Supplement A, p. 23, proof of Lemma A23, first display.
The printed diagonal-omission bound fails for every positive size in the fair identity-outcome
family. It satisfies regularity and the three asymptotic restrictions. Interference and
dependence are diagonal, the covariance and mixing entries are one quarter on the diagonal
and zero elsewhere, and both average mixing coefficients vanish exactly. The normalized full
sum and arm-size variance equal 1/n, while the off-diagonal mixing sum is zero. At n=4 the
claimed inequality would be one quarter at most zero.
-/
def T15WholeStatement : Prop :=
  T15Statement ∧
  (∀ {n : ℕ}, 0 < n → let E := identityPopulation n
    ProductDesign E ∧ NoSpillovers E ∧
    (∀ q s : ℝ, 2 ≤ q → 1 ≤ s → Regularity E 2 q s) ∧
    (∀ i j, interferenceIndicator E i j = if i = j then 1 else 0) ∧
    (∀ i j, dependenceIndicator E i j = if i = j then 1 else 0) ∧
    averageDependence E = 1 ∧
    (∀ θ : ℝ, externalMixing E θ = 0 ∧ internalMixing E θ = 0) ∧
    (∀ i j, covariance E.design (fun z => treatmentValue (z i))
      (fun z => treatmentValue (z j)) = if i = j then 1/4 else 0) ∧
    (∀ i j, assignmentCovariance E i j = if i = j then 1/4 else 0) ∧
    (∀ i j, mixingCoefficient E.design (fun z => z i) (fun z => z j) =
      if i = j then 1/4 else 0) ∧
    fullAssignmentSum E = 1/(n : ℝ) ∧ offDiagonalMixingSum E = 0 ∧
    ¬ fullAssignmentSum E ≤ offDiagonalMixingSum E ∧
    variance E.design (fun z => estimatedArmSize E true z / n) = 1/(n : ℝ)) ∧
  (fullAssignmentSum (identityPopulation 4) = 1/4 ∧
    offDiagonalMixingSum (identityPopulation 4) = 0 ∧ ¬ (1/4 : ℝ) ≤ 0)

end
end SAP.P009a
