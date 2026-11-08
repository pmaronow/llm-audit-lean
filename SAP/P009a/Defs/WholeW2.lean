import Mathlib
import SAP.P009a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a

open Filter MeasureTheory
open scoped BigOperators Topology Classical

noncomputable section

/-- Assumption 1 for one experiment, allowing the bounded-moment endpoint. -/
def WholeRegularity {n : ℕ} (E : FiniteExperiment n) (k : ℝ)
    (q s : ExtendedOrder) : Prop :=
  0 < k ∧ 2 ≤ q ∧ 1 ≤ s ∧
  (∀ i, k⁻¹ ≤ armProbability E i true ∧ armProbability E i true ≤ 1-k⁻¹) ∧
  (∀ i, OrderBound E.design (E.outcome i) k q) ∧
  (∀ i b, OrderBound E.design (potentialResponse E i b) k s)

/-- The external mixing exponent, with its limiting value at infinite order. -/
def wholeExternalExponent (q : ExtendedOrder) : ℝ :=
  if q = ⊤ then 1 else (q.untopD 0-2)/q.untopD 0

def absoluteArmCovarianceSum {n : ℕ} (E : FiniteExperiment n) (b : Bool) (a : ℕ) : ℝ :=
  ∑ i, ∑ j, |covariance E.design (armResponse E b a i) (armResponse E b a j)|

def dependentArmCovarianceSum {n : ℕ} (E : FiniteExperiment n) (b : Bool) (a : ℕ) : ℝ :=
  ∑ i, ∑ j, dependenceIndicator E i j *
    |covariance E.design (armResponse E b a i) (armResponse E b a j)|

def externalMixingSum {n : ℕ} (E : FiniteExperiment n) (θ : ℝ) : ℝ :=
  ∑ i, ∑ j, (1-dependenceIndicator E i j) * mixingPower
    (mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j)) θ

def squareArmTotal {n : ℕ} (E : FiniteExperiment n) (b : Bool) (z : TreatmentVector n) : ℝ :=
  ∑ i, armResponse E b 2 i z / armProbability E i b ^ 2

def assignmentMixingSum {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  ∑ i, ∑ j, mixingCoefficient E.design (fun z => z i) (fun z => z j)

def offAssignmentMixingSum {n : ℕ} (E : FiniteExperiment n) : ℝ :=
  ∑ i, ∑ j, (1-dependenceIndicator E i j) *
    mixingCoefficient E.design (fun z => z i) (fun z => z j)

/-- The corrected A9 and A22 chains, retaining each intermediate comparison. -/
def WholeMeanChains {n : ℕ} (E : FiniteExperiment n) (k θ : ℝ) (b : Bool) : Prop :=
  variance E.design (estimatedArmMean E b) ≤ k^2/(n:ℝ)^2 * absoluteArmCovarianceSum E b 1 ∧
  (ProductDesign E →
    (∀ i j, (1-dependenceIndicator E i j) *
      covariance E.design (armResponse E b 1 i) (armResponse E b 1 j) = 0) ∧
    absoluteArmCovarianceSum E b 1 = dependentArmCovarianceSum E b 1 ∧
    k^2/(n:ℝ)^2 * dependentArmCovarianceSum E b 1 ≤ k^4/(n:ℝ)*averageDependence E) ∧
  (∀ i j, dependenceIndicator E i j = 0 →
    |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)| ≤
      10*k^2*mixingPower
        (mixingCoefficient E.design (relevantTreatments E i) (relevantTreatments E j)) θ) ∧
  (∀ i j, dependenceIndicator E i j = 1 →
    |covariance E.design (armResponse E b 1 i) (armResponse E b 1 j)| ≤ k^2) ∧
  k^2/(n:ℝ)^2 * absoluteArmCovarianceSum E b 1 ≤
    k^4/(n:ℝ)*averageDependence E + 10*k^4/(n:ℝ)^2*externalMixingSum E θ ∧
  k^4/(n:ℝ)*averageDependence E + 10*k^4/(n:ℝ)^2*externalMixingSum E θ =
    k^4/(n:ℝ)*averageDependence E + 10*k^4/(n:ℝ)*externalMixing E θ

/-- The corrected A23 chain. Every sum here includes diagonal pairs. -/
def WholeCountChains {n : ℕ} (E : FiniteExperiment n) (k θ : ℝ) (b : Bool) : Prop :=
  (∀ i j, |covariance E.design (fun z => if z i = b then 1 else 0)
    (fun z => if z j = b then 1 else 0)| ≤
      mixingCoefficient E.design (fun z => z i) (fun z => z j)) ∧
  variance E.design (fun z => estimatedArmSize E b z / n) ≤ k^2/(n:ℝ)^2 *
    (∑ i, ∑ j, |covariance E.design (fun z => if z i = b then 1 else 0)
      (fun z => if z j = b then 1 else 0)|) ∧
  k^2/(n:ℝ)^2 * (∑ i, ∑ j, |covariance E.design (fun z => if z i = b then 1 else 0)
    (fun z => if z j = b then 1 else 0)|) ≤ k^2/(n:ℝ)^2*assignmentMixingSum E ∧
  k^2/(n:ℝ)^2*assignmentMixingSum E ≤
    k^2/(n:ℝ)*averageDependence E + k^2/(n:ℝ)^2*offAssignmentMixingSum E ∧
  k^2/(n:ℝ)*averageDependence E + k^2/(n:ℝ)^2*offAssignmentMixingSum E ≤
    k^2/(n:ℝ)*averageDependence E + k^2/(n:ℝ)*externalMixing E θ

/-- The corrected A25 chain, including the two-arm variance comparison. -/
def WholeSquareChains {n : ℕ} (E : FiniteExperiment n) (k : ℝ) : Prop :=
  (∀ b,
    variance E.design (squareArmTotal E b) ≤ k^4*absoluteArmCovarianceSum E b 2 ∧
    (∀ i j, (1-dependenceIndicator E i j) *
      covariance E.design (armResponse E b 2 i) (armResponse E b 2 j) = 0) ∧
    absoluteArmCovarianceSum E b 2 = dependentArmCovarianceSum E b 2 ∧
    k^4*dependentArmCovarianceSum E b 2 ≤ k^8*(n:ℝ)*averageDependence E) ∧
  variance E.design (fun z => (n:ℝ)*bernoulliVarianceEstimate E z) ≤
    2/(n:ℝ)^2 * (∑ b : Bool, variance E.design (squareArmTotal E b)) ∧
  2/(n:ℝ)^2 * (∑ b : Bool, variance E.design (squareArmTotal E b)) ≤
    4*k^8*averageDependence E/(n:ℝ)

/--
P009-T4. Supplement A, pp. 3, 8, 22–23, 25: Lemma A3 and corrected variance chains.
For square-integrable real random variables on any probability space, the weighted variance is
the double covariance sum and is bounded by K squared times the absolute covariance sum.
Assumption 1B alone gives the absolute power-covariance bound. Under Assumption 1, every
intermediate inequality and equality of A9, A22, A23 and A25 holds, including cancellation,
all diagonal mixing terms, and the final two-arm variance comparison. Moment orders may be
finite or infinite; zero mixing to the zeroth power means zero. The chains hold for every
admissible order, hence also for the maximum in Definition 9 whenever that maximum exists.
-/
def T4WholeStatement : Prop :=
  (∀ {Ω U : Type*} [MeasurableSpace Ω] [Fintype U]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : U → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (w : U → ℝ) (K : ℝ)
    (hw : ∀ i, 0 < w i ∧ w i ≤ K),
    ProbabilityTheory.variance (fun ω => ∑ i, w i * X i ω) P =
      ∑ i, ∑ j, w i*w j*ProbabilityTheory.covariance (X i) (X j) P ∧
    ProbabilityTheory.variance (fun ω => ∑ i, w i * X i ω) P ≤
      K^2*(∑ i, ∑ j, |ProbabilityTheory.covariance (X i) (X j) P|)) ∧
  (∀ {n : ℕ} (E : FiniteExperiment n) (k : ℝ) (q : ExtendedOrder)
    (hk : 0 < k) (a : ℕ) (ha : a = 1 ∨ a = 2)
    (hqa : ((2*a : ℕ) : ExtendedOrder) ≤ q)
    (hMoment : ∀ i, OrderBound E.design (E.outcome i) k q) (i j : Fin n) (b : Bool),
    |covariance E.design (armResponse E b a i) (armResponse E b a j)| ≤ k^(2*a)) ∧
  (∀ {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) (k : ℝ) (q s : ExtendedOrder),
    WholeRegularity E k q s →
    (∀ b, WholeMeanChains E k (wholeExternalExponent q) b ∧
      WholeCountChains E k (wholeExternalExponent q) b) ∧
    (4 ≤ q → ProductDesign E → WholeSquareChains E k))

/--
P009-T5. Supplement A, pp. 6–7, proof of Proposition 1.
The printed claim is false: a regular fair Bernoulli interference family has density tending
to the positive limsup one quarter, yet attains that threshold at only the four positive
sizes 1, 2, 3 and 4. Its full interference and dependence graphs, exact density, parity gaps,
and failure of Assumption 2 are stated. This refutes the limsup selection step.
-/
def T5WholeStatement : Prop :=
  T5Statement ∧
  (∀ n (hn : 0 < n), let E := clusterPopulation n hn
    (∀ i j, Affects E i j ↔ i = j ∨ (i.val = 0 ∧ j.val < clusterSize n)) ∧
    (∀ i j, SharesCause E i j ↔ i = j ∨ (i.val < clusterSize n ∧ j.val < clusterSize n)) ∧
    averageDependence E/(n:ℝ) = clusterDensity n) ∧
  clusterDensity 1 = 1 ∧ clusterDensity 2 = 1/2 ∧
  clusterDensity 3 = 1/3 ∧ clusterDensity 4 = 1/4 ∧
  (∀ m, 3 ≤ m → 0 < 1/4-clusterDensity (2*m)) ∧
  (∀ m, 2 ≤ m → 0 < 1/4-clusterDensity (2*m+1)) ∧
  Filter.limsup (fun t => averageDependence (clusterSequence.experiment t)/sampleSize clusterSequence t)
    atTop = 1/4 ∧
  (0:ℝ) < 1/4 ∧ ¬ SparseDependence clusterSequence ∧
  Set.Finite {t | (1/4 : ℝ)*sampleSize clusterSequence t ≤ averageDependence (clusterSequence.experiment t)}

/-- A growing square-size star family used as a witness to the false dominance implication. -/
def wholeStarSequence : ExperimentSequence where
  N := fun t => (t+2)*(t+2)
  positive := by intro t; positivity
  grows := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with t ht
    nlinarith
  experiment := fun t => fairPopulation ((t+2)*(t+2)) (starPopulationResponse (t+2) (by omega))

/--
P009-T11. Section 6.1, p. 691, discussion of Proposition 7.
Under uniform q>=4 regularity, independent Bernoulli assignment and restricted interference,
d_AVG/C1 tending to infinity need not make B2 eventually largest in absolute value among
tau_MSQ/d_AVG, B1 and B2.
This refutes only that reading of the printed dominance guidance.
Restricted: Only the failure of guaranteed eventual largest-in-absolute-value dominance is asserted,
for sequences with uniform q>=4 regularity, independent Bernoulli assignment, restricted
interference, and d_AVG/C1 tending to infinity. The specified square-size m-block fair-Bernoulli
witness and its full outcome schedule are not stated. Omitted witness clauses are: the full-cube
[0,2] bounds and regularity at every moment order; the exact interference and dependence graphs,
C1=2, d_AVG=m=sqrt(n), the ratio m/2 and its divergence, and Assumption 2 for that family; the
expected direct effects all equal to 1, tau_MSQ=1 and tau_MSQ/d_AVG=1/m; the xi and weighted-xi
formulas, reciprocal products and B1=2/m^2>0; the arm-independent conditional covariances, their
alternating-sum cancellations and B2=0; the comparison 0=B2<B1<=tau_MSQ/d_AVG with equality of the
last two terms exactly at m=2; and the extension to every n>=4 with its floor-defined blocks,
isolated units, and exact C1, d_AVG, tau_MSQ, B1 and B2 formulas. The printed big-O bounds and
Proposition 7 are not refuted.
-/
def T11WholeStatement : Prop :=
  ¬ (∀ (S : ExperimentSequence) (k q s : ℝ),
    SequenceRegularity S k q s → 4 ≤ q →
    (∀ t, ProductDesign (S.experiment t)) → SparseDependence S →
    Tendsto (fun t => averageDependence (S.experiment t)/averageOutgoing (S.experiment t)) atTop atTop →
    ∀ᶠ t in atTop,
      |meanSquaredEffect (S.experiment t)/averageDependence (S.experiment t)| ≤
        |indirectBias (S.experiment t)| ∧
      |directBias (S.experiment t)| ≤ |indirectBias (S.experiment t)|)

/-- The three conclusions when B2 dominates in relative magnitude. -/
def WholeBiasDominance (S : ExperimentSequence) : Prop :=
  Tendsto (fun t => 1/(averageDependence (S.experiment t)*|indirectBias (S.experiment t)|))
    atTop (nhds 0) ∧
  vanishingRelativeTo (fun t => meanSquaredEffect (S.experiment t)/averageDependence (S.experiment t))
    (fun t => |indirectBias (S.experiment t)|) ∧
  vanishingRelativeTo (fun t => directBias (S.experiment t)) (fun t => |indirectBias (S.experiment t)|)

/--
P009-T12. Section 6.1, p. 691, corrected discussion of Proposition 7.
The finite bounds on B1, B2 and the mean squared effect imply vanishing of the first two
normalized terms when average dependence dominates average outgoing interference, while B2
stays bounded. No positive lower bound on B2 follows: a regular restricted-interference
sequence has B2 zero and both other terms positive. The additional ratio condition implies
relative dominance and the reciprocal limit on its nonzero-denominator domain; an eventual
positive lower bound on the magnitude of B2 suffices for that condition.
-/
def T12WholeStatement : Prop :=
  (∀ {n : ℕ} (hn : 0 < n) (E : FiniteExperiment n) (k q s : ℝ),
    Regularity E k q s → 4 ≤ q → ProductDesign E →
    |directBias E| ≤ 12*k^4*(averageOutgoing E-1)/averageDependence E ∧
    |indirectBias E| ≤ 4*k^4*(averageDependence E-1)/averageDependence E ∧
    4*k^4*(averageDependence E-1)/averageDependence E ≤ 4*k^4 ∧
    0 ≤ meanSquaredEffect E ∧ meanSquaredEffect E ≤ 4*k^4) ∧
  (∀ (S : ExperimentSequence) (k q s : ℝ),
    SequenceRegularity S k q s → 4 ≤ q → (∀ t, ProductDesign (S.experiment t)) →
    Tendsto (fun t => averageDependence (S.experiment t)/averageOutgoing (S.experiment t)) atTop atTop →
    Tendsto (fun t => meanSquaredEffect (S.experiment t)/averageDependence (S.experiment t)) atTop (nhds 0) ∧
    Tendsto (fun t => directBias (S.experiment t)) atTop (nhds 0) ∧
    boundedRelativeTo (fun t => indirectBias (S.experiment t)) (fun _ => 1) ∧
    ((∀ᶠ t in atTop, indirectBias (S.experiment t) ≠ 0) →
      Tendsto (fun t => averageOutgoing (S.experiment t)/
        (averageDependence (S.experiment t)*|indirectBias (S.experiment t)|)) atTop (nhds 0) →
      WholeBiasDominance S) ∧
    (∀ c : ℝ, 0 < c → (∀ᶠ t in atTop, c ≤ |indirectBias (S.experiment t)|) →
      (∀ᶠ t in atTop, indirectBias (S.experiment t) ≠ 0) ∧
      Tendsto (fun t => averageOutgoing (S.experiment t)/
        (averageDependence (S.experiment t)*|indirectBias (S.experiment t)|)) atTop (nhds 0) ∧
      WholeBiasDominance S)) ∧
  (∃ S : ExperimentSequence, SequenceRegularity S 2 4 1 ∧
    (∀ t, ProductDesign (S.experiment t)) ∧ SparseDependence S ∧
    Tendsto (fun t => averageDependence (S.experiment t)/averageOutgoing (S.experiment t)) atTop atTop ∧
    ∀ t, indirectBias (S.experiment t) = 0 ∧ 0 < directBias (S.experiment t) ∧
      0 < meanSquaredEffect (S.experiment t)/averageDependence (S.experiment t))

/--
P009-T13. Section 6.1, p. 691, discussion of direct spillovers.
The printed claim is false: in the stated fair three-unit experiment all absolute outcomes
are at most one and regularity holds at every moment order. Changing the first treatment
changes the second outcome by 2 z3 minus 1, always nonzero. Both expected spillovers and the
weighted expected spillover nevertheless vanish, refuting the direct-interference implication.
-/
def T13WholeStatement : Prop :=
  ProductDesign cancellingPopulation ∧
  (∀ z, cancellingPopulation.design.mass z = 1/8) ∧
  (∀ i z, cancellingPopulation.outcome i z =
    if i = 1 then treatmentValue (z 0)*(2*treatmentValue (z 2)-1) else 0) ∧
  (∀ i z, |cancellingPopulation.outcome i z| ≤ 1) ∧
  (∀ q s : ℝ, 2 ≤ q → 1 ≤ s → Regularity cancellingPopulation 2 q s) ∧
  WholeRegularity cancellingPopulation 2 ⊤ ⊤ ∧
  (∀ (a : Bool) (z : TreatmentVector 3),
    cancellingPopulation.outcome 1 (Function.update (Function.update z 1 a) 0 true) -
      cancellingPopulation.outcome 1 (Function.update (Function.update z 1 a) 0 false) =
        2*treatmentValue (z 2)-1 ∧
    (2*treatmentValue (z 2)-1 = -1 ∨ 2*treatmentValue (z 2)-1 = 1) ∧
    2*treatmentValue (z 2)-1 ≠ 0) ∧
  Affects cancellingPopulation 0 1 ∧
  expectedSpillover cancellingPopulation 1 0 false = 0 ∧
  expectedSpillover cancellingPopulation 1 0 true = 0 ∧
  weightedSpillover cancellingPopulation 1 0 = 0 ∧
  ¬ (∀ {n : ℕ} (E : FiniteExperiment n), ProductDesign E → Regularity E 2 4 1 →
    ∀ i j, i ≠ j → Affects E i j → weightedSpillover E j i ≠ 0)

end
end SAP.P009a
