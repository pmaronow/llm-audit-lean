import Mathlib
import SAP.P006a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a
noncomputable section

/-- The ordinary L1 domain of the estimator conditional means, only on the stated class. -/
def EstimatorL1 {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (P : Set (C → ℝ)) : Prop :=
  ∀ π ∈ P, ∀ i, Integrable (fun ω => E.μhat π ω (E.X i ω)) (E.law π)

/-- The deterministic true-baseline implementation of an estimator. -/
def oracleBaseline {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) : Experiment Ω C n :=
  { E with μhat := fun _ _ x => E.μ0 x }

/-- The realized ATO reward. -/
def atoSample {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (π : C → ℝ) (ω : Ω) : ℝ :=
  wATO (fun i => E.T π i ω) (E.observed π ω)

/-- The realized ATT reward. -/
def attSample {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (π : C → ℝ) (ω : Ω) : ℝ :=
  wATT (E.μhat π ω) (fun i => E.X i ω) (fun i => E.T π i ω) (E.observed π ω)

/-- The empty-sample probability, exact objective, and both conditional-mean identities.
The conditional expressions occur only when the treatment probability is positive. -/
def AveragePolicyFacts {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (m π : C → ℝ) (r : Ω → ℝ) : Prop :=
  (E.law π {ω | treatedCount (fun i => E.T π i ω) = 0}).toReal = (1-E.q π)^n ∧
  (E.law π {ω | 0 < treatedCount (fun i => E.T π i ω)}).toReal = 1-(1-E.q π)^n ∧
  (∫ ω, r ω ∂E.law π) = E.averageObjective m π ∧
  E.averageObjective m π =
    (if 0 < E.q π then (1-(1-E.q π)^n)*(E.A m π/E.q π) else 0) ∧
  (0 < E.q π →
    (∀ i, eventMean (E.law π) {ω | E.T π i ω = true}
      (fun ω => m (E.X i ω)) = E.A m π/E.q π) ∧
    eventMean (E.law π) {ω | 0 < treatedCount (fun i => E.T π i ω)} r = E.A m π/E.q π)

/-- The optimal marked mass at fixed treatment mass. Only used for q in [0,1],
where the whole statement certifies a nonempty fiber and an attained finite maximum. -/
def finiteFrontier {K : ℕ} (p m : Fin K → ℝ) (q : ℝ) : ℝ :=
  bestValue {π | π ∈ finitePolicies ∧ finiteMass p π = q} (finiteA p m)

/-- Exact finite-support frontiers and attained maxima, including the scalar maximum over q. -/
def ScalarFrontierFacts {K : ℕ} (n : ℕ) (p m : Fin K → ℝ) : Prop :=
  (∀ q ∈ Set.Icc (0 : ℝ) 1, ∃ π,
    IsBest {π | π ∈ finitePolicies ∧ finiteMass p π = q} (finiteA p m) π) ∧
  (∀ j q, prefixMass p j ≤ q → q ≤ prefixMass p j+p j →
    finiteFrontier p m q = prefixA p m j + m j*(q-prefixMass p j)) ∧
  (∃ q, IsBest (Set.Icc (0 : ℝ) 1)
    (fun q => emptyFactor n q * finiteFrontier p m q) q) ∧
  bestValue finitePolicies (fun π => emptyFactor n (finiteMass p π)*finiteA p m π) =
    bestValue (Set.Icc (0 : ℝ) 1) (fun q => emptyFactor n q*finiteFrontier p m q)

/-- P006-T2; PDF pp. 15-16 (Propositions 6 and 7); PDF pp. 4-5 (Section 3).
The zero-on-empty ATO and conditionally unbiased ATT rewards have exact expectation
h_n(q) A, empty probability (1-q)^n, and conditional means A/q when q>0.
Their best responses maximize this finite-sample objective. On finite support the
fixed-mass frontier is attained by a fractional threshold, and maximizing it over
q gives an attained threshold optimum. Such an optimum can treat a nonmaximal
score. The printed positive-maximizer rule optimizes the population conditional
average; for one unit the corrected objective is A. Oracle and independent
pointwise-unbiased estimators supply the vector condition on its ordinary L1 domain.
-/
def T2WholeStatement : Prop :=
  (∀ {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n), OutcomeStanding E →
    (∀ π, Admissible π → AveragePolicyFacts E E.μ1 π (atoSample E π)) ∧
    (∀ π, IsBest {π | Admissible π} E.expectedATO π ↔
      IsBest {π | Admissible π} (E.averageObjective E.μ1) π) ∧
    (∀ P : Set (C → ℝ), (∀ π ∈ P, Admissible π) → EstimatorL1 E P →
      VectorUnbiased E P →
      (∀ π ∈ P, AveragePolicyFacts E E.τ π (attSample E π)) ∧
      (∀ π, IsBest P E.expectedATT π ↔ IsBest P (E.averageObjective E.τ) π)) ∧
    (EstimatorL1 (oracleBaseline E) {π | Admissible π} ∧
      VectorUnbiased (oracleBaseline E) {π | Admissible π}) ∧
    (∀ P : Set (C → ℝ), (∀ π ∈ P, Admissible π) → EstimatorL1 E P →
      PointwiseUnbiased E P → IndependentEstimator E P → VectorUnbiased E P)) ∧
  (∀ {K : ℕ} (hK : 0 < K) (n : ℕ), 0 < n →
    ∀ p m : Fin K → ℝ, (∀ i, 0 < p i) → (∑ i, p i) = 1 → Antitone m →
    (∀ j q, prefixMass p j ≤ q → q ≤ prefixMass p j+p j →
      thresholdRule p j q ∈ finitePolicies ∧
      finiteMass p (thresholdRule p j q) = q ∧
      finiteA p m (thresholdRule p j q) = prefixA p m j+m j*(q-prefixMass p j) ∧
      ∀ π ∈ finitePolicies, finiteMass p π = q →
        finiteA p m π ≤ prefixA p m j+m j*(q-prefixMass p j)) ∧
    (∃ j q, prefixMass p j ≤ q ∧ q ≤ prefixMass p j+p j ∧
      IsBest finitePolicies (fun π => emptyFactor n (finiteMass p π)*finiteA p m π)
        (thresholdRule p j q)) ∧
    ScalarFrontierFacts n p m ∧
    (if 0 < m ⟨0,hK⟩ then
      IsBest finitePolicies (finiteConditionalAverage p m) (printedAverageRule m) ∧
        finiteConditionalAverage p m (printedAverageRule m) = m ⟨0,hK⟩
    else IsBest finitePolicies (finiteConditionalAverage p m) (fun _ => 0))) ∧
  (IsBest binaryPolicies rewardE001 (17/18,1) ∧
    (∀ π ∈ binaryPolicies, rewardE001 π = rewardE001 (17/18,1) ↔ π = (17/18,1)) ∧
    0 < binaryRule (17/18,1) false ∧ effectE001 false < effectE001 true) ∧
  (∀ n q, 0 < q → emptyFactor n q = (1-(1-q)^n)/q) ∧
  (∀ q A, emptyFactor 1 q*A = A)

/-- The incorrect printed closed form, evaluated on the exact two-type example. -/
def printedRegretE001 : ℝ :=
  ∑ x : Bool, (1/2 : ℝ)*effectE001 x *
    (if 0 < effectE001 x ∧ ¬ ∀ z, effectE001 z ≤ effectE001 x then 1 else 0)

/-- P006-T3; PDF p. 5 (Proposition 2); PDF pp. 17-18 (Appendix B.4).
For every feasible class containing zero, vector-conditionally unbiased ATT has
expected reward h_n(q)V and h_n(q)>=1. Zero has reward and welfare zero.
Every reward best response has nonnegative reward and welfare, hence regret at
most the finite supremum of feasible welfare. An attained welfare maximum gives
the stated maximum formula. Per-policy identities require no maximizers and no
estimator moments outside the feasible class. In the two-type example the actual
regret is 1/40, whereas the printed closed form is 9/20.
-/
def T3WholeStatement : Prop :=
  (∀ {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n), OutcomeStanding E → ∀ P : Set (C → ℝ),
    (∀ π ∈ P, Admissible π) → (fun _ => 0) ∈ P → EstimatorL1 E P →
    VectorUnbiased E P →
    (∀ π ∈ P, E.V π = E.A E.τ π ∧
      E.expectedATT π = emptyFactor n (E.q π)*E.V π ∧ 1 ≤ emptyFactor n (E.q π)) ∧
    E.expectedATT (fun _ => 0) = 0 ∧ E.V (fun _ => 0) = 0 ∧
    (Set.Nonempty (E.V '' P) ∧ BddAbove (E.V '' P)) ∧
    (∀ b, IsBest P E.expectedATT b →
      0 ≤ E.expectedATT b ∧ 0 ≤ E.V b ∧ regret P E.V b ≤ bestValue P E.V ∧
      ∀ s, IsBest P E.V s →
        bestValue P E.V = E.V s ∧ regret P E.V b = E.V s-E.V b)) ∧
  ((∀ π, rewardE001ATT π = rewardE001 π) ∧
    IsBest binaryPolicies rewardE001ATT (17/18,1) ∧
    (∀ π ∈ binaryPolicies, rewardE001ATT π = rewardE001ATT (17/18,1) ↔ π = (17/18,1)) ∧
    regret binaryPolicies (binaryWelfare (1/2) effectE001) (17/18,1) = 1/40 ∧
    printedRegretE001 = 9/20 ∧
    printedRegretE001 ≠ regret binaryPolicies (binaryWelfare (1/2) effectE001) (17/18,1))

/-- A public Boolean population and a constant private covariate. -/
def infoCovariate (i : Fin 2) (ω : Bool × Bool) : Bool × Unit :=
  (if i = 0 then ω.1 else ω.2, ())

/-- Two independent fair Boolean covariates. -/
def infoLaw : Measure (Bool × Bool) :=
  (bernoulliMeasure true false ⟨1/2, by norm_num⟩).prod
    (bernoulliMeasure true false ⟨1/2, by norm_num⟩)

instance infoLaw_isProbabilityMeasure : IsProbabilityMeasure infoLaw := by
  unfold infoLaw
  infer_instance

/-- A bounded data-dependent estimator: its random state is the first public covariate. -/
def infoEstimator (ω : Bool × Bool) (c : Bool × Unit) : ℝ :=
  if c.1 = ω.1 then 1 else -1

/-- P006-T8; PDF p. 7 (Theorem 3); PDF pp. 21-22 (Lemma 2 and Proposition 10).
The printed claim is false: the included general Lemma 2 need not equal n times
a fixed unit's score contribution. With two independent fair Boolean public
covariates, constant private covariates, zero potential outcomes, and treatment
identically one, the bounded estimator 2*1{x=X_1}-1 is pointwise unbiased and
conditionally independent of treatment. Its evaluated means are 1 and 0, so the
actual expected TT reward is -1; the asserted right sides are -2 and 0.
This refutes the general supporting lemma, not the corrected main bound under
its stronger treated-unbiasedness assumption or the independent-auxiliary result.
-/
def T8WholeStatement : Prop :=
  IsProbabilityMeasure infoLaw ∧
  IndepFun Prod.fst Prod.snd infoLaw ∧
  IdentDistrib Prod.fst Prod.snd infoLaw infoLaw ∧
  Admissible (fun _ : Bool × Unit => (1 : ℝ)) ∧
  (∀ i : Fin 2,
    infoLaw[(fun _ => (1 : ℝ)) | MeasurableSpace.comap (infoCovariate i) inferInstance]
      =ᵐ[infoLaw] (fun _ => 1) ∧
    infoLaw[(fun _ => (0 : ℝ)) | MeasurableSpace.comap (infoCovariate i) inferInstance]
      =ᵐ[infoLaw] (fun _ => 0) ∧
    CondIndepFun (MeasurableSpace.comap (infoCovariate i) inferInstance)
      (measurable_of_finite (infoCovariate i)).comap_le (fun _ : Bool × Bool => true)
      (fun ω => infoEstimator ω (infoCovariate i ω)) infoLaw ∧
    CondIndepFun (MeasurableSpace.comap (infoCovariate i) inferInstance)
      (measurable_of_finite (infoCovariate i)).comap_le (fun _ : Bool × Bool => true)
      (fun _ => ((0 : ℝ), (0 : ℝ))) infoLaw) ∧
  (∀ c : Bool × Unit, Integrable (fun ω => infoEstimator ω c) infoLaw ∧
    (∫ ω, infoEstimator ω c ∂infoLaw) = 0) ∧
  (∀ ω c, |infoEstimator ω c| ≤ 1) ∧
  (∀ i : Fin 2, Integrable (fun ω => infoEstimator ω (infoCovariate i ω)) infoLaw ∧
    infoLaw[(fun ω => (1 : ℝ)*infoEstimator ω (infoCovariate i ω)) |
      MeasurableSpace.comap (infoCovariate i) inferInstance] =ᵐ[infoLaw]
    (fun ω => (1 : ℝ)*infoLaw[(fun η => infoEstimator η (infoCovariate i η)) |
      MeasurableSpace.comap (infoCovariate i) inferInstance] ω)) ∧
  (∫ ω, infoEstimator ω (infoCovariate 0 ω) ∂infoLaw) = 1 ∧
  (∫ ω, infoEstimator ω (infoCovariate 1 ω) ∂infoLaw) = 0 ∧
  (∫ ω, wTT (infoEstimator ω) (fun i => infoCovariate i ω)
    (fun _ => true) (fun _ => 0) ∂infoLaw) = -1 ∧
  (∀ i : Fin 2,
    (∫ ω, wTT (infoEstimator ω) (fun j => infoCovariate j ω)
      (fun _ => true) (fun _ => 0) ∂infoLaw) ≠
    2*((∫ _ω : Bool × Bool, (0 : ℝ) ∂infoLaw) -
      ∫ ω, infoEstimator ω (infoCovariate i ω) ∂infoLaw))

/-- One-unit oracle experiment with an independent uniform treatment seed.
All policies are fixed measurable functions into [0,1]; outcomes are 0 and 1. -/
def uniformOracle (ν : Measure ℝ) : Experiment (ℝ × ℝ) ℝ 1 where
  hn := by norm_num
  PX := ν
  μ0 := fun _ => 0
  μ1 := fun _ => 1
  law := fun _ => ν.prod intervalLaw
  X := fun _ ω => ω.1
  Y0 := fun _ _ => 0
  Y1 := fun _ _ => 1
  T := fun π _ ω => decide (ω.2 ≤ π ω.1)
  μhat := fun _ _ _ => 0

/-- P006-T12; PDF p. 6 (Theorem 2); PDF p. 20 (Appendix C.2).
Counterexample to the sufficiency reading of the printed absolute-continuity
direction: P_agent << P_reference alone need not supply the named
reference-to-agent density. Lebesgue probability on [0,1] and its
half-Lebesgue, half-atom reference have the same support and satisfy the printed
direction, but the reference has mass 1/2 at the Lebesgue-null singleton {1/2}
and has no representing density. Complete both agents with one unit, independent
uniform treatment seeds, unconstrained policies, potential outcomes 0 and 1,
common zero baseline and oracle estimator. Every other stochastic-model condition
holds and both treatment effects are identically one.
This does not refute the ranking conclusion under a separate assumption that
the named representing density exists.
-/
def T12WholeStatement : Prop :=
  T12Statement ∧
  Standing (uniformOracle referenceWithAtom) ∧ Standing (uniformOracle intervalLaw) ∧
  (uniformOracle referenceWithAtom).PX = referenceWithAtom ∧
  (uniformOracle intervalLaw).PX = intervalLaw ∧
  (uniformOracle referenceWithAtom).PX ≪ referenceWithAtom ∧
  (uniformOracle intervalLaw).PX ≪ referenceWithAtom ∧
  (∀ x, (uniformOracle referenceWithAtom).τ x = 1 ∧
    (uniformOracle intervalLaw).τ x = 1) ∧
  VectorUnbiased (uniformOracle referenceWithAtom) {π | Admissible π} ∧
  VectorUnbiased (uniformOracle intervalLaw) {π | Admissible π} ∧
  IndepFun Prod.fst Prod.snd
    ((referenceWithAtom.prod intervalLaw).prod (intervalLaw.prod intervalLaw))

/-- The positive-part mean in [0,infinity], including meaningful infinite expectations. -/
def extendedPositiveMean {C : Type*} [MeasurableSpace C] (P0 : Measure C)
    (τ : C → ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (positivePart (τ x)) ∂P0

/-- P006-T14; PDF p. 5 (Definitions 1 and 2); PDF pp. 19-20 (score corrections).
Pointwise treatment-effect dominance orders reference positive-part expectations
in [0,infinity], without a finiteness assumption. When both positive parts are
integrable, the same comparison holds for real expectations. Each corrected
ranking compares its own agent's score, and the weighted reward evaluates the
unit's own weight inside the sum; the separate score identities belong to T30,
T7 and T13 as specified by the canonical claim.
-/
def T14WholeStatement : Prop :=
  (∀ t : ℝ, positivePart t = max t 0) ∧
  (∀ {C : Type*} [MeasurableSpace C] (P0 : Measure C) (τj τk : C → ℝ),
    (∀ x, τk x ≤ τj x) → extendedPositiveMean P0 τk ≤ extendedPositiveMean P0 τj) ∧
  (∀ {C : Type*} [MeasurableSpace C] (P0 : Measure C) (τj τk : C → ℝ),
    (∀ x, τk x ≤ τj x) → Integrable (fun x => positivePart (τj x)) P0 →
    Integrable (fun x => positivePart (τk x)) P0 →
    (∫ x, positivePart (τk x) ∂P0) ≤ ∫ x, positivePart (τj x) ∂P0)

end
end SAP.P006a
