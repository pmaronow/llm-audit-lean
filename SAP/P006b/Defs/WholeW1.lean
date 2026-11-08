import Mathlib
import SAP.P006b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The standing outcome, sampling and randomization assumptions, without an
integrability condition on an unused estimator. Replacing that field by zero
retains every outcome and treatment field of the original experiment. -/
def outcomeExperiment {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) : Experiment Ω C n :=
  { E with μhat := fun _ _ _ => 0 }

def OutcomeStanding {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) : Prop := Standing (outcomeExperiment E)

/-- Corrected T6/T8 condition: only the treated estimator residual must be
integrable; its conditional mean given the agent's information is zero. -/
def TreatedMoment {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (a : C → ℝ) : Prop :=
  ∀ π, Admissible π → ∀ i,
    Integrable (fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω))) (E.law π) ∧
    (E.law π)[(fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω))) | E.covariateSigma i]
        =ᵐ[E.law π] (fun _ => (0 : ℝ))

def publicFiniteMean {X : Type*} {K : ℕ}
    (p : X → Fin K → ℝ) (m : X × Fin K → ℝ) (x : X) : ℝ :=
  ∑ u, p x u * m (x,u)

/-- Joint distribution with public law Q and finite conditional type masses p.
The u-th term gives public sets their probability weighted by p(x,u).
Normalization and measurability are required in the comparison statement. -/
def finiteConditionalLaw {X : Type*} [MeasurableSpace X] {K : ℕ}
    (Q : Measure X) (p : X → Fin K → ℝ) : Measure (X × Fin K) :=
  ∑ u : Fin K, (Q.withDensity (fun x => ENNReal.ofReal (p x u))).map (fun x => (x,u))

def finiteMarginalDeviation {X : Type*} {K : ℕ}
    (p : X → Fin K → ℝ) (m : X × Fin K → ℝ) (c : X × Fin K) : ℝ :=
  |publicFiniteMean p m c.1 - m c|

/-- Joint law of one binary type and its conditionally Bernoulli treatment.
Products of this law give iid units; all sums here are over the full real policy square. -/
def binaryPopulationLaw (p : ℝ) (π : BinaryPolicy) : Measure (Bool × Bool) :=
  ∑ z : Bool × Bool,
    ENNReal.ofReal (coinMass p z.1 * coinMass (binaryRule π z.1) z.2) •
      Measure.dirac z

def binaryObserved (y0 y1 : Bool → ℝ) (z : Bool × Bool) : ℝ :=
  if z.2 then y1 z.1 else y0 z.1

def binaryUntreatedMass (p : ℝ) (π : BinaryPolicy) : ℝ :=
  (1-p)*(1-π.1) + p*(1-π.2)

def binarySelectedBaseline (p : ℝ) (y0 : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ((1-p)*y0 false*(1-π.1) + p*y0 true*(1-π.2)) / binaryUntreatedMass p π

/-- Actual one-unit score with the population endogenous baseline. -/
def binaryEndogenousTT (p : ℝ) (y0 y1 : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∫ z, (binaryObserved y0 y1 z - binarySelectedBaseline p y0 π) * bit z.2
    ∂binaryPopulationLaw p π

def binaryActualWelfare (p : ℝ) (y0 y1 : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∫ z, binaryObserved y0 y1 z - y0 z.1 ∂binaryPopulationLaw p π

def binaryMarginalHeterogeneity (p : ℝ) (y0 : Bool → ℝ) : ℝ :=
  let m := (1-p)*y0 false + p*y0 true
  (1-p)*|m-y0 false| + p*|m-y0 true|

def T17BadProbability (L : ℝ) : ℝ := 1/(2*L)
def T17BadY0 (L : ℝ) : Bool → ℝ :=
  fun u => if u then -L else 1/(2*(1-T17BadProbability L))
def T17BadY1 (L : ℝ) : Bool → ℝ := fun u => if u then 0 else -L/2
def T17BadPolicies : Set BinaryPolicy := {(1,0), (0,1)}

/-- A constant-public-covariate, deterministic-outcome family with one unit.
Both feasible policies have untreated mass. The score is an actual integral,
and the asserted baseline is its actual untreated conditional outcome mean. -/
def T17BadFamily (L : ℝ) : Prop :=
  let p := T17BadProbability L
  let y0 := T17BadY0 L
  let y1 := T17BadY1 L
  let F := binaryEndogenousTT p y0 y1
  let V := binaryActualWelfare p y0 y1
  0 < p ∧ p < 1 ∧
  (1-p)*y0 false+p*y0 true = 0 ∧
  binaryMarginalHeterogeneity p y0 = 1 ∧
  (∀ π ∈ T17BadPolicies,
    binaryFeasible π ∧ IsProbabilityMeasure (binaryPopulationLaw p π) ∧
    0 < binaryUntreatedMass p π ∧
    (binaryPopulationLaw p π {z | z.2 = false}).toReal = binaryUntreatedMass p π ∧
    eventMean (binaryPopulationLaw p π) {z | z.2 = false} (binaryObserved y0 y1) =
      binarySelectedBaseline p y0 π) ∧
  binarySelectedBaseline p y0 (1,0) = -L ∧
  binarySelectedBaseline p y0 (0,1) = 1/(2*(1-p)) ∧
  F (1,0) = (1-p)*L/2 ∧ F (0,1) = -p/(2*(1-p)) ∧
  (∀ π, IsBest T17BadPolicies F π ↔ π = (1,0)) ∧
  IsBest T17BadPolicies V (0,1) ∧
  V (0,1) = 1/2 ∧ V (1,0) = -(1-p)*L/2-1/2 ∧
  regret T17BadPolicies V (1,0) = L/2+3/4

def T17ConditionalMeanStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {K n : ℕ}
    (E : Experiment Ω (Fin K) n), OutcomeStanding E →
    ∀ (p : Fin K → ℝ), (∀ u, 0 < p u) → (∑ u, p u) = 1 →
    (∀ u, (E.PX {u}).toReal = p u) →
    ∀ π, Admissible π → 0 < finiteMass p (fun u => 1-π u) → ∀ i,
      Integrable (fun ω => E.observed π ω i) (E.law π) ∧
      (E.law π {ω | E.T π i ω = false}).toReal = finiteMass p (fun u => 1-π u) ∧
      0 < (E.law π {ω | E.T π i ω = false}).toReal ∧
      eventMean (E.law π) {ω | E.T π i ω = false}
        (fun ω => E.observed π ω i) = finiteSelectedBaseline p E.μ0 π

def T17ComparisonStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] {K : ℕ} (Q : Measure X),
    IsProbabilityMeasure Q → ∀ (p : X → Fin K → ℝ) (m : X × Fin K → ℝ),
    (∀ u, Measurable (fun x => p x u)) → Measurable m →
    (∀ x u, 0 < p x u) → (∀ x, ∑ u, p x u = 1) →
    Integrable (maximumDeviation m) (finiteConditionalLaw Q p) →
    (∀ x u, |publicFiniteMean p m x-m (x,u)| ≤ maximumDeviation m (x,u)) ∧
    IsProbabilityMeasure (finiteConditionalLaw Q p) ∧
    Integrable (finiteMarginalDeviation p m) (finiteConditionalLaw Q p) ∧
    (∫ c, finiteMarginalDeviation p m c ∂finiteConditionalLaw Q p) ≤
      ∫ c, maximumDeviation m c ∂finiteConditionalLaw Q p

def T17AssumptionImplicationStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] {K : ℕ} (Q : Measure X),
    IsProbabilityMeasure Q → ∀ (p : X → Fin K → ℝ) (m : X × Fin K → ℝ),
    (∀ u, Measurable (fun x => p x u)) → Measurable m →
    (∀ x u, 0 < p x u) → (∀ x, ∑ u, p x u = 1) →
    Integrable (maximumDeviation m) (finiteConditionalLaw Q p) →
    ∀ γ, (∫ c, maximumDeviation m c ∂finiteConditionalLaw Q p) ≤ γ →
      (∫ c, finiteMarginalDeviation p m c ∂finiteConditionalLaw Q p) ≤ γ

/-- The public untreated mean for a supplied conditional law of the private type.
The comparison statements include the usual measurability and integrability
conditions, and existence of the displayed finite maximum deviations. -/
def kernelMarginalBaseline {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) (m : X × U → ℝ) (x : X) : ℝ :=
  ∫ u, m (x,u) ∂κ x

def kernelMarginalDeviation {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) (m : X × U → ℝ) (c : X × U) : ℝ :=
  |kernelMarginalBaseline κ m c.1 - m c|

/-- General companion comparison, without a finite-support or atom assumption.
A supplied Markov kernel represents the conditional law of U given X; hence no
standard Borel hypothesis is needed to construct a conditional law here. -/
def T17KernelComparisonStatement : Prop :=
  ∀ {X U : Type} [MeasurableSpace X] [MeasurableSpace U] [Nonempty U]
    (Q : Measure X), IsProbabilityMeasure Q →
    ∀ (κ : Kernel X U), IsMarkovKernel κ → ∀ (m : X × U → ℝ),
    Measurable m → Integrable m (Q.compProd κ) →
    (∀ c : X × U, ∃ v, ∀ u, |m c-m (c.1,u)| ≤ |m c-m (c.1,v)|) →
    Integrable (maximumDeviation m) (Q.compProd κ) →
    IsProbabilityMeasure (Q.compProd κ) ∧
    Integrable (kernelMarginalDeviation κ m) (Q.compProd κ) ∧
    (∀ᵐ c ∂Q.compProd κ, kernelMarginalDeviation κ m c ≤ maximumDeviation m c) ∧
    (∫ c, kernelMarginalDeviation κ m c ∂Q.compProd κ) ≤
      ∫ c, maximumDeviation m c ∂Q.compProd κ

def T17KernelAssumptionImplicationStatement : Prop :=
  ∀ {X U : Type} [MeasurableSpace X] [MeasurableSpace U] [Nonempty U]
    (Q : Measure X), IsProbabilityMeasure Q →
    ∀ (κ : Kernel X U), IsMarkovKernel κ → ∀ (m : X × U → ℝ),
    Measurable m → Integrable m (Q.compProd κ) →
    (∀ c : X × U, ∃ v, ∀ u, |m c-m (c.1,u)| ≤ |m c-m (c.1,v)|) →
    Integrable (maximumDeviation m) (Q.compProd κ) →
    ∀ γ, (∫ c, maximumDeviation m c ∂Q.compProd κ) ≤ γ →
      (∫ c, kernelMarginalDeviation κ m c ∂Q.compProd κ) ≤ γ

/-- P006-T17; PDF p. 23 (Appendix D.3, paragraph after Assumption 4).
For finite positive-mass conditional types, the actual untreated outcome mean
is the probability-weighted selection ratio. Leaving only one type untreated
selects its mean; treating only it selects the complementary mean (the three-type
values are 0 and 2). Under the usual measure-theoretic conditions, for every
conditional probability kernel, including infinite and nonatomic private spaces,
the marginal deviation is integrable and bounded almost surely and in expectation
by the maximum deviation. Thus Assumption 4 implies Assumption 2 with the same
constant. Marginal heterogeneity alone cannot bound endogenous-baseline regret:
it can equal 1 while regret exceeds every prescribed positive threshold. -/
def T17WholeStatement : Prop :=
  T17ConditionalMeanStatement ∧ T17SelectionStatement ∧ T17ExampleStatement ∧
  T17ComparisonStatement ∧ T17AssumptionImplicationStatement ∧
  T17KernelComparisonStatement ∧ T17KernelAssumptionImplicationStatement ∧
  (∀ M : ℝ, 0 < M → ∃ L : ℝ, 1 < L ∧ T17BadFamily L ∧
    M < regret T17BadPolicies
      (binaryActualWelfare (T17BadProbability L) (T17BadY0 L) (T17BadY1 L)) (1,0))

/-- The printed claim is false: P006-T18; PDF p. 17 (Appendix B.4, proof of
Proposition 1). The fair two-unit deterministic example has samplewise ATO
bounded by the event that some type is 1, with equality under (0,1). Its exact
reward is b(4-a-b)/4, uniquely maximized at (0,1), with value 3/4. Welfare is
a/2-3b/2, with maximum 1/2 and selected value -3/2. Regret is 2; the printed
expression is -1. Every feasible policy's regret from an attained maximum is
nonnegative. -/
def T18WholeStatement : Prop :=
  T18Statement ∧
  (∀ x0 x1 t0 t1 : Bool,
    wATO ![t0,t1] ![outcomeP1 x0,outcomeP1 x1] ≤
      (if x0 || x1 then (1 : ℝ) else 0)) ∧
  (∀ x0 x1 : Bool,
    wATO ![x0,x1] ![outcomeP1 x0,outcomeP1 x1] =
      (if x0 || x1 then (1 : ℝ) else 0)) ∧
  (∀ π, rewardP1 (1/2) π = π.2*(4-π.1-π.2)/4) ∧
  (∀ π, IsBest binaryPolicies (rewardP1 (1/2)) π ↔ π = (0,1)) ∧
  (∀ π, binaryWelfare (1/2) (effectP1 4) π = π.1/2-3*π.2/2) ∧
  bestValue binaryPolicies (binaryWelfare (1/2) (effectP1 4)) = 1/2 ∧
  binaryWelfare (1/2) (effectP1 4) (1,0) = 1/2 ∧
  binaryWelfare (1/2) (effectP1 4) (0,1) = -3/2 ∧
  ((1-(1/2 : ℝ))-(1/2)*(4-1) = 1-(1/2)*4) ∧
  (∀ {P : Type} (S : Set P) (V : P → ℝ) (s π : P),
    IsBest S V s → π ∈ S → 0 ≤ regret S V π)

/-- Public covariates have arbitrary law Q, independent of the fair private bit. -/
def fairPrivateLaw : Measure Bool :=
  ∑ u : Bool, (ENNReal.ofReal (1/2 : ℝ)) • Measure.dirac u

def policyCoordinates {X : Type*} [MeasurableSpace X]
    (Q : Measure X) (π : X × Bool → ℝ) : BinaryPolicy :=
  (∫ x, π (x,false) ∂Q, ∫ x, π (x,true) ∂Q)

def privateBadRule {X : Type*} : X × Bool → ℝ := fun c => if c.2 then 0 else 1
def privateGoodRule {X : Type*} : X × Bool → ℝ := fun c => if c.2 then 1 else 0

def T25Model {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
    (E : Experiment Ω (X × Bool) n) (Q : Measure X) (α β η : ℝ) : Prop :=
  OutcomeStanding E ∧ IsProbabilityMeasure Q ∧ E.PX = Q.prod fairPrivateLaw ∧
  E.μ0 = (fun c => lowerBoundY0 α c.2) ∧
  E.μ1 = (fun c => lowerBoundY1 β η c.2) ∧
  (∀ π, Admissible π → ∀ ω x u v, E.μhat π ω (x,u) = E.μhat π ω (x,v)) ∧
  TreatedMoment E (fun _ => 0)

def T25FamilyConclusion {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
    (E : Experiment Ω (X × Bool) n) (Q : Measure X) (α β η : ℝ) : Prop :=
  (∀ π, Admissible π →
    binaryFeasible (policyCoordinates Q π) ∧
    E.expectedTT π = (n : ℝ)*(∫ c, π c*(E.μ1 c-0) ∂E.PX) ∧
    E.expectedTT π = (n : ℝ)*(β*(policyCoordinates Q π).1-η*(policyCoordinates Q π).2)/2 ∧
    E.V π = ((β-α)*(policyCoordinates Q π).1+(α-η)*(policyCoordinates Q π).2)/2) ∧
  (∀ x, (∫ u, E.μ0 (x,u) ∂fairPrivateLaw) = 0) ∧
  (∫ c, |(0 : ℝ)-E.μ0 c| ∂E.PX) = α ∧
  (∀ γ, (∫ c, |(0 : ℝ)-E.μ0 c| ∂E.PX) ≤ γ ↔ α ≤ γ) ∧
  IsBest {π | Admissible π} E.V privateGoodRule ∧
  bestValue {π | Admissible π} E.V = (α-η)/2 ∧
  IsBest {π | Admissible π} E.expectedTT privateBadRule ∧
  (η = 0 →
    (∀ π, IsBest {π | Admissible π} E.expectedTT π ↔
      Admissible π ∧ (policyCoordinates Q π).1 = 1) ∧
    (∀ π, Admissible π → ((policyCoordinates Q π).1 = 1 ↔ ∀ᵐ x ∂Q, π (x,false) = 1)) ∧
    (∀ π, IsBest {π | Admissible π} E.expectedTT π →
      regret {π | Admissible π} E.V π = α-β/2-α*(policyCoordinates Q π).2/2) ∧
    regret {π | Admissible π} E.V privateBadRule = α-β/2) ∧
  (0 < η →
    (∀ π, IsBest {π | Admissible π} E.expectedTT π ↔
      Admissible π ∧ (∀ᵐ x ∂Q, π (x,false) = 1) ∧ (∀ᵐ x ∂Q, π (x,true) = 0)) ∧
    (∀ π, IsBest {π | Admissible π} E.expectedTT π →
      regret {π | Admissible π} E.V π = α-(β+η)/2))

def T25GeneralStatement : Prop :=
  ∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
    (E : Experiment Ω (X × Bool) n) (Q : Measure X) (α β η : ℝ),
    T25Model E Q α β η → 0 < β → β < α → 0 ≤ η → η < α →
    T25FamilyConclusion E Q α β η

/-- P006-T25; PDF p. 7 (Section 5); PDF pp. 22-23 (Appendix D.2).
For arbitrary public covariates independent of a fair binary private type,
integrable noisy outcomes and every estimator satisfying corrected T8, the TT
reward, full response set, welfare, regret and minimal marginal heterogeneity
are the stated two-coordinate formulas. The displayed bad response attains
regret alpha-beta/2. Taking beta=min(epsilon,alpha/2) gives the lower bound.
For 0<beta,eta<alpha the perturbed family has a unique response up to null sets
and regret alpha-(beta+eta)/2; taking both parameters to be that minimum gives
the same lower bound. The deterministic zero-estimator family supplies actual
finite-sample existential witnesses. -/
def T25WholeStatement : Prop :=
  T25GeneralStatement ∧ T25Statement ∧
  (∀ α ε : ℝ, 0 < α → 0 < ε →
    let δ := min ε (α/2)
    0 < δ ∧ δ < α ∧ δ ≤ ε ∧
    (∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
      (E : Experiment Ω (X × Bool) n) (Q : Measure X),
      T25Model E Q α δ 0 →
      IsBest {π | Admissible π} E.expectedTT privateBadRule ∧
      regret {π | Admissible π} E.V privateBadRule = α-δ/2 ∧
      α-ε ≤ regret {π | Admissible π} E.V privateBadRule) ∧
    (∀ {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
      (E : Experiment Ω (X × Bool) n) (Q : Measure X),
      T25Model E Q α δ δ →
      (∀ π, IsBest {π | Admissible π} E.expectedTT π →
        regret {π | Admissible π} E.V π = α-(δ+δ)/2 ∧
        α-ε ≤ regret {π | Admissible π} E.V π)) ∧
    (∀ n : ℕ, 0 < n →
      IsBest binaryPolicies (fun π => (n : ℝ)*lowerBoundReward δ 0 π) (1,0) ∧
      regret binaryPolicies (lowerBoundWelfare α δ 0) (1,0) = α-δ/2 ∧
      α-ε ≤ regret binaryPolicies (lowerBoundWelfare α δ 0) (1,0) ∧
      IsBest binaryPolicies (fun π => (n : ℝ)*lowerBoundReward δ δ π) (1,0) ∧
      regret binaryPolicies (lowerBoundWelfare α δ δ) (1,0) = α-(δ+δ)/2 ∧
      α-ε ≤ regret binaryPolicies (lowerBoundWelfare α δ δ) (1,0)))

def T29Model {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (E : Experiment Ω Bool n) (p α β : ℝ) : Prop :=
  OutcomeStanding E ∧ (∀ u, (E.PX {u}).toReal = coinMass p u) ∧
  E.μ0 = (fun u => if u then β else α) ∧ E.μ1 = outcomeP1

def T29FamilyConclusion {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (E : Experiment Ω Bool n) (p α β : ℝ) : Prop :=
  (∀ π ∈ binaryPolicies,
    E.expectedATO (binaryRule π) = emptyFactor n ((1-p)*π.1+p*π.2)*(p*π.2) ∧
    E.V (binaryRule π) = (1-p)*π.1*(-α)+p*π.2*(1-β)) ∧
  (2 ≤ n → ∀ π, IsBest binaryPolicies (fun ρ => E.expectedATO (binaryRule ρ)) π ↔
    π = (0,1)) ∧
  (n = 1 → ∀ π, IsBest binaryPolicies (fun ρ => E.expectedATO (binaryRule ρ)) π ↔
    binaryFeasible π ∧ π.2 = 1) ∧
  (α < 0 → β = 0 →
    E.τ false = -α ∧ 0 < E.τ false ∧ E.τ true = 1 ∧
    IsBest binaryPolicies (fun ρ => E.V (binaryRule ρ)) (1,1) ∧
    bestValue binaryPolicies (fun ρ => E.V (binaryRule ρ)) = -α*(1-p)+p ∧
    E.V (binaryRule (0,1)) = p ∧
    regret binaryPolicies (fun ρ => E.V (binaryRule ρ)) (0,1) = -α*(1-p))

/-- P006-T29; PDF p. 4 (Section 3); PDF p. 17 (Appendix B.4).
ATO regret exceeds every positive threshold. For every iid integrable
conditional-outcome law in the binary family, its exact expected reward is
h_n(q)pb. For n>=2 the unique response is (0,1); for n=1 exactly b=1 is
required. In the first failure mode welfare has maximum -alpha(1-p)+p,
selected value p and regret -alpha(1-p), which diverges as alpha tends to
minus infinity at fixed 0<p<1. The claim allows arbitrary outcome noise. -/
def T29WholeStatement : Prop :=
  T29Statement ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (E : Experiment Ω Bool n) (p α β : ℝ),
    0 < p → p < 1 → T29Model E p α β → T29FamilyConclusion E p α β) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    (F : ℝ → Experiment Ω Bool n) (p : ℝ), 0 < p → p < 1 →
    (∀ α, α < 0 → T29Model (F α) p α 0) →
    Tendsto (fun α => regret binaryPolicies (fun ρ => (F α).V (binaryRule ρ)) (0,1))
      atBot atTop)

def positiveEffectMean {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) : ℝ := ∫ x, E.τ x * positiveRule E.τ x ∂E.PX

def uniformRankingPair {C : Type*} (τj τk : C → ℝ) (Sj Sk : ℝ) : Prop :=
  (∀ x, τk x ≤ τj x) → Sk ≤ Sj

def relativeRankingPair {C : Type*} [MeasurableSpace C] (Q : Measure C)
    (τj τk : C → ℝ) (Sj Sk : ℝ) : Prop :=
  (∫ x, τk x ∂Q) ≤ (∫ x, τj x ∂Q) → Sk ≤ Sj

def T30MaximumStatement : Prop :=
  ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n), OutcomeStanding E → TreatedMoment E E.μ0 →
    IsBest {π | Admissible π} E.expectedTT (positiveRule E.τ) ∧
    bestValue {π | Admissible π} E.expectedTT = (n : ℝ)*positiveEffectMean E

def T30PairStatement : Prop :=
  ∀ {Ωj Ωk C : Type} [MeasurableSpace Ωj] [MeasurableSpace Ωk] [MeasurableSpace C]
    {nj nk : ℕ} (Ej : Experiment Ωj C nj) (Ek : Experiment Ωk C nk),
    OutcomeStanding Ej → OutcomeStanding Ek →
    TreatedMoment Ej Ej.μ0 → TreatedMoment Ek Ek.μ0 →
    Ej.μ0 = Ek.μ0 → Ej.PX = Ek.PX → (∀ x, Ek.τ x ≤ Ej.τ x) →
    0 < positiveEffectMean Ek →
    positiveEffectMean Ek ≤ positiveEffectMean Ej ∧ 0 < positiveEffectMean Ej ∧
    ((nj : ℝ)*positiveEffectMean Ej < (nk : ℝ)*positiveEffectMean Ek ↔
      (nj : ℝ) < (nk : ℝ)*positiveEffectMean Ek/positiveEffectMean Ej) ∧
    ((nj : ℝ)*positiveEffectMean Ej < (nk : ℝ)*positiveEffectMean Ek →
      bestValue {π | Admissible π} Ej.expectedTT < bestValue {π | Admissible π} Ek.expectedTT ∧
      ¬ uniformRankingPair Ej.τ Ek.τ
        (bestValue {π | Admissible π} Ej.expectedTT) (bestValue {π | Admissible π} Ek.expectedTT) ∧
      (∀ Q : Measure C, IsProbabilityMeasure Q → Integrable Ej.τ Q → Integrable Ek.τ Q →
        (∫ x, Ek.τ x ∂Q) ≤ (∫ x, Ej.τ x ∂Q) ∧
        ¬ relativeRankingPair Q Ej.τ Ek.τ
          (bestValue {π | Admissible π} Ej.expectedTT) (bestValue {π | Admissible π} Ek.expectedTT)))

def T30ExistenceStatement : Prop :=
  ∃ (Ej : Experiment (Fin 1 → Bool × Bool) Bool 1)
    (Ek : Experiment (Fin 2 → Bool × Bool) Bool 2),
    OutcomeStanding Ej ∧ OutcomeStanding Ek ∧
    TreatedMoment Ej Ej.μ0 ∧ TreatedMoment Ek Ek.μ0 ∧
    Ej.PX = fairPrivateLaw ∧ Ek.PX = fairPrivateLaw ∧
    Ej.μ0 = (fun _ => 0) ∧ Ek.μ0 = (fun _ => 0) ∧
    Ej.μ1 = (fun _ => 1) ∧ Ek.μ1 = (fun _ => 1) ∧
    bestValue {π | Admissible π} Ej.expectedTT = 1 ∧
    bestValue {π | Admissible π} Ek.expectedTT = 2 ∧
    ¬ uniformRankingPair Ej.τ Ek.τ 1 2 ∧
    ¬ relativeRankingPair fairPrivateLaw Ej.τ Ek.τ 1 2

/-- P006-T30; PDF p. 6 (Section 4); PDF pp. 18-19 (Appendix C.2).
Under the usual measure-theoretic conditions (policies are measurable maps into
[0,1]; outcomes, conditional means and the treated estimator residual are
integrable), with corrected T6 and otherwise unconstrained policies, each agent's
attained maximum TT score is its sample size times its mean positive effect.
For two agents with the common untreated mean of the multi-agent setting,
identical covariate laws, pointwise effect dominance and a positive mean positive
effect for the dominated agent, these positive-effect means are ordered; a
reversed sample-size-weighted inequality violates both ranking properties, for
every reference law with finite effect means. The ratio condition is equivalent
because its denominator is positive. Identical unit effects with sample sizes
1 and 2 give actual best scores 1 and 2 and witness the existential failure of
both properties. -/
def T30WholeStatement : Prop :=
  T30MaximumStatement ∧ T30PairStatement ∧ T30ExistenceStatement

end
end SAP.P006b
