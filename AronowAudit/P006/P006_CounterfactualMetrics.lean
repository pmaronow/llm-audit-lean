import Mathlib

/-!
P006: On Counterfactual Metrics for Social Welfare: Incentives, Ranking,
and Information Asymmetry. All locations are one-based PDF pages.
The file contains definitions, counterexamples to printed claims and
corrected results.
-/

namespace AronowAudit.P006

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Section 2, PDF p. 3: "treatment rule π : X → [0,1]".
Measurability makes the standing measurable-function reading explicit. -/
def Admissible {C : Type*} [MeasurableSpace C] (π : C → ℝ) : Prop :=
  Measurable π ∧ ∀ x, 0 ≤ π x ∧ π x ≤ 1

/-- Section 2, PDF p. 3: "Tᵢ^π ∈ {0,1}". Boolean treatment, cast to ℝ. -/
def bit (t : Bool) : ℝ := if t then 1 else 0

/-- Reward Functions 1–4, PDF pp. 4–6: "Σᵢ Tᵢ^π". -/
def treatedCount {n : ℕ} (T : Fin n → Bool) : ℝ := ∑ i, bit (T i)

/-- Reward Function 1, PDF p. 4: "Σᵢ Yᵢ Tᵢ^π / Σᵢ Tᵢ^π", and
"0 otherwise". The zero-on-empty branch is retained explicitly. -/
def wATO {n : ℕ} (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  if 0 < treatedCount T then (∑ i, Y i * bit (T i)) / treatedCount T else 0

/-- Reward Function 2, PDF p. 4: "Σᵢ (Yᵢ − μ̂₀(Xᵢ)) Tᵢ^π / Σᵢ Tᵢ^π",
and "0 otherwise". -/
def wATT {C : Type*} {n : ℕ} (μhat : C → ℝ) (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  wATO T (fun i => Y i - μhat (X i))

/-- Reward Function 4, PDF p. 6: "Σᵢ (Yᵢ − μ̂₀(Xᵢ)) Tᵢ^π g(Xᵢ)".
The weight is evaluated at each unit's own covariate. -/
def wWeightedTT {C : Type*} {n : ℕ} (μhat g : C → ℝ) (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  ∑ i, (Y i - μhat (X i)) * bit (T i) * g (X i)

/-- Reward Function 3, PDF p. 5: "Σᵢ (Yᵢ − μ̂₀(Xᵢ)) Tᵢ^π". -/
def wTT {C : Type*} {n : ℕ} (μhat : C → ℝ) (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  wWeightedTT μhat (fun _ => 1) X T Y

/-- Reward Function 5 (TO), PDF p. 15: "Σᵢ Yᵢ Tᵢ^π". -/
def wTO {n : ℕ} (T : Fin n → Bool) (Y : Fin n → ℝ) : ℝ :=
  ∑ i, Y i * bit (T i)

/-- Section 2, PDF p. 3: "π^w ∈ arg max_{π∈PiSet} E[w]".
Membership is non-strict, so ties and every best response are represented. -/
def IsBest {P : Type*} (PiSet : Set P) (f : P → ℝ) (π : P) : Prop :=
  π ∈ PiSet ∧ ∀ π' ∈ PiSet, f π' ≤ f π

/-- Section 2, PDF p. 3: "max_{π̃∈PiSet} V(π̃)".
The supremum agrees with the printed maximum whenever `IsBest` has a witness.
Regret theorems supply or assume such a witness. The abstract ranking
definitions extend the notation to suprema; their concrete applications
certify attained maxima separately. -/
def bestValue {P : Type*} (PiSet : Set P) (f : P → ℝ) : ℝ := sSup (f '' PiSet)

/-- Section 2, PDF p. 3: "R(π) = max_{π̃∈PiSet} V(π̃) − V(π)". -/
def regret {P : Type*} (PiSet : Set P) (V : P → ℝ) (π : P) : ℝ :=
  bestValue PiSet V - V π

/-- Lemma 1, PDF pp. 15–16: "π*(x)=1 if τ(x)>0; 0 otherwise". -/
def positiveRule {C : Type*} (m : C → ℝ) : C → ℝ :=
  fun x => if 0 < m x then 1 else 0

/-- Propositions 6–7, PDF pp. 15–16: "1 if x ∈ arg maxₓ m(x) and m(x)>0;
0 otherwise". This is the printed rule, not a repaired rule. -/
def printedAverageRule {C : Type*} (m : C → ℝ) : C → ℝ :=
  fun x => if (∀ z, m z ≤ m x) ∧ 0 < m x then 1 else 0

/-- Corrected Propositions 6–7 (T2): "hₙ(q)=Σ_{j=0}^{n−1}(1−q)^j". -/
def emptyFactor (n : ℕ) (q : ℝ) : ℝ := ∑ j ∈ Finset.range n, (1 - q) ^ j

/-- Section 2, PDF p. 3, and Appendix B.1, p. 14: "bold Z ... vector of
i.i.d. random variables"; "integration ... with respect to the probability
measure". An experiment includes the full joint law of sample, randomization,
and random estimator. A policy is fixed before this law is integrated.
`C` is X for full information and X×U for private information. -/
structure Experiment (Ω C : Type*) [MeasurableSpace Ω] [MeasurableSpace C]
    (n : ℕ) where
  /-- Section 2, PDF p. 3: "i ∈ {1,...,n}"; the sample is nonempty. -/
  hn : 0 < n
  /-- Appendix B.1, PDF p. 14: integration "with respect to the probability
  measure" for X; Section 2, p. 3, supplies the iid covariate draw. -/
  PX : Measure C
  /-- Section 2, PDF p. 3: "μ_t(X)=E[Y_i(t)|X]", here t=0. -/
  μ0 : C → ℝ
  /-- Section 2, PDF p. 3: "μ_t(X)=E[Y_i(t)|X]", here t=1. -/
  μ1 : C → ℝ
  /-- Section 2, PDF p. 3: "maximizes their expected reward". This is the
  joint randomization/sample/estimator probability law for a fixed policy. -/
  law : (C → ℝ) → Measure Ω
  /-- Section 2, PDF p. 3: "X_i ∈ X" sampled independently and identically. -/
  X : Fin n → Ω → C
  /-- Section 2, PDF p. 3: "Y_i(t) ... potential outcome", here t=0. -/
  Y0 : Fin n → Ω → ℝ
  /-- Section 2, PDF p. 3: "Y_i(t) ... potential outcome", here t=1. -/
  Y1 : Fin n → Ω → ℝ
  /-- Section 2, PDF p. 3: "π(X_i)=P(T_i^π=1|X_i)". -/
  T : (C → ℝ) → Fin n → Ω → Bool
  /-- Assumption 1, PDF p. 4: "the principal accesses an estimator μ̂0(x)".
  Randomness and the policy-dependent agent-data version of D.3 are retained;
  unbiasedness is a separate property, not built into this object. -/
  μhat : (C → ℝ) → Ω → C → ℝ

namespace Experiment

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}

/-- Section 2, PDF p. 3: "τ(X)=E[Yᵢ(1)−Yᵢ(0)|X]". -/
def τ (E : Experiment Ω C n) : C → ℝ := fun x => E.μ1 x - E.μ0 x

/-- Section 2, PDF p. 3: "Yᵢ=Yᵢ(Tᵢ^π)" under SUTVA. -/
def observed (E : Experiment Ω C n) (π : C → ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => if E.T π i ω then E.Y1 i ω else E.Y0 i ω

/-- Section 2, PDF p. 3: "V(π)=E[Yᵢ(Tᵢ^π)−Yᵢ(0)]".
The index is 0 in Lean; identical distribution makes its choice immaterial. -/
def V (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ ω, E.observed π ω ⟨0, E.hn⟩ - E.Y0 ⟨0, E.hn⟩ ω ∂E.law π

/-- Lemma 1, PDF p. 16: "V(π)=∫τ(Xᵢ)π(Xᵢ)dP_X". -/
def meanWelfare (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ x, π x * E.τ x ∂E.PX

/-- Reward Functions 1–4, PDF pp. 4–6; unconditional expectation over all
sample, treatment and estimator randomness, as in Section 2, p. 3. -/
def expectedATO (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ ω, wATO (fun i => E.T π i ω) (E.observed π ω) ∂E.law π

/-- Reward Function 2, PDF p. 4 and Section 2, p. 3: unconditional "E[w]" of the printed zero-on-empty ATT reward. -/
def expectedATT (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ ω, wATT (E.μhat π ω) (fun i => E.X i ω)
    (fun i => E.T π i ω) (E.observed π ω) ∂E.law π

/-- Reward Function 4, PDF p. 6: unconditional "E[w^g_TT]" with each unit's own X,T,Y arguments. -/
def expectedWeightedTT (E : Experiment Ω C n) (g π : C → ℝ) : ℝ :=
  ∫ ω, wWeightedTT (E.μhat π ω) g (fun i => E.X i ω)
    (fun i => E.T π i ω) (E.observed π ω) ∂E.law π

/-- Reward Function 3, PDF p. 5: unconditional "E[w_TT]", the weighted reward with g=1. -/
def expectedTT (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  E.expectedWeightedTT (fun _ => 1) π

/-- Corrected Propositions 6–7 (T2): "q(π)=E[π(Xᵢ)]" and
"A(π)=E[m(Xᵢ)π(Xᵢ)]". -/
def q (E : Experiment Ω C n) (π : C → ℝ) : ℝ := ∫ x, π x ∂E.PX

/-- Corrected Propositions 6–7 (T2), PDF pp. 15–16: "A(π)=E[m(X)π(X)]". -/
def A (E : Experiment Ω C n) (m π : C → ℝ) : ℝ := ∫ x, m x * π x ∂E.PX

/-- Corrected Propositions 6–7 (T2), PDF pp. 15–16: "F_n(π)=h_n(q(π))A(π)"; this is not used to define the actual reward expectation. -/
def averageObjective (E : Experiment Ω C n) (m π : C → ℝ) : ℝ :=
  emptyFactor n (E.q π) * E.A m π

/-- Appendix B.3, PDF p. 15: conditioning on "Xᵢ". -/
def covariateSigma (E : Experiment Ω C n) (i : Fin n) : MeasurableSpace Ω :=
  MeasurableSpace.comap (E.X i) inferInstance

/-- Corrected ATT hypothesis (T2): conditioning on the full "X,T^π" vectors. -/
def vectorSigma (E : Experiment Ω C n) (π : C → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => ((fun i => E.X i ω), (fun i => E.T π i ω)))
    inferInstance

end Experiment

/-- Standing assumptions of Section 2 (PDF p. 3), strong ignorability in
Appendix B.3 (p. 15), and the i.i.d./independent treatment assumptions.
The potential-outcome population law is fixed across policies.
The indicator conditional-moment identity expresses full binary-treatment
conditional independence from the potential-outcome pair, not merely equality
of its mean. Explicit integrability prevents Lean's zero-valued integral of a
nonintegrable function from being mistaken for an expectation. -/
structure Standing {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) : Prop where
  px_probability : IsProbabilityMeasure E.PX
  means_measurable : Measurable E.μ0 ∧ Measurable E.μ1
  means_integrable : Integrable E.μ0 E.PX ∧ Integrable E.μ1 E.PX
  law_probability : ∀ π, Admissible π → IsProbabilityMeasure (E.law π)
  measurable_units : ∀ π, Admissible π → ∀ i,
    Measurable (E.X i) ∧ Measurable (E.Y0 i) ∧ Measurable (E.Y1 i) ∧
    Measurable (E.T π i)
  integrable_units : ∀ π, Admissible π → ∀ i,
    Integrable (E.Y0 i) (E.law π) ∧ Integrable (E.Y1 i) (E.law π) ∧
    Integrable (fun ω => E.μhat π ω (E.X i ω)) (E.law π)
  covariate_law : ∀ π, Admissible π → ∀ i,
    IdentDistrib (E.X i) (fun x : C => x) (E.law π) E.PX
  potential_law_fixed : ∀ π π', Admissible π → Admissible π' → ∀ i,
    IdentDistrib (fun ω => (E.X i ω,E.Y0 i ω,E.Y1 i ω))
      (fun ω => (E.X i ω,E.Y0 i ω,E.Y1 i ω)) (E.law π) (E.law π')
  iid_independent : ∀ π, Admissible π →
    iIndepFun (fun i ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω)) (E.law π)
  iid_identical : ∀ π, Admissible π → ∀ i j,
    IdentDistrib (fun ω => (E.X i ω, E.Y0 i ω, E.Y1 i ω, E.T π i ω))
      (fun ω => (E.X j ω, E.Y0 j ω, E.Y1 j ω, E.T π j ω)) (E.law π) (E.law π)
  conditional_means : ∀ π, Admissible π → ∀ i,
    (E.law π)[E.Y0 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ0 (E.X i ω)) ∧
    (E.law π)[E.Y1 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ1 (E.X i ω))
  bernoulli : ∀ π, Admissible π → ∀ i,
    (E.law π)[(fun ω => bit (E.T π i ω)) | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => π (E.X i ω))
  ignorability : ∀ π, Admissible π → ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
    (E.law π)[(fun ω => bit (E.T π i ω) *
      B.indicator (fun _ => (1 : ℝ)) (E.Y0 i ω, E.Y1 i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) *
        (E.law π)[(fun η => B.indicator (fun _ => (1 : ℝ))
          (E.Y0 i η, E.Y1 i η)) | E.covariateSigma i] ω)

/-- Assumption 1, PDF p. 4: "E[μ̂₀(x)]=μ₀(x) ∀x". This is deliberately
separate from unbiasedness at the random evaluation covariate. -/
def PointwiseUnbiased {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) : Prop :=
  ∀ π ∈ PiSet, ∀ x, Integrable (fun ω => E.μhat π ω x) (E.law π) ∧
    (∫ ω, E.μhat π ω x ∂E.law π) = E.μ0 x

/-- Corrected Assumption 1′ (T6/T8): "E[Tᵢ^π(μ̂₀(Xᵢ)−μ₀(Xᵢ))|Xᵢ]=0",
with C=X×U when information is asymmetric. The `baseline` is μ₀(X), not
μ₀(X,U), in the private-information model. -/
def TreatedUnbiased {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (baseline : C → ℝ) (PiSet : Set (C → ℝ)) : Prop :=
  ∀ π ∈ PiSet, ∀ i,
    (E.law π)[(fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - baseline (E.X i ω))) | E.covariateSigma i]
      =ᵐ[E.law π] (fun _ => (0 : ℝ))

/-- Corrected average-reward hypothesis (T2):
"E[μ̂₀(Xᵢ)|X,T^π]=μ₀(Xᵢ)" for every unit. -/
def VectorUnbiased {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) : Prop :=
  ∀ π ∈ PiSet, ∀ i,
    (E.law π)[(fun ω => E.μhat π ω (E.X i ω)) | E.vectorSigma π]
      =ᵐ[E.law π] (fun ω => E.μ0 (E.X i ω))

/-- Concrete binary-covariate examples (T1, T4, T5, T18, T25), with
π=(u,v). False denotes 0 and true denotes 1. -/
abbrev BinaryPolicy := ℝ × ℝ

/-- Section 2, PDF p. 3: "π : X → [0,1]" specialized to the two-point support; the two real coordinates are π(0),π(1). -/
def binaryRule (p : BinaryPolicy) : Bool → ℝ := fun x => if x then p.2 else p.1

/-- Propositions 6–7, PDF pp. 15–16: "all functions π:X→[0,1]" on two points, represented by the closed unit square. -/
def binaryFeasible (p : BinaryPolicy) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

/-- Section 2, PDF p. 3: the "set of possible treatment rules Π" specialized to the unconstrained two-point support. -/
def binaryPolicies : Set BinaryPolicy := {p | binaryFeasible p}

/-- Section 2, PDF p. 3: "π(Xᵢ)=P(Tᵢ^π=1|Xᵢ)".
These are the two exact Bernoulli masses; all policies below range over the
whole real square [0,1]², not a probability grid. -/
def coinMass (q : ℝ) (t : Bool) : ℝ := if t then q else 1 - q

/-- Exact two-unit i.i.d. reward expectation (T1/T18).
Covariates have P(X=1)=p; conditional treatment coins multiply independently.
Potential treated outcomes are the deterministic function m. The observed
outcome on an untreated unit is irrelevant to ATO because it is multiplied by
T. Both the covariate and treatment sums enumerate all 16 states. -/
def twoATO (p : ℝ) (m : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ x0 : Bool, ∑ x1 : Bool, ∑ t0 : Bool, ∑ t1 : Bool,
    coinMass p x0 * coinMass p x1 *
      coinMass (binaryRule π x0) t0 * coinMass (binaryRule π x1) t1 *
      wATO ![t0, t1] ![m x0, m x1]

/-- Exact one-unit TT/ATT expectation (T4/T5).
The baseline is a random function `est observedCovariate queryCovariate`.
The treatment coin is independent given the observed covariate. -/
def oneTT (y1 : Bool → ℝ) (est : Bool → Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ x : Bool, ∑ t : Bool,
    (1 / 2 : ℝ) * coinMass (binaryRule π x) t *
      wTT (est x) ![x] ![t] ![y1 x]

/-- Section 2, PDF p. 3; Lemma 1, p. 16: binary weighted-sum welfare
"E[π(X)τ(X)]", with P(X=1)=p. -/
def binaryWelfare (p : ℝ) (τ : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  (1 - p) * π.1 * τ false + p * π.2 * τ true

/-- Finite probability certificate used in all binary counterexamples:
each treatment mass is nonnegative and the two masses sum to one. -/
theorem coin_is_probability (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    (∀ t, 0 ≤ coinMass q t) ∧ (∑ t : Bool, coinMass q t) = 1 := by
  constructor
  · intro t; cases t <;> simp [coinMass] <;> linarith [hq.1, hq.2]
  · simp [coinMass, Fintype.sum_bool]

/-- The exact two-unit treatment count (Reward Functions 1–4, pp. 4–6). -/
theorem treatedCount_two (t0 t1 : Bool) :
    treatedCount ![t0,t1] = bit t0 + bit t1 := by
  unfold treatedCount
  rw [Fin.sum_univ_two]
  rfl

/-- All four treatment realizations of the paper's two-unit ATO reward. -/
theorem wATO_two (t0 t1 : Bool) (y0 y1 : ℝ) :
    wATO ![t0,t1] ![y0,y1] =
      if t0 then (if t1 then (y0+y1)/2 else y0) else (if t1 then y1 else 0) := by
  unfold wATO
  rw [treatedCount_two, Fin.sum_univ_two]
  cases t0 <;> cases t1 <;> norm_num [bit]

/-- The exact two-unit expectation in T1/T18, obtained by finite enumeration. -/
theorem twoATO_formula (p m0 m1 : ℝ) (π : BinaryPolicy) :
    twoATO p (fun x => if x then m1 else m0) π =
      (2 - ((1-p)*π.1+p*π.2)) * ((1-p)*m0*π.1+p*m1*π.2) := by
  simp [twoATO, coinMass, binaryRule, wATO_two, Fintype.sum_bool]
  ring

/-- T1: the paper's two positive conditional effects, 9/10 and 1. -/
def effectE001 (x : Bool) : ℝ := if x then 1 else 9/10

/-- T1: the exact zero-on-empty ATO/ATT objective for n=2. -/
def rewardE001 (π : BinaryPolicy) : ℝ := twoATO (1/2) effectE001 π

/-- T1: the polynomial objective F₂(u,v). -/
theorem rewardE001_formula (π : BinaryPolicy) :
    rewardE001 π = (9*π.1+10*π.2)*(4-π.1-π.2)/40 := by
  unfold rewardE001 effectE001
  rw [twoATO_formula]
  ring

/-- P006-T1 (Propositions 6–7, PDF pp. 15–16), concrete counterexample.
The printed rule is (0,1); treat-all earns 19/20 rather than 3/4.
The exact unique stochastic best response is (17/18,1), whose regret is 1/40.
All comparisons are over the full feasible square. μ₀=μ̂₀=0, so ATO=ATT
and conditional as well as pointwise estimator unbiasedness holds. -/
theorem T1_average_counterexample :
    (∀ x, printedAverageRule effectE001 x = binaryRule (0,1) x) ∧
    rewardE001 (0,1) = 3/4 ∧ rewardE001 (1,1) = 19/20 ∧
    rewardE001 (0,1) < rewardE001 (1,1) ∧
    (∀ π ∈ binaryPolicies, rewardE001 π ≤ rewardE001 (17/18,1)) ∧
    (∀ π ∈ binaryPolicies, rewardE001 π = rewardE001 (17/18,1) ↔ π = (17/18,1)) ∧
    rewardE001 (17/18,1) = 1369/1440 ∧
    IsBest binaryPolicies (binaryWelfare (1/2) effectE001) (1,1) ∧
    binaryWelfare (1/2) effectE001 (1,1) -
      binaryWelfare (1/2) effectE001 (17/18,1) = 1/40 ∧
    binaryWelfare (1/2) effectE001 (1,1) -
      binaryWelfare (1/2) effectE001 (0,1) = 9/20 := by
  have formula := rewardE001_formula
  have gap (π : BinaryPolicy) :
      1369/1440 - rewardE001 π =
        (9/40)*(π.1-17/18)^2 + (1-π.2)*(30-19*π.1-10*π.2)/40 := by
    rw [formula]; ring
  have nonneg (π : BinaryPolicy) (hπ : binaryFeasible π) :
      0 ≤ (1-π.2)*(30-19*π.1-10*π.2) := by
    rcases hπ with ⟨h0,h0u,h1,h1u⟩
    exact mul_nonneg (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; cases x <;> norm_num [printedAverageRule, effectE001, binaryRule]
  · rw [formula]; norm_num
  · rw [formula]; norm_num
  · rw [formula, formula]; norm_num
  · intro π hπ
    have hn := nonneg π hπ
    have hs := sq_nonneg (π.1-17/18)
    rw [formula (17/18,1)]; norm_num
    nlinarith [gap π]
  · intro π hπ
    constructor
    · intro heq
      have hval : rewardE001 (17/18,1) = 1369/1440 := by rw [formula]; norm_num
      have hn := nonneg π hπ
      have hs := sq_nonneg (π.1-17/18)
      have he : (9/40)*(π.1-17/18)^2 +
          (1-π.2)*(30-19*π.1-10*π.2)/40 = 0 := by linarith [gap π]
      have h0 : π.1 = 17/18 := by nlinarith
      rcases hπ with ⟨hp0,hp0u,hp1,hp1u⟩
      have h1 : π.2 = 1 := by rw [h0] at he; nlinarith
      exact Prod.ext h0 h1
    · intro h; rw [h]
  · rw [formula]; norm_num
  · refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ
    rcases hπ with ⟨h0,h0u,h1,h1u⟩
    dsimp [binaryWelfare, effectE001]; nlinarith
  · norm_num [binaryWelfare, effectE001]
  · norm_num [binaryWelfare, effectE001]

/-- A witnessed maximum equals the supremum used in the paper's regret.
Section 2, PDF p. 3. This lemma does not assume an unproved limit theorem. -/
theorem bestValue_eq {P : Type*} {PiSet : Set P} {f : P → ℝ} {π : P}
    (h : IsBest PiSet f π) : bestValue PiSet f = f π := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨π, h.1, rfl⟩, ?_⟩
  rintro y ⟨q, hq, rfl⟩
  exact h.2 q hq

/-- Exact one-unit TT expectation (Reward Function 3, PDF p. 5).
The same equality holds for ATT when n=1. -/
theorem oneTT_formula (y1 : Bool → ℝ) (est : Bool → Bool → ℝ)
    (π : BinaryPolicy) :
    oneTT y1 est π =
      (π.1*(y1 false-est false false)+π.2*(y1 true-est true true))/2 := by
  simp [oneTT, wTT, wWeightedTT, bit, coinMass, binaryRule,
    Fintype.sum_bool, Fin.sum_univ_one]
  ring

/-- T4, estimator of witness A (P006-E002): 2·1(x=X₁)−1.
The argument order is observed covariate, then queried covariate. -/
def estA (s x : Bool) : ℝ := if x = s then 1 else -1

/-- T4, estimator of witness B (P006-E002): 1−2·1(x=X₁). -/
def estB (s x : Bool) : ℝ := -estA s x

/-- T4: pointwise means of the random estimator under fair X. -/
def fixedEstimatorMean (est : Bool → Bool → ℝ) (x : Bool) : ℝ :=
  ∑ s : Bool, (1/2 : ℝ) * est s x

/-- T4: μ₀=0 and μ₁=τ=±1/2, with fair binary covariates. -/
def welfareA (π : BinaryPolicy) : ℝ :=
  binaryWelfare (1/2) (fun _ => 1/2) π

/-- Section 2, PDF p. 3: "V(π)" for T4 witness B; μ0=0 and τ=−1/2 on the fair two-point covariate law. -/
def welfareB (π : BinaryPolicy) : ℝ :=
  binaryWelfare (1/2) (fun _ => -1/2) π

/-- T4: the actual unconditional TT reward under witnesses A and B. -/
def rewardA (π : BinaryPolicy) : ℝ := oneTT (fun _ => 1/2) estA π

/-- Reward Function 3, PDF p. 5: "E[w_TT]" for T4 witness B, using the actual finite random-estimator and treatment sum. -/
def rewardB (π : BinaryPolicy) : ℝ := oneTT (fun _ => -1/2) estB π

/-- T4: all four exact linear functionals, retaining the random baseline. -/
theorem witnesses_AB_formula (π : BinaryPolicy) :
    rewardA π = -(π.1+π.2)/4 ∧ welfareA π = (π.1+π.2)/4 ∧
    rewardB π = (π.1+π.2)/4 ∧ welfareB π = -(π.1+π.2)/4 := by
  rw [rewardA, rewardB, oneTT_formula, oneTT_formula]
  simp [estA, estB, welfareA, welfareB, binaryWelfare]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- P006-T4 (Assumption 1, PDF p. 4; Propositions 2,3,7,9 and Theorems 1,3).
Both estimators are pointwise unbiased but take values ±1 at their evaluation
point. All policies and all hypotheses are certified by exact Bernoulli sums.
Witness A uniquely treats nobody, with regret 1/2 although γ_marg=0.
Witness B uniquely treats everybody with welfare −1/2 and maximum welfare 0. -/
theorem T4_unbiasedness_counterexamples :
    (∀ x, fixedEstimatorMean estA x = 0 ∧ fixedEstimatorMean estB x = 0) ∧
    (∀ x, estA x x = 1 ∧ estB x x = -1) ∧
    IsBest binaryPolicies rewardA (0,0) ∧
    (∀ π ∈ binaryPolicies, rewardA π = rewardA (0,0) ↔ π = (0,0)) ∧
    IsBest binaryPolicies welfareA (1,1) ∧
    regret binaryPolicies welfareA (0,0) = 1/2 ∧
    rewardA (1,1) ≠ welfareA (1,1) ∧
    IsBest binaryPolicies rewardB (1,1) ∧
    (∀ π ∈ binaryPolicies, rewardB π = rewardB (1,1) ↔ π = (1,1)) ∧
    IsBest binaryPolicies welfareB (0,0) ∧
    regret binaryPolicies welfareB (1,1) = 1/2 ∧
    bestValue binaryPolicies welfareB = 0 := by
  have forms := witnesses_AB_formula
  have bestA : IsBest binaryPolicies rewardA (0,0) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ
    rcases hπ with ⟨h0,h0u,h1,h1u⟩
    rw [(forms π).1, (forms (0,0)).1]; dsimp; linarith
  have optA : IsBest binaryPolicies welfareA (1,1) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ
    rcases hπ with ⟨h0,h0u,h1,h1u⟩
    rw [(forms π).2.1, (forms (1,1)).2.1]; dsimp; linarith
  have bestB : IsBest binaryPolicies rewardB (1,1) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ
    rcases hπ with ⟨h0,h0u,h1,h1u⟩
    rw [(forms π).2.2.1, (forms (1,1)).2.2.1]; dsimp; linarith
  have optB : IsBest binaryPolicies welfareB (0,0) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ
    rcases hπ with ⟨h0,h0u,h1,h1u⟩
    rw [(forms π).2.2.2, (forms (0,0)).2.2.2]; dsimp; linarith
  refine ⟨?_, ?_, bestA, ?_, optA, ?_, ?_, bestB, ?_, optB, ?_, ?_⟩
  · intro x; cases x <;> norm_num [fixedEstimatorMean, estA, estB, Fintype.sum_bool]
  · intro x; simp [estA, estB]
  · intro π hπ; constructor
    · intro he
      rcases hπ with ⟨h0,h0u,h1,h1u⟩
      rw [(forms π).1, (forms (0,0)).1] at he
      exact Prod.ext (by dsimp at he; linarith) (by dsimp at he; linarith)
    · rintro rfl; rfl
  · rw [regret, bestValue_eq optA]
    norm_num [welfareA, binaryWelfare]
  · rw [(forms (1,1)).1, (forms (1,1)).2.1]; norm_num
  · intro π hπ; constructor
    · intro he
      rcases hπ with ⟨h0,h0u,h1,h1u⟩
      rw [(forms π).2.2.1, (forms (1,1)).2.2.1] at he
      exact Prod.ext (by dsimp at he; linarith) (by dsimp at he; linarith)
    · rintro rfl; rfl
  · rw [regret, bestValue_eq optB]
    norm_num [welfareB, binaryWelfare]
  · rw [bestValue_eq optB]; norm_num [welfareB, binaryWelfare]

/-- T5: the shared estimator 1(x=Xʲ)−1(x=Xᵏ) (P006-E002).
The two observed covariates are independent fair Bernoulli draws. -/
def sharedEst (xj xk x : Bool) : ℝ := (if x = xj then 1 else 0) -
  (if x = xk then 1 else 0)

/-- T5: agent-specific expected scores, each using its own covariate and outcome.
Both normalized RN weights are one, and both sample sizes are one. -/
def scoreJ (π : BinaryPolicy) : ℝ :=
  ∑ xj : Bool, ∑ xk : Bool, ∑ t : Bool,
    (1/4 : ℝ) * coinMass (binaryRule π xj) t *
      wTT (sharedEst xj xk) ![xj] ![t] ![1/4]

/-- Section 4, PDF p. 5 and Theorem 2, p. 6: agent k's own expected weighted TT score in T5's shared-estimator counterexample. -/
def scoreK (π : BinaryPolicy) : ℝ :=
  ∑ xj : Bool, ∑ xk : Bool, ∑ t : Bool,
    (1/4 : ℝ) * coinMass (binaryRule π xk) t *
      wTT (sharedEst xj xk) ![xk] ![t] ![1/8]

/-- T5: exact expected scores from all joint sample and treatment states. -/
theorem ranking_witness_formula (π : BinaryPolicy) :
    scoreJ π = -(π.1+π.2)/8 ∧ scoreK π = 5*(π.1+π.2)/16 := by
  simp [scoreJ, scoreK, sharedEst, wTT, wWeightedTT, bit, binaryRule,
    coinMass, Fintype.sum_bool, Fin.sum_univ_one]
  constructor <;> ring

/-- P006-T5 (Theorem 2, PDF pp. 6,20), concrete ranking counterexample.
Pointwise unbiasedness and identical covariate/reference distributions hold.
Agent j's effects 1/4 exceed agent k's 1/8 everywhere and in reference mean,
but their maximum scores are 0 and 5/8. -/
theorem T5_ranking_counterexample :
    (∀ x, (∑ xj : Bool, ∑ xk : Bool, (1/4 : ℝ)*sharedEst xj xk x) = 0) ∧
    (∀ xj, (∑ xk : Bool, (1/2 : ℝ)*sharedEst xj xk xj) = 1/2) ∧
    (∀ xk, (∑ xj : Bool, (1/2 : ℝ)*sharedEst xj xk xk) = -1/2) ∧
    IsBest binaryPolicies scoreJ (0,0) ∧ IsBest binaryPolicies scoreK (1,1) ∧
    bestValue binaryPolicies scoreJ = 0 ∧ bestValue binaryPolicies scoreK = 5/8 ∧
    bestValue binaryPolicies scoreJ < bestValue binaryPolicies scoreK ∧
    (1/8 : ℝ) ≤ 1/4 := by
  have forms := ranking_witness_formula
  have hj : IsBest binaryPolicies scoreJ (0,0) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ; rcases hπ with ⟨h0,h0u,h1,h1u⟩
    rw [(forms π).1, (forms (0,0)).1]; dsimp; linarith
  have hk : IsBest binaryPolicies scoreK (1,1) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ; rcases hπ with ⟨h0,h0u,h1,h1u⟩
    rw [(forms π).2, (forms (1,1)).2]; dsimp; linarith
  have hvj : bestValue binaryPolicies scoreJ = 0 := by
    rw [bestValue_eq hj, (forms (0,0)).1]; norm_num
  have hvk : bestValue binaryPolicies scoreK = 5/8 := by
    rw [bestValue_eq hk, (forms (1,1)).2]; norm_num
  refine ⟨?_, ?_, ?_, hj, hk, hvj, hvk, ?_, by norm_num⟩
  · intro x; cases x <;> norm_num [sharedEst, Fintype.sum_bool]
  · intro xj; cases xj <;> norm_num [sharedEst, Fintype.sum_bool]
  · intro xk; cases xk <;> norm_num [sharedEst, Fintype.sum_bool]
  · rw [hvj, hvk]; norm_num

/-- Proposition 1's family, PDF p. 17: μ₁(0)=0, μ₁(1)=1. -/
def outcomeP1 (x : Bool) : ℝ := if x then 1 else 0

/-- Proposition 1, second failure mode: μ₀=(-1,β), so τ=(1,1−β). -/
def effectP1 (β : ℝ) (x : Bool) : ℝ := if x then 1-β else 1

/-- Exact finite-n=2 ATO reward in Proposition 1, without importing its
invalid general best-response characterization. -/
def rewardP1 (p : ℝ) (π : BinaryPolicy) : ℝ := twoATO p outcomeP1 π

/-- Proposition 1's n=2 family has a best response (0,1). -/
theorem rewardP1_best (p : ℝ) (hp : 0 < p ∧ p < 1) :
    IsBest binaryPolicies (rewardP1 p) (0,1) := by
  refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
  intro π hπ
  rcases hπ with ⟨h0,h0u,h1,h1u⟩
  have hmul : 0 ≤ (1-p)*π.1*(p*π.2) :=
    mul_nonneg (mul_nonneg (by linarith) h0) (mul_nonneg hp.1.le h1)
  have hx : p*π.2 ≤ p := by nlinarith [hp.1]
  have hl : 0 ≤ p*π.2 := mul_nonneg hp.1.le h1
  have hid : p*(2-p) - (p*π.2)*(2-p*π.2) =
      (p-p*π.2)*(2-p-p*π.2) := by ring
  have hgap : 0 ≤ (p-p*π.2)*(2-p-p*π.2) :=
    mul_nonneg (by linarith) (by linarith [hp.2])
  unfold rewardP1 outcomeP1
  rw [twoATO_formula, twoATO_formula]
  dsimp
  nlinarith

/-- P006-T18 (Proposition 1 proof, PDF p. 17), exact sign-error counterexample.
With p=1/2, β=4, n=2 the actual best-response regret is 2.
The printed value 1−pβ is −1. -/
theorem T18_regret_sign_counterexample :
    IsBest binaryPolicies (rewardP1 (1/2)) (0,1) ∧
    rewardP1 (1/2) (0,1) = 3/4 ∧
    IsBest binaryPolicies (binaryWelfare (1/2) (effectP1 4)) (1,0) ∧
    regret binaryPolicies (binaryWelfare (1/2) (effectP1 4)) (0,1) = 2 ∧
    (1 - (1/2 : ℝ)*4) = -1 ∧ (2 : ℝ) ≠ -1 := by
  have hw : IsBest binaryPolicies (binaryWelfare (1/2) (effectP1 4)) (1,0) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ; rcases hπ with ⟨h0,h0u,h1,h1u⟩
    dsimp [binaryWelfare, effectP1]; linarith
  refine ⟨rewardP1_best _ (by norm_num), ?_, hw, ?_, by norm_num, by norm_num⟩
  · unfold rewardP1 outcomeP1; rw [twoATO_formula]; norm_num
  · rw [regret, bestValue_eq hw]; norm_num [binaryWelfare, effectP1]

/-- P006-T19 (corrected Proposition 1 proof, PDF p. 17).
For 0<p<1 and β>1, the welfare optimum treats only covariate 0,
and the regret of (0,1) is 1−2p+pβ, exceeding 1−pβ by 2p(β−1).
The n=2 best response is established above. -/
theorem T19_corrected_regret (p β : ℝ) (hp : 0 < p ∧ p < 1) (hβ : 1 < β) :
    IsBest binaryPolicies (binaryWelfare p (effectP1 β)) (1,0) ∧
    bestValue binaryPolicies (binaryWelfare p (effectP1 β)) = 1-p ∧
    binaryWelfare p (effectP1 β) (0,1) = p*(1-β) ∧
    regret binaryPolicies (binaryWelfare p (effectP1 β)) (0,1) = 1-2*p+p*β ∧
    (1-2*p+p*β) - (1-p*β) = 2*p*(β-1) ∧ 0 < 2*p*(β-1) := by
  have hw : IsBest binaryPolicies (binaryWelfare p (effectP1 β)) (1,0) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ; rcases hπ with ⟨h0,h0u,h1,h1u⟩
    have hm0 : (1-p)*π.1 ≤ 1-p := by nlinarith [hp.2]
    have hm1 : p*π.2*(1-β) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hp.1.le h1) (by linarith)
    dsimp [binaryWelfare, effectP1]; linarith
  refine ⟨hw, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bestValue_eq hw]; simp [binaryWelfare, effectP1]
  · simp [binaryWelfare, effectP1]
  · rw [regret, bestValue_eq hw]; dsimp [binaryWelfare, effectP1]; ring
  · ring
  · exact mul_pos (mul_pos (by norm_num) hp.1) (by linarith)

/-- T19(iv), PDF p. 17: corrected regret tends to +∞ as β→+∞.
The limit is stated as a filter limit and not reduced to a numeric example. -/
theorem T19_corrected_regret_tendsto (p : ℝ) (hp : 0 < p) :
    Tendsto (fun β : ℝ => 1-2*p+p*β) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  filter_upwards [eventually_ge_atTop ((M-1+2*p)/p)] with β hβ
  have hmul := (div_le_iff₀ hp).mp hβ
  linarith

/-- P006-T29, headline Proposition 1 (PDF pp. 4,17): ATO regret may be
arbitrarily large. For every M>0 the explicit n=2, p=1/2 family has
μ₀(0)=−2(M+1), μ₀(1)=0, and a genuine best response with regret M+1.
This proves the existential printed headline, not only growth of a formula. -/
theorem T29_ato_unbounded (M : ℝ) (hM : 0 < M) :
    ∃ α : ℝ, α < 0 ∧
      IsBest binaryPolicies (rewardP1 (1/2)) (0,1) ∧
      IsBest binaryPolicies
        (binaryWelfare (1/2) (fun x => if x then 1 else -α)) (1,1) ∧
      M < regret binaryPolicies
        (binaryWelfare (1/2) (fun x => if x then 1 else -α)) (0,1) := by
  let α := -2*(M+1)
  have hα : α < 0 := by dsimp [α]; linarith
  have hw : IsBest binaryPolicies
      (binaryWelfare (1/2) (fun x => if x then 1 else -α)) (1,1) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ; rcases hπ with ⟨h0,h0u,h1,h1u⟩
    have hmul : (-α)*π.1 ≤ -α := by nlinarith
    dsimp [binaryWelfare]; nlinarith
  refine ⟨α, hα, rewardP1_best _ (by norm_num), hw, ?_⟩
  rw [regret, bestValue_eq hw]
  dsimp [binaryWelfare, α]; linarith

/-- Conditional mean on an event of positive probability, used for N>0 in T2
and the observation indicators in Appendix A.1. This is a normalized restricted
integral; every statistical use below includes positivity. -/
def eventMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) (f : Ω → ℝ) : ℝ :=
  (∫ ω in s, f ω ∂μ) / (μ s).toReal


/-- Finite-support objects in T2(iii): pⱼ>0, Σpⱼ=1 and m₁≥⋯≥m_K.
Lean uses indices 0,…,K−1. All stochastic policies remain allowed. -/
def finitePolicies {K : ℕ} : Set (Fin K → ℝ) :=
  {π | ∀ i, 0 ≤ π i ∧ π i ≤ 1}

/-- Corrected Propositions 6–7 (T2), PDF pp. 15–16: "q(π)=Σ_j p_j π_j" on a finite support. -/
def finiteMass {K : ℕ} (p π : Fin K → ℝ) : ℝ := ∑ i, p i * π i

/-- Corrected Propositions 6–7 (T2), PDF pp. 15–16: "A(π)=Σ_j p_j m_j π_j" on a finite support; reused for finite welfare and weighted gain. -/
def finiteA {K : ℕ} (p m π : Fin K → ℝ) : ℝ := ∑ i, p i * m i * π i

/-- T2(iii): "Q_{j−1}=Σ_{ℓ<j}p_ℓ", "B_{j−1}=Σ_{ℓ<j}p_ℓm_ℓ". -/
def prefixMass {K : ℕ} (p : Fin K → ℝ) (j : Fin K) : ℝ :=
  ∑ i, if i < j then p i else 0

/-- Corrected Propositions 6–7 (T2), PDF pp. 15–16: "B_{j-1}=Σ_{ℓ<j}p_ℓ m_ℓ" with zero-based Fin indices. -/
def prefixA {K : ℕ} (p m : Fin K → ℝ) (j : Fin K) : ℝ :=
  ∑ i, if i < j then p i * m i else 0

/-- T2(iii), corrected finite-n best response: treat every score above the
boundary, randomize at the boundary, treat none below it. -/
def thresholdRule {K : ℕ} (p : Fin K → ℝ) (j : Fin K) (q : ℝ) : Fin K → ℝ :=
  fun i => if i < j then 1 else if i = j then (q-prefixMass p j)/p j else 0

/-- T2(iv): the population conditional-average objective maximized by the
printed rule, which differs from the printed finite-n sample reward. -/
def finiteConditionalAverage {K : ℕ} (p m π : Fin K → ℝ) : ℝ :=
  if 0 < finiteMass p π then finiteA p m π / finiteMass p π else 0


/-- T2(iv): with total sample size `n = 1`, the finite-sample objective is `A(π)`.
This is an exact finite lemma, not a replacement for the general theorem. -/
theorem T2_one_unit_factor (q A : ℝ) : emptyFactor 1 q * A = A := by
  simp [emptyFactor]

/-- T3(i): hₙ(q)≥1 for n≥1 and q∈[0,1]. -/
theorem emptyFactor_ge_one (n : ℕ) (hn : 0 < n) (q : ℝ)
    (hq : 0 ≤ q ∧ q ≤ 1) : 1 ≤ emptyFactor n q := by
  have hnon : ∀ j ∈ Finset.range n, 0 ≤ (1-q)^j := by
    intro j hj; exact pow_nonneg (by linarith [hq.2]) _
  have h := Finset.single_le_sum hnon (Finset.mem_range.mpr hn)
  simpa [emptyFactor] using h

/-- The exact decision argument replacing Proposition 2's printed proof
(PDF pp. 17–18): a feasible zero policy and a positive multiplier force
nonnegative best-response welfare and regret at most the welfare maximum. -/
theorem positive_factor_regret {P : Type*} (PiSet : Set P) (V h : P → ℝ)
    (z b s : P) (hz : z ∈ PiSet) (hVz : V z = 0)
    (hh : ∀ π ∈ PiSet, 1 ≤ h π)
    (hb : IsBest PiSet (fun π => h π * V π) b) (hs : IsBest PiSet V s) :
    0 ≤ V b ∧ regret PiSet V b ≤ bestValue PiSet V := by
  have hc := hb.2 z hz
  change h z * V z ≤ h b * V b at hc
  rw [hVz, mul_zero] at hc
  have hpos : 0 < h b := lt_of_lt_of_le zero_lt_one (hh b hb.1)
  have hV : 0 ≤ V b := by nlinarith
  exact ⟨hV, by dsimp [regret]; linarith⟩


/-- A random-function estimator independent of the evaluation design,
as in the sufficient implementation in T6(iv), Appendix D.2, PDF p. 21.
The estimator is a jointly measurable function of auxiliary randomness Z
and the query x, with Z independent of the full (X,T) vectors. This gives
the paper's auxiliary-data implementation and retains random evaluation. -/
def IndependentEstimator {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) : Prop :=
  ∃ (A : Type) (mA : MeasurableSpace A),
    letI : MeasurableSpace A := mA
    ∃ (Z : Ω → A) (f : (C → ℝ) → A → C → ℝ),
      Measurable Z ∧
      ∀ π ∈ PiSet, Measurable (fun z : A × C => f π z.1 z.2) ∧
        (∀ ω x, E.μhat π ω x = f π (Z ω) x) ∧
        IndepFun Z (fun ω => ((fun i => E.X i ω), (fun i => E.T π i ω))) (E.law π)


/-- Section 5, PDF p. 6: "μ₀(X)=E[μ₀(X,U)|X]".
C=X×U is the agent's covariate, and b₀ is the principal's baseline using
only X. This condition preserves the paper's marginal estimand. -/
def MarginalBaseline {Ω X U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (b0 : X → ℝ) : Prop :=
  Measurable b0 ∧ Integrable (fun c => b0 c.1) E.PX ∧
    ∀ π, Admissible π → ∀ i,
      (E.law π)[(fun ω => E.μ0 (E.X i ω)) |
        MeasurableSpace.comap (fun ω => (E.X i ω).1) inferInstance]
        =ᵐ[E.law π] (fun ω => b0 (E.X i ω).1)

/-- Section 5, PDF p. 6: the principal's reward "does not depend on Uᵢ".
The estimator is the same at (x,u) and (x,u′), for every realization. -/
def EstimatorUsesOnlyX {Ω X U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) : Prop :=
  ∀ π ω x u u', E.μhat π ω (x,u) = E.μhat π ω (x,u')

/-- Assumption 2, PDF p. 6: "E[|μ₀(X)−μ₀(X,U)|]≤γ_marg". -/
def marginalHeterogeneity {Ω X U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (b0 : X → ℝ) : ℝ :=
  ∫ c, |b0 c.1-E.μ0 c| ∂E.PX

/-- Appendix D.2, PDF p. 21: "V̂(π)=(1/n)E[w_TT]". -/
def normalizedTT {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  E.expectedTT π / n

/-- The decision inequality in Proposition 10 and Theorems 3 and 5,
PDF pp. 21–24: a uniform error bound γ between the expected normalized score
and welfare implies best-response regret ≤2γ. -/
theorem uniform_error_regret {P : Type*} (PiSet : Set P) (S V : P → ℝ)
    (b s : P) (hb : IsBest PiSet S b) (hs : IsBest PiSet V s) (γ : ℝ)
    (herror : ∀ π ∈ PiSet, |S π-V π| ≤ γ) :
    regret PiSet V b ≤ 2*γ := by
  have hbs := hb.2 s hs.1
  have hse := (abs_le.mp (herror s hs.1)).1
  have hbe := (abs_le.mp (herror b hb.1)).2
  rw [regret, bestValue_eq hs]
  linarith


/-- Conditional mean independence of the estimator from the treatment coin,
needed by the second term of Lemma 2 (PDF p. 21). This keeps μ̂₀ inside its
expectation; it does not replace it by μ₀. -/
def EstimatorCoinMeanIndependent {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) : Prop :=
  ∀ π ∈ PiSet, ∀ i,
    (E.law π)[(fun ω => bit (E.T π i ω)*E.μhat π ω (E.X i ω)) |
      E.covariateSigma i] =ᵐ[E.law π]
        (fun ω => π (E.X i ω) *
          (E.law π)[(fun η => E.μhat π η (E.X i η)) | E.covariateSigma i] ω)


/-- Definition 1, corrected (T14), PDF p. 5: for all j,k, pointwise dominance
of τʲ over τᵏ implies the same ordering of the agents' maximum own scores.
The callback score j is always evaluated on agent j's experiment. -/
def UniformRankPreservation {K : Type*} {C : Type*}
    (PiSet : K → Set (C → ℝ)) (score : K → (C → ℝ) → ℝ) (τ : K → C → ℝ) : Prop :=
  ∀ j k, (∀ x, τ k x ≤ τ j x) →
    bestValue (PiSet k) (score k) ≤ bestValue (PiSet j) (score j)

/-- Definition 2, corrected (T14), PDF p. 5: reference-population mean
dominance implies the same ordering of the maximum own scores. -/
def RelativeRankPreservation {K C : Type*} [MeasurableSpace C]
    (P0 : Measure C) (PiSet : K → Set (C → ℝ)) (score : K → (C → ℝ) → ℝ)
    (τ : K → C → ℝ) : Prop :=
  ∀ j k, (∫ x, τ k x ∂P0) ≤ (∫ x, τ j x ∂P0) →
    bestValue (PiSet k) (score k) ≤ bestValue (PiSet j) (score j)

/-- The positive-part treatment-effect functional in the ranking proofs,
PDF pp. 19–20: "τ(x)1(τ(x)>0)". -/
def positivePart (t : ℝ) : ℝ := t * (if 0 < t then 1 else 0)

/-- The integrand in the corrected inequality of T14 is max(t,0). -/
theorem positivePart_eq_max (t : ℝ) : positivePart t = max t 0 := by
  by_cases ht : 0 < t
  · simp [positivePart, ht, max_eq_left ht.le]
  · simp [positivePart, ht, max_eq_right (le_of_not_gt ht)]

/-- P006-T14(f), corrected implication in Theorem 2's proof (PDF p. 20).
Pointwise dominance of agent j over agent k implies dominance of their
reference-population expected positive treatment effects. Definitions 1–2
and the corrected indexed reward are defined above and reused throughout. -/
theorem T14_corrected_rank_inequality {C : Type*} [MeasurableSpace C]
    (P0 : Measure C) (τj τk : C → ℝ) (horder : ∀ x, τk x ≤ τj x)
    (hj : Integrable (fun x => positivePart (τj x)) P0)
    (hk : Integrable (fun x => positivePart (τk x)) P0) :
    (∫ x, positivePart (τk x) ∂P0) ≤ (∫ x, positivePart (τj x) ∂P0) := by
  apply integral_mono hk hj
  intro x
  change positivePart (τk x) ≤ positivePart (τj x)
  rw [positivePart_eq_max, positivePart_eq_max]
  exact max_le_max (horder x) le_rfl

/-- Theorem 2's corrected normalized derivative (PDF pp. 6,20):
"g_k=(1/n_k)dP_X₀/dP_Xᵏ". The reference is the numerator measure.
Theorem 1's strict positivity is not imposed: the density can vanish. -/
def referenceWeight {C : Type*} [MeasurableSpace C]
    (n : ℕ) (P0 Pk : Measure C) : C → ℝ :=
  fun x => (n : ℝ)⁻¹ * (P0.rnDeriv Pk x).toReal


/-- Exact two-unit TT expectation for the constant-effect agents in
Proposition 4 (PDF pp. 18–19). All covariate and treatment states are summed. -/
def twoTTConstant (π : BinaryPolicy) : ℝ :=
  ∑ x0 : Bool, ∑ x1 : Bool, ∑ t0 : Bool, ∑ t1 : Bool,
    (1/4 : ℝ) * coinMass (binaryRule π x0) t0 *
      coinMass (binaryRule π x1) t1 *
      wTT (fun _ : Bool => 0) ![x0,x1] ![t0,t1] ![1,1]

/-- P006-T30, headline Proposition 4 (PDF pp. 6,18–19).
With μ₀=μ̂₀=0, τʲ=τᵏ=1, identical covariates and reference population,
n_j=1 and n_k=2, the maximum scores are 1<2. Both ordering premises hold,
so both ranking desiderata fail. This is the paper's existential reading. -/
theorem T30_TT_ranking_failure :
    IsBest binaryPolicies (oneTT (fun _ => 1) (fun _ _ => 0)) (1,1) ∧
    IsBest binaryPolicies twoTTConstant (1,1) ∧
    bestValue binaryPolicies (oneTT (fun _ => 1) (fun _ _ => 0)) = 1 ∧
    bestValue binaryPolicies twoTTConstant = 2 ∧
    bestValue binaryPolicies (oneTT (fun _ => 1) (fun _ _ => 0)) <
      bestValue binaryPolicies twoTTConstant ∧
    (∀ x : Bool, (1 : ℝ) ≤ 1) ∧ (1 : ℝ) ≤ 1 := by
  have one (π : BinaryPolicy) :
      oneTT (fun _ => 1) (fun _ _ => 0) π = (π.1+π.2)/2 := by
    rw [oneTT_formula]; ring
  have two (π : BinaryPolicy) : twoTTConstant π = π.1+π.2 := by
    simp [twoTTConstant, coinMass, binaryRule, wTT, wWeightedTT, bit,
      Fintype.sum_bool, Fin.sum_univ_two]
    ring
  have ho : IsBest binaryPolicies (oneTT (fun _ => 1) (fun _ _ => 0)) (1,1) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ; rcases hπ with ⟨h0,h0u,h1,h1u⟩
    rw [one, one]; dsimp; linarith
  have ht : IsBest binaryPolicies twoTTConstant (1,1) := by
    refine ⟨by norm_num [binaryPolicies, binaryFeasible], ?_⟩
    intro π hπ; rcases hπ with ⟨h0,h0u,h1,h1u⟩
    rw [two, two]; dsimp; linarith
  have hvo : bestValue binaryPolicies (oneTT (fun _ => 1) (fun _ _ => 0)) = 1 := by
    rw [bestValue_eq ho, one]; norm_num
  have hvt : bestValue binaryPolicies twoTTConstant = 2 := by
    rw [bestValue_eq ht, two]; norm_num
  exact ⟨ho, ht, hvo, hvt, by rw [hvo,hvt]; norm_num,
    fun _ => le_rfl, le_rfl⟩

/-- Appendix E.2.1, PDF p. 25: "σ(z)=1/(1+e^(−z))". -/
def logistic (z : ℝ) : ℝ := 1/(1+Real.exp (-z))

/-- Appendix E.2.1, PDF p. 25: the fitted linear predictor
"β̂₀+β̂₁ᵀx+β̂₂t+β̂₃ᵀxt". -/
structure LogisticFit (d : ℕ) where
  β0 : ℝ
  β1 : Fin d → ℝ
  β2 : ℝ
  β3 : Fin d → ℝ

/-- Appendix E.2.1, PDF p. 25: "β0+β1ᵀx+β2 t+β3ᵀxt", including the treatment/covariate interaction. -/
def linearPredictor {d : ℕ} (β : LogisticFit d) (x : Fin d → ℝ) (t : Bool) : ℝ :=
  β.β0 + (∑ j, β.β1 j*x j) + β.β2*bit t + (∑ j, β.β3 j*x j*bit t)

/-- Outcome coding in Section 6 and E.2.1, PDF pp. 7,25:
"Y=1 if the horse lived", "Y=−1 if the horse died". -/
def signedOutcome (alive : Bool) : ℝ := if alive then 1 else -1

/-- The conditional mean of a signed Bernoulli outcome, as an exact
two-point probability-weighted sum. -/
def signedBernoulliMean (p : ℝ) : ℝ :=
  ∑ y : Bool, coinMass p y * signedOutcome y

/-- Strict sigmoid bounds, used in T21(iii), PDF p. 25. -/
theorem logistic_bounds (z : ℝ) : 0 < logistic z ∧ logistic z < 1 := by
  have he := Real.exp_pos (-z)
  have hd : 0 < 1+Real.exp (-z) := by linarith
  exact ⟨div_pos zero_lt_one hd, (div_lt_one hd).mpr (by linarith)⟩

/-- The mean of the 1/−1 outcome is 2p−1, Appendix E.2.1, PDF p. 25. -/
theorem signed_mean_formula (p : ℝ) : signedBernoulliMean p = 2*p-1 := by
  simp [signedBernoulliMean, coinMass, signedOutcome, Fintype.sum_bool]
  ring

/-- P006-T21: corrected E.2.1 mean and treatment-effect formula (PDF p. 25).
The logistic survival-probability equation is unchanged. Every real fitted
predictor gives μ_t=2σ(η_t)−1 and τ=2(σ(η₁)−σ(η₀)); σ(η_t) itself is
never this signed conditional mean. The theorem is uniform in fitted
coefficients, covariates and treatment. -/
theorem T21_corrected_logistic_mean {d : ℕ} (β : LogisticFit d) (x : Fin d → ℝ) :
    (∀ t, signedBernoulliMean (logistic (linearPredictor β x t)) =
        2*logistic (linearPredictor β x t)-1) ∧
    signedBernoulliMean (logistic (linearPredictor β x true)) -
      signedBernoulliMean (logistic (linearPredictor β x false)) =
        2*(logistic (linearPredictor β x true)-logistic (linearPredictor β x false)) ∧
    (∀ z : ℝ, 2*logistic z-1 ≠ logistic z) := by
  refine ⟨fun t => signed_mean_formula _, ?_, ?_⟩
  · rw [signed_mean_formula, signed_mean_formula]; ring
  · intro z heq
    have h := (logistic_bounds z).2
    linarith

/-- T20: the exact four-state potential-outcome distribution from P006-E008.
The state (y0,y1) denotes the two survival indicators; X is constant 0. -/
def logisticWitnessMass (y0 y1 : Bool) : ℝ :=
  (1/2 : ℝ) * coinMass (1/4) y1

/-- P006-T20 (E.2.1, PDF p. 25), concrete logistic-mean counterexample.
The joint probabilities are 1/8,3/8,1/8,3/8. The survival probabilities
σ(0)=1/2 and σ(−log 3)=1/4 satisfy the printed logistic model, but the
signed means are 0 and −1/2. The TO treatment decisions consequently differ. -/
theorem T20_logistic_counterexample :
    (∀ y0 y1, 0 ≤ logisticWitnessMass y0 y1) ∧
    (∑ y0 : Bool, ∑ y1 : Bool, logisticWitnessMass y0 y1) = 1 ∧
    (∑ y0 : Bool, ∑ y1 : Bool,
      logisticWitnessMass y0 y1 * bit y0) = 1/2 ∧
    (∑ y0 : Bool, ∑ y1 : Bool,
      logisticWitnessMass y0 y1 * bit y1) = 1/4 ∧
    logistic 0 = 1/2 ∧ logistic (-Real.log 3) = 1/4 ∧
    (∑ y0 : Bool, ∑ y1 : Bool,
      logisticWitnessMass y0 y1 * signedOutcome y0) = 0 ∧
    (∑ y0 : Bool, ∑ y1 : Bool,
      logisticWitnessMass y0 y1 * signedOutcome y1) = -1/2 ∧
    (if 0 < (-1/2 : ℝ) then (1 : ℝ) else 0) = 0 ∧
    (if 0 < logistic (-Real.log 3) then (1 : ℝ) else 0) = 1 := by
  have hlog : logistic (-Real.log 3) = 1/4 := by
    norm_num [logistic, Real.exp_log (by norm_num : (0:ℝ) < 3)]
  refine ⟨?_, ?_, ?_, ?_, ?_, hlog, ?_, ?_, ?_, ?_⟩
  · intro y0 y1; cases y0 <;> cases y1 <;> norm_num [logisticWitnessMass, coinMass]
  · norm_num [logisticWitnessMass, coinMass, Fintype.sum_bool]
  · norm_num [logisticWitnessMass, coinMass, bit, Fintype.sum_bool]
  · norm_num [logisticWitnessMass, coinMass, bit, Fintype.sum_bool]
  · norm_num [logistic]
  · norm_num [logisticWitnessMass, coinMass, signedOutcome, Fintype.sum_bool]
  · norm_num [logisticWitnessMass, coinMass, signedOutcome, Fintype.sum_bool]
  · norm_num
  · rw [hlog]; norm_num

/-- T9: "B={i:τ̂_i>0}", Section 6 and Table 1, PDF pp. 7–9. -/
def beneficiaries {n : ℕ} (τhat : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < τhat i)

/-- T9: "S=Σ_{i∈B}τ̂_i". -/
def positiveEffectSum {n : ℕ} (τhat : Fin n → ℝ) : ℝ :=
  ∑ i ∈ beneficiaries τhat, τhat i

/-- T9: "V*=S/n", the full analysis-sample fitted utility. -/
def fittedOptimalUtility {n : ℕ} (τhat : Fin n → ℝ) : ℝ :=
  positiveEffectSum τhat / n

/-- T9: "b=S/k", the benefit among the strictly positive-effect units.
This denominator differs from the full-sample size. -/
def beneficiaryMean {n : ℕ} (τhat : Fin n → ℝ) : ℝ :=
  positiveEffectSum τhat / (beneficiaries τhat).card

/-- P006-T9(a): the exact same-numerator identity and strict inequality,
for any fitted effects with 0<k<n. No claim about clinical effects is made. -/
theorem T9_denominator_identity {n : ℕ} (τhat : Fin n → ℝ) (hn : 0 < n)
    (hk : 0 < (beneficiaries τhat).card) :
    beneficiaryMean τhat =
      fittedOptimalUtility τhat * ((n : ℝ)/(beneficiaries τhat).card) ∧
    ((beneficiaries τhat).card < n →
      fittedOptimalUtility τhat < beneficiaryMean τhat) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hk0 : ((beneficiaries τhat).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hS : 0 < positiveEffectSum τhat := by
    apply Finset.sum_pos
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact Finset.card_pos.mp hk
  constructor
  · dsimp [beneficiaryMean, fittedOptimalUtility]; field_simp
  · intro hkn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hkpos : (0:ℝ) < (beneficiaries τhat).card := by exact_mod_cast hk
    have hknr : ((beneficiaries τhat).card : ℝ) < n := by exact_mod_cast hkn
    dsimp [fittedOptimalUtility, beneficiaryMean]
    apply (div_lt_div_iff₀ hnpos hkpos).mpr
    nlinarith

/-- P006-T9(b),(c): exact notebook-output rounding intervals imply the
correct beneficiary-mean intervals and exclude the two three-decimal prose
values in Section 6 (PDF pp. 7–8). The stored fitted utilities are hypotheses,
not measurements or a refit certified by Lean. -/
theorem T9_corrected_numeric_intervals (vH bH vS bS : ℝ)
    (hHl : 293907/2000000 ≤ vH) (hHu : vH ≤ 293909/2000000)
    (hH : bH = vH*(255/62))
    (hSl : 50371/2000000 ≤ vS) (hSu : vS ≤ 50373/2000000)
    (hS : bS = vS*(7264/1360)) :
    14989257/24800000 ≤ bH ∧ bH ≤ 14989359/24800000 ∧ 59/400 < bH ∧
    672601/5000000 ≤ bS ∧ bS ≤ 11434671/85000000 ∧ 51/2000 < bS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- P006-T9(d): Table 1's printed utilities and treatment rates alone
force beneficiary means >0.604 and >0.134, allowing the displayed rates
and utilities to have been rounded or truncated. -/
theorem T9_from_printed_table (vH rH vS rS : ℝ)
    (hHr : 0 < rH) (hHv : 14694/100000 ≤ vH) (hHrU : rH ≤ 2432/10000)
    (hSr : 0 < rS) (hSv : 2517/100000 ≤ vS) (hSrU : rS ≤ 1873/10000) :
    604/1000 < vH/rH ∧ 134/1000 < vS/rS := by
  constructor
  · apply (lt_div_iff₀ hHr).mpr; linarith
  · apply (lt_div_iff₀ hSr).mpr; linarith




/-- Appendix E.4, PDF p. 26, corrected: "G_x={i:X_i=x}". -/
def empiricalGroup {C : Type*} [DecidableEq C] {n : ℕ}
    (X : Fin n → C) (x : C) : Finset (Fin n) := Finset.univ.filter (fun i => X i = x)

/-- T22: the corrected empirical conditional mean, with the sum of all
matching indicators in its denominator, not a free-index single indicator. -/
def empiricalMean {C : Type*} [DecidableEq C] {n : ℕ}
    (X : Fin n → C) (m : Fin n → ℝ) (x : C) : ℝ :=
  (∑ i ∈ empiricalGroup X x, m i) / (empiricalGroup X x).card


/-- P006-T22(a),(b): corrected empirical conditioning (PDF p. 26).
Every nonempty covariate group has a mean between its minimum and maximum,
zero sum of deviations, and the average of the group means assigned back
to each row equals the original overall average. The bounds are quantified
over all lower and upper group bounds, equivalently the attained finite
minimum and maximum. -/
theorem T22_corrected_empirical_mean {C : Type*} [DecidableEq C] {n : ℕ}
    (X : Fin n → C) (m : Fin n → ℝ) (hn : 0 < n) :
    (∀ x, (empiricalGroup X x).Nonempty →
      (∀ l h : ℝ, (∀ i ∈ empiricalGroup X x, l ≤ m i ∧ m i ≤ h) →
        l ≤ empiricalMean X m x ∧ empiricalMean X m x ≤ h) ∧
      (∑ i ∈ empiricalGroup X x, (m i-empiricalMean X m x)) = 0) ∧
    (∑ i, empiricalMean X m (X i))/n = (∑ i, m i)/n  := by
  have parts (x : C) (hG : (empiricalGroup X x).Nonempty) :
      (∀ l h : ℝ, (∀ i ∈ empiricalGroup X x, l ≤ m i ∧ m i ≤ h) →
        l ≤ empiricalMean X m x ∧ empiricalMean X m x ≤ h) ∧
      (∑ i ∈ empiricalGroup X x, (m i-empiricalMean X m x)) = 0 := by
    have hcard : (0:ℝ) < (empiricalGroup X x).card := by
      exact_mod_cast Finset.card_pos.mpr hG
    constructor
    · intro l h hb
      have hl : ((empiricalGroup X x).card : ℝ)*l ≤
          (∑ i ∈ empiricalGroup X x, m i) := by
        simpa using Finset.sum_le_sum (fun i hi => (hb i hi).1)
      have hh : (∑ i ∈ empiricalGroup X x, m i) ≤
          ((empiricalGroup X x).card : ℝ)*h := by
        simpa using Finset.sum_le_sum (fun i hi => (hb i hi).2)
      unfold empiricalMean
      constructor
      · apply (le_div_iff₀ hcard).mpr; nlinarith
      · apply (div_le_iff₀ hcard).mpr; nlinarith
    · rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const,nsmul_eq_mul]
      unfold empiricalMean
      field_simp [ne_of_gt hcard]
      ring
  refine ⟨parts,?_⟩
  let values := Finset.univ.image X
  have maps : ∀ i ∈ (Finset.univ : Finset (Fin n)), X i ∈ values := by
    intro i hi; exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  have fiber (f : Fin n → ℝ) :
      (∑ x ∈ values, ∑ i ∈ empiricalGroup X x, f i) = ∑ i, f i := by
    simpa [empiricalGroup] using Finset.sum_fiberwise_of_maps_to maps f
  have total : (∑ i, empiricalMean X m (X i)) = ∑ i, m i := by
    calc
      (∑ i, empiricalMean X m (X i)) =
          ∑ x ∈ values, ∑ i ∈ empiricalGroup X x, empiricalMean X m (X i) :=
        (fiber (fun i => empiricalMean X m (X i))).symm
      _ = ∑ x ∈ values, ∑ i ∈ empiricalGroup X x, m i := by
        apply Finset.sum_congr rfl
        intro x hx
        have hG : (empiricalGroup X x).Nonempty := by
          rcases Finset.mem_image.mp hx with ⟨i,hi,hix⟩
          exact ⟨i,Finset.mem_filter.mpr ⟨hi,hix⟩⟩
        have hc : ((empiricalGroup X x).card : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hG)
        have he : (∑ i ∈ empiricalGroup X x, empiricalMean X m (X i)) =
            (∑ i ∈ empiricalGroup X x, empiricalMean X m x) := by
          apply Finset.sum_congr rfl
          intro i hi; rw [(Finset.mem_filter.mp hi).2]
        rw [he]
        simp only [Finset.sum_const,nsmul_eq_mul]
        unfold empiricalMean
        field_simp [hc]
      _ = ∑ i, m i := fiber m
  rw [total]


/-- P006-T22(c): with two matching rows (1,3), the corrected group mean is 2;
dividing the group sum by the single matching indicator returns 4. -/
theorem T22_two_row_example :
    empiricalMean (fun _ : Fin 2 => (0:ℕ)) ![1,3] 0 = 2 ∧
    ((1+3 : ℝ)/1) = 4 := by
  norm_num [empiricalMean, empiricalGroup, Fin.sum_univ_two]

/-- One-unit treatment count, Reward Functions 1–4, PDF pp. 4–6. -/
theorem treatedCount_one (t : Bool) : treatedCount ![t] = bit t := by
  unfold treatedCount
  rw [Fin.sum_univ_one]
  rfl

/-- The n=1 ATO reward, with the paper's empty-sample convention. -/
theorem wATO_one (t : Bool) (y : ℝ) : wATO ![t] ![y] = if t then y else 0 := by
  unfold wATO
  rw [treatedCount_one, Fin.sum_univ_one]
  cases t <;> norm_num [bit]

/-- Appendix A.2, PDF p. 14: "D ... distribution over X,Yᵢ(1),Yᵢ(0)".
The tuple is stored as (X,(Y0,Y1)). -/
abbrev OutcomeLaw (C : Type*) [MeasurableSpace C] := Measure (C × (ℝ × ℝ))

/-- Finite-mean distributions in the standing assumptions and corrected
Theorem 4: both potential outcomes have finite absolute means. -/
def FiniteOutcomeLaw {C : Type*} [MeasurableSpace C] (D : OutcomeLaw C) : Prop :=
  IsProbabilityMeasure D ∧ Integrable (fun z => z.2.1) D ∧
    Integrable (fun z => z.2.2) D

/-- Appendix A.2, PDF p. 14: the fixed joint law of "(X,Yᵢ(1))". -/
def treatedProjection {C : Type*} : C × (ℝ × ℝ) → C × ℝ :=
  fun z => (z.1,z.2.2)

/-- Exact one-unit ATO expectation after the independent conditional
Bernoulli treatment draw (Appendix A.2; T10). The untreated potential outcome
is retained in the observed outcome before applying the printed reward. -/
def oneATOExpectation {C : Type*} [MeasurableSpace C]
    (D : OutcomeLaw C) (π : C → ℝ) : ℝ :=
  ∫ z, (∑ t : Bool, coinMass (π z.1) t *
    wATO ![t] ![if t then z.2.2 else z.2.1]) ∂D

/-- The n=1 ATO expectation depends only on treated outcomes and covariates,
for every distribution and policy, not just the one-atom family. -/
theorem oneATOExpectation_formula {C : Type*} [MeasurableSpace C]
    (D : OutcomeLaw C) (π : C → ℝ) :
    oneATOExpectation D π = ∫ z, π z.1 * z.2.2 ∂D := by
  simp [oneATOExpectation, Fintype.sum_bool, coinMass, wATO_one]

/-- The full invariance hypothesis of Theorem 4 holds for the n=1 ATO
reward: any two joint laws with the same (X,Y1) marginal give identical
expected reward for every fixed measurable policy. -/
theorem oneATO_invariance {C : Type*} [MeasurableSpace C]
    (D D' : OutcomeLaw C) (π : C → ℝ) (hπ : Measurable π)
    (hD : Measure.map treatedProjection D = Measure.map treatedProjection D') :
    oneATOExpectation D π = oneATOExpectation D' π := by
  have hproj : Measurable (treatedProjection : C × (ℝ × ℝ) → C × ℝ) :=
    measurable_fst.prodMk measurable_snd.snd
  have hd : IdentDistrib treatedProjection treatedProjection D D' :=
    ⟨hproj.aemeasurable, hproj.aemeasurable, hD⟩
  have hf : Measurable (fun z : C × ℝ => π z.1 * z.2) :=
    (hπ.comp measurable_fst).mul measurable_snd
  rw [oneATOExpectation_formula, oneATOExpectation_formula]
  exact (hd.comp hf).integral_eq

/-- Welfare under an outcome law, from Lemma 1 (PDF p. 16):
"E[π(X)(Y1−Y0)]". Conditional treatment randomization gives this marginal
form without restricting the joint distribution of the potential outcomes. -/
def outcomeWelfare {C : Type*} [MeasurableSpace C]
    (D : OutcomeLaw C) (π : C → ℝ) : ℝ :=
  ∫ z, π z.1 * (z.2.2-z.2.1) ∂D

/-- P006-T10, Theorem 4 as printed (PDF p. 14), concrete counterexample.
X=0 (a singleton type), n=1, Π={always treat}; D_B has Y1=1,Y0=1+B.
Assumption 3 holds, invariance for ALL distributions is proved above, and
the sole feasible policy has regret zero under EVERY finite-mean law.
There is no feasible zero policy, and the printed lower bound 0≥B fails. -/
theorem T10_singleton_feasible_counterexample (B : ℝ) (hB : 0 < B) :
    let D : OutcomeLaw Unit := Measure.dirac ((),(1+B,1))
    let PiSet : Set (Unit → ℝ) := {fun _ => 1}
    FiniteOutcomeLaw D ∧
    IsBest PiSet (oneATOExpectation D) (fun _ => 1) ∧
    (∫ z, (1 : ℝ) ∂D) = 1 ∧
    outcomeWelfare D (fun _ => 1) = -B ∧
    regret PiSet (outcomeWelfare D) (fun _ => 1) = 0 ∧
    (∀ V : (Unit → ℝ) → ℝ, regret PiSet V (fun _ => 1) = 0) ∧
    (fun _ : Unit => (0:ℝ)) ∉ PiSet ∧ ¬ (0 ≥ B) := by
  dsimp
  have hb (f : (Unit → ℝ) → ℝ) : IsBest {fun _ : Unit => (1:ℝ)} f (fun _ => 1) := by
    refine ⟨Set.mem_singleton _, ?_⟩
    intro π hπ; have heq := Set.mem_singleton_iff.mp hπ; rw [heq]
  refine ⟨?_, hb _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨inferInstance, integrable_dirac (by simp), integrable_dirac (by simp)⟩
  · simp
  · simp [outcomeWelfare]
  · rw [regret, bestValue_eq (hb _)]; ring
  · intro V; rw [regret, bestValue_eq (hb V)]; ring
  · simp only [Set.mem_singleton_iff]
    intro h; have hc := congrFun h (); norm_num at hc
  · linarith

/-- Assumption 3, Appendix A.2, PDF p. 14: some finite-mean distribution
has a best response with E[π(X)]>0. The reward functional is the unconditional
E_D[w] as a function of D and the fixed policy; no invariance is built into it. -/
def NondegenerateReward {C : Type*} [MeasurableSpace C]
    (PiSet : Set (C → ℝ)) (reward : OutcomeLaw C → (C → ℝ) → ℝ) : Prop :=
  ∃ D π, FiniteOutcomeLaw D ∧ IsBest PiSet (reward D) π ∧
    0 < (∫ z, π z.1 ∂D)

/-- Theorem 4's invariance hypothesis, Appendix A.2, PDF p. 14.
Only the untreated potential outcome distribution is changed; the joint
law of covariates and treated outcomes is fixed. -/
def TreatedDataInvariant {C : Type*} [MeasurableSpace C]
    (PiSet : Set (C → ℝ)) (reward : OutcomeLaw C → (C → ℝ) → ℝ) : Prop :=
  ∀ D D', FiniteOutcomeLaw D → FiniteOutcomeLaw D' →
    Measure.map treatedProjection D = Measure.map treatedProjection D' →
    ∀ π ∈ PiSet, reward D π = reward D' π

/-- The corrected family in T11: retain (X,Y1) and set Y0=Y1+B everywhere. -/
def shiftedOutcomeLaw {C : Type*} [MeasurableSpace C]
    (D : OutcomeLaw C) (B : ℝ) : OutcomeLaw C :=
  Measure.map (fun z => (z.1,(z.2.2+B,z.2.2))) D

/-- P006-T11: corrected Theorem 4, PDF p. 14.
Zero treatment is feasible. Nondegeneracy and treated-data invariance imply
unbounded attainable regret for SOME best response. A positive-treatment
best response is retained while Y0 is shifted to Y1+B, and its regret is Bc.
No assertion is made that every tied best response has large regret. -/
theorem T11_corrected_impossibility {C : Type*} [MeasurableSpace C]
    (PiSet : Set (C → ℝ)) (hπ : ∀ π ∈ PiSet, Admissible π)
    (hz : (fun _ => 0) ∈ PiSet) (reward : OutcomeLaw C → (C → ℝ) → ℝ)
    (hN : NondegenerateReward PiSet reward) (hI : TreatedDataInvariant PiSet reward) :
    (∀ M : ℝ, 0 < M →
      ∃ D π, FiniteOutcomeLaw D ∧ IsBest PiSet (reward D) π ∧
        M < regret PiSet (outcomeWelfare D) π) ∧
    (∀ D π, FiniteOutcomeLaw D → IsBest PiSet (reward D) π →
      0 < (∫ z, π z.1 ∂D) → ∀ B : ℝ, 0 < B →
      FiniteOutcomeLaw (shiftedOutcomeLaw D B) ∧
      Measure.map treatedProjection (shiftedOutcomeLaw D B) =
        Measure.map treatedProjection D ∧
      IsBest PiSet (reward (shiftedOutcomeLaw D B)) π ∧
      (∀ π' ∈ PiSet, outcomeWelfare (shiftedOutcomeLaw D B) π' =
        -B*(∫ z, π' z.1 ∂D)) ∧
      bestValue PiSet (outcomeWelfare (shiftedOutcomeLaw D B)) = 0 ∧
      regret PiSet (outcomeWelfare (shiftedOutcomeLaw D B)) π =
        B*(∫ z, π z.1 ∂D))  := by
  have family (D : OutcomeLaw C) (π : C → ℝ) (hD : FiniteOutcomeLaw D)
      (hb : IsBest PiSet (reward D) π) (hc : 0 < (∫ z, π z.1 ∂D))
      (B : ℝ) (hB : 0 < B) :
      FiniteOutcomeLaw (shiftedOutcomeLaw D B) ∧
      Measure.map treatedProjection (shiftedOutcomeLaw D B) =
        Measure.map treatedProjection D ∧
      IsBest PiSet (reward (shiftedOutcomeLaw D B)) π ∧
      (∀ π' ∈ PiSet, outcomeWelfare (shiftedOutcomeLaw D B) π' =
        -B*(∫ z, π' z.1 ∂D)) ∧
      bestValue PiSet (outcomeWelfare (shiftedOutcomeLaw D B)) = 0 ∧
      regret PiSet (outcomeWelfare (shiftedOutcomeLaw D B)) π =
        B*(∫ z, π z.1 ∂D) := by
    letI : IsProbabilityMeasure D := hD.1
    let F : C × (ℝ × ℝ) → C × (ℝ × ℝ) := fun z => (z.1,(z.2.2+B,z.2.2))
    have hf : Measurable F :=
      measurable_fst.prodMk ((measurable_snd.snd.add_const B).prodMk measurable_snd.snd)
    have hvalid : FiniteOutcomeLaw (shiftedOutcomeLaw D B) := by
      refine ⟨?_, ?_, ?_⟩
      · change IsProbabilityMeasure (Measure.map F D)
        exact ⟨by rw [Measure.map_apply hf MeasurableSet.univ]; simp⟩
      · change Integrable (fun z => z.2.1) (Measure.map F D)
        apply (integrable_map_measure measurable_snd.fst.aestronglyMeasurable hf.aemeasurable).mpr
        simpa [F,Function.comp_def] using hD.2.2.add (integrable_const B)
      · change Integrable (fun z => z.2.2) (Measure.map F D)
        apply (integrable_map_measure measurable_snd.snd.aestronglyMeasurable hf.aemeasurable).mpr
        simpa [F,Function.comp_def] using hD.2.2
    have ht : Measurable (treatedProjection : C × (ℝ × ℝ) → C × ℝ) :=
      measurable_fst.prodMk measurable_snd.snd
    have hmap : Measure.map treatedProjection (shiftedOutcomeLaw D B) =
        Measure.map treatedProjection D := by
      change Measure.map treatedProjection (Measure.map F D) = _
      rw [Measure.map_map ht hf]
      rfl
    have hw (π' : C → ℝ) (hπ' : π' ∈ PiSet) :
        outcomeWelfare (shiftedOutcomeLaw D B) π' = -B*(∫ z, π' z.1 ∂D) := by
      have hp := (hπ π' hπ').1
      have hm : Measurable (fun z : C × (ℝ × ℝ) => π' z.1*(z.2.2-z.2.1)) :=
        (hp.comp measurable_fst).mul (measurable_snd.snd.sub measurable_snd.fst)
      unfold outcomeWelfare shiftedOutcomeLaw
      rw [integral_map hf.aemeasurable hm.aestronglyMeasurable]
      have he : (fun z : C × (ℝ × ℝ) =>
          π' (F z).1*((F z).2.2-(F z).2.1)) = (fun z => -B*π' z.1) := by
        funext z; dsimp [F]; ring
      change (∫ z, π' (F z).1*((F z).2.2-(F z).2.1) ∂D) = _
      rw [he,integral_const_mul]
    have hb' : IsBest PiSet (reward (shiftedOutcomeLaw D B)) π := by
      refine ⟨hb.1, ?_⟩
      intro q hq
      rw [hI _ _ hvalid hD hmap q hq, hI _ _ hvalid hD hmap π hb.1]
      exact hb.2 q hq
    have hzmax : IsBest PiSet (outcomeWelfare (shiftedOutcomeLaw D B)) (fun _ => 0) := by
      refine ⟨hz, ?_⟩
      intro q hq
      rw [hw q hq, hw (fun _ => 0) hz]
      simp only [integral_zero,mul_zero]
      have hn : 0 ≤ (∫ z, q z.1 ∂D) := integral_nonneg (fun z => (hπ q hq).2 z.1 |>.1)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hn
    have hv : bestValue PiSet (outcomeWelfare (shiftedOutcomeLaw D B)) = 0 := by
      rw [bestValue_eq hzmax,hw (fun _ => 0) hz]
      simp
    refine ⟨hvalid,hmap,hb',hw,hv,?_⟩
    rw [regret,hv,hw π hb.1]
    ring
  constructor
  · intro M hM
    rcases hN with ⟨D,π,hD,hb,hc⟩
    let B := (M+1)/(∫ z, π z.1 ∂D)
    have hB : 0 < B := div_pos (by linarith) hc
    have hF := family D π hD hb hc B hB
    refine ⟨shiftedOutcomeLaw D B,π,hF.1,hF.2.2.1,?_⟩
    rw [hF.2.2.2.2.2]
    dsimp [B]
    rw [div_mul_cancel₀ _ (ne_of_gt hc)]
    linarith
  · exact family


/-- T11's final finite arithmetic: B=(M+1)/c gives regret Bc=M+1>M. -/
theorem T11_unbounded_shift_arithmetic (M c : ℝ) (hM : 0 < M) (hc : 0 < c) :
    0 < (M+1)/c ∧ M < ((M+1)/c)*c := by
  constructor
  · exact div_pos (by linarith) hc
  · rw [div_mul_cancel₀ _ (ne_of_gt hc)]; linarith

/-- T12 (P006-E005): Lebesgue probability on [0,1], represented as a
measure on ℝ restricted to its common support. -/
def intervalLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- T12: P_X0=(1/2)λ+(1/2)δ_{1/2}. -/
def referenceWithAtom : Measure ℝ :=
  (1/2 : ℝ≥0∞) • intervalLaw + (1/2 : ℝ≥0∞) • Measure.dirac (1/2)

/-- Multiplication by a nonzero mass preserves support. Used to certify the
common-support hypothesis in T12 rather than discarding that hypothesis. -/
theorem smul_support_eq {C : Type*} [MeasurableSpace C] [TopologicalSpace C]
    (μ : Measure C) (c : ℝ≥0∞) (hc : c ≠ 0) : (c • μ).support = μ.support := by
  have h1 : c • μ ≪ μ := by
    intro s hs
    simp [Measure.smul_apply, hs]
  have h2 : μ ≪ c • μ := by
    intro s hs
    have hm : c * μ s = 0 := by simpa [Measure.smul_apply] using hs
    exact (mul_eq_zero.mp hm).resolve_left hc
  exact Set.Subset.antisymm h1.support_mono h2.support_mono

/-- P006-T12 (Theorem 2, PDF pp. 6,20), the exact continuous counterexample.
Both laws are probability laws with support [0,1]. The printed absolute
continuity λ≪P0 holds, but the required reverse fails at {1/2}; hence there
is no nonnegative measurable density of P0 with respect to λ.
This refutes existence of the named weight, not ranking with a valid weight. -/
theorem T12_density_direction_counterexample :
    intervalLaw Set.univ = 1 ∧ referenceWithAtom Set.univ = 1 ∧
    intervalLaw.support = Set.Icc 0 1 ∧ referenceWithAtom.support = Set.Icc 0 1 ∧
    intervalLaw ≪ referenceWithAtom ∧
    intervalLaw ({1/2} : Set ℝ) = 0 ∧ referenceWithAtom ({1/2} : Set ℝ) = 1/2 ∧
    ¬ referenceWithAtom ≪ intervalLaw ∧
    ¬ ∃ f : ℝ → ℝ≥0∞, Measurable f ∧ referenceWithAtom = intervalLaw.withDensity f := by
  have hLeb1 : intervalLaw Set.univ = 1 := by
    simp [intervalLaw, Real.volume_Icc]
  have hR1 : referenceWithAtom Set.univ = 1 := by
    have hd : (Measure.dirac (1/2 : ℝ)) Set.univ = 1 := by simp
    simp only [referenceWithAtom,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      hLeb1,hd,mul_one]
    exact ENNReal.add_halves 1
  have hAC : intervalLaw ≪ referenceWithAtom := by
    intro s hs
    have hadd : (1/2 : ℝ≥0∞)*intervalLaw s +
        (1/2 : ℝ≥0∞)*(Measure.dirac (1/2 : ℝ)) s = 0 := by
      simpa only [referenceWithAtom,Measure.add_apply,Measure.smul_apply,smul_eq_mul] using hs
    have hm : (1/2 : ℝ≥0∞)*intervalLaw s = 0 := (add_eq_zero.mp hadd).1
    exact (mul_eq_zero.mp hm).resolve_left (by norm_num)
  have hLebpoint : intervalLaw ({1/2} : Set ℝ) = 0 := by
    apply le_antisymm
    · calc
        intervalLaw ({1/2} : Set ℝ) ≤ volume ({1/2} : Set ℝ) := Measure.restrict_le_self _
        _ = 0 := by simp
    · exact zero_le
  have hRpoint : referenceWithAtom ({1/2} : Set ℝ) = 1/2 := by
    have hd : (Measure.dirac (1/2 : ℝ)) ({1/2} : Set ℝ) = 1 := by simp
    simp only [referenceWithAtom,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      hLebpoint,hd,mul_zero,zero_add,mul_one]
  have hnot : ¬ referenceWithAtom ≪ intervalLaw := by
    intro h
    have hzero := h hLebpoint
    rw [hRpoint] at hzero
    norm_num at hzero
  have hLebsupport : intervalLaw.support = Set.Icc 0 1 := by
    apply Set.Subset.antisymm
    · have hu := (volume : Measure ℝ).support_restrict_subset (s := Set.Icc 0 1)
      intro x hx
      have hh := (hu hx).1
      simpa [isClosed_Icc.closure_eq] using hh
    · have hi : Set.Ioo (0:ℝ) 1 ⊆ intervalLaw.support := by
        have h := (volume : Measure ℝ).interior_inter_support (s := Set.Icc 0 1)
        simpa [intervalLaw, interior_Icc, Measure.support_eq_univ] using h
      have hc := closure_minimal hi intervalLaw.isClosed_support
      simpa [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] using hc
  have hRsupport : referenceWithAtom.support = Set.Icc 0 1 := by
    apply Set.Subset.antisymm
    · apply Measure.support_subset_of_isClosed isClosed_Icc
      rw [mem_ae_iff]
      have hLebc : intervalLaw (Set.Icc (0:ℝ) 1)ᶜ = 0 := by
        simp [intervalLaw, Measure.restrict_apply (measurableSet_Icc.compl)]
      have hDc : (Measure.dirac (1/2 : ℝ)) (Set.Icc (0:ℝ) 1)ᶜ = 0 := by
        rw [Measure.dirac_apply]
        exact Set.indicator_of_notMem (by norm_num) _
      simpa only [referenceWithAtom,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
        hLebc,hDc,mul_zero,add_zero]
    · rw [← hLebsupport]
      exact hAC.support_mono
  refine ⟨hLeb1,hR1,hLebsupport,hRsupport,hAC,hLebpoint,hRpoint,hnot,?_⟩
  rintro ⟨f,hf,heq⟩
  apply hnot
  rw [heq]
  exact withDensity_absolutelyContinuous _ _

/-- T15's SUTVA observation for deterministic potential outcomes. -/
def deterministicObserved (y0 y1 : Bool → ℝ) (x t : Bool) : ℝ :=
  if t then y1 x else y0 x

/-- T15: complete observed-data mass (X,T,Y), for fair binary X and
conditionally independent Bernoulli treatment under a fixed policy. -/
def binaryObservedMass (y0 y1 : Bool → ℝ) (π : BinaryPolicy)
    (record : Bool × Bool × ℝ) : ℝ :=
  ∑ x : Bool, ∑ t : Bool, (1/2 : ℝ)*coinMass (binaryRule π x) t *
    (if record = (x,t,deterministicObserved y0 y1 x t) then 1 else 0)

/-- T15: one-point observed-data law with π=1. The U and X spaces are
singletons, so the maximum heterogeneity Δ is identically zero. -/
def singletonObservedMass (y0 y1 : ℝ) (record : Bool × ℝ) : ℝ :=
  ∑ t : Bool, coinMass 1 t * (if record = (t,if t then y1 else y0) then 1 else 0)

/-- P006-T15 (Appendix D.3, PDF pp. 23–24), both positivity counterexamples.
The printed π>0 holds while the untreated arm is absent at x=0.
Two models with untreated means 0 and 2 produce identical observed laws,
even in the second witness where untreated units have total mass 1/4.
The examples concern identification and the premise of Lemma 3, not failure
of a regret bound when a valid untreated conditional mean exists. -/
theorem T15_untreated_positivity_counterexamples :
    (∀ record, singletonObservedMass 0 1 record = singletonObservedMass 2 1 record) ∧
    (1 : ℝ) > 0 ∧ coinMass 1 false = 0 ∧ (0 : ℝ) ≠ 2 ∧
    (∀ record, binaryObservedMass (fun _ => 0) (fun _ => 1) (1,1/2) record =
      binaryObservedMass (fun x => if x then 0 else 2) (fun _ => 1) (1,1/2) record) ∧
    (∀ x, 0 < binaryRule (1,1/2) x) ∧
    coinMass (binaryRule (1,1/2) false) false = 0 ∧
    (∑ x : Bool, (1/2 : ℝ)*coinMass (binaryRule (1,1/2) x) false) = 1/4 ∧
    binaryObservedMass (fun _ => 0) (fun _ => 1) (1,1/2) (false,true,1) = 1/2 ∧
    binaryObservedMass (fun _ => 0) (fun _ => 1) (1,1/2) (true,true,1) = 1/4 ∧
    binaryObservedMass (fun _ => 0) (fun _ => 1) (1,1/2) (true,false,0) = 1/4 := by
  refine ⟨?_, by norm_num, by norm_num [coinMass], by norm_num,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro record; simp [singletonObservedMass, coinMass, Fintype.sum_bool]
  · intro record
    simp [binaryObservedMass, deterministicObserved, coinMass, binaryRule, Fintype.sum_bool]
  · intro x; cases x <;> norm_num [binaryRule]
  · norm_num [coinMass, binaryRule]
  · norm_num [coinMass, binaryRule, Fintype.sum_bool]
  · norm_num [binaryObservedMass, deterministicObserved, coinMass, binaryRule, Fintype.sum_bool]
  · norm_num [binaryObservedMass, deterministicObserved, coinMass, binaryRule, Fintype.sum_bool]
  · norm_num [binaryObservedMass, deterministicObserved, coinMass, binaryRule, Fintype.sum_bool]

/-- Corrected D.3 positivity, PDF p. 23 (T16):
"q_π(x)=E[1−π(x,U)|X=x]". κ x is P_{U|X=x}. -/
def untreatedProbability {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) (π : (X × U) → ℝ) (x : X) : ℝ :=
  ∫ u, 1-π (x,u) ∂κ x

/-- Lemma 3 in corrected T16, PDF p. 24: the untreated conditional law has
density "(1−π(x,u))/q_π(x)" with respect to P_{U|X=x}. -/
def untreatedConditionalLaw {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) (π : (X × U) → ℝ) (x : X) : Measure U :=
  (κ x).withDensity (fun u => ENNReal.ofReal
    ((1-π (x,u))/untreatedProbability κ π x))

/-- D.3, PDF p. 23: "μ̂₀^π(x)=E[Y|T^π=0,X=x]".
Here it is a population conditional mean, not a finite-sample fitted estimator.
The numerator and denominator implement the corrected untreated selection. -/
def selectedBaseline {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (κ : Kernel X U) (μ0 : (X × U) → ℝ) (π : (X × U) → ℝ) (x : X) : ℝ :=
  (∫ u, μ0 (x,u)*(1-π (x,u)) ∂κ x) / untreatedProbability κ π x

/-- Assumption 4, PDF p. 23: "Δ(x,u)=max_{ũ∈U}|μ₀(x,u)−μ₀(x,ũ)|".
Represented here by the real supremum of the absolute-difference range. -/
def maximumDeviation {X U : Type*} (μ0 : (X × U) → ℝ) (c : X × U) : ℝ :=
  sSup (Set.range (fun u => |μ0 c-μ0 (c.1,u)|))


/-- T16's sufficient pointwise replacement π(x,u)<1 and the corrected
full-information identification sentence in D.3 (PDF p. 23).
The theorem quantifies over every real probability rule and Markov κ. -/
theorem T16_sufficient_positivity {X U : Type*} [MeasurableSpace X]
    [MeasurableSpace U] (κ : Kernel X U) (hκ : IsMarkovKernel κ)
    (π : (X × U) → ℝ) (hπ : Admissible π) (hlt : ∀ c, π c < 1) :
    (∀ x, 0 < untreatedProbability κ π x) ∧
    (∀ b0 : X → ℝ, ∀ x,
      selectedBaseline κ (fun c => b0 c.1) π x = b0 x) := by
  letI : IsMarkovKernel κ := hκ
  have hq (x : X) : 0 < untreatedProbability κ π x := by
    have hm : Measurable (fun u => 1-π (x,u)) :=
      measurable_const.sub (hπ.1.comp (measurable_const.prodMk measurable_id))
    have hn (u : U) : 0 ≤ 1-π (x,u) := by
      have h := (hπ.2 (x,u)).2
      linarith
    have hi : Integrable (fun u => 1-π (x,u)) (κ x) :=
      (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ (by
        intro u
        rw [Real.norm_eq_abs, abs_of_nonneg (hn u)]
        have h := (hπ.2 (x,u)).1
        linarith))
    have hs : Function.support (fun u => 1-π (x,u)) = Set.univ := by
      ext u
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      have h := hlt (x,u)
      linarith
    unfold untreatedProbability
    apply (integral_pos_iff_support_of_nonneg hn hi).mpr
    rw [hs]
    simp
  refine ⟨hq, ?_⟩
  intro b0 x
  unfold selectedBaseline
  change (∫ u, b0 x*(1-π (x,u)) ∂κ x) / untreatedProbability κ π x = _
  rw [integral_const_mul]
  change b0 x*untreatedProbability κ π x / untreatedProbability κ π x = b0 x
  exact mul_div_cancel_right₀ _ (ne_of_gt (hq x))

/-- T17(a), finite types at a fixed X=x (Appendix D.3, PDF p. 23):
"Σ μ₀(x,u)p_u(1−π(x,u)) / Σ p_u(1−π(x,u))". -/
def finiteSelectedBaseline {K : ℕ} (p m π : Fin K → ℝ) : ℝ :=
  finiteA p m (fun i => 1-π i) / finiteMass p (fun i => 1-π i)

/-- T17(b): only the selected positive-mass type is left untreated. -/
def leaveOnlyType {K : ℕ} (j : Fin K) : Fin K → ℝ :=
  fun i => if i = j then 0 else 1

/-- T17(c): treatment is allocated only to the selected type. -/
def treatOnlyType {K : ℕ} (j : Fin K) : Fin K → ℝ :=
  fun i => if i = j then 1 else 0

/-- P006-T17(a)–(c), corrected selection mechanism in D.3, PDF p. 23.
Leaving only j untreated yields μ̂₀^π=μ₀(x,j). Treating only j instead yields
the weighted mean over its complement. This theorem uses finite positive-mass
types; it does not claim that a singleton of nonatomic U can be selected with
positive probability. -/
theorem T17_selected_type {K : ℕ} (p m : Fin K → ℝ) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (j : Fin K) :
    finiteMass p (fun i => 1-leaveOnlyType j i) = p j ∧
    finiteSelectedBaseline p m (leaveOnlyType j) = m j ∧
    ((∃ i : Fin K, i ≠ j) →
      0 < finiteMass p (fun i => 1-treatOnlyType j i) ∧
      finiteSelectedBaseline p m (treatOnlyType j) =
        (∑ i, if i = j then 0 else p i*m i) /
        (∑ i, if i = j then 0 else p i)) := by
  have hm : finiteMass p (fun i => 1-leaveOnlyType j i) = p j := by
    simp [finiteMass, leaveOnlyType, sub_ite, mul_ite]
  refine ⟨hm, ?_, ?_⟩
  · unfold finiteSelectedBaseline
    rw [hm]
    have ha : finiteA p m (fun i => 1-leaveOnlyType j i) = p j*m j := by
      simp [finiteA, leaveOnlyType, sub_ite, mul_ite]
    rw [ha]
    field_simp [ne_of_gt (hp j)]
  · rintro ⟨i,hij⟩
    have hnonneg (k : Fin K) (_ : k ∈ (Finset.univ : Finset (Fin K))) :
        0 ≤ p k*(1-treatOnlyType j k) := by
      by_cases hkj : k = j
      · simp [treatOnlyType,hkj]
      · simp [treatOnlyType,hkj,(hp k).le]
    have hi := Finset.single_le_sum hnonneg (Finset.mem_univ i)
    have hil : p i ≤ finiteMass p (fun k => 1-treatOnlyType j k) := by
      simpa [finiteMass,treatOnlyType,hij] using hi
    refine ⟨lt_of_lt_of_le (hp i) hil,?_⟩
    simp [finiteSelectedBaseline, finiteA, finiteMass, treatOnlyType, sub_ite, mul_ite]

/-- T17(c): three equally likely types with μ₀=(0,1,3).
Treat only type 0: baseline 2. Leave only type 0 untreated: baseline 0. -/
theorem T17_three_type_example :
    finiteSelectedBaseline (fun _ : Fin 3 => 1/3) ![0,1,3]
      (treatOnlyType 0) = 2 ∧
    finiteSelectedBaseline (fun _ : Fin 3 => 1/3) ![0,1,3]
      (leaveOnlyType 0) = 0 ∧ (2 : ℝ) ≠ 0 := by
  norm_num [finiteSelectedBaseline, finiteA, finiteMass, treatOnlyType,
    leaveOnlyType, Fin.sum_univ_succ]


/-- T16 finite convexity lemma: any nonnegative normalized distribution of
untreated types gives a baseline between the smallest and largest type means.
Lower and upper bounds are arbitrary, so this includes attained extrema. -/
theorem finite_convex_mean_bounds {K : ℕ} (p m : Fin K → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (l h : ℝ)
    (hb : ∀ i, l ≤ m i ∧ m i ≤ h) :
    l ≤ (∑ i, p i*m i) ∧ (∑ i, p i*m i) ≤ h := by
  constructor
  · calc
      l = ∑ i, p i*l := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ i, p i*m i := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hb i).1 (hp i))
  · calc
      (∑ i, p i*m i) ≤ ∑ i, p i*h := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hb i).2 (hp i))
      _ = h := by rw [← Finset.sum_mul, hsum, one_mul]

/-- T23 (P006-N005): probability of Y0=1 is 1/2 in World A and 3/4 in
World B. X is the singleton 0 and Y1 is the constant 1. -/
def missingWorldPrevalence (world : Bool) : ℝ := if world then 3/4 else 1/2

/-- T23: untreated observation probabilities are 1/4 versus 3/4 according
to Y0 in World A, and 1/2 for both Y0 values in World B. -/
def missingObservationProbability (world y0 : Bool) : ℝ :=
  if world then 1/2 else if y0 then 3/4 else 1/4

/-- T23: the entire finite joint law of (Y0,T,R), generated in the order
Y0, independent fair T, then possibly outcome-dependent R. All treated
outcomes are observed. This order verifies treatment ignorability explicitly. -/
def missingWorldMass (world y0 t r : Bool) : ℝ :=
  coinMass (missingWorldPrevalence world) y0 * (1/2 : ℝ) *
    (if t then (if r then 1 else 0)
      else coinMass (missingObservationProbability world y0) r)

/-- T23: the observed record (T,R,Z), with Z missing when R=0.
X=0 is suppressed because it is the same fixed constant in both worlds. -/
def missingRecord (y0 t r : Bool) : Bool × Bool × Option Bool :=
  (t,r,if r then some (if t then true else y0) else none)

/-- T23: the induced observed-data probability mass, including the
observation indicator rather than hiding the missingness. -/
def missingObservedMass (world : Bool) (record : Bool × Bool × Option Bool) : ℝ :=
  ∑ y0 : Bool, ∑ t : Bool, ∑ r : Bool, missingWorldMass world y0 t r *
    (if missingRecord y0 t r = record then 1 else 0)

/-- T23: the population untreated mean and the available untreated mean. -/
def missingWorldMean (world : Bool) : ℝ :=
  ∑ y0 : Bool, ∑ t : Bool, ∑ r : Bool, missingWorldMass world y0 t r * bit y0

/-- Appendix A.1 item 2, PDF p. 13: the mean "untreated outcomes" among observed untreated units, normalized by their observed probability, in T23's finite worlds. -/
def missingUntreatedObservedMean (world : Bool) : ℝ :=
  (∑ y0 : Bool, missingWorldMass world y0 false true * bit y0) /
    (∑ y0 : Bool, missingWorldMass world y0 false true)

/-- P006-T23 (Appendix A.1(2), PDF p. 13), exact nonidentification witness.
Both full joint tables are probability distributions. Potential outcomes and
treatment factorize, untreated and observed-untreated positivity hold,
and every observed record has the same mass. Nevertheless μ₀ is 1/2 in
World A and 3/4 in World B; the observed untreated mean is 3/4 in both. -/
theorem T23_missing_outcome_counterexample :
    (∀ world y0 t r, 0 ≤ missingWorldMass world y0 t r) ∧
    (∀ world, (∑ y0 : Bool, ∑ t : Bool, ∑ r : Bool,
      missingWorldMass world y0 t r) = 1) ∧
    (∀ world y0 t, (∑ r : Bool, missingWorldMass world y0 t r) =
      coinMass (missingWorldPrevalence world) y0 * (1/2 : ℝ)) ∧
    (∀ world, (∑ y0 : Bool, ∑ r : Bool,
      missingWorldMass world y0 false r) = 1/2 ∧
      (∑ y0 : Bool, missingWorldMass world y0 false true) = 1/4) ∧
    (∀ record, missingObservedMass false record = missingObservedMass true record) ∧
    missingWorldMean false = 1/2 ∧ missingWorldMean true = 3/4 ∧
    (∀ world, missingUntreatedObservedMean world = 3/4) ∧
    missingUntreatedObservedMean false - missingWorldMean false = 1/4 := by
  have hmeans : missingWorldMean false = 1/2 ∧ missingWorldMean true = 3/4 := by
    norm_num [missingWorldMean, missingWorldMass, missingWorldPrevalence,
      missingObservationProbability, coinMass, bit, Fintype.sum_bool]
  have hobserved : ∀ world, missingUntreatedObservedMean world = 3/4 := by
    intro world; cases world <;>
      norm_num [missingUntreatedObservedMean, missingWorldMass, missingWorldPrevalence,
        missingObservationProbability, coinMass, bit, Fintype.sum_bool]
  refine ⟨?_, ?_, ?_, ?_, ?_, hmeans.1, hmeans.2, hobserved, ?_⟩
  · intro world y0 t r; cases world <;> cases y0 <;> cases t <;> cases r <;>
      norm_num [missingWorldMass, missingWorldPrevalence, missingObservationProbability, coinMass]
  · intro world; cases world <;>
      norm_num [missingWorldMass, missingWorldPrevalence, missingObservationProbability,
        coinMass, Fintype.sum_bool]
  · intro world y0 t; cases world <;> cases y0 <;> cases t <;>
      norm_num [missingWorldMass, missingWorldPrevalence, missingObservationProbability,
        coinMass, Fintype.sum_bool]
  · intro world; cases world <;>
      norm_num [missingWorldMass, missingWorldPrevalence, missingObservationProbability,
        coinMass, Fintype.sum_bool]
  · rintro ⟨t,r,z⟩
    cases t <;> cases r <;> cases z with
    | none =>
        norm_num [missingObservedMass, missingRecord, missingWorldMass,
          missingWorldPrevalence, missingObservationProbability, coinMass, Fintype.sum_bool]
    | some y =>
        cases y <;> norm_num [missingObservedMass, missingRecord, missingWorldMass,
          missingWorldPrevalence, missingObservationProbability, coinMass, Fintype.sum_bool]
  · rw [hobserved false, hmeans.1]; norm_num


/-- T24(ii)'s finite algebra: for a proper observed fraction 0<q<1,
the observed mean equals the mixture mean iff it equals the missing mean. -/
theorem T24_mixture_mean_iff (q m1 m0 : ℝ) (hq : 0 < q ∧ q < 1) :
    m1 = q*m1+(1-q)*m0 ↔ m1 = m0 := by
  constructor
  · intro h
    have hp : 0 < 1-q := by linarith [hq.2]
    have heq : (1-q)*(m1-m0) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (ne_of_gt hp))
  · intro h; rw [h]; ring

/-- Positive scaling preserves all maximizers; the n>0 factor in total
rewards, as used in Propositions 3,5,9 and the ranking proofs. -/
theorem scale_best_iff {P : Type*} (PiSet : Set P) (f : P → ℝ)
    (c : ℝ) (hc : 0 < c) (π : P) :
    IsBest PiSet (fun p => c*f p) π ↔ IsBest PiSet f π := by
  constructor
  · rintro ⟨hπ,hmax⟩
    refine ⟨hπ, ?_⟩
    intro p hp
    have hh := hmax p hp
    change c*f p ≤ c*f π at hh
    exact (mul_le_mul_iff_right₀ hc).mp hh
  · rintro ⟨hπ,hmax⟩
    refine ⟨hπ, ?_⟩
    intro p hp
    change c*f p ≤ c*f π
    exact (mul_le_mul_iff_right₀ hc).mpr (hmax p hp)

/-- Proposition 5's outcomes, Appendix D.2, PDF pp. 22–23:
"μ₀(x,0)=α; μ₀(x,1)=−α", "μ₁(x,0)=β; μ₁(x,1)=0".
η=0 gives the printed example; η>0 gives a variant with a unique best response.
X is the constant 0 and U is a fair binary variable. -/
def lowerBoundY0 (α : ℝ) (u : Bool) : ℝ := if u then -α else α

/-- Proposition 5 proof, PDF p. 22: "μ1(0)=β, μ1(1)=0"; η=0 gives the printed construction, η>0 gives the corrected unique-response perturbation. -/
def lowerBoundY1 (β η : ℝ) (u : Bool) : ℝ := if u then -η else β

/-- T25: the exact expected TT reward per patient, with μ̂₀=μ₀(X)=0.
The finite treatment sum is retained rather than assuming the displayed
objective of the paper's proof. -/
def lowerBoundReward (β η : ℝ) (π : BinaryPolicy) : ℝ :=
  oneTT (lowerBoundY1 β η) (fun _ _ => 0) π

/-- T25: V(π)=E[π(X,U)τ(X,U)] over the same fair binary U law. -/
def lowerBoundWelfare (α β η : ℝ) (π : BinaryPolicy) : ℝ :=
  binaryWelfare (1/2) (fun u => lowerBoundY1 β η u-lowerBoundY0 α u) π

/-- T25: the exact marginal heterogeneity from Assumption 2, PDF p. 6.
The marginal untreated mean is zero in this family. -/
def lowerBoundGamma (α : ℝ) : ℝ :=
  (∑ u : Bool, (1/2 : ℝ)*|0-lowerBoundY0 α u|)

/-- T25(i),(iii),(v): exact reward, welfare, and marginal-baseline formulas. -/
theorem lower_bound_formulas (α β η : ℝ) (π : BinaryPolicy) :
    lowerBoundReward β η π = (β*π.1-η*π.2)/2 ∧
    lowerBoundWelfare α β η π = ((β-α)*π.1+(α-η)*π.2)/2 ∧
    (∑ u : Bool, (1/2 : ℝ)*lowerBoundY0 α u) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold lowerBoundReward
    rw [oneTT_formula]
    simp [lowerBoundY1]; ring
  · dsimp [lowerBoundWelfare, binaryWelfare, lowerBoundY1, lowerBoundY0]; ring
  · simp [lowerBoundY0, Fintype.sum_bool]

/-- T25(v): γ_marg=α, so no smaller heterogeneity bound is possible. -/
theorem lower_bound_gamma_eq (α : ℝ) (hα : 0 ≤ α) :
    lowerBoundGamma α = α := by
  simp [lowerBoundGamma, lowerBoundY0, abs_of_nonneg hα, abs_neg, Fintype.sum_bool]
  ring

/-- T25(ii): the entire best-response set in the printed example:
p₀=1 while p₁ is arbitrary. This preserves the paper's existential reading
and does not falsely claim uniqueness of its displayed policy. -/
theorem lower_bound_best_response_iff (β : ℝ) (hβ : 0 < β) (π : BinaryPolicy) :
    IsBest binaryPolicies (lowerBoundReward β 0) π ↔
      binaryFeasible π ∧ π.1 = 1 := by
  have forms := lower_bound_formulas (0:ℝ) β 0
  constructor
  · rintro ⟨hπ,hmax⟩
    have hh := hmax (1,0) (by norm_num [binaryPolicies, binaryFeasible])
    rw [(forms (1,0)).1, (forms π).1] at hh
    rcases hπ with ⟨h0,h0u,h1,h1u⟩
    exact ⟨⟨h0,h0u,h1,h1u⟩, by dsimp at hh; nlinarith⟩
  · rintro ⟨hπ,heq⟩
    refine ⟨hπ, ?_⟩
    intro q hq
    rcases hq with ⟨h0,h0u,h1,h1u⟩
    rw [(forms q).1, (forms π).1, heq]
    nlinarith

/-- T25(iii): in both the printed and perturbed family, the welfare optimum
treats U=1 and not U=0, with value (α−η)/2. -/
theorem lower_bound_welfare_optimum (α β η : ℝ) (hβα : β < α) (hηα : η < α) :
    IsBest binaryPolicies (lowerBoundWelfare α β η) (0,1) ∧
    bestValue binaryPolicies (lowerBoundWelfare α β η) = (α-η)/2 := by
  have forms := lower_bound_formulas α β η
  have hw : IsBest binaryPolicies (lowerBoundWelfare α β η) (0,1) := by
    refine ⟨by norm_num [binaryPolicies,binaryFeasible], ?_⟩
    intro q hq
    rcases hq with ⟨h0,h0u,h1,h1u⟩
    have hm0 : (β-α)*q.1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) h0
    have hm1 : (α-η)*q.2 ≤ α-η := by nlinarith
    rw [(forms q).2.1, (forms (0,1)).2.1]
    dsimp; linarith
  refine ⟨hw, ?_⟩
  rw [bestValue_eq hw, (forms (0,1)).2.1]
  ring

/-- P006-T25(i)–(v), Proposition 5 and its corrected reward display,
PDF pp. 7,22–23. All finite expectations, the complete argmax set,
welfare maximum, selected and arbitrary best-response regrets, and the
tight heterogeneity constant are proved for the printed family. -/
theorem T25_printed_lower_bound_family (n : ℕ) (hn : 0 < n)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hβα : β < α) :
    (∀ π, (n : ℝ)*lowerBoundReward β 0 π = (n : ℝ)*β*π.1/2) ∧
    (∀ π, IsBest binaryPolicies (fun p => (n : ℝ)*lowerBoundReward β 0 p) π ↔
      binaryFeasible π ∧ π.1 = 1) ∧
    IsBest binaryPolicies (lowerBoundWelfare α β 0) (0,1) ∧
    bestValue binaryPolicies (lowerBoundWelfare α β 0) = α/2 ∧
    (∀ π, IsBest binaryPolicies (fun p => (n : ℝ)*lowerBoundReward β 0 p) π →
      regret binaryPolicies (lowerBoundWelfare α β 0) π = α-β/2-α*π.2/2) ∧
    regret binaryPolicies (lowerBoundWelfare α β 0) (1,0) = α-β/2 ∧
    lowerBoundGamma α = α := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hw := lower_bound_welfare_optimum α β 0 hβα hα
  have hv : bestValue binaryPolicies (lowerBoundWelfare α β 0) = α/2 := by
    simpa using hw.2
  refine ⟨?_, ?_, hw.1, hv, ?_, ?_, lower_bound_gamma_eq α hα.le⟩
  · intro π; rw [(lower_bound_formulas α β 0 π).1]; ring
  · intro π
    rw [scale_best_iff _ _ _ hnr, lower_bound_best_response_iff β hβ]
  · intro π hπ
    have hp0 := (lower_bound_best_response_iff β hβ π).mp
      ((scale_best_iff _ _ _ hnr π).mp hπ)
    rw [regret, hv, (lower_bound_formulas α β 0 π).2.1, hp0.2]
    ring
  · rw [regret, hv, (lower_bound_formulas α β 0 (1,0)).2.1]; ring

/-- P006-T25(vi), headline Proposition 5 (PDF p. 7).
For each α>0 and ε>0 choose β=min(ε,α/2). The paper's displayed policy
(1,0) is a best response with regret at least γ_marg−ε, for any n≥1.
This is existence of a bad best response, not a universal assertion about
all tied best responses of the printed family. -/
theorem T25_existential_lower_bound (n : ℕ) (hn : 0 < n)
    (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ β < α ∧
      IsBest binaryPolicies (fun π => (n : ℝ)*lowerBoundReward β 0 π) (1,0) ∧
      regret binaryPolicies (lowerBoundWelfare α β 0) (1,0) ≥ lowerBoundGamma α-ε := by
  let β := min ε (α/2)
  have hβ : 0 < β := lt_min hε (by linarith)
  have hβε : β ≤ ε := min_le_left _ _
  have hβα2 : β ≤ α/2 := min_le_right _ _
  have hβα : β < α := by linarith
  have hF := T25_printed_lower_bound_family n hn α β hα hβ hβα
  refine ⟨β,hβ,hβα,?_,?_⟩
  · exact (hF.2.1 (1,0)).mpr ⟨by norm_num [binaryFeasible],rfl⟩
  · rw [hF.2.2.2.2.2.1, lower_bound_gamma_eq α hα.le]; linarith

/-- T25(vii): with μ₁(U=1)=−η and β,η>0 the maximizing response is uniquely
(1,0), and not a freely selected member of a tie. -/
theorem lower_bound_perturbed_best_iff (β η : ℝ) (hβ : 0 < β) (hη : 0 < η)
    (π : BinaryPolicy) :
    IsBest binaryPolicies (lowerBoundReward β η) π ↔ π = (1,0) := by
  have forms := lower_bound_formulas (0:ℝ) β η
  constructor
  · rintro ⟨hπ,hmax⟩
    have hh := hmax (1,0) (by norm_num [binaryPolicies,binaryFeasible])
    rw [(forms (1,0)).1, (forms π).1] at hh
    rcases hπ with ⟨h0,h0u,h1,h1u⟩
    have hm0 : β*π.1 ≤ β := by nlinarith
    have hm1 : 0 ≤ η*π.2 := mul_nonneg hη.le h1
    have hp1 : π.2 = 0 := by dsimp at hh; nlinarith
    have hp0 : π.1 = 1 := by dsimp at hh; rw [hp1] at hh; nlinarith
    exact Prod.ext hp0 hp1
  · rintro rfl
    refine ⟨by norm_num [binaryPolicies,binaryFeasible], ?_⟩
    intro q hq; rcases hq with ⟨h0,h0u,h1,h1u⟩
    have hm0 : β*q.1 ≤ β := by nlinarith
    have hm1 : 0 ≤ η*q.2 := mul_nonneg hη.le h1
    rw [(forms q).1, (forms (1,0)).1]
    dsimp; linarith

/-- P006-T25(vii): a variant with a unique best response.
Set β=η=min(ε,α/2). Every best response is (1,0) and has
R=α−(β+η)/2≥γ_marg−ε. This variant is separate from the
printed existential lower-bound construction. -/
theorem T25_unique_response_variant (n : ℕ) (hn : 0 < n)
    (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < α ∧
      IsBest binaryPolicies (fun π => (n : ℝ)*lowerBoundReward δ δ π) (1,0) ∧
      (∀ π, IsBest binaryPolicies (fun p => (n : ℝ)*lowerBoundReward δ δ p) π →
        π = (1,0) ∧
        regret binaryPolicies (lowerBoundWelfare α δ δ) π =
          α-(δ+δ)/2 ∧
        regret binaryPolicies (lowerBoundWelfare α δ δ) π ≥ lowerBoundGamma α-ε) := by
  let δ := min ε (α/2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδα2 : δ ≤ α/2 := min_le_right _ _
  have hδα : δ < α := by linarith
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hb : ∀ π, IsBest binaryPolicies (fun p => (n : ℝ)*lowerBoundReward δ δ p) π ↔
      π = (1,0) := by
    intro π; rw [scale_best_iff _ _ _ hnr, lower_bound_perturbed_best_iff δ δ hδ hδ]
  refine ⟨δ,hδ,hδα,(hb (1,0)).mpr rfl,?_⟩
  intro π hπ
  have heq := (hb π).mp hπ
  have hw := (lower_bound_welfare_optimum α δ δ hδα hδα).2
  have hr : regret binaryPolicies (lowerBoundWelfare α δ δ) π = α-(δ+δ)/2 := by
    rw [heq, regret, hw, (lower_bound_formulas α δ δ (1,0)).2.1]; ring
  refine ⟨heq,hr,?_⟩
  rw [hr, lower_bound_gamma_eq α hα.le]; linarith


/-- Exact i.i.d. finite-sample ATO expectation for arbitrary sample size,
used to state every sample-size clause of the Proposition 1 family (T29).
Both covariate and treatment vectors are summed with their product masses. -/
def finiteIIDAverage (n : ℕ) (p : ℝ) (m : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ X : Fin n → Bool, ∑ T : Fin n → Bool,
    (∏ i, coinMass p (X i)) * (∏ i, coinMass (binaryRule π (X i)) (T i)) *
      wATO T (fun i => m (X i))


/-- Finite conditional estimator/treatment model for T6 and T7.
p is the covariate law, r(x,a) the auxiliary/evaluation estimator law given x,
and treatment is an independent Bernoulli draw given x. This permits random
estimators correlated with the evaluated covariate. All moments below are
finite sums, and the condition is the corrected treated moment, not merely
fixed-x unbiasedness. The actual weighted TT reward is evaluated at n=1
before its n-patient expectation multiplier is applied. -/
def finiteRandomWeightedTT {K L : ℕ} (n : ℕ) (p : Fin K → ℝ)
    (r : Fin K → Fin L → ℝ) (μ1 : Fin K → ℝ) (est : Fin L → Fin K → ℝ)
    (g π : Fin K → ℝ) : ℝ :=
  (n : ℝ) * ∑ x, p x * ∑ a, r x a *
    ∑ t : Bool, coinMass (π x) t *
      wWeightedTT (est a) g ![x] ![t] ![μ1 x]

/-- T6(i)/T7(i), finite exact expected-reward lemma.
The corrected treated moment makes the random evaluated baseline cancel
even if the estimator's conditional law depends on x. The conclusion is
proved from the reward's full probability-weighted treatment/estimator sum. -/
theorem T6_finite_reward_identity {K L : ℕ} (n : ℕ) (p : Fin K → ℝ)
    (r : Fin K → Fin L → ℝ) (μ0 μ1 : Fin K → ℝ)
    (est : Fin L → Fin K → ℝ) (g π : Fin K → ℝ)
    (hr : ∀ x, ∑ a, r x a = 1)
    (hU : ∀ x, π x*(∑ a, r x a*(est a x-μ0 x)) = 0) :
    finiteRandomWeightedTT n p r μ1 est g π =
      (n : ℝ)*(∑ x, p x*π x*(μ1 x-μ0 x)*g x) := by
  have base (x : Fin K) (a : Fin L) :
      (∑ t : Bool, coinMass (π x) t *
        wWeightedTT (est a) g ![x] ![t] ![μ1 x]) =
          π x*(μ1 x-est a x)*g x := by
    simp [coinMass,wWeightedTT,bit,Fintype.sum_bool,Fin.sum_univ_one,mul_assoc]
  have inner (x : Fin K) :
      (∑ a, r x a*(π x*(μ1 x-est a x)*g x)) =
        π x*g x*(μ1 x-∑ a, r x a*est a x) := by
    calc
      (∑ a, r x a*(π x*(μ1 x-est a x)*g x)) =
          π x*g x*(∑ a, r x a*(μ1 x-est a x)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha; ring
      _ = _ := by
        simp_rw [mul_sub,Finset.sum_sub_distrib]
        rw [← Finset.sum_mul,hr x,one_mul]
        ring
  unfold finiteRandomWeightedTT
  simp_rw [base]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [inner]
  have herror := hU x
  simp_rw [mul_sub,Finset.sum_sub_distrib] at herror
  rw [← Finset.sum_mul,hr x,one_mul] at herror
  have he : π x*(μ1 x-∑ a, r x a*est a x) = π x*(μ1 x-μ0 x) := by
    nlinarith
  calc
    p x*(π x*g x*(μ1 x-∑ a, r x a*est a x)) =
      p x*(π x*(μ1 x-∑ a, r x a*est a x))*g x := by ring
    _ = p x*(π x*(μ1 x-μ0 x))*g x := by rw [he]
    _ = _ := by ring

/-- T6(ii), finite random-estimator model: the actual expected TT reward
and welfare have the same argmax set for every feasible class, and every TT
best response has zero regret. -/
theorem T6_finite_corrected_alignment {K L : ℕ} (n : ℕ) (hn : 0 < n)
    (p : Fin K → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (r : Fin K → Fin L → ℝ) (hr0 : ∀ x a, 0 ≤ r x a) (hr : ∀ x, ∑ a, r x a = 1)
    (μ0 μ1 : Fin K → ℝ) (est : Fin L → Fin K → ℝ) (PiSet : Set (Fin K → ℝ))
    (hπ : PiSet ⊆ finitePolicies)
    (hU : ∀ π ∈ PiSet, ∀ x, π x*(∑ a, r x a*(est a x-μ0 x)) = 0) :
    let V := finiteA p (fun x => μ1 x-μ0 x)
    let S := finiteRandomWeightedTT n p r μ1 est (fun _ => 1)
    (∀ π ∈ PiSet, S π = (n : ℝ)*V π) ∧
    (∀ π, IsBest PiSet S π ↔ IsBest PiSet V π) ∧
    (∀ π, IsBest PiSet S π → regret PiSet V π = 0) := by
  dsimp
  have identity (π : Fin K → ℝ) (hπ : π ∈ PiSet) :
      finiteRandomWeightedTT n p r μ1 est (fun _ => 1) π =
        (n : ℝ)*finiteA p (fun x => μ1 x-μ0 x) π := by
    rw [T6_finite_reward_identity n p r μ0 μ1 est (fun _ => 1) π hr (hU π hπ)]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx; dsimp; ring
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have eqbest (π : Fin K → ℝ) :
      IsBest PiSet (finiteRandomWeightedTT n p r μ1 est (fun _ => 1)) π ↔
        IsBest PiSet (finiteA p (fun x => μ1 x-μ0 x)) π := by
    constructor
    · rintro ⟨hπ,hmax⟩
      refine ⟨hπ,?_⟩
      intro q hq
      have hh := hmax q hq
      rw [identity q hq, identity π hπ] at hh
      exact (mul_le_mul_iff_right₀ hnr).mp hh
    · rintro ⟨hπ,hmax⟩
      refine ⟨hπ,?_⟩
      intro q hq
      rw [identity q hq,identity π hπ]
      exact (mul_le_mul_iff_right₀ hnr).mpr (hmax q hq)
  refine ⟨identity,eqbest,?_⟩
  intro π hb
  rw [regret,bestValue_eq ((eqbest π).mp hb)]
  ring

/-- Lemma 1 and Theorem 1's exact pointwise inequality (PDF pp. 15–16,19):
for any treatment probability in [0,1], πτ≤τ1(τ>0). -/
theorem pointwise_policy_gain_le (t q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    t*q ≤ positivePart t := by
  by_cases ht : 0 < t
  · simp only [positivePart,if_pos ht,mul_one]
    nlinarith [hq.2]
  · simp only [positivePart,if_neg ht,mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt ht) hq.1

/-- T7(ii), exact finite optimization lemma for strictly positive weights.
The unconstrained positive-effect rule maximizes both weighted expected
treatment gain and unweighted welfare, with zero welfare regret.
No arbitrary feasible class is substituted for the unconstrained one. -/
theorem T7_finite_positive_rule {K : ℕ} (p g τ : Fin K → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hg : ∀ x, 0 < g x) :
    IsBest finitePolicies (finiteA p (fun x => g x*τ x)) (positiveRule τ) ∧
    IsBest finitePolicies (finiteA p τ) (positiveRule τ) ∧
    regret finitePolicies (finiteA p τ) (positiveRule τ) = 0 := by
  have hfeas : positiveRule τ ∈ finitePolicies := by
    intro x; unfold positiveRule; split_ifs <;> norm_num
  have opt (w : Fin K → ℝ) (hw : ∀ x, 0 ≤ w x) :
      IsBest finitePolicies (fun π => ∑ x, w x*τ x*π x) (positiveRule τ) := by
    refine ⟨hfeas,?_⟩
    intro π hπ
    apply Finset.sum_le_sum
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (pointwise_policy_gain_le (τ x) (π x) (hπ x)) (hw x)
    simpa [positivePart,positiveRule,mul_assoc] using hh
  have hv : IsBest finitePolicies (finiteA p τ) (positiveRule τ) := opt p hp
  have hw : IsBest finitePolicies (finiteA p (fun x => g x*τ x)) (positiveRule τ) := by
    have ho := opt (fun x => p x*g x) (fun x => mul_nonneg (hp x) (hg x).le)
    change IsBest finitePolicies (fun π => ∑ x, p x*(g x*τ x)*π x) _
    simpa only [mul_assoc] using ho
  exact ⟨hw,hv,by rw [regret,bestValue_eq hv];ring⟩


/-- Reward Functions 1 and 2, PDF p. 4: when μ̂0=0 the two realized
zero-on-empty average rewards coincide, for every sample and treatment vector.
This certifies that T1 refutes both printed propositions with the same law. -/
theorem wATT_zero {C : Type*} {n : ℕ} (X : Fin n → C)
    (T : Fin n → Bool) (Y : Fin n → ℝ) :
    wATT (fun _ => 0) X T Y = wATO T Y := by
  simp [wATT]

/-- T1(c), first proof displays of Propositions 6 and 7 (PDF pp. 15–16):
the population treated conditional mean is 1, while the unconditional
finite-sample average reward is 3/4 at the printed rule. -/
theorem T1_conditional_mean_mismatch :
    finiteConditionalAverage (fun _ : Fin 2 => 1/2) ![9/10,1] ![0,1] = 1 ∧
    rewardE001 (0,1) = 3/4 ∧ (3/4 : ℝ) < 1 := by
  rw [rewardE001_formula]
  norm_num [finiteConditionalAverage,finiteMass,finiteA,Fin.sum_univ_two]

/-- Reward Functions 2 and 3, PDF pp. 4–5: with one unit the zero-on-empty
ATT reward equals TT for every realized baseline, outcome and treatment.
Thus the one-unit estimator witnesses in T4 apply to both rewards. -/
theorem wATT_one_eq_TT {C : Type*} (μhat : C → ℝ) (x : C) (t : Bool) (y : ℝ) :
    wATT μhat ![x] ![t] ![y] = wTT μhat ![x] ![t] ![y] := by
  cases t <;> simp [wATT,wTT,wWeightedTT,wATO,treatedCount,bit,Fin.sum_univ_one]

/-- T29's first failure mode (Proposition 1 proof, PDF p. 17):
for every 0<p<1 and α<0 the welfare optimum treats both types and the
regret of the ATO policy (0,1) is −α(1−p).
This finite welfare identity does not assume the invalid general rule
of Proposition 6. -/
theorem T29_first_mode_welfare (p α : ℝ) (hp : 0 < p ∧ p < 1) (hα : α < 0) :
    IsBest binaryPolicies
      (binaryWelfare p (fun x => if x then 1 else -α)) (1,1) ∧
    bestValue binaryPolicies (binaryWelfare p (fun x => if x then 1 else -α)) =
      -α*(1-p)+p ∧
    regret binaryPolicies (binaryWelfare p (fun x => if x then 1 else -α)) (0,1) =
      -α*(1-p) := by
  have hbest : IsBest binaryPolicies
      (binaryWelfare p (fun x => if x then 1 else -α)) (1,1) := by
    refine ⟨by norm_num [binaryPolicies,binaryFeasible],?_⟩
    intro π hπ
    have h0 := mul_le_mul_of_nonneg_left hπ.2.1
      (mul_nonneg (by linarith : 0 ≤ 1-p) (by linarith : 0 ≤ -α))
    have h1 := mul_le_mul_of_nonneg_left hπ.2.2.2 hp.1.le
    dsimp [binaryWelfare]
    nlinarith
  refine ⟨hbest,?_,?_⟩
  · rw [bestValue_eq hbest]; dsimp [binaryWelfare]; ring
  · rw [regret,bestValue_eq hbest]; dsimp [binaryWelfare]; ring

/-- T29, Proposition 1 proof, PDF p. 17: its first-mode regret tends to
+∞ as α tends to −∞ at fixed p∈(0,1). This is the stated filter limit of
the exact finite welfare-regret identity above. -/
theorem T29_first_mode_tendsto (p : ℝ) (hp : p < 1) :
    Tendsto (fun α : ℝ => -α*(1-p)) atBot atTop := by
  apply tendsto_atTop.2
  intro M
  filter_upwards [eventually_le_atBot (-M/(1-p))] with α hα
  have hpos : 0 < 1-p := by linarith
  have hh := (le_div_iff₀ hpos).mp hα
  nlinarith

/-- Section 2, PDF p. 3 and Appendix B.1, p. 14: expectation of an additive
reward over n iid units is n times its one-unit expectation. This finite
lemma derives the identity from the full product probability sum; it does
not define that expectation to be n times a marginal mean. -/
theorem iid_additive_expectation {A : Type*} [Fintype A] (n : ℕ)
    (p f : A → ℝ) (hp : ∑ a, p a = 1) :
    (∑ z : Fin n → A, (∏ i, p (z i)) * (∑ i, f (z i))) =
      (n : ℝ)*(∑ a, p a*f a) := by
  have marginal (i : Fin n) :
      (∑ z : Fin n → A, (∏ j, p (z j))*f (z i)) = ∑ a, p a*f a := by
    have factor (z : Fin n → A) :
        (∏ j, p (z j))*f (z i) =
          ∏ j, p (z j)*(if j = i then f (z j) else 1) := by
      rw [Finset.prod_mul_distrib,Fintype.prod_ite_eq']
    simp_rw [factor]
    rw [← Fintype.prod_sum (fun (j : Fin n) (a : A) =>
      p a*(if j = i then f a else 1))]
    have term (j : Fin n) :
        (∑ a, p a*(if j = i then f a else 1)) =
          (if j = i then (∑ a, p a*f a) else 1) := by
      by_cases hj : j = i
      · simp [hj]
      · simp [hj,hp]
    simp_rw [term]
    simp [Fintype.prod_ite_eq']
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [marginal]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.mul_sum]

/-- Section 2, PDF p. 3; Reward Function 3, p. 5: the actual iid n-patient
TT expectation for deterministic treated potential means and μ̂0=0 on
fair binary covariates. The product law is over every vector of covariate
and independent conditional-Bernoulli treatment realizations. -/
def finiteIIDTT (n : ℕ) (y1 : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ z : Fin n → (Bool × Bool),
    (∏ i, (1/2 : ℝ)*coinMass (binaryRule π (z i).1) (z i).2) *
      wTT (fun _ => 0) (fun i => (z i).1) (fun i => (z i).2)
        (fun i => y1 (z i).1)

/-- T25(i), corrected reward display, PDF p. 22: the n multiplier in the
printed lower-bound construction follows from the actual full iid sample
reward. Potential outcomes on untreated units do not affect the TT reward
because their contributions are multiplied by zero. -/
theorem T25_exact_sample_reward (n : ℕ) (β η : ℝ) (π : BinaryPolicy) :
    finiteIIDTT n (lowerBoundY1 β η) π = (n : ℝ)*lowerBoundReward β η π := by
  let p : Bool × Bool → ℝ := fun z => (1/2 : ℝ)*coinMass (binaryRule π z.1) z.2
  let f : Bool × Bool → ℝ := fun z => lowerBoundY1 β η z.1*bit z.2
  have hp : ∑ z, p z = 1 := by
    simp [p,Fintype.sum_prod_type,coinMass,Fintype.sum_bool,binaryRule] <;> ring
  have hi := iid_additive_expectation n p f hp
  unfold finiteIIDTT wTT wWeightedTT
  simp only [sub_zero,mul_one]
  change (∑ z : Fin n → (Bool × Bool), (∏ i, p (z i)) * (∑ i, f (z i))) = _
  rw [hi]
  congr 1
  simp [p,f,lowerBoundReward,oneTT,wTT,wWeightedTT,Fin.sum_univ_one,
    Fintype.sum_prod_type]

/-- Appendix A.1(2), PDF p. 13: under outcome/treatment independence,
the mean untreated potential outcome among untreated units equals its
population mean whenever the untreated arm has positive probability.
This proves a conditional-stratum identification step using actual integrals. -/
theorem independent_untreated_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (hμ : IsProbabilityMeasure μ) (Y0 : Ω → ℝ) (T : Ω → Bool)
    (hY : Measurable Y0) (hT : Measurable T) (hint : Integrable Y0 μ)
    (hI : IndepFun Y0 T μ) (hp : 0 < (μ {ω | T ω = false}).toReal) :
    eventMean μ {ω | T ω = false} Y0 = (∫ ω, Y0 ω ∂μ) := by
  letI : IsProbabilityMeasure μ := hμ
  let A := {ω | T ω = false}
  let g : Bool → ℝ := fun t => if t = false then 1 else 0
  have hA : MeasurableSet A := measurableSet_eq_fun hT measurable_const
  have hg : Measurable g := measurable_of_finite _
  have he : (fun ω => g (T ω)) = A.indicator (fun _ => (1:ℝ)) := by
    funext ω
    cases ht : T ω <;> simp [g,A,Set.indicator,ht]
  have hIg : IndepFun Y0 (fun ω => g (T ω)) μ := by
    simpa [Function.comp_def] using hI.comp measurable_id hg
  have hprod := hIg.integral_fun_mul_eq_mul_integral hY.aestronglyMeasurable
    (hg.comp hT).aestronglyMeasurable
  have hep (ω : Ω) : g (T ω) = A.indicator (fun _ => (1:ℝ)) ω := congrFun he ω
  simp_rw [hep] at hprod
  have hone : (∫ ω, A.indicator (fun _ => (1:ℝ)) ω ∂μ) = (μ A).toReal := by
    simpa only [smul_eq_mul,mul_one,measureReal_def] using
      (integral_indicator_const (μ := μ) (1:ℝ) hA)
  rw [hone] at hprod
  have hl : (∫ ω, Y0 ω*A.indicator (fun _ => (1:ℝ)) ω ∂μ) =
      (∫ ω in A, Y0 ω ∂μ) := by
    rw [← integral_indicator hA]
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator,hω]
  rw [hl] at hprod
  unfold eventMean
  change (∫ ω in A, Y0 ω ∂μ) / (μ A).toReal = _
  rw [hprod]
  exact mul_div_cancel_right₀ _ (ne_of_gt hp)

/-- T24(i), corrected Appendix A.1(2), PDF p. 13: under the printed
no-confounding and positivity conditions plus representativeness in mean,
μ0(x) is the actual observed-untreated mean. This is quantified over every
conditional law at a fixed covariate stratum, with random observation R. -/
theorem T24_representative_identification {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (hμ : IsProbabilityMeasure μ)
    (Y0 Y1 : Ω → ℝ) (T R : Ω → Bool)
    (hm : Measurable Y0 ∧ Measurable Y1 ∧ Measurable T ∧ Measurable R)
    (hint : Integrable Y0 μ ∧ Integrable Y1 μ)
    (hI : IndepFun (fun ω => (Y0 ω,Y1 ω)) T μ)
    (hT : 0 < (μ {ω | T ω = false}).toReal)
    (hR : 0 < (μ {ω | T ω = false ∧ R ω = true}).toReal)
    (hrep : eventMean μ {ω | T ω = false ∧ R ω = true} Y0 =
      eventMean μ {ω | T ω = false} Y0) :
    (∫ ω, Y0 ω ∂μ) =
      eventMean μ {ω | T ω = false ∧ R ω = true}
        (fun ω => if T ω then Y1 ω else Y0 ω) := by
  have hI0 : IndepFun Y0 T μ := by
    simpa [Function.comp_def] using hI.comp measurable_fst measurable_id
  have hbase := independent_untreated_mean μ hμ Y0 T hm.1 hm.2.2.1 hint.1 hI0 hT
  have hA : MeasurableSet {ω | T ω = false ∧ R ω = true} :=
    (measurableSet_eq_fun hm.2.2.1 measurable_const).inter
      (measurableSet_eq_fun hm.2.2.2 measurable_const)
  calc
    (∫ ω, Y0 ω ∂μ) = eventMean μ {ω | T ω = false} Y0 := hbase.symm
    _ = eventMean μ {ω | T ω = false ∧ R ω = true} Y0 := hrep.symm
    _ = _ := by
      unfold eventMean
      congr 1
      apply setIntegral_congr_fun hA
      intro ω hω
      simp [hω.1]

/-- T2(iv), corrected Propositions 6–7, PDF pp. 15–16: on a finite
positive-mass support, the printed arg-max-only rule does maximize the
population conditional average A/q when the maximum mean is positive.
When all means are nonpositive, zero treatment maximizes the conventionally
zero-on-no-treatment conditional objective. This is the population objective,
not the actual finite-sample average reward. -/
theorem T2_population_conditional_rule {K : ℕ} (p m : Fin K → ℝ)
    (hp : ∀ i, 0 < p i) (j : Fin K) (hmax : ∀ i, m i ≤ m j) :
    if 0 < m j then
      IsBest finitePolicies (finiteConditionalAverage p m) (printedAverageRule m) ∧
        finiteConditionalAverage p m (printedAverageRule m) = m j
    else IsBest finitePolicies (finiteConditionalAverage p m) (fun _ => 0) := by
  have admiss : printedAverageRule m ∈ finitePolicies := by
    intro i
    unfold printedAverageRule
    split_ifs <;> norm_num
  have upper (π : Fin K → ℝ) (hπ : π ∈ finitePolicies) :
      finiteA p m π ≤ m j*finiteMass p π := by
    unfold finiteA finiteMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right (hmax i) (mul_nonneg (hp i).le (hπ i).1)
    nlinarith
  by_cases hj : 0 < m j
  · simp only [ite_eq_left hj]
    have rulej : printedAverageRule m j = 1 := by
      simp [printedAverageRule,hmax,hj]
    have qpos : 0 < finiteMass p (printedAverageRule m) := by
      have h := Finset.single_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin K))) =>
          mul_nonneg (hp i).le (admiss i).1) (Finset.mem_univ j)
      rw [rulej,mul_one] at h
      exact lt_of_lt_of_le (hp j) h
    have exactA : finiteA p m (printedAverageRule m) =
        m j*finiteMass p (printedAverageRule m) := by
      unfold finiteA finiteMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hr : (∀ z, m z ≤ m i) ∧ 0 < m i
      · have hmi : m i = m j := le_antisymm (hmax i) (hr.1 j)
        have hri : printedAverageRule m i = 1 := by simp [printedAverageRule,hr]
        rw [hri,hmi]
        ring
      · simp [printedAverageRule,hr]
    have value : finiteConditionalAverage p m (printedAverageRule m) = m j := by
      unfold finiteConditionalAverage
      rw [ite_eq_left qpos,exactA]
      exact mul_div_cancel_right₀ _ (ne_of_gt qpos)
    refine ⟨⟨admiss,?_⟩,value⟩
    intro π hπ
    rw [value]
    unfold finiteConditionalAverage
    by_cases hq : 0 < finiteMass p π
    · rw [ite_eq_left hq]
      exact (div_le_iff₀ hq).mpr (upper π hπ)
    · rw [ite_eq_right hq]
      exact hj.le
  · simp only [ite_eq_right hj]
    refine ⟨by intro i; norm_num,?_⟩
    intro π hπ
    have ha : finiteA p m π ≤ 0 := by
      unfold finiteA
      apply Finset.sum_nonpos
      intro i hi
      have hm : m i ≤ 0 := le_trans (hmax i) (le_of_not_gt hj)
      have h := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (hp i).le (hπ i).1) hm
      nlinarith
    have zero : finiteConditionalAverage p m (fun _ => 0) = 0 := by
      simp [finiteConditionalAverage,finiteMass,finiteA]
    rw [zero]
    unfold finiteConditionalAverage
    split_ifs with hq
    · exact div_nonpos_of_nonpos_of_nonneg ha hq.le
    · exact le_rfl

/-- Appendix D.2, PDF p. 21: "auxiliary data" independent of the treatment
population and randomization. This finite design draws one shared estimator
state a with law r, then n iid covariate/treatment pairs with mass
p(x) Bernoulli(π(x))(t). The realized reward is the printed weighted TT sum
with the same random function est(a,·) evaluated at every patient. -/
def finiteAuxWeightedTT {K L : ℕ} (n : ℕ) (p : Fin K → ℝ) (r : Fin L → ℝ)
    (μ1 : Fin K → ℝ) (est : Fin L → Fin K → ℝ) (g π : Fin K → ℝ) : ℝ :=
  ∑ a, r a * ∑ z : Fin n → (Fin K × Bool),
    (∏ i, p (z i).1*coinMass (π (z i).1) (z i).2) *
      wWeightedTT (est a) g (fun i => (z i).1) (fun i => (z i).2)
        (fun i => μ1 (z i).1)

/-- T6(iv)/T7(i), Appendix D.2, PDF p. 21: the full finite joint sample law
with one shared independent auxiliary-estimator function reduces to n
one-unit weighted reward expectations. The sample-size multiplier and
random evaluation are both derived from the actual realized reward. -/
theorem T6_finite_aux_actual_identity {K L : ℕ} (n : ℕ)
    (p : Fin K → ℝ) (hp : ∑ x, p x = 1) (r : Fin L → ℝ)
    (μ1 : Fin K → ℝ) (est : Fin L → Fin K → ℝ) (g π : Fin K → ℝ) :
    finiteAuxWeightedTT n p r μ1 est g π =
      finiteRandomWeightedTT n p (fun _ => r) μ1 est g π := by
  let q : Fin K × Bool → ℝ := fun z => p z.1*coinMass (π z.1) z.2
  let f : Fin L → Fin K × Bool → ℝ :=
    fun a z => (μ1 z.1-est a z.1)*bit z.2*g z.1
  have hq : ∑ z, q z = 1 := by
    rw [Fintype.sum_prod_type]
    have each (x : Fin K) : (∑ t : Bool, q (x,t)) = p x := by
      simp [q,coinMass,Fintype.sum_bool] <;> ring
    simp_rw [each]
    exact hp
  have sample (a : Fin L) :
      (∑ z : Fin n → (Fin K × Bool), (∏ i, q (z i))*
        wWeightedTT (est a) g (fun i => (z i).1) (fun i => (z i).2)
          (fun i => μ1 (z i).1)) =
      (n : ℝ)*(∑ x, p x*∑ t : Bool, coinMass (π x) t*
        wWeightedTT (est a) g ![x] ![t] ![μ1 x]) := by
    change (∑ z : Fin n → (Fin K × Bool), (∏ i, q (z i))*(∑ i, f a (z i))) = _
    rw [iid_additive_expectation n q (f a) hq]
    congr 1
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    simp [q,f,wWeightedTT,Fin.sum_univ_one,mul_assoc]
  unfold finiteAuxWeightedTT finiteRandomWeightedTT
  change (∑ a, r a*(∑ z : Fin n → (Fin K × Bool), (∏ i, q (z i))*
        wWeightedTT (est a) g (fun i => (z i).1) (fun i => (z i).2)
          (fun i => μ1 (z i).1))) = _
  simp_rw [sample]
  calc
    (∑ a, r a*((n : ℝ)*(∑ x, p x*∑ t : Bool, coinMass (π x) t*
        wWeightedTT (est a) g ![x] ![t] ![μ1 x]))) =
      (n : ℝ)*(∑ a, r a*(∑ x, p x*∑ t : Bool, coinMass (π x) t*
        wWeightedTT (est a) g ![x] ![t] ![μ1 x])) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha; ring
    _ = _ := by
      congr 1
      calc
        (∑ a, r a*(∑ x, p x*∑ t : Bool, coinMass (π x) t*
            wWeightedTT (est a) g ![x] ![t] ![μ1 x])) =
          ∑ a, ∑ x, r a*(p x*∑ t : Bool, coinMass (π x) t*
            wWeightedTT (est a) g ![x] ![t] ![μ1 x]) := by
          simp_rw [Finset.mul_sum]
        _ = ∑ x, ∑ a, r a*(p x*∑ t : Bool, coinMass (π x) t*
            wWeightedTT (est a) g ![x] ![t] ![μ1 x]) := by
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring

/-- T6(iv), corrected sufficient auxiliary-data implementation, PDF p. 21:
finite pointwise unbiasedness plus a shared auxiliary-estimator state drawn
independently of the evaluation design yields the exact actual weighted TT
identity. This permits a random function, not only a nonrandom oracle. -/
theorem T6_finite_auxiliary_estimation {K L : ℕ} (n : ℕ)
    (p : Fin K → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (r : Fin L → ℝ) (hr0 : ∀ a, 0 ≤ r a) (hr : ∑ a, r a = 1)
    (μ0 μ1 : Fin K → ℝ) (est : Fin L → Fin K → ℝ) (g π : Fin K → ℝ)
    (hπ : π ∈ finitePolicies) (hU : ∀ x, (∑ a, r a*est a x) = μ0 x) :
    finiteAuxWeightedTT n p r μ1 est g π =
      (n : ℝ)*(∑ x, p x*π x*(μ1 x-μ0 x)*g x) := by
  rw [T6_finite_aux_actual_identity n p hsum r μ1 est g π]
  apply T6_finite_reward_identity n p (fun _ => r) μ0 μ1 est g π (fun _ => hr)
  intro x
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [← Finset.sum_mul,hr,hU x]
  simp

/-- Assumption 2, PDF p. 6: "E[|μ0(X)−μ0(X,U)|]" for fair binary X
and a constant private covariate U. The two arguments are respectively the
principal's marginal and the full-information untreated conditional means. -/
def binaryMarginalHeterogeneity (b0 μ0 : Bool → ℝ) : ℝ :=
  ∑ x : Bool, (1/2 : ℝ)*|b0 x-μ0 x|

/-- T4(A5), Theorem 3 and Assumption 2, PDF pp. 6–7,22: the concrete
pointwise-unbiased estimator witness has γ_marg=0 with constant private U,
but its proved TT best-response regret 1/2 exceeds 2γ_marg. -/
theorem T4_zero_heterogeneity_bound_failure :
    binaryMarginalHeterogeneity (fun _ => 0) (fun _ => 0) = 0 ∧
    2*binaryMarginalHeterogeneity (fun _ => 0) (fun _ => 0) <
      regret binaryPolicies welfareA (0,0) := by
  have hg : binaryMarginalHeterogeneity (fun _ => 0) (fun _ => 0) = 0 := by
    simp [binaryMarginalHeterogeneity]
  have hr : regret binaryPolicies welfareA (0,0) = 1/2 :=
    T4_unbiasedness_counterexamples.2.2.2.2.2.1
  exact ⟨hg,by rw [hg,hr];norm_num⟩

/-- T15(a), Assumption 4, Appendix D.3, PDF p. 23: with the singleton
private covariate U, Δ(x,u)=0 for every covariate and every untreated mean
function, so E[Δ]=0 under any covariate law. This certifies γ_max=0 in both
untreated-positivity counterexample worlds, even when their μ0 values differ. -/
theorem T15_constant_private_heterogeneity {X : Type*} [MeasurableSpace X]
    (μ0 : (X × Unit) → ℝ) (PX : Measure (X × Unit)) :
    (∀ c, maximumDeviation μ0 c = 0) ∧
    (∫ c, maximumDeviation μ0 c ∂PX) = 0 := by
  have hd (c : X × Unit) : maximumDeviation μ0 c = 0 := by
    rcases c with ⟨x,u⟩
    cases u
    have he : (fun v : Unit => |μ0 (x,())-μ0 (x,v)|) = (fun _ => (0:ℝ)) := by
      funext v
      cases v
      simp
    change sSup (Set.range (fun v : Unit => |μ0 (x,())-μ0 (x,v)|)) = 0
    rw [he]
    simp
  refine ⟨hd,?_⟩
  simp_rw [hd]
  simp

/-- Section 2, PDF p. 3 (SUTVA and observation of treated outcomes only),
and Reward Functions 1–5, pp. 4–6,15: replacing an untreated outcome slot by
its treated potential outcome leaves each reward unchanged.
Thus the finite expectation formulas that fill untreated slots with μ1
compute exactly the rewards from the SUTVA observed outcomes. -/
theorem realized_rewards_SUTVA {C : Type*} {n : ℕ} (μhat g : C → ℝ)
    (X : Fin n → C) (T : Fin n → Bool) (Y0 Y1 : Fin n → ℝ) :
    wATO T (fun i => if T i then Y1 i else Y0 i) = wATO T Y1 ∧
    wATT μhat X T (fun i => if T i then Y1 i else Y0 i) = wATT μhat X T Y1 ∧
    wWeightedTT μhat g X T (fun i => if T i then Y1 i else Y0 i) =
      wWeightedTT μhat g X T Y1 ∧
    wTO T (fun i => if T i then Y1 i else Y0 i) = wTO T Y1 := by
  have numerator (b : Fin n → ℝ) :
      (∑ i, ((if T i then Y1 i else Y0 i)-b i)*bit (T i)) =
        (∑ i, (Y1 i-b i)*bit (T i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    cases ht : T i <;> simp [ht,bit]
  refine ⟨?_,?_,?_,?_⟩
  · unfold wATO
    have he := numerator (fun _ => 0)
    simp only [sub_zero] at he
    rw [he]
  · unfold wATT wATO
    rw [numerator (fun i => μhat (X i))]
  · unfold wWeightedTT
    apply Finset.sum_congr rfl
    intro i hi
    cases ht : T i <;> simp [ht,bit]
  · unfold wTO
    simpa only [sub_zero] using numerator (fun _ => 0)

/-- Section 2, PDF p. 3: "V(π)=E[Y_i(T_i^π)−Y_i(0)]" in the binary
finite-population models. Potential outcomes are deterministic given the
covariate; both the covariate law and the conditional treatment coin are
summed, and the observed outcome is explicitly the SUTVA outcome. -/
def binaryObservedWelfare (p : ℝ) (y0 y1 : Bool → ℝ) (π : BinaryPolicy) : ℝ :=
  ∑ x : Bool, ∑ t : Bool, coinMass p x*coinMass (binaryRule π x) t*
    ((if t then y1 x else y0 x)-y0 x)

/-- Lemma 1, PDF pp. 15–16: the exact finite welfare identity
E[Y(T)−Y0]=E[π(X)(Y1(X)−Y0(X))]. This derives the binary welfare functional
used in the counterexamples directly from the observed-potential-outcome
law, independently of any asserted incentive-alignment theorem. -/
theorem binaryWelfare_SUTVA (p : ℝ) (y0 y1 : Bool → ℝ) (π : BinaryPolicy) :
    binaryObservedWelfare p y0 y1 π =
      binaryWelfare p (fun x => y1 x-y0 x) π := by
  simp [binaryObservedWelfare,binaryWelfare,coinMass,binaryRule,Fintype.sum_bool] <;> ring

end
end AronowAudit.P006

