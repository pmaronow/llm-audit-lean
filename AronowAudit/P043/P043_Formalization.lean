import Mathlib

/-!
P043: Green, Aronow, Bergan, Greene, Paris, and Weinberger (2011), pp. 471–475.
The paper is an empirical report. The potential-outcome objects below are the
definitions used here, not notation or theorems claimed by the publication.
All expectations are exact finite weighted sums. Randomization is represented
by the product of a population law and a nondegenerate Bernoulli assignment.
-/

namespace AronowAudit.P043

open Finset
noncomputable section
universe u v

/-- A finite population law for the exact constructions in P043-N014 and P043-E002.
Weights are nonnegative and sum to one. This is a finite version of the
targets' population probability law. -/
structure Population (Ω : Type u) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

/-- Expectation over the population: `E[f]`. Every real-valued variable on
this finite space is integrable. -/
def mean {Ω : Type u} [Fintype Ω] (P : Population Ω) (f : Ω → ℝ) : ℝ :=
  ∑ i, P.mass i * f i

/-- The indicator `1{A}` of a population event. -/
def indicator (A : Prop) : ℝ := @ite ℝ A (Classical.propDecidable A) 1 0

/-- Probability of a population event, an expectation of its indicator. -/
def eventProb {Ω : Type u} [Fintype Ω] (P : Population Ω) (A : Ω → Prop) : ℝ :=
  mean P (fun i => indicator (A i))

/-- Conditional population mean: numerator divided by event
probability. The value at a zero-probability event is unused in the theorem. -/
def eventMean {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (A : Ω → Prop) (f : Ω → ℝ) : ℝ :=
  mean P (fun i => indicator (A i) * f i) / eventProb P A

/-- Binary assignment scored "0 for control and 1 for treatment" (p. 471,
equation (1)). `false` denotes control and `true` treatment. -/
def assignment (t : Bool) : ℝ := if t then 1 else 0

/-- The Bernoulli assignment mass, generalizing the witnesses' fair coin.
Theorems concerning conditional means require `0 < p < 1`. -/
def armProb (p : ℝ) (t : Bool) : ℝ := if t then p else 1 - p

/-- Joint state mass for independent assignment and population type (p. 472:
"the treatment, which is randomly assigned, is assumed to be statistically
independent of these two disturbance terms"). All potentials depend only on
type; taking this product makes assignment independent of their entire profile. -/
def jointMass {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (t : Bool) (i : Ω) : ℝ := armProb p t * P.mass i

/-- Conditional expectation given the assignment arm, from the joint law:
`E[f | T=t]`. The numerator is an unnormalized finite sum over that arm. -/
def armMean {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (t : Bool) (f : Bool → Ω → ℝ) : ℝ :=
  (∑ i, jointMass P p t i * f t i) / armProb p t

/-- The reduced-form contrast "between random assignment and support for
civil liberties" (p. 473), or the analogous first-stage contrast for knowledge. -/
def contrast {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f : Bool → Ω → ℝ) : ℝ :=
  armMean P p true f - armMean P p false f

/-- Expectation over the joint randomized law, written as the two arm sums. -/
def designMean {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f : Bool → Ω → ℝ) : ℝ :=
  (1 - p) * mean P (f false) + p * mean P (f true)

/-- Population covariance, not the GLS sampling covariance. Used to relate
the binary-assignment Wald and regression coefficients. -/
def covariance {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f g : Bool → Ω → ℝ) : ℝ :=
  designMean P p (fun t i => f t i * g t i) - designMean P p f * designMean P p g

/-- Population variance over the randomization law, `Cov(f,f)`. -/
def variance {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f : Bool → Ω → ℝ) : ℝ := covariance P p f f

/-- Population coefficient on assignment in a regression with an intercept,
`Cov(T,f)/Var(T)`. This is not an estimated GLS coefficient. -/
def assignmentSlope {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f : Bool → Ω → ℝ) : ℝ :=
  covariance P p (fun t _ => assignment t) f /
    variance P p (fun t _ => assignment t)

/-- Linearity of a finite expectation, supporting T2 and T5. -/
theorem mean_add {Ω : Type u} [Fintype Ω] (P : Population Ω) (f g : Ω → ℝ) :
    mean P (fun i => f i + g i) = mean P f + mean P g := by
  simp [mean, mul_add, sum_add_distrib]

/-- Subtraction of finite expectations, supporting the causal contrasts. -/
theorem mean_sub {Ω : Type u} [Fintype Ω] (P : Population Ω) (f g : Ω → ℝ) :
    mean P (fun i => f i - g i) = mean P f - mean P g := by
  simp [mean, mul_sub, sum_sub_distrib]

/-- A constant's expectation is the constant; population mass is one. -/
theorem mean_const {Ω : Type u} [Fintype Ω] (P : Population Ω) (c : ℝ) :
    mean P (fun _ => c) = c := by
  simp only [mean, ← sum_mul, P.total, one_mul]


/-- Nonnegative variables have nonnegative expectations (T5 weights). -/
theorem mean_nonneg {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (f : Ω → ℝ) (h : ∀ i, 0 ≤ f i) : 0 ≤ mean P f := by
  exact sum_nonneg (fun i _ => mul_nonneg (P.nonneg i) (h i))


/-- Assignment is independent of EVERY population event, hence of the joint
potential-outcome profile and both disturbances, as required on p. 472. -/
theorem assignment_independent {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (t : Bool) (A : Ω → Prop) :
    (∑ i, jointMass P p t i * indicator (A i)) = armProb p t * eventProb P A := by
  simpa [jointMass, eventProb, mean, mul_assoc] using
    (mul_sum (univ : Finset Ω) (fun i => P.mass i * indicator (A i)) (armProb p t)).symm

/-- Random assignment identifies each arm's potential-outcome mean; this is
T2(i) and the expectation step in T5(i), not an assumed identification axiom. -/
theorem armMean_eq {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (t : Bool) (f : Bool → Ω → ℝ) :
    armMean P p t f = mean P (f t) := by
  have hn : armProb p t ≠ 0 := by
    cases t <;> simp [armProb] <;> linarith [hp.1, hp.2]
  unfold armMean jointMass
  simp_rw [mul_assoc]
  rw [← mul_sum]
  exact mul_div_cancel_left₀ _ hn

/-- The randomized difference in conditional means equals the difference in
population potential means. -/
theorem contrast_eq {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (f : Bool → Ω → ℝ) :
    contrast P p f = mean P (f true) - mean P (f false) := by
  simp only [contrast, armMean_eq P p hp]

/-- The binary-assignment covariance factor in T1(A5), T4(a2), and T5(i). -/
theorem assignment_covariance {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (f : Bool → Ω → ℝ) :
    covariance P p (fun t _ => assignment t) f =
      p * (1 - p) * (mean P (f true) - mean P (f false)) := by
  simp [covariance, designMean, assignment, mean_const]
  ring

/-- Bernoulli assignment variance, supporting the population regression ratio. -/
theorem assignment_variance {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ) :
    variance P p (fun t _ => assignment t) = p * (1 - p) := by
  rw [variance, assignment_covariance]
  simp [assignment, mean_const]

/-- The population regression coefficient on randomized binary assignment
equals the conditional-mean contrast. -/
theorem assignmentSlope_eq {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (f : Bool → Ω → ℝ) :
    assignmentSlope P p f = contrast P p f := by
  have h : p * (1 - p) ≠ 0 := ne_of_gt (mul_pos hp.1 (sub_pos.mpr hp.2))
  rw [assignmentSlope, assignment_covariance, assignment_variance, contrast_eq P p hp]
  exact mul_div_cancel_left₀ _ h

/-- "potential knowledge K(t)" and "potential support
S(t,k)". The support intervention is acyclic and well-defined for every real
knowledge value. Observed variables use consistency, K=K(T), S=S(T,K(T)). -/
structure MediationModel (Ω : Type u) where
  knowledge : Bool → Ω → ℝ
  support : Bool → ℝ → Ω → ℝ

/-- Consistent observed support in the mediation model. -/
def observedSupport {Ω : Type u} (m : MediationModel Ω) (t : Bool) (i : Ω) : ℝ :=
  m.support t (m.knowledge t i) i

/-- `τ = E[S|T=1]-E[S|T=0]`, the reduced form on p. 473. -/
def reducedForm {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : MediationModel Ω) : ℝ := contrast P p (observedSupport m)

/-- "M=E[S(0,K(1))-S(0,K(0))]", mediation holding assignment at 0. -/
def mediated {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : MediationModel Ω) : ℝ :=
  mean P (fun i => m.support false (m.knowledge true i) i -
    m.support false (m.knowledge false i) i)

/-- "D=E[S(1,K(1))-S(0,K(1))]", NET nonknowledge contrast at
treated knowledge. This D is unrelated to equation (1)'s stratum dummies. -/
def direct {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : MediationModel Ω) : ℝ :=
  mean P (fun i => m.support true (m.knowledge true i) i -
    m.support false (m.knowledge true i) i)

/-- T2(ii): each unit's total contrast is the direct contrast at treated
knowledge plus the mediation contrast at control assignment. -/
theorem mediation_unit_identity {Ω : Type u} (m : MediationModel Ω) (i : Ω) :
    m.support true (m.knowledge true i) i - m.support false (m.knowledge false i) i =
      (m.support true (m.knowledge true i) i - m.support false (m.knowledge true i) i) +
      (m.support false (m.knowledge true i) i - m.support false (m.knowledge false i) i) := by
  ring


/-- Linear structural special case: K(t)=α+a t+u₁ and
S(t,k)=σ+b k+c t+u₂. Disturbances are arbitrary functions of population type,
so they may be correlated with one another and are independent of assignment. -/
def linearModel {Ω : Type u} (α a σ b c : ℝ) (u₁ u₂ : Ω → ℝ) : MediationModel Ω :=
  ⟨fun t i => α + a * assignment t + u₁ i,
   fun t k i => σ + b * k + c * assignment t + u₂ i⟩


/-- T2(v): for a positive first stage, τ/a=b+c/a and it bounds the
knowledge slope b exactly when the NET other-channel coefficient c is nonnegative. -/
theorem linear_iv_direction (a b c : ℝ) (ha : 0 < a) :
    (a * b + c) / a = b + c / a ∧
    ((a * b + c) / a ≥ b ↔ c ≥ 0) := by
  constructor
  · field_simp
  · rw [ge_iff_le, le_div_iff₀ ha]
    constructor <;> intro h <;> nlinarith

/-- T2(v): nonnegative individual other-channel coefficients suffice for a
nonnegative NET coefficient. The converse is false (e.g. -1 and 2). -/
theorem net_channels {n : ℕ} (c : Fin n → ℝ) :
    (∀ j, 0 ≤ c j) → 0 ≤ ∑ j, c j := by
  intro h
  exact sum_nonneg (fun j _ => h j)

/-- T2(v): net nonnegativity does not require every channel to be nonnegative. -/
theorem net_channels_not_necessary :
    ∃ c : Fin 2 → ℝ, 0 ≤ ∑ j, c j ∧ ¬ (∀ j, 0 ≤ c j) := by
  refine ⟨![(-1 : ℝ), 2], ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ]
  · intro h
    have := h 0
    norm_num at this

/-- Uniform finite population, used for the exact latent-type laws in the
witnesses. This is unrelated to the empirical sample frequencies. -/
def uniformPopulation (Ω : Type u) [Fintype Ω] [Nonempty Ω] : Population Ω where
  mass := fun _ => 1 / (Fintype.card Ω : ℝ)
  nonneg := fun _ => by positivity
  total := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

/-- Independent product of two exogenous population laws. -/
def productPopulation {Ω Ξ : Type u} [Fintype Ω] [Fintype Ξ]
    (P : Population Ω) (Q : Population Ξ) : Population (Ω × Ξ) where
  mass := fun i => P.mass i.1 * Q.mass i.2
  nonneg := fun i => mul_nonneg (P.nonneg i.1) (Q.nonneg i.2)
  total := by simp [Fintype.sum_prod_type, ← mul_sum, P.total, Q.total]

/-- Iterated finite expectation for independent population types (T1). -/
theorem mean_product {Ω Ξ : Type u} [Fintype Ω] [Fintype Ξ]
    (P : Population Ω) (Q : Population Ξ) (f : Ω × Ξ → ℝ) :
    mean (productPopulation P Q) f = mean P (fun i => mean Q (fun j => f (i,j))) := by
  simp [mean, productPopulation, Fintype.sum_prod_type, mul_sum, mul_assoc]

/-- Conditional mean under the witnesses' independent fair assignment. -/
theorem fair_armMean {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (t : Bool) (f : Bool → Ω → ℝ) : armMean P (1/2) t f = mean P (f t) :=
  armMean_eq P (1/2) (by norm_num) t f

/-- T1(A)'s independent signs: u₁ is uniform on {-1/5,1/5}, u₂ on
{-1/10,1/10}. Their latent type is a pair of independent fair Boolean signs. -/
def linearPopulation : Population (Bool × Bool) :=
  productPopulation (uniformPopulation Bool) (uniformPopulation Bool)

/-- The knowledge disturbance, with its two explicit values. -/
def linearU₁ (i : Bool × Bool) : ℝ := if i.1 then 1/5 else -1/5

/-- The support disturbance, with its two explicit values. -/
def linearU₂ (i : Bool × Bool) : ℝ := if i.2 then 1/10 else -1/10

/-- T1(A): K(t)=8+(6/5)t+u₁;
S(t,k)=23/10+(k-8)/20-(3/50)t+u₂. These are illustrative scores. -/
def linearWitness : MediationModel (Bool × Bool) :=
  ⟨fun t i => 8 + (6/5) * assignment t + linearU₁ i,
   fun t k i => 23/10 + (1/20) * (k-8) - (3/50) * assignment t + linearU₂ i⟩

/-- T1(A4): direct substitution cancels treatment in observed support. -/
theorem linear_observed_support (t : Bool) (i : Bool × Bool) :
    observedSupport linearWitness t i = 23/10 + linearU₁ i / 20 + linearU₂ i := by
  simp only [observedSupport, linearWitness]
  ring

/-- T1(A1,A3,A4,A5)'s exact numerical claims, including population slopes. -/
def LinearNumericClaims : Prop :=
  contrast linearPopulation (1/2) linearWitness.knowledge = 6/5 ∧
  mediated linearPopulation linearWitness = 3/50 ∧
  direct linearPopulation linearWitness = -3/50 ∧
  reducedForm linearPopulation (1/2) linearWitness = 0 ∧
  variance linearPopulation (1/2) (fun t _ => assignment t) = 1/4 ∧
  covariance linearPopulation (1/2) (fun t _ => assignment t)
    (observedSupport linearWitness) = 0 ∧
  covariance linearPopulation (1/2) (fun t _ => assignment t) linearWitness.knowledge = 3/10 ∧
  assignmentSlope linearPopulation (1/2) (observedSupport linearWitness) = 0 ∧
  assignmentSlope linearPopulation (1/2) linearWitness.knowledge = 6/5 ∧
  (6/5 : ℝ) * (1/20) = 3/50 ∧ (6/5 : ℝ) * (1/20) + (-3/50) = 0

/-- T1(A)'s numerical identities are exact finite-sum computations. -/
theorem linear_numbers : LinearNumericClaims := by
  unfold LinearNumericClaims
  simp only [assignmentSlope_eq linearPopulation (1/2) (by norm_num), reducedForm,
    contrast_eq linearPopulation (1/2) (by norm_num), assignment_variance, assignment_covariance]
  norm_num [mean, mediated, direct, observedSupport, linearWitness, linearPopulation,
    productPopulation, uniformPopulation, linearU₁, linearU₂, assignment,
    Fintype.sum_prod_type]

/-- T1(A4): both conditional support laws have four atoms, 219/100,
221/100, 239/100, 241/100, each of probability 1/4; other values have mass zero. -/
theorem linear_support_law (t : Bool) (y : ℝ) :
    armMean linearPopulation (1/2) t
      (fun z i => indicator (observedSupport linearWitness z i = y)) =
      if y = 219/100 ∨ y = 221/100 ∨ y = 239/100 ∨ y = 241/100 then 1/4 else 0 := by
  rw [fair_armMean]
  simp_rw [linear_observed_support]
  by_cases h₁ : y = 219/100 <;> by_cases h₂ : y = 221/100 <;>
    by_cases h₃ : y = 239/100 <;> by_cases h₄ : y = 241/100 <;>
    simp_all [mean, linearPopulation, productPopulation, uniformPopulation,
      linearU₁, linearU₂, indicator, Fintype.sum_prod_type] <;> norm_num <;> simp_all [eq_comm]

/-- T1(A), complete linear witness: each joint state has probability 1/8,
the two disturbances have independent fair signs, knowledge increases in every
unit, support strictly increases with knowledge, yet τ=0<M=3/50. This refutes
only an unconditional extension of the contextual comparison on p. 474 without asserting anything
about the actual curriculum or its fitted estimates. -/
def LinearWitnessClaims : Prop :=
    (∀ t i, jointMass linearPopulation (1/2) t i = 1/8) ∧
    (∀ r s : Bool, eventProb linearPopulation (fun i => i.1 = r ∧ i.2 = s) = 1/4) ∧
    (∀ r : Bool, eventProb linearPopulation (fun i => i.1 = r) = 1/2 ∧
      eventProb linearPopulation (fun i => i.2 = r) = 1/2) ∧
    (∀ i, linearWitness.knowledge true i - linearWitness.knowledge false i = 6/5 ∧
      0 < linearWitness.knowledge true i - linearWitness.knowledge false i) ∧
    (∀ t k h i, 0 < h → linearWitness.support t (k+h) i - linearWitness.support t k i = h/20 ∧
      0 < linearWitness.support t (k+h) i - linearWitness.support t k i) ∧
    LinearNumericClaims ∧
    (∀ t y, armMean linearPopulation (1/2) t
      (fun z i => indicator (observedSupport linearWitness z i = y)) =
      if y = 219/100 ∨ y = 221/100 ∨ y = 239/100 ∨ y = 241/100 then 1/4 else 0) ∧
    reducedForm linearPopulation (1/2) linearWitness < mediated linearPopulation linearWitness ∧
    0 < mediated linearPopulation linearWitness

/-- T1(A): the complete linear-witness claims on the p. 474 attribution direction. -/
theorem linear_counterexample : LinearWitnessClaims := by
  unfold LinearWitnessClaims
  refine ⟨?_, ?_, ?_, ?_, ?_, linear_numbers, linear_support_law, ?_, ?_⟩
  · intro t i
    cases t <;> norm_num [jointMass, armProb, linearPopulation,
      productPopulation, uniformPopulation]
  · intro r s
    cases r <;> cases s <;> norm_num [eventProb, mean, indicator, linearPopulation,
      productPopulation, uniformPopulation, Fintype.sum_prod_type]
  · intro r
    cases r <;> norm_num [eventProb, mean, indicator, linearPopulation,
      productPopulation, uniformPopulation, Fintype.sum_prod_type]
  · intro i
    norm_num [linearWitness, assignment]
  · intro t k h i hh
    have he : linearWitness.support t (k+h) i - linearWitness.support t k i = h/20 := by
      simp only [linearWitness]
      ring
    exact ⟨he, by rw [he]; positivity⟩
  · have h := linear_numbers
    rcases h with ⟨_, hm, _, ht, _⟩
    rw [hm, ht]
    norm_num
  · have h := linear_numbers
    rw [h.2.1]
    norm_num

/-- T1(B)'s independent exogenous law: W=1,...,5 and V=1,...,100.
Lean stores the zero-based values, and the model adds one to V. -/
def integerPopulation : Population (Fin 5 × Fin 100) :=
  productPopulation (uniformPopulation (Fin 5)) (uniformPopulation (Fin 100))

/-- T1(B): K(t)=8+t(1+1{W=5});
S(t,k)=2+1{V≤36+5(k-8)-6t}. The support intervention is defined for every
real k, and observed scores are integers within the 2007 index ranges. -/
def integerWitness : MediationModel (Fin 5 × Fin 100) :=
  ⟨fun t i => 8 + assignment t * (1 + indicator (i.1.val = 4)),
   fun t k i => 2 + indicator ((i.2.val : ℝ) + 1 ≤
     36 + 5 * (k-8) - 6 * assignment t)⟩

/-- T1(B)'s general political knowledge score is identically 2 under both
assignments, inside Table 3's 2007 range 0–5. -/
def integerGeneralKnowledge (_t : Bool) (_i : Fin 5 × Fin 100) : ℝ := 2

/-- Counting initial segments gives the exact probability q/n without
enumerating the witnesses' 1000 joint states (T1(B)). -/
theorem uniform_initial_segment (n : ℕ) [NeZero n] (q : ℕ) (hq : q ≤ n) :
    mean (uniformPopulation (Fin n))
      (fun v => indicator ((v.val : ℝ) + 1 ≤ (q : ℝ))) = (q : ℝ) / n := by
  have hfun : (fun v : Fin n => indicator ((v.val : ℝ) + 1 ≤ (q : ℝ))) =
      (fun v => if v.val < q then (1 : ℝ) else 0) := by
    funext v
    have he : (v.val : ℝ) + 1 ≤ (q : ℝ) ↔ v.val < q := by
      exact_mod_cast (Nat.succ_le_iff : v.val + 1 ≤ q ↔ v.val < q)
    simp only [indicator, Nat.cast_add, Nat.cast_one, he]
  rw [hfun]
  unfold mean
  simp only [uniformPopulation, Fintype.card_fin, ← mul_sum, sum_boole, Fin.card_filter_val_lt,
    min_eq_right hq]
  ring

/-- T1(B): integrating out V gives support mean 2 plus threshold/100. -/
theorem integer_threshold_mean (t : Bool) (k : ℝ) (w : Fin 5) (q : ℕ)
    (hq : q ≤ 100) (he : 36 + 5 * (k-8) - 6 * assignment t = (q : ℝ)) :
    mean (uniformPopulation (Fin 100))
      (fun v => integerWitness.support t k (w,v)) = 2 + (q : ℝ)/100 := by
  simp only [integerWitness, he]
  rw [mean_add, mean_const, uniform_initial_segment 100 q hq]
  norm_num

/-- T1(B2): the six relevant fixed-dose means, valid at k=8,9,10. -/
theorem integer_fixed_support_mean (t : Bool) (k : ℝ) (w : Fin 5)
    (hk : k = 8 ∨ k = 9 ∨ k = 10) :
    mean (uniformPopulation (Fin 100)) (fun v => integerWitness.support t k (w,v)) =
      2 + (36 + 5*(k-8) - 6*assignment t)/100 := by
  rcases hk with rfl | rfl | rfl <;> cases t
  · convert integer_threshold_mean false 8 w 36 (by norm_num) (by norm_num [assignment]) using 1 <;> norm_num [assignment]
  · convert integer_threshold_mean true 8 w 30 (by norm_num) (by norm_num [assignment]) using 1 <;> norm_num [assignment]
  · convert integer_threshold_mean false 9 w 41 (by norm_num) (by norm_num [assignment]) using 1 <;> norm_num [assignment]
  · convert integer_threshold_mean true 9 w 35 (by norm_num) (by norm_num [assignment]) using 1 <;> norm_num [assignment]
  · convert integer_threshold_mean false 10 w 46 (by norm_num) (by norm_num [assignment]) using 1 <;> norm_num [assignment]
  · convert integer_threshold_mean true 10 w 40 (by norm_num) (by norm_num [assignment]) using 1 <;> norm_num [assignment]

/-- T1(B1): integrating out V and the five W values gives the knowledge
means 8 and 46/5. This is a population calculation, not Table 4's estimate. -/
theorem integer_knowledge_mean (t : Bool) :
    mean integerPopulation (integerWitness.knowledge t) = 8 + (6/5) * assignment t := by
  unfold integerPopulation
  rw [mean_product]
  simp only [integerWitness, mean_const]
  cases t <;> norm_num [mean, uniformPopulation, indicator, assignment, Fin.sum_univ_succ]

/-- T1(B3): all four nested intervention means; in particular the three
specified means are 59/25, 121/50, and 59/25. -/
theorem integer_nested_support_mean (t z : Bool) :
    mean integerPopulation (fun i => integerWitness.support t (integerWitness.knowledge z i) i) =
      2 + (36 + 6*assignment z - 6*assignment t)/100 := by
  unfold integerPopulation
  rw [mean_product]
  have inner (w : Fin 5) :
      mean (uniformPopulation (Fin 100))
        (fun v => integerWitness.support t (integerWitness.knowledge z (w,v)) (w,v)) =
        2 + (36 + 5*((8 + assignment z * (1 + indicator (w.val=4))) - 8) -
          6*assignment t)/100 := by
    apply integer_fixed_support_mean
    cases z <;> by_cases h : w.val = 4 <;> norm_num [integerWitness, assignment, indicator, h]
  simp_rw [inner]
  cases z <;> cases t <;>
    norm_num [mean, uniformPopulation, indicator, assignment, Fin.sum_univ_succ]

/-- T1(B2): the population mean at each fixed k=8,9,10 follows from counting
the threshold's initial segment, independent of W. -/
theorem integer_fixed_population_mean (t : Bool) (k : ℝ) (hk : k=8 ∨ k=9 ∨ k=10) :
    mean integerPopulation (fun i => integerWitness.support t k i) =
      2 + (36 + 5*(k-8) - 6*assignment t)/100 := by
  unfold integerPopulation
  rw [mean_product]
  simp_rw [integer_fixed_support_mean t k _ hk]
  rw [mean_const]

/-- T1(B1): exact knowledge values and the support and general-knowledge
range checks against Table 3's 2007 ranges, p. 472 (PDF p. 10). -/
theorem integer_ranges (t : Bool) (i : Fin 5 × Fin 100) :
    integerWitness.knowledge false i = 8 ∧
    integerWitness.knowledge true i = (if i.1.val = 4 then 10 else 9) ∧
    integerWitness.knowledge t i ∈ ({8,9,10} : Finset ℝ) ∧
    0 ≤ integerWitness.knowledge t i ∧ integerWitness.knowledge t i ≤ 15 ∧
    observedSupport integerWitness t i ∈ ({2,3} : Finset ℝ) ∧
    0 ≤ observedSupport integerWitness t i ∧ observedSupport integerWitness t i ≤ 3 ∧
    integerGeneralKnowledge t i = 2 ∧
    0 ≤ integerGeneralKnowledge t i ∧ integerGeneralKnowledge t i ≤ 5 := by
  unfold observedSupport integerWitness integerGeneralKnowledge
  cases t <;> by_cases hw : i.1.val = 4 <;> simp [assignment, indicator, hw] <;>
    split_ifs <;> norm_num at * <;> linarith

/-- T1(B2): increasing knowledge by one never decreases support and changes
it by either zero or one. This holds even outside the two relevant margins. -/
theorem integer_unit_increment (t : Bool) (k : ℝ) (i : Fin 5 × Fin 100) :
    integerWitness.support t (k+1) i - integerWitness.support t k i ∈ ({0,1} : Finset ℝ) := by
  by_cases h₀ : (i.2.val : ℝ) + 1 ≤ 36 + 5*(k-8) - 6*assignment t
  · have h₁ : (i.2.val : ℝ) + 1 ≤ 36 + 5*((k+1)-8) - 6*assignment t := by linarith
    simp [integerWitness, indicator, h₀, h₁]
  · by_cases h₁ : (i.2.val : ℝ) + 1 ≤ 36 + 5*((k+1)-8) - 6*assignment t <;>
      simp [integerWitness, indicator, h₀, h₁]

/-- T1(B2): a one-unit increase at k=8 or k=9 has mean support effect 1/20,
strictly positive, for either assignment. -/
theorem integer_mean_increment (t : Bool) (k : ℝ) (hk : k=8 ∨ k=9) :
    mean integerPopulation (fun i => integerWitness.support t (k+1) i -
      integerWitness.support t k i) = 1/20 := by
  have hk₀ : k=8 ∨ k=9 ∨ k=10 := by rcases hk with h|h <;> simp [h]
  have hk₁ : k+1=8 ∨ k+1=9 ∨ k+1=10 := by rcases hk with h|h <;> norm_num [h]
  rw [mean_sub, integer_fixed_population_mean t (k+1) hk₁,
    integer_fixed_population_mean t k hk₀]
  ring

/-- T1(B1,B3): all exact expectation and contrast values for the bounded
integer witness, retaining the specified mediation ordering. -/
def IntegerNumericClaims : Prop :=
  armMean integerPopulation (1/2) false integerWitness.knowledge = 8 ∧
  armMean integerPopulation (1/2) true integerWitness.knowledge = 46/5 ∧
  mean integerPopulation (fun i => integerWitness.knowledge true i - integerWitness.knowledge false i) = 6/5 ∧
  mean integerPopulation (fun i => integerWitness.support false (integerWitness.knowledge false i) i) = 59/25 ∧
  mean integerPopulation (fun i => integerWitness.support false (integerWitness.knowledge true i) i) = 121/50 ∧
  mean integerPopulation (fun i => integerWitness.support true (integerWitness.knowledge true i) i) = 59/25 ∧
  mediated integerPopulation integerWitness = 3/50 ∧
  direct integerPopulation integerWitness = -3/50 ∧
  reducedForm integerPopulation (1/2) integerWitness = 0

/-- T1(B)'s exact numbers follow from the preceding threshold counts. -/
theorem integer_numbers : IntegerNumericClaims := by
  unfold IntegerNumericClaims reducedForm observedSupport
  simp only [fair_armMean, reducedForm, contrast_eq integerPopulation (1/2) (by norm_num),
    observedSupport, mediated, direct, mean_sub, integer_knowledge_mean, integer_nested_support_mean]
  norm_num [assignment]

/-- T1(B4): the probability of observed support 3 is 9/25 in either arm. -/
theorem integer_support_three (t : Bool) :
    armMean integerPopulation (1/2) t
      (fun z i => indicator (observedSupport integerWitness z i = 3)) = 9/25 := by
  rw [fair_armMean]
  have hi (i : Fin 5 × Fin 100) :
      indicator (observedSupport integerWitness t i = 3) = observedSupport integerWitness t i - 2 := by
    simp only [observedSupport, integerWitness, indicator]
    split_ifs <;> norm_num at *
  simp_rw [hi]
  rw [mean_sub, mean_const]
  change mean integerPopulation (fun i => integerWitness.support t (integerWitness.knowledge t i) i) - 2 = _
  rw [integer_nested_support_mean]
  ring

/-- T1(B4): the entire conditional observed support distribution is identical
in both arms: mass 16/25 at 2 and mass 9/25 at 3. -/
theorem integer_support_law (t : Bool) (y : ℝ) :
    armMean integerPopulation (1/2) t
      (fun z i => indicator (observedSupport integerWitness z i = y)) =
      if y = 2 then 16/25 else if y = 3 then 9/25 else 0 := by
  by_cases hy₂ : y=2
  · subst y
    have hi (i : Fin 5 × Fin 100) :
        indicator (observedSupport integerWitness t i = 2) =
          1 - indicator (observedSupport integerWitness t i = 3) := by
      have hr := (integer_ranges t i).2.2.2.2.2.1
      simp only [mem_insert, mem_singleton] at hr
      rcases hr with h|h <;> simp [h, indicator]
    rw [fair_armMean]
    simp_rw [hi]
    have hthree : mean integerPopulation
        (fun i => indicator (observedSupport integerWitness t i = 3)) = 9/25 := by
      simpa only [fair_armMean] using integer_support_three t
    rw [mean_sub, mean_const, hthree]
    norm_num
  · by_cases hy₃ : y=3
    · subst y
      simpa using integer_support_three t
    · have hi (i : Fin 5 × Fin 100) : indicator (observedSupport integerWitness t i = y) = 0 := by
        have hr := (integer_ranges t i).2.2.2.2.2.1
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with h|h <;> simp [h, indicator, Ne.symm hy₂, Ne.symm hy₃]
      rw [fair_armMean]
      simp_rw [hi]
      simp [mean_const, hy₂, hy₃]

/-- T1(B), complete bounded witness: 1000 equally likely joint states,
integer outcomes in the 2007 index ranges, mean causal increments 1/20,
M=3/50, D=-3/50, τ=0, and identical conditional support laws. Assignment is
independent of both exogenous types by `assignment_independent`. -/
def IntegerWitnessClaims : Prop :=
    (∀ t i, jointMass integerPopulation (1/2) t i = 1/1000) ∧
    (∀ t i, integerWitness.knowledge t i ∈ ({8,9,10} : Finset ℝ) ∧
      observedSupport integerWitness t i ∈ ({2,3} : Finset ℝ) ∧
      integerGeneralKnowledge t i = 2) ∧
    (∀ t k, k=8 ∨ k=9 →
      (∀ i, integerWitness.support t (k+1) i - integerWitness.support t k i ∈ ({0,1} : Finset ℝ)) ∧
      mean integerPopulation (fun i => integerWitness.support t (k+1) i - integerWitness.support t k i) = 1/20) ∧
    IntegerNumericClaims ∧
    (∀ t y, armMean integerPopulation (1/2) t
      (fun z i => indicator (observedSupport integerWitness z i = y)) =
      if y=2 then 16/25 else if y=3 then 9/25 else 0) ∧
    reducedForm integerPopulation (1/2) integerWitness < mediated integerPopulation integerWitness ∧
    0 < mediated integerPopulation integerWitness

/-- T1(B): the complete bounded integer-witness claims on the p. 474 attribution direction. -/
theorem integer_counterexample : IntegerWitnessClaims := by
  unfold IntegerWitnessClaims
  refine ⟨?_, ?_, ?_, integer_numbers, integer_support_law, ?_, ?_⟩
  · intro t i
    cases t <;> norm_num [jointMass, armProb, integerPopulation, productPopulation, uniformPopulation]
  · intro t i
    have h := integer_ranges t i
    exact ⟨h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩
  · intro t k hk
    exact ⟨integer_unit_increment t k, integer_mean_increment t k hk⟩
  · have h := integer_numbers
    rw [h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2]
    norm_num
  · have h := integer_numbers
    rw [h.2.2.2.2.2.2.1]
    norm_num

/-- T1's two exact witnesses refute an unconditional extension, not the contextual p. 474 comparison
τ≥M. `linear_counterexample` and `integer_counterexample` give every numeric
claim; the generic product-law theorem supplies independence for any event. -/
theorem mediation_counterexamples : LinearWitnessClaims ∧ IntegerWitnessClaims ∧
    reducedForm linearPopulation (1/2) linearWitness = 0 ∧
    mediated linearPopulation linearWitness = 3/50 ∧
    direct linearPopulation linearWitness = -3/50 ∧
    reducedForm integerPopulation (1/2) integerWitness = 0 ∧
    mediated integerPopulation integerWitness = 3/50 ∧
    direct integerPopulation integerWitness = -3/50 ∧
    (∀ A t, (∑ i, jointMass linearPopulation (1/2) t i * indicator (A i)) =
      armProb (1/2) t * eventProb linearPopulation A) ∧
    (∀ A t, (∑ i, jointMass integerPopulation (1/2) t i * indicator (A i)) =
      armProb (1/2) t * eventProb integerPopulation A) := by
  have ha := linear_numbers
  have hb := integer_numbers
  exact ⟨linear_counterexample, integer_counterexample, ha.2.2.2.1, ha.2.1, ha.2.2.1,
    hb.2.2.2.2.2.2.2.2, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1,
    fun A t => assignment_independent _ _ t A,
    fun A t => assignment_independent _ _ t A⟩

/-- Integer potential knowledge K_i(z) and exclusion-restricted
support response Y_i(k). Using a response without an assignment argument
enforces exclusion for every intervention. Potential support is its identical
extension to both assignments; no monotonicity of knowledge is built in. -/
structure IVModel (Ω : Type u) where
  knowledge : Bool → Ω → ℕ
  response : ℕ → Ω → ℝ


/-- Consistent observed knowledge K=K(Z), embedded in ℝ for expectations. -/
def ivKnowledge {Ω : Type u} (m : IVModel Ω) (z : Bool) (i : Ω) : ℝ := m.knowledge z i

/-- Consistent observed support Y=Y(K(Z)) under exclusion. -/
def ivOutcome {Ω : Type u} (m : IVModel Ω) (z : Bool) (i : Ω) : ℝ :=
  m.response (m.knowledge z i) i

/-- The first-stage contrast Δ_K. -/
def firstStage {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) : ℝ := contrast P p (ivKnowledge m)

/-- The support reduced-form contrast Δ_Y. -/
def ivReducedForm {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) : ℝ := contrast P p (ivOutcome m)

/-- The population Wald/IV ratio β_IV=Δ_Y/Δ_K. -/
def ivRatio {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) : ℝ := ivReducedForm P p m / firstStage P p m

/-- "students whose knowledge ... is augmented" (pp. 474–475)
are types with K(1)>K(0). This is a latent population event. -/
def increaser {Ω : Type u} (m : IVModel Ω) (i : Ω) : Prop :=
  m.knowledge false i < m.knowledge true i

/-- Mean total induced support effect among increasers. In T4's
witnesses every increase is exactly one unit, so this is also the mean per-unit effect. -/
def increaserEffect {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : IVModel Ω) : ℝ :=
  eventMean P (increaser m)
    (fun i => m.response (m.knowledge true i) i - m.response (m.knowledge false i) i)

/-- Conditional observable law of (K,Y) in arm z, from independent assignment. -/
def conditionalObservableLaw {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (m : IVModel Ω) (z : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  eventProb P (fun i => m.knowledge z i = k ∧ ivOutcome m z i = y)

/-- Full joint law of (Z,K,Y); the object on which an identifying functional
may depend. Independence multiplies the arm law by its probability. -/
def observableLaw {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) (x : Bool × (ℕ × ℝ)) : ℝ :=
  armProb p x.1 * conditionalObservableLaw P m x.1 x.2.1 x.2.2

/-- T4's threshold response H(k)=1{k≥9}. -/
def knowledgeMargin (k : ℕ) : ℝ := indicator (9 ≤ k)

/-- H is nondecreasing; this supplies the extra monotone-support property
of the IV counterexamples, not the missing monotone-knowledge assumption. -/
theorem knowledgeMargin_monotone : Monotone knowledgeMargin := by
  intro k l h
  by_cases hk : 9 ≤ k
  · have hl : 9 ≤ l := le_trans hk h
    simp [knowledgeMargin, indicator, hk, hl]
  · by_cases hl : 9 ≤ l <;> simp [knowledgeMargin, indicator, hk, hl]

/-- T4(a)'s two-type population: up has mass 2/3, down mass 1/3. -/
def upDownPopulation : Population Bool where
  mass := fun i => if i then 2/3 else 1/3
  nonneg := fun i => by cases i <;> norm_num
  total := by norm_num

/-- T4(a): up=(8,9,3+H), down=(9,8,2+2H).
Exclusion and consistency are part of `IVModel`'s representation. -/
def upDownWitness : IVModel Bool :=
  ⟨fun z i => if i then (if z then 9 else 8) else (if z then 8 else 9),
   fun k i => if i then 3 + knowledgeMargin k else 2 + 2*knowledgeMargin k⟩

/-- T4(a1)–(a4): exact arm means, first stage, reduced form, IV and covariance
ratios, increaser mass and effect, and the cancellation arithmetic. -/
def UpDownNumericClaims : Prop :=
  armMean upDownPopulation (1/2) false (ivKnowledge upDownWitness) = 25/3 ∧
  armMean upDownPopulation (1/2) true (ivKnowledge upDownWitness) = 26/3 ∧
  firstStage upDownPopulation (1/2) upDownWitness = 1/3 ∧
  0 < firstStage upDownPopulation (1/2) upDownWitness ∧
  armMean upDownPopulation (1/2) false (ivOutcome upDownWitness) = 10/3 ∧
  armMean upDownPopulation (1/2) true (ivOutcome upDownWitness) = 10/3 ∧
  ivReducedForm upDownPopulation (1/2) upDownWitness = 0 ∧
  ivRatio upDownPopulation (1/2) upDownWitness = 0 ∧
  covariance upDownPopulation (1/2) (fun z _ => assignment z) (ivKnowledge upDownWitness) = 1/12 ∧
  covariance upDownPopulation (1/2) (fun z _ => assignment z) (ivOutcome upDownWitness) = 0 ∧
  covariance upDownPopulation (1/2) (fun z _ => assignment z) (ivOutcome upDownWitness) /
    covariance upDownPopulation (1/2) (fun z _ => assignment z) (ivKnowledge upDownWitness) = 0 ∧
  eventProb upDownPopulation (increaser upDownWitness) = 2/3 ∧
  increaserEffect upDownPopulation upDownWitness = 1 ∧
  (2/3 : ℝ)*1 + (1/3)*(-2) = 0

/-- T4(a)'s exact numbers, computed from all latent types without simulation. -/
theorem upDown_numbers : UpDownNumericClaims := by
  unfold UpDownNumericClaims ivRatio firstStage ivReducedForm ivKnowledge ivOutcome
  simp only [fair_armMean, contrast_eq upDownPopulation (1/2) (by norm_num), assignment_covariance]
  norm_num [mean, upDownPopulation, upDownWitness, knowledgeMargin, indicator,
    eventProb, increaser, increaserEffect, eventMean, ivOutcome]

/-- T4(a3,a5): increasers are exactly up; each crosses only margin 9 and
has effect 1, while all potential knowledge scores are 8 or 9 and all support
responses are 2,3,4 within Table 3's 2008 ranges. Support is nondecreasing. -/
def UpDownUnitClaims (i : Bool) : Prop :=
    (increaser upDownWitness i ↔ i = true) ∧
    (increaser upDownWitness i → upDownWitness.knowledge false i = 8 ∧
      upDownWitness.knowledge true i = 9 ∧
      upDownWitness.response 9 i - upDownWitness.response 8 i = 1) ∧
    (∀ z, upDownWitness.knowledge z i ∈ ({8,9} : Finset ℕ) ∧ upDownWitness.knowledge z i ≤ 18) ∧
    (∀ k, upDownWitness.response k i ∈ ({2,3,4} : Finset ℝ) ∧
      0 ≤ upDownWitness.response k i ∧ upDownWitness.response k i ≤ 7) ∧
    Monotone (fun k => upDownWitness.response k i)

/-- T4(a3,a5): type-level effects and the 2008 ranges for the T4(a) witness. -/
theorem upDown_unit_properties (i : Bool) : UpDownUnitClaims i := by
  unfold UpDownUnitClaims
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases i <;> simp [increaser, upDownWitness]
  · cases i <;> norm_num [increaser, upDownWitness, knowledgeMargin, indicator]
  · intro z
    cases i <;> cases z <;> norm_num [upDownWitness]
  · intro k
    cases i <;> by_cases h : 9 ≤ k <;> norm_num [upDownWitness, knowledgeMargin, indicator, h]
  · intro k l h
    have hh := knowledgeMargin_monotone h
    cases i <;> simp only [upDownWitness, Bool.false_eq_true, ↓reduceIte] <;> linarith


/-- T4(b), model A's five equally weighted types:
(8,9,3+H),(8,9,3+H),(9,8,2+2H),(8,8,2),(9,9,4). -/
def modelA : IVModel (Fin 5) :=
  ⟨fun z i => if z then ![9,9,8,8,9] i else ![8,8,9,8,9] i,
   fun k i => ![3+knowledgeMargin k, 3+knowledgeMargin k, 2+2*knowledgeMargin k, 2, 4] i⟩

/-- T4(b), model B's five equally weighted types:
(8,9,3+H),(8,9,3+H),(9,8,2+2H),(8,9,2+2H),(9,8,2+2H). -/
def modelB : IVModel (Fin 5) :=
  ⟨fun z i => if z then ![9,9,8,9,8] i else ![8,8,9,8,9] i,
   fun k i => ![3+knowledgeMargin k, 3+knowledgeMargin k,
     2+2*knowledgeMargin k, 2+2*knowledgeMargin k, 2+2*knowledgeMargin k] i⟩

/-- T4(b1)'s exact conditional probability table. The indicator formula
also states that all unlisted observable values have probability zero. -/
def fiveTypeObservableLaw (z : Bool) (k : ℕ) (y : ℝ) : ℝ :=
  if z then (2/5)*indicator (k=8 ∧ y=2) + (3/5)*indicator (k=9 ∧ y=4)
  else (1/5)*indicator (k=8 ∧ y=2) + (2/5)*indicator (k=8 ∧ y=3) +
    (2/5)*indicator (k=9 ∧ y=4)

/-- T4(b1): both models have the stated same complete conditional observable
law, not just equal first moments. -/
theorem models_conditional_law (z : Bool) (k : ℕ) (y : ℝ) :
    conditionalObservableLaw (uniformPopulation (Fin 5)) modelA z k y = fiveTypeObservableLaw z k y ∧
    conditionalObservableLaw (uniformPopulation (Fin 5)) modelB z k y = fiveTypeObservableLaw z k y := by
  by_cases h₁ : k=8 ∧ y=2 <;> by_cases h₂ : k=8 ∧ y=3 <;>
    by_cases h₃ : k=9 ∧ y=4 <;> cases z <;> constructor <;>
    norm_num [conditionalObservableLaw, eventProb, mean, uniformPopulation,
      modelA, modelB, ivOutcome, fiveTypeObservableLaw, knowledgeMargin, indicator,
      Fin.sum_univ_succ, eq_comm, h₁, h₂, h₃]

/-- T4(b1): with the same assignment probability, models A and B have
identical full joint laws of (Z,K,Y), for every observable value. -/
theorem models_observable_law (p : ℝ) :
    observableLaw (uniformPopulation (Fin 5)) p modelA =
    observableLaw (uniformPopulation (Fin 5)) p modelB := by
  funext x
  unfold observableLaw
  rw [(models_conditional_law x.1 x.2.1 x.2.2).1,
    (models_conditional_law x.1 x.2.1 x.2.2).2]

/-- T4(b2)'s common numerical values for either five-type model. -/
def FiveTypeNumericClaims (m : IVModel (Fin 5)) : Prop :=
  armMean (uniformPopulation (Fin 5)) (1/2) false (ivKnowledge m) = 42/5 ∧
  armMean (uniformPopulation (Fin 5)) (1/2) true (ivKnowledge m) = 43/5 ∧
  firstStage (uniformPopulation (Fin 5)) (1/2) m = 1/5 ∧
  0 < firstStage (uniformPopulation (Fin 5)) (1/2) m ∧
  armMean (uniformPopulation (Fin 5)) (1/2) false (ivOutcome m) = 16/5 ∧
  armMean (uniformPopulation (Fin 5)) (1/2) true (ivOutcome m) = 16/5 ∧
  ivReducedForm (uniformPopulation (Fin 5)) (1/2) m = 0 ∧
  ivRatio (uniformPopulation (Fin 5)) (1/2) m = 0

/-- T4(b2,b3): identical IV quantities, but increaser masses 2/5 and 3/5
and mean induced one-unit effects 1 and 4/3 in A and B respectively. -/
theorem models_numbers : FiveTypeNumericClaims modelA ∧ FiveTypeNumericClaims modelB ∧
    eventProb (uniformPopulation (Fin 5)) (increaser modelA) = 2/5 ∧
    eventProb (uniformPopulation (Fin 5)) (increaser modelB) = 3/5 ∧
    increaserEffect (uniformPopulation (Fin 5)) modelA = 1 ∧
    increaserEffect (uniformPopulation (Fin 5)) modelB = 4/3 := by
  unfold FiveTypeNumericClaims ivRatio firstStage ivReducedForm ivKnowledge ivOutcome
  simp only [fair_armMean, contrast_eq (uniformPopulation (Fin 5)) (1/2) (by norm_num)]
  norm_num [mean, uniformPopulation, modelA, modelB, knowledgeMargin, indicator,
    eventProb, increaser, increaserEffect, eventMean, ivOutcome, Fin.sum_univ_succ]

/-- T4(b): both models respect the 2008 index ranges, have nondecreasing
support responses, and every increaser crosses exactly the 8→9 margin. -/
def FiveTypeUnitClaims (m : IVModel (Fin 5)) (i : Fin 5) : Prop :=
    (∀ z, m.knowledge z i ∈ ({8,9} : Finset ℕ) ∧ m.knowledge z i ≤ 18) ∧
    (∀ k, 0 ≤ m.response k i ∧ m.response k i ≤ 7) ∧
    Monotone (fun k => m.response k i) ∧
    (increaser m i → m.knowledge false i = 8 ∧ m.knowledge true i = 9)

/-- T4(b): range, monotone-support and one-unit-increaser properties of either five-type model. -/
theorem models_unit_properties (m : IVModel (Fin 5)) (hm : m=modelA ∨ m=modelB) (i : Fin 5) : FiveTypeUnitClaims m i := by
  unfold FiveTypeUnitClaims
  rcases hm with rfl | rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro z
      fin_cases i <;> cases z <;> norm_num [modelA]
    · intro k
      fin_cases i <;> by_cases h : 9 ≤ k <;> norm_num [modelA, knowledgeMargin, indicator, h]
    · intro k l h
      have hh := knowledgeMargin_monotone h
      fin_cases i <;> norm_num [modelA] <;> linarith
    · fin_cases i <;> norm_num [modelA, increaser]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro z
      fin_cases i <;> cases z <;> norm_num [modelB]
    · intro k
      fin_cases i <;> by_cases h : 9 ≤ k <;> norm_num [modelB, knowledgeMargin, indicator, h]
    · intro k l h
      have hh := knowledgeMargin_monotone h
      fin_cases i <;> norm_num [modelB] <;> linarith
    · fin_cases i <;> norm_num [modelB, increaser]

/-- T4(b4): no functional of the full observable law can equal the increaser
effect in both admissible models. Consequently such an effect is not identified
by assignment independence, exclusion, consistency, and a positive first stage. -/
def IncreaserNonidentificationClaim : Prop :=
    ¬ ∃ F : ((Bool × (ℕ × ℝ) → ℝ) → ℝ),
      F (observableLaw (uniformPopulation (Fin 5)) (1/2) modelA) =
        increaserEffect (uniformPopulation (Fin 5)) modelA ∧
      F (observableLaw (uniformPopulation (Fin 5)) (1/2) modelB) =
        increaserEffect (uniformPopulation (Fin 5)) modelB

/-- T4(b4): the exact full-observable-law nonidentification claim. -/
theorem increaser_nonidentification : IncreaserNonidentificationClaim := by
  unfold IncreaserNonidentificationClaim
  rintro ⟨F, hA, hB⟩
  have h := models_numbers
  rw [h.2.2.2.2.1] at hA
  rw [h.2.2.2.2.2] at hB
  rw [models_observable_law (1/2)] at hA
  linarith

/-- T4's counterexamples jointly verify the zero IV ratio with positive
increaser effects and equality of the complete observable laws with different
increaser effects. Supporting lemmas establish all ranges, type-level effects,
arbitrary increaser averages, and the impossibility of an identifying function. -/
theorem iv_counterexamples : UpDownNumericClaims ∧ (∀ i, UpDownUnitClaims i) ∧
    FiveTypeNumericClaims modelA ∧ FiveTypeNumericClaims modelB ∧
    observableLaw (uniformPopulation (Fin 5)) (1/2) modelA =
      observableLaw (uniformPopulation (Fin 5)) (1/2) modelB ∧
    increaserEffect (uniformPopulation (Fin 5)) modelA = 1 ∧
    increaserEffect (uniformPopulation (Fin 5)) modelB = 4/3 ∧
    (∀ z k y, conditionalObservableLaw (uniformPopulation (Fin 5)) modelA z k y = fiveTypeObservableLaw z k y ∧
      conditionalObservableLaw (uniformPopulation (Fin 5)) modelB z k y = fiveTypeObservableLaw z k y) ∧
    (∀ m i, m=modelA ∨ m=modelB → FiveTypeUnitClaims m i) ∧
    IncreaserNonidentificationClaim := by
  exact ⟨upDown_numbers, upDown_unit_properties, models_numbers.1, models_numbers.2.1,
    models_observable_law (1/2), models_numbers.2.2.2.2.1, models_numbers.2.2.2.2.2,
    models_conditional_law, fun m i hm => models_unit_properties m hm i, increaser_nonidentification⟩

/-- T5's marginal causal increment δ_i(j)=Y_i(j)-Y_i(j-1). -/
def doseIncrement {Ω : Type u} (m : IVModel Ω) (j : ℕ) (i : Ω) : ℝ :=
  m.response j i - m.response (j-1) i

/-- T5's crossing indicator C_i(j)=1{K_i(0)<j≤K_i(1)}. -/
def crossing {Ω : Type u} (m : IVModel Ω) (j : ℕ) (i : Ω) : ℝ :=
  indicator (m.knowledge false i < j ∧ j ≤ m.knowledge true i)

/-- T5(v)'s signed crossing R_i(j)=1{K_i(1)≥j}-1{K_i(0)≥j}. -/
def signedCrossing {Ω : Type u} (m : IVModel Ω) (j : ℕ) (i : Ω) : ℝ :=
  indicator (j ≤ m.knowledge true i) - indicator (j ≤ m.knowledge false i)

/-- T5(iv)'s weight numerator P(K_i(0)<j≤K_i(1)). -/
def marginProb {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : IVModel Ω) (j : ℕ) : ℝ :=
  eventProb P (fun i => m.knowledge false i < j ∧ j ≤ m.knowledge true i)

/-- T5(iv)'s normalized margin weight w_j=P(C_i(j)=1)/Δ_K. -/
def marginWeight {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) (j : ℕ) : ℝ := marginProb P m j / firstStage P p m

/-- T5(iv)'s conditional mean dose increment among students crossing j.
Only positive-probability margins appear in the final formula. -/
def marginEffect {Ω : Type u} [Fintype Ω] (P : Population Ω) (m : IVModel Ω) (j : ℕ) : ℝ :=
  eventMean P (fun i => m.knowledge false i < j ∧ j ≤ m.knowledge true i) (doseIncrement m j)

/-- Nonnegative event indicators support the repaired IV weights (T5). -/
theorem indicator_nonneg (A : Prop) : 0 ≤ indicator A := by
  by_cases h : A <;> simp [indicator, h]

/-- A finite expectation commutes with any finite sum (T5(iii)). -/
theorem mean_sum {Ω : Type u} {I : Type v} [Fintype Ω] (P : Population Ω)
    (s : Finset I) (f : I → Ω → ℝ) :
    mean P (fun i => ∑ j ∈ s, f j i) = ∑ j ∈ s, mean P (f j) := by
  simp only [mean, mul_sum]
  rw [sum_comm]

/-- An event with probability zero contributes zero to any finite weighted
outcome sum. This justifies omitting zero-probability margins in T5(iv). -/
theorem zero_event_numerator {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (A : Ω → Prop) (f : Ω → ℝ) (hA : eventProb P A = 0) :
    mean P (fun i => indicator (A i) * f i) = 0 := by
  have hw (i : Ω) : P.mass i * indicator (A i) = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (P.nonneg i) (indicator_nonneg (A i)))).mp hA i (mem_univ i)
  unfold mean
  apply sum_eq_zero
  intro i _
  rw [← mul_assoc, hw, zero_mul]

/-- T5(i): the population identities for the potential-knowledge and
potential-support contrasts. Under exclusion, consistency and independent
assignment, these hold when `0 < p ∧ p < 1`. -/
def IVPopulationContrastClaims {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ) (m : IVModel Ω) : Prop :=
    firstStage P p m = mean P (fun i => (m.knowledge true i : ℝ) - m.knowledge false i) ∧
    ivReducedForm P p m = mean P (fun i => m.response (m.knowledge true i) i -
      m.response (m.knowledge false i) i)

/-- T5(i): independent assignment, exclusion and consistency identify both population contrasts. -/
theorem iv_population_contrasts {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (m : IVModel Ω) : IVPopulationContrastClaims P p m := by
  unfold IVPopulationContrastClaims
  unfold firstStage ivReducedForm
  constructor <;> rw [contrast_eq P p hp, ← mean_sub] <;> rfl

/-- T5(i): the covariance ratios and conditional-mean ratios agree whenever
the first stage is nonzero. This needs no knowledge monotonicity. -/
def IVCovarianceClaims {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ) (m : IVModel Ω) : Prop :=
    covariance P p (fun z _ => assignment z) (ivKnowledge m) = p*(1-p)*firstStage P p m ∧
    covariance P p (fun z _ => assignment z) (ivOutcome m) = p*(1-p)*ivReducedForm P p m ∧
    (firstStage P p m ≠ 0 →
      covariance P p (fun z _ => assignment z) (ivOutcome m) /
        covariance P p (fun z _ => assignment z) (ivKnowledge m) = ivRatio P p m)

/-- T5(i): the covariance factor and IV-ratio identities under independent binary assignment. -/
theorem iv_covariance_ratio {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (m : IVModel Ω) : IVCovarianceClaims P p m := by
  unfold IVCovarianceClaims
  have hk : covariance P p (fun z _ => assignment z) (ivKnowledge m) = p*(1-p)*firstStage P p m := by
    rw [assignment_covariance, firstStage, contrast_eq P p hp]
  have hy : covariance P p (fun z _ => assignment z) (ivOutcome m) = p*(1-p)*ivReducedForm P p m := by
    rw [assignment_covariance, ivReducedForm, contrast_eq P p hp]
  refine ⟨hk, hy, ?_⟩
  intro hfirst
  have hf : p*(1-p) ≠ 0 := ne_of_gt (mul_pos hp.1 (sub_pos.mpr hp.2))
  rw [hk, hy, ivRatio]
  exact mul_div_mul_left _ _ hf

/-- Finite telescoping across a prefix of the bounded integer knowledge
range. This is the fixed-population lemma behind T5(ii),(v). -/
theorem prefix_increment_sum (J k : ℕ) (hk : k ≤ J) (f : ℕ → ℝ) :
    (∑ r ∈ range J, indicator (r < k) * (f (r+1) - f r)) = f k - f 0 := by
  have hs : (range J).filter (fun r => r < k) = range k := by
    ext r
    simp only [mem_filter, mem_range]
    omega
  calc
    _ = ∑ r ∈ (range J).filter (fun r => r < k), (f (r+1)-f r) := by
      simp only [sum_filter, indicator, ite_mul, one_mul, zero_mul]
    _ = ∑ r ∈ range k, (f (r+1)-f r) := by rw [hs]
    _ = f k - f 0 := sum_range_sub f k

/-- T5(v): signed telescoping for any two bounded integer doses, even when
knowledge decreases. No response shape assumption is used. -/
theorem signed_dose_identity (J k₀ k₁ : ℕ) (h₀ : k₀ ≤ J) (h₁ : k₁ ≤ J) (f : ℕ → ℝ) :
    f k₁ - f k₀ = ∑ r ∈ range J,
      (indicator (r+1 ≤ k₁) - indicator (r+1 ≤ k₀)) * (f (r+1)-f r) := by
  have he (r k : ℕ) : r+1 ≤ k ↔ r < k := by omega
  simp_rw [he, sub_mul, sum_sub_distrib, prefix_increment_sum J k₁ h₁,
    prefix_increment_sum J k₀ h₀]
  ring

/-- T5(v): each signed crossing is -1,0,or 1. -/
theorem signed_crossing_values {Ω : Type u} (m : IVModel Ω) (j : ℕ) (i : Ω) :
    signedCrossing m j i ∈ ({-1,0,1} : Finset ℝ) := by
  by_cases h₁ : j ≤ m.knowledge true i <;> by_cases h₀ : j ≤ m.knowledge false i <;>
    norm_num [signedCrossing, indicator, h₁, h₀]

/-- T5(v): under individual knowledge monotonicity, the signed crossing
equals the nonnegative crossing indicator. -/
theorem signed_crossing_monotone {Ω : Type u} (m : IVModel Ω) (j : ℕ) (i : Ω)
    (hmono : m.knowledge false i ≤ m.knowledge true i) :
    signedCrossing m j i = crossing m j i := by
  by_cases h₁ : j ≤ m.knowledge true i
  · by_cases h₀ : j ≤ m.knowledge false i
    · have hn : ¬ m.knowledge false i < j := by omega
      simp [signedCrossing, crossing, indicator, h₁, h₀, hn]
    · have hl : m.knowledge false i < j := by omega
      simp [signedCrossing, crossing, indicator, h₁, h₀, hl]
  · have h₀ : ¬ j ≤ m.knowledge false i := by omega
    simp [signedCrossing, crossing, indicator, h₁, h₀]

/-- T5(v)'s two exact pointwise signed identities for support and knowledge.
Printed margins j=1,...,J are stored as r+1 for r in range J. -/
def IVSignedUnitClaims {Ω : Type u} (m : IVModel Ω) (J : ℕ) (i : Ω) : Prop :=
    m.response (m.knowledge true i) i - m.response (m.knowledge false i) i =
      ∑ r ∈ range J, signedCrossing m (r+1) i * doseIncrement m (r+1) i ∧
    (m.knowledge true i : ℝ) - m.knowledge false i =
      ∑ r ∈ range J, signedCrossing m (r+1) i

/-- T5(v): exact signed support and dose telescoping for every bounded unit. -/
theorem iv_signed_unit_identities {Ω : Type u} (m : IVModel Ω) (J : ℕ) (i : Ω)
    (hb : m.knowledge false i ≤ J ∧ m.knowledge true i ≤ J) : IVSignedUnitClaims m J i := by
  unfold IVSignedUnitClaims
  constructor
  · simpa [signedCrossing, doseIncrement] using
      signed_dose_identity J _ _ hb.1 hb.2 (fun k => m.response k i)
  · simpa [signedCrossing, Nat.cast_add, Nat.cast_one] using
      signed_dose_identity J _ _ hb.1 hb.2 (fun k => (k : ℝ))

/-- T5(ii): monotone integer knowledge responses telescope to crossed
one-unit increments, and the same indicators count the knowledge increase. -/
def IVMonotoneUnitClaims {Ω : Type u} (m : IVModel Ω) (J : ℕ) (i : Ω) : Prop :=
    m.response (m.knowledge true i) i - m.response (m.knowledge false i) i =
      ∑ r ∈ range J, crossing m (r+1) i * doseIncrement m (r+1) i ∧
    (m.knowledge true i : ℝ) - m.knowledge false i =
      ∑ r ∈ range J, crossing m (r+1) i

/-- T5(ii): support and dose telescope over upward-crossed margins under knowledge monotonicity. -/
theorem iv_monotone_unit_identities {Ω : Type u} (m : IVModel Ω) (J : ℕ) (i : Ω)
    (hb : m.knowledge false i ≤ J ∧ m.knowledge true i ≤ J)
    (hm : m.knowledge false i ≤ m.knowledge true i) : IVMonotoneUnitClaims m J i := by
  unfold IVMonotoneUnitClaims
  simpa only [IVSignedUnitClaims, signed_crossing_monotone m _ i hm] using iv_signed_unit_identities m J i hb

/-- T5(ii): nonincreasers cross no upward margin, so only increasers enter
the repaired estimand. In particular, students with K(1)=K(0) contribute zero. -/
theorem nonincreaser_crossing_zero {Ω : Type u} (m : IVModel Ω) (i : Ω)
    (h : ¬ increaser m i) (j : ℕ) : crossing m j i = 0 := by
  have hx : ¬ (m.knowledge false i < j ∧ j ≤ m.knowledge true i) := by
    unfold increaser at h
    omega
  simp [crossing, indicator, hx]

/-- T5(v): a downward-crossed margin contributes -1. This precisely records
the negative contribution excluded by knowledge monotonicity. -/
theorem defier_signed_crossing {Ω : Type u} (m : IVModel Ω) (i : Ω) (j : ℕ)
    (h : m.knowledge true i < j ∧ j ≤ m.knowledge false i) :
    signedCrossing m j i = -1 := by
  have hn : ¬ j ≤ m.knowledge true i := by omega
  simp [signedCrossing, indicator, hn, h.2]

/-- T5(iii): expectation of the telescoping identities gives the support
numerator and first-stage denominator as finite sums over crossed margins. -/
def IVMarginTotalClaims {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ) (m : IVModel Ω) (J : ℕ) : Prop :=
    ivReducedForm P p m = ∑ r ∈ range J, mean P (fun i => crossing m (r+1) i * doseIncrement m (r+1) i) ∧
    firstStage P p m = ∑ r ∈ range J, marginProb P m (r+1)

/-- T5(iii): finite expectations of the crossed-margin telescoping identities. -/
theorem iv_margin_totals {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (m : IVModel Ω) (J : ℕ)
    (hb : ∀ i, m.knowledge false i ≤ J ∧ m.knowledge true i ≤ J)
    (hm : ∀ i, m.knowledge false i ≤ m.knowledge true i) : IVMarginTotalClaims P p m J := by
  unfold IVMarginTotalClaims
  have hpop := iv_population_contrasts P p hp m
  constructor
  · rw [hpop.2]
    calc
      _ = mean P (fun i => ∑ r ∈ range J, crossing m (r+1) i * doseIncrement m (r+1) i) := by
        congr 1
        funext i
        exact (iv_monotone_unit_identities m J i (hb i) (hm i)).1
      _ = _ := mean_sum P _ _
  · rw [hpop.1]
    calc
      _ = mean P (fun i => ∑ r ∈ range J, crossing m (r+1) i) := by
        congr 1
        funext i
        exact (iv_monotone_unit_identities m J i (hb i) (hm i)).2
      _ = _ := mean_sum P _ _

/-- Every crossed-margin probability is nonnegative, supporting T5(iv). -/
theorem marginProb_nonneg {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (m : IVModel Ω) (j : ℕ) : 0 ≤ marginProb P m j :=
  mean_nonneg P _ (fun i => indicator_nonneg _)

/-- T5(iv): a positive-probability margin's weight times its conditional
increment equals its unnormalized causal contribution divided by the first stage. -/
theorem margin_contribution {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (m : IVModel Ω) (j : ℕ) (hfirst : 0 < firstStage P p m) :
    (if 0 < marginProb P m j then marginWeight P p m j * marginEffect P m j else 0) =
      mean P (fun i => crossing m j i * doseIncrement m j i) / firstStage P p m := by
  by_cases hj : 0 < marginProb P m j
  · simp only [hj, ↓reduceIte, marginWeight, marginEffect, eventMean]
    change (marginProb P m j / firstStage P p m) *
      (mean P (fun i => crossing m j i * doseIncrement m j i) / marginProb P m j) = _
    field_simp [ne_of_gt hj, ne_of_gt hfirst]
  · have hz : marginProb P m j = 0 := le_antisymm (le_of_not_gt hj) (marginProb_nonneg P m j)
    have hn := zero_event_numerator P
      (fun i => m.knowledge false i < j ∧ j ≤ m.knowledge true i) (doseIncrement m j) hz
    change mean P (fun i => crossing m j i * doseIncrement m j i) = 0 at hn
    simp [hj, hn]

/-- T5(iv), complete repaired multilevel IV estimand: monotone bounded
integer knowledge, independent nondegenerate assignment, exclusion,
consistency and a positive first stage yield nonnegative margin weights
summing to one and a weighted average over positive-probability crossed
margins. The causal increments may have either sign. -/
def IVMarginAverageClaims {Ω : Type u} [Fintype Ω] (P : Population Ω) (p : ℝ) (m : IVModel Ω) (J : ℕ) : Prop :=
    (∀ j, 0 ≤ marginWeight P p m j) ∧
    (∑ r ∈ range J, marginWeight P p m (r+1)) = 1 ∧
    ivRatio P p m = ∑ r ∈ (range J).filter (fun r => 0 < marginProb P m (r+1)),
      marginWeight P p m (r+1) * marginEffect P m (r+1)

/-- T5(iv): nonnegative normalized margin weights and the corrected multilevel IV formula. -/
theorem corrected_multilevel_iv {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (m : IVModel Ω) (J : ℕ)
    (hb : ∀ i, m.knowledge false i ≤ J ∧ m.knowledge true i ≤ J)
    (hm : ∀ i, m.knowledge false i ≤ m.knowledge true i)
    (hfirst : 0 < mean P (fun i => (m.knowledge true i : ℝ) - m.knowledge false i)) : IVMarginAverageClaims P p m J := by
  unfold IVMarginAverageClaims
  classical
  have hfs : 0 < firstStage P p m := by rw [(iv_population_contrasts P p hp m).1]; exact hfirst
  have ht := iv_margin_totals P p hp m J hb hm
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact div_nonneg (marginProb_nonneg P m j) hfs.le
  · unfold marginWeight
    rw [← sum_div, ← ht.2, div_self (ne_of_gt hfs)]
  · rw [sum_filter]
    simp_rw [margin_contribution P p m _ hfs]
    rw [← sum_div, ← ht.1]
    rfl


/-- T5, complete corrected IV statement for bounded integer knowledge.
The joint-law representation enforces assignment independence, exclusion and
consistency. This collects identification, covariance equivalence, pointwise
and expected monotone telescoping, the normalized conditional-margin formula,
and the general signed formulas that remain valid without monotonicity. -/
theorem iv_repair {Ω : Type u} [Fintype Ω] (P : Population Ω)
    (p : ℝ) (hp : 0 < p ∧ p < 1) (m : IVModel Ω) (J : ℕ)
    (hb : ∀ i, m.knowledge false i ≤ J ∧ m.knowledge true i ≤ J)
    (hm : ∀ i, m.knowledge false i ≤ m.knowledge true i)
    (hfirst : 0 < mean P (fun i => (m.knowledge true i : ℝ) - m.knowledge false i)) :
    IVPopulationContrastClaims P p m ∧ IVCovarianceClaims P p m ∧
    (∀ i, IVMonotoneUnitClaims m J i) ∧ IVMarginTotalClaims P p m J ∧
    IVMarginAverageClaims P p m J ∧
    (∀ (m' : IVModel Ω) J' i, m'.knowledge false i ≤ J' ∧ m'.knowledge true i ≤ J' →
      IVSignedUnitClaims m' J' i) ∧
    (∀ i j, ¬ increaser m i → crossing m j i = 0) ∧
    (∀ i j, signedCrossing m j i ∈ ({-1,0,1} : Finset ℝ) ∧ signedCrossing m j i = crossing m j i) ∧
    (∀ (m' : IVModel Ω) i j, m'.knowledge true i < j ∧ j ≤ m'.knowledge false i →
      signedCrossing m' j i = -1) := by
  exact ⟨iv_population_contrasts P p hp m, iv_covariance_ratio P p hp m,
    fun i => iv_monotone_unit_identities m J i (hb i) (hm i),
    iv_margin_totals P p hp m J hb hm, corrected_multilevel_iv P p hp m J hb hm hfirst,
    fun m' J' i hb' => iv_signed_unit_identities m' J' i hb',
    fun i j h => nonincreaser_crossing_zero m i h j,
    fun i j => ⟨signed_crossing_values m j i, signed_crossing_monotone m j i (hm i)⟩,
    fun m' i j h => defier_signed_crossing m' i j h⟩

end
end AronowAudit.P043

