import Mathlib

/-!
P009: Sävje, Aronow and Hudgens, Average treatment effects in the presence of
unknown interference. Randomization designs use finite weighted laws. The
general coverage theorem and simulation sampling formulas also use measures.
Unit labels are zero-based Fin n; paper unit i is Lean unit i-1.
-/

namespace AronowAudit.P009

open scoped BigOperators
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Section 3.1, p. 676: "an n-dimensional binary vector" in {0,1}^n. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

/-- The numerical value of a binary assignment: false is control, true is treatment. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- Section 3.1, p. 676: "The probability distribution of Z is the design".
A finite probability law, with nonnegative masses summing to one. -/
structure Law (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

/-- Section 3.1, p. 676: "The design is the sole source of randomness".
Expectations are weighted finite sums, not superpopulation expectations. -/
def mean {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.mass ω * X ω

/-- Finite expectation preserves constants because the design masses sum to one. -/
theorem mean_const {Ω : Type*} [Fintype Ω] (P : Law Ω) (c : ℝ) :
    mean P (fun _ => c) = c := by
  simp only [mean, ← Finset.sum_mul, P.total, one_mul]

/-- Finite expectation is additive; used in the paper's exact finite identities. -/
theorem mean_add {Ω : Type*} [Fintype Ω] (P : Law Ω) (X Y : Ω → ℝ) :
    mean P (fun ω => X ω + Y ω) = mean P X + mean P Y := by
  simp [mean, mul_add, Finset.sum_add_distrib]

/-- Finite expectation preserves subtraction. -/
theorem mean_sub {Ω : Type*} [Fintype Ω] (P : Law Ω) (X Y : Ω → ℝ) :
    mean P (fun ω => X ω - Y ω) = mean P X - mean P Y := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

/-- Constants can be taken outside finite expectation. -/
theorem mean_const_mul {Ω : Type*} [Fintype Ω] (P : Law Ω) (c : ℝ) (X : Ω → ℝ) :
    mean P (fun ω => c * X ω) = c * mean P X := by
  simp [mean, Finset.mul_sum, mul_left_comm, mul_assoc]

/-- Division by a fixed design quantity commutes with finite expectation. -/
theorem mean_div {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) (c : ℝ) :
    mean P (fun ω => X ω/c) = mean P X/c := by
  simp only [div_eq_mul_inv, mul_comm _ c⁻¹]
  exact mean_const_mul P c⁻¹ X

/-- Finite expectation commutes with a finite sum. -/
theorem mean_sum {Ω U : Type*} [Fintype Ω] [Fintype U]
    (P : Law Ω) (X : U → Ω → ℝ) :
    mean P (fun ω => ∑ i, X i ω) = ∑ i, mean P (X i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

/-- Probability of an event under the finite design. -/
def prob {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) : ℝ :=
  mean P (fun ω => if A ω then 1 else 0)

/-- Event probabilities under the randomization law are nonnegative. -/
theorem probability_nonnegative {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) :
    0 ≤ prob P A := by
  unfold prob mean
  apply Finset.sum_nonneg
  intro ω _
  by_cases hω : A ω <;> simp [hω, P.nonneg ω]

/-- Finite union bound, used for the corrected plug-in coverage argument. -/
theorem probability_union_bound {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A B C : Ω → Prop) (h : ∀ ω, A ω → B ω ∨ C ω) :
    prob P A ≤ prob P B + prob P C := by
  unfold prob mean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω <;> by_cases hb : B ω <;> by_cases hc : C ω <;>
    simp [ha, hb, hc, P.nonneg ω] <;> try linarith [P.nonneg ω]
  exact False.elim ((h ω ha).elim hb hc)

/-- Complementary event probabilities sum to one on the finite design. -/
theorem probability_complement {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) :
    prob P (fun ω => ¬ A ω) = 1-prob P A := by
  unfold prob
  calc
    _ = mean P (fun ω => 1-(if A ω then 1 else 0)) := by
      congr 1
      funext ω
      by_cases hω : A ω <;> simp [hω]
    _ = _ := by rw [mean_sub, mean_const]

/-- Conditional expectation, defined as a ratio of finite sums. Every substantive
use requires positive event probability; the totalized value at probability zero
is not a claim that the paper defines conditioning there. -/
def cmean {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) (X : Ω → ℝ) : ℝ :=
  mean P (fun ω => if A ω then X ω else 0) / prob P A

/-- Design-based covariance, the expected product of the centered variables. -/
def cov {Ω : Type*} [Fintype Ω] (P : Law Ω) (X Y : Ω → ℝ) : ℝ :=
  mean P (fun ω => (X ω - mean P X) * (Y ω - mean P Y))

/-- Design-based variance. -/
def var {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) : ℝ := cov P X X

/-- Every design variance is nonnegative, as a weighted sum of squares. -/
theorem variance_nonnegative {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) :
    0 ≤ var P X := by
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (P.nonneg ω) (mul_self_nonneg _)

/-- T29's corrected Cauchy–Schwarz step, for arbitrary random variables on
the finite design. Both centered variables retain their own indices. -/
theorem covariance_cauchy_schwarz {Ω : Type*} [Fintype Ω] (P : Law Ω) (X Y : Ω → ℝ) :
    |cov P X Y| ≤ Real.sqrt (var P X * var P Y) := by
  let f := fun ω => Real.sqrt (P.mass ω)*(X ω-mean P X)
  let g := fun ω => Real.sqrt (P.mass ω)*(Y ω-mean P Y)
  have hp : ∀ ω, f ω*g ω = P.mass ω*((X ω-mean P X)*(Y ω-mean P Y)) := by
    intro ω
    dsimp [f, g]
    calc
      _ = (Real.sqrt (P.mass ω))^2*((X ω-mean P X)*(Y ω-mean P Y)) := by ring
      _ = _ := by rw [Real.sq_sqrt (P.nonneg ω)]
  have hf : ∀ ω, f ω^2 = P.mass ω*((X ω-mean P X)*(X ω-mean P X)) := by
    intro ω
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (P.nonneg ω), pow_two]
  have hg : ∀ ω, g ω^2 = P.mass ω*((Y ω-mean P Y)*(Y ω-mean P Y)) := by
    intro ω
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (P.nonneg ω), pow_two]
  apply Real.abs_le_sqrt
  simpa only [hp, hf, hg, var, cov, mean] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g)

/-- Covariance conditional on an event, using the same conditional distribution
for both centering terms and for the final expectation. -/
def ccov {Ω : Type*} [Fintype Ω] (P : Law Ω) (A : Ω → Prop) (X Y : Ω → ℝ) : ℝ :=
  cmean P A (fun ω => (X ω - cmean P A X) * (Y ω - cmean P A Y))

/-- Section 3.1, p. 676: "Each unit has a function y_i : {0,1}^n → R".
Outcomes are specified on the entire cube, including assignments of probability
zero. The observed Y_i is evaluation of this function. -/
structure Experiment (n : ℕ) where
  design : Law (Assignment n)
  outcome : Fin n → Assignment n → ℝ

/-- Marginal treatment probability p_i = Pr(Z_i=1), Definition 6, p. 682. -/
def marginal {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool) : ℝ :=
  prob E.design (fun z => z i = b)

/-- The treated and control marginal probabilities sum to one. -/
theorem marginal_partition {n : ℕ} (E : Experiment n) (i : Fin n) :
    marginal E i true+marginal E i false = 1 := by
  classical
  unfold marginal prob
  rw [← mean_add]
  calc
    _ = mean E.design (fun _ => 1) := by
      congr 1
      funext z
      cases hz : z i <;> simp [hz]
    _ = 1 := mean_const E.design 1

/-- y_i(b;z_-i), pp. 676–677. Replacing coordinate i retains all other
coordinates, and avoids treating an off-support counterfactual as an observation. -/
def potential {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool)
    (z : Assignment n) : ℝ := E.outcome i (Function.update z i b)

/-- p. 677: "The assignment-conditional unit-level treatment effect" is
y_i(1;z_-i)-y_i(0;z_-i). -/
def effect {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) : ℝ :=
  potential E i true z - potential E i false z

/-- Definition 2, p. 677: "the average of the assignment-conditional unit-level
treatment effects under a given assignment". -/
def ateAt {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  (∑ i, effect E i z) / n

/-- Section 3.2, p. 676: under no interference, equal own assignments imply
equal outcomes, for every pair of assignments in the full cube. -/
def NoInterference {n : ℕ} (E : Experiment n) : Prop :=
  ∀ i z z', z i = z' i → E.outcome i z = E.outcome i z'

/-- Definition 1, p. 677: the ATE under no interference. The all-control vector
is a reference for the other coordinates; NoInterference makes this immaterial. -/
def ate {n : ℕ} (E : Experiment n) : ℝ := ateAt E (fun _ => false)

/-- Definition 3, p. 677: "The expected average treatment effect (EATE) is the
expected assignment-conditional average treatment effect". -/
def eate {n : ℕ} (E : Experiment n) : ℝ := mean E.design (ateAt E)

/-- Definition 4, p. 678: "the average difference between the conditional
expected outcomes for the two treatment conditions". -/
def adse {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, (cmean E.design (fun z => z i = true) (E.outcome i) -
    cmean E.design (fun z => z i = false) (E.outcome i))) / n

/-- Definition A1, Supplement A, p. 2: inverse probability weighted arm mean. -/
def muHat {n : ℕ} (E : Experiment n) (b : Bool) (z : Assignment n) : ℝ :=
  (∑ i, (if z i = b then E.outcome i z else 0) / marginal E i b) / n

/-- Definition A1, Supplement A, p. 2: the estimated arm population size. -/
def nHat {n : ℕ} (E : Experiment n) (b : Bool) (z : Assignment n) : ℝ :=
  ∑ i, (if z i = b then (1 : ℝ) else 0) / marginal E i b


/-- Definition A1, Supplement A, p. 2: breve mu_z, the conditional potential mean. -/
def muBreve {n : ℕ} (E : Experiment n) (b : Bool) : ℝ :=
  (∑ i, cmean E.design (fun z => z i = b) (potential E i b)) / n

/-- Definition 6, p. 682: the Horvitz–Thompson treatment effect estimator. -/
def ht {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  muHat E true z - muHat E false z

/-- Both arm denominators are nonzero: the domain of the paper's Hájek formula. -/
def ArmsNonempty {n : ℕ} (E : Experiment n) (z : Assignment n) : Prop :=
  nHat E true z ≠ 0 ∧ nHat E false z ≠ 0

/-- Definition 6, p. 682: the Hájek estimator, extended by zero on the empty-arm
event. On ArmsNonempty this is exactly the printed ratio. This is a stated
modeling convention for the paper's undefined event (P009-E015). -/
def hajek {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  if ArmsNonempty E z then
    (n : ℝ) * muHat E true z / nHat E true z -
    (n : ℝ) * muHat E false z / nHat E false z
  else 0

/-- Section 4, p. 680: "unit i interferes with unit j if changing i's treatment
changes j's outcome under at least one treatment assignment"; "a unit
interferes with itself even if its own treatment does not affect its outcome". -/
def Interferes {n : ℕ} (E : Experiment n) (i j : Fin n) : Prop :=
  i = j ∨ ∃ z z', (∀ ℓ, ℓ ≠ i → z ℓ = z' ℓ) ∧ E.outcome j z ≠ E.outcome j z'

/-- The printed binary interference indicator I_ij, Section 4, p. 680. -/
def I {n : ℕ} (E : Experiment n) (i j : Fin n) : ℝ :=
  if Interferes E i j then 1 else 0

/-- A finite structural certificate for explicit linear counterexamples:
when outcome j is the sum of assignments in G, the incoming interfering
treatments are precisely G together with the mandated self-interference. -/
theorem interferes_sum_bit {n : ℕ} (E : Experiment n) (j i : Fin n)
    (G : Finset (Fin n)) (hy : ∀ z, E.outcome j z = ∑ ℓ ∈ G, bit (z ℓ)) :
    Interferes E i j ↔ i = j ∨ i ∈ G := by
  constructor
  · intro h
    rcases h with hij | ⟨z, z', hagree, hne⟩
    · exact Or.inl hij
    · by_contra hnot
      have hiG : i ∉ G := by tauto
      apply hne
      rw [hy z, hy z']
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      rw [hagree ℓ (by intro heq; subst ℓ; exact hiG hℓ)]
  · intro h
    rcases h with hij | hiG
    · exact Or.inl hij
    · refine Or.inr ⟨(fun _ => false), Function.update (fun _ => false) i true, ?_, ?_⟩
      · intro ℓ hℓ
        simp [Function.update_of_ne hℓ]
      · rw [hy, hy]
        simp [bit, Function.update, hiG]

/-- Definition 5, p. 681: d_ij is the indicator of a common interfering unit. -/
def Dependent {n : ℕ} (E : Experiment n) (i j : Fin n) : Prop :=
  ∃ ℓ, Interferes E ℓ i ∧ Interferes E ℓ j

/-- Definition 5, p. 681: binary interference dependence indicator d_ij. -/
def d {n : ℕ} (E : Experiment n) (i j : Fin n) : ℝ :=
  if Dependent E i j then 1 else 0

/-- p. 681: d_i = sum_j d_ij, including the self-dependence. -/
def degree {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ := ∑ j, d E i j

/-- Definition 5, p. 681: "interference dependence", d_AVG. -/
def dAvg {n : ℕ} (E : Experiment n) : ℝ := (∑ i, degree E i) / n

/-- p. 681: c_i = sum_j I_ij counts outcomes affected by treatment i. -/
def outgoing {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ := ∑ j, I E i j

/-- Definition A3, Supplement A, p. 9: reflected c_i counts incoming treatments. -/
def incoming {n : ℕ} (E : Experiment n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => Interferes E j i)).card

/-- p. 681: C_1, the mean outgoing interference count. -/
def C1 {n : ℕ} (E : Experiment n) : ℝ := (∑ i, outgoing E i) / n

/-- p. 681: C_2, the root mean square outgoing interference count. -/
def C2 {n : ℕ} (E : Experiment n) : ℝ :=
  Real.sqrt ((∑ i, outgoing E i ^ 2) / n)

/-- p. 681: C_p = [n^-1 sum_i c_i^p]^(1/p), for positive real p. -/
def Cp {n : ℕ} (E : Experiment n) (p : ℝ) : ℝ :=
  Real.rpow ((∑ i, Real.rpow (outgoing E i) p) / n) (1 / p)

/-- p. 681: "C_infinity ... is the maximum c_i over U". For n>0, the
finite supremum is this maximum. -/
def Cinf {n : ℕ} (E : Experiment n) : ℝ := sSup (Set.range (outgoing E))

/-- pp. 692 and 693: d_MAX is the maximum of d_i. -/
def dMax {n : ℕ} (E : Experiment n) : ℝ := sSup (Set.range (degree E))

/-- p. 692: d_RMS is sqrt(n^-1 sum_i d_i^2). -/
def dRMS {n : ℕ} (E : Experiment n) : ℝ := Real.sqrt ((∑ i, degree E i ^ 2) / n)

/-- Definition 7, p. 685: a symmetric pairing with no unit paired to itself. -/
structure Pairing (n : ℕ) where
  partner : Fin n ≃ Fin n
  involution : ∀ i, partner (partner i) = i
  no_fixed : ∀ i, partner i ≠ i

/-- Definition 7, p. 685: e_ij is an existence indicator, not a witness count. -/
def e {n : ℕ} (E : Experiment n) (ρ : Pairing n) (i j : Fin n) : ℝ :=
  if ¬ Dependent E i j ∧ ∃ ℓ, Interferes E ℓ i ∧ Interferes E (ρ.partner ℓ) j
  then 1 else 0

/-- Definition 7, p. 685: average pair-induced interference dependence. -/
def eAvg {n : ℕ} (E : Experiment n) (ρ : Pairing n) : ℝ :=
  (∑ i, ∑ j, e E ρ i j) / n

/-- Definition 8, p. 685: R_SUM = sum_i I_(rho(i),i). -/
def rSum {n : ℕ} (E : Experiment n) (ρ : Pairing n) : ℝ :=
  ∑ i, I E (ρ.partner i) i

/-- p. 683: Bernoulli randomization has product assignment probabilities,
with each probability strictly between zero and one. -/
def Bernoulli {n : ℕ} (E : Experiment n) : Prop :=
  (∀ i, 0 < marginal E i true ∧ marginal E i true < 1) ∧
  ∀ z, E.design.mass z = ∏ i, (if z i then marginal E i true else 1 - marginal E i true)

/-- p. 684: complete randomization is uniform over assignments with m treated units. -/
def Complete {n : ℕ} (E : Experiment n) (m : ℕ) : Prop :=
  0 < m ∧ m < n ∧ ∀ z, E.design.mass z =
    if (∑ i, if z i then (1 : ℕ) else 0) = m then 1 / (n.choose m : ℝ) else 0

/-- p. 685: paired randomization assigns one treated unit in each pair and
gives probability 2^(-n/2) to each supported vector. -/
def Paired {n : ℕ} (E : Experiment n) (ρ : Pairing n) : Prop :=
  Even n ∧ ∀ z, E.design.mass z =
    if ∀ i, z i ≠ z (ρ.partner i) then 1 / (2 : ℝ) ^ (n / 2) else 0

/-- Assumption 1, p. 682: the three regularity conditions for a fixed population.
Real q and s allow the paper's fractional moments; k is positive and finite. -/
def Regular {n : ℕ} (E : Experiment n) (k q s : ℝ) : Prop :=
  0 < k ∧ 2 ≤ q ∧ 1 ≤ s ∧
  (∀ i, k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1 - k⁻¹) ∧
  (∀ i, mean E.design (fun z => Real.rpow |E.outcome i z| q) ≤ Real.rpow k q) ∧
  (∀ i b, mean E.design (fun z => Real.rpow |potential E i b z| s) ≤ Real.rpow k s)

/-- p. 687: tilde Z_i masks treatments which cannot affect outcome i. -/
def masked {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) : Assignment n :=
  fun j => if Interferes E j i then z j else false

/-- p. 687: tilde Z_-i; the own coordinate is set to zero rather than deleted.
This is an injective recoding of the deleted vector and generates the same events. -/
def maskedOthers {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) : Assignment n :=
  Function.update (masked E i z) i false

/-- p. 687: alpha(X,Y) = sup of |Pr(A and B)-Pr(A)Pr(B)| over events
generated by X and Y. On a finite space these are preimages of subsets of
their codomains; no restriction to single-atom events is made. -/
def alpha {Ω A B : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → A) (Y : Ω → B) : ℝ :=
  sSup {r | ∃ (S : Set A) (T : Set B),
    r = |prob P (fun ω => X ω ∈ S ∧ Y ω ∈ T) -
      prob P (fun ω => X ω ∈ S) * prob P (fun ω => Y ω ∈ T)|}

/-- Definition 9, p. 687: the explicit convention 0^0=0 for mixing powers. -/
def mixPower (a θ : ℝ) : ℝ := if a = 0 then 0 else Real.rpow a θ

/-- Definition 9, p. 687: the external coefficient for a selected admissible
moment exponent q. An exponent of infinity is represented by θ=1, separately. -/
def alphaExt {n : ℕ} (E : Experiment n) (θ : ℝ) : ℝ :=
  (∑ i, ∑ j, (1 - d E i j) * mixPower
    (alpha E.design (masked E i) (masked E j)) θ) / n

/-- Definition 9, p. 687: internal mixing with exponent (s-1)/s, or θ=1 for
the bounded-outcome convention. -/
def alphaInt {n : ℕ} (E : Experiment n) (θ : ℝ) : ℝ :=
  ∑ i, mixPower (alpha E.design (fun z => z i) (maskedOthers E i)) θ

/-- Section 6.1, p. 689: the conventional Bernoulli variance estimator. -/
def vBER {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ :=
  (∑ i, ((if z i then E.outcome i z ^ 2 else 0) / marginal E i true ^ 2 +
    (if z i then 0 else E.outcome i z ^ 2) / marginal E i false ^ 2)) / (n : ℝ) ^ 2

/-- p. 690: tau_MSQ is the average of squared expected direct effects,
not the expectation of squared assignment-specific effects. -/
def msq {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, mean E.design (effect E i) ^ 2) / n

/-- p. 690: xi_ij(a) is the expected spillover on outcome i from treatment j,
holding i's treatment at a. Statements using xi require i≠j. -/
def xi {n : ℕ} (E : Experiment n) (i j : Fin n) (a : Bool) : ℝ :=
  mean E.design (fun z =>
    E.outcome i (Function.update (Function.update z i a) j true) -
    E.outcome i (Function.update (Function.update z i a) j false))

/-- p. 690: breve xi_ij=(1-p_i)xi_ij(1)+p_i xi_ij(0). -/
def xiBreve {n : ℕ} (E : Experiment n) (i j : Fin n) : ℝ :=
  (1 - marginal E i true) * xi E i j true + marginal E i true * xi E i j false

/-- p. 690: breve Y_i=(1-p_i)E[Y_i|Z_i=1]+p_i E[Y_i|Z_i=0]. -/
def yBreve {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ :=
  (1 - marginal E i true) * cmean E.design (fun z => z i = true) (E.outcome i) +
  marginal E i true * cmean E.design (fun z => z i = false) (E.outcome i)

/-- Proposition 7, p. 690: the direct-spillover contribution B_1. -/
def B1 {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, ∑ j, if j = i then 0 else
    xiBreve E i j * xiBreve E j i +
    2 * yBreve E j * (xi E i j true - xi E i j false)) / ((n : ℝ) * dAvg E)

/-- Proposition 7, p. 690: the indirect conditional-covariance contribution B_2. -/
def B2 {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, ∑ j, if j = i then 0 else
    ∑ a : Bool, ∑ b : Bool,
      (1 - 2 * bit a) * (1 - 2 * bit b) *
        ccov E.design (fun z => z i = a ∧ z j = b) (E.outcome i) (E.outcome j)) /
      ((n : ℝ) * dAvg E)

/-- p. 692: sigma_i^2, the variance of the unaveraged HT contribution. -/
def sigmaSq {n : ℕ} (E : Experiment n) (i : Fin n) : ℝ :=
  var E.design (fun z => (if z i then E.outcome i z else 0) / marginal E i true -
    (if z i then 0 else E.outcome i z) / marginal E i false)

/-- Proposition 8, p. 692: SD of the unit contribution variances. -/
def sdSigmaSq {n : ℕ} (E : Experiment n) : ℝ :=
  Real.sqrt ((∑ i, (sigmaSq E i - (∑ j, sigmaSq E j) / n) ^ 2) / n)

/-- p. 692: the quadratic form v^T D v of the symmetric dependence matrix. -/
def quadD {n : ℕ} (E : Experiment n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * d E i j * v j

/-- pp. 692–693: lambda_max, the largest eigenvalue of the symmetric matrix D.
Represented by the equivalent maximum Rayleigh quotient on the unit sphere.
For this nonnegative symmetric D it is also the spectral radius. -/
def lambdaMax {n : ℕ} (E : Experiment n) : ℝ :=
  sSup {r | ∃ v : Fin n → ℝ, (∑ i, v i ^ 2) = 1 ∧ r = quadD E v}

/-- p. 691: the AVG inflated variance estimator. -/
def vAVG {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ := dAvg E * vBER E z

/-- p. 692: the MAX inflated variance estimator. -/
def vMAX {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ := dMax E * vBER E z

/-- p. 693: the SR inflated variance estimator. -/
def vSR {n : ℕ} (E : Experiment n) (z : Assignment n) : ℝ := lambdaMax E * vBER E z

/-- Lemma A25, Supplement A pp. 24–25: a_n, the mean of n times vBER. -/
def aVariance {n : ℕ} (E : Experiment n) : ℝ :=
  (∑ i, (cmean E.design (fun z => z i = true) (fun z => E.outcome i z ^ 2) /
    marginal E i true + cmean E.design (fun z => z i = false)
      (fun z => E.outcome i z ^ 2) / marginal E i false)) / n

/-- Assumption 7, p. 694: "bounded unit-level effects" on the full cube. -/
def BoundedEffects {n : ℕ} (E : Experiment n) (K : ℝ) : Prop :=
  ∀ i z, |effect E i z| ≤ K

/-- pp. 694–695: total variation δ(P,Q). Half the sum of absolute mass
differences is the exact finite-space representation of the event supremum. -/
def totalVariation {Ω : Type*} [Fintype Ω] (P Q : Law Ω) : ℝ :=
  (∑ ω, |P.mass ω - Q.mass ω|) / 2

/-- Supplement A, pp. 39–41: L_r distance between binary assignments. -/
def lrDistance {n : ℕ} (r : ℝ) (z z' : Assignment n) : ℝ :=
  Real.rpow (∑ i, Real.rpow |bit (z i) - bit (z' i)| r) (1 / r)

/-- Lemma 2, pp. 695–696: C_(r/(r-1)), with the stated C_infinity convention
at r=1. -/
def conjugateC {n : ℕ} (E : Experiment n) (r : ℝ) : ℝ :=
  if r = 1 then Cinf E else Cp E (r / (r - 1))

/-- p. 696: J(P,Q), joint laws with marginals P and Q. -/
def Coupling {Ω : Type*} [Fintype Ω] (P Q : Law Ω) (J : Law (Ω × Ω)) : Prop :=
  (∀ x, ∑ y, J.mass (x,y) = P.mass x) ∧
  (∀ y, ∑ x, J.mass (x,y) = Q.mass y)

/-- p. 696: W_r is the infimum of the expected L_r assignment distance over
couplings. Its Wasserstein order is ONE; the subscript only specifies the ground
metric. It is not the usual rth-order Wasserstein distance. -/
def wasserstein {n : ℕ} (r : ℝ) (P Q : Law (Assignment n)) : ℝ :=
  sInf {v | ∃ J : Law (Assignment n × Assignment n), Coupling P Q J ∧
    v = mean J (fun zz => lrDistance r zz.1 zz.2)}

/-- Section 5, pp. 681–682: an arbitrary deterministic sequence of finite
populations and designs, with sample sizes tending to infinity. Allowing N(t)
also covers the even-size paired-randomization regime. -/
structure Study where
  N : ℕ → ℕ
  positive : ∀ t, 0 < N t
  grows : Tendsto N atTop atTop
  experiment : (t : ℕ) → Experiment (N t)

/-- The sample size, viewed as a real number. -/
def size (S : Study) (t : ℕ) : ℝ := S.N t

/-- Assumption 1, p. 682: common constants along the sequence. -/
def RegularSequence (S : Study) (k q s : ℝ) : Prop :=
  ∀ t, Regular (S.experiment t) k q s

/-- Assumption 2, p. 683: d_AVG=o(n). -/
def Restricted (S : Study) : Prop :=
  Tendsto (fun t => dAvg (S.experiment t) / size S t) atTop (nhds 0)

/-- Ordinary deterministic little-o, for the positive scales used in the paper.
This quotient formulation does not silently weaken an asymptotic conclusion. -/
def LittleO (f g : ℕ → ℝ) : Prop := Tendsto (fun t => f t / g t) atTop (nhds 0)

/-- The paper's ordinary O bound, meaning an eventual uniform bound in magnitude. -/
def BigO (f g : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ t in atTop, |f t| ≤ C * |g t|

/-- Convergence in probability on changing finite randomization spaces:
Pr(|X_n|>epsilon)→0 for every epsilon>0. -/
def InProbability (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun t => prob (S.experiment t).design (fun z => ε < |X t z|))
    atTop (nhds 0)

/-- O_p as used in the proof of Lemma A5, Supplement A p. 4: for each epsilon,
a common positive cutoff controls the tail eventually. -/
def Op (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ K > 0, ∀ᶠ t in atTop,
    prob (S.experiment t).design (fun z => K * a t ≤ |X t z|) ≤ ε

/-- Definition 10, p. 691: the printed iterated limit of the lower scaled
variance-error probability. Inner limits are required to exist. For these monotone
lower tails it is equivalent to convergence to zero at every fixed positive
tolerance; see `conservative_additive_lower_tails`. -/
def Conservative (S : Study) (Vhat : (t : ℕ) → Assignment (S.N t) → ℝ) : Prop :=
  ∃ L : ℝ → ℝ,
    (∀ ε > 0, Tendsto (fun t => prob (S.experiment t).design (fun z =>
      size S t / dAvg (S.experiment t) *
        (Vhat t z - var (S.experiment t).design (ht (S.experiment t))) ≤ -ε))
      atTop (nhds (L ε))) ∧ Tendsto L (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- A positive lower bound eventually, equivalent to liminf>0 for nonnegative
sequences; used for variance regularity and tau_MSQ=Omega(1). -/
def PositiveLiminf (a : ℕ → ℝ) : Prop :=
  ∃ c > 0, ∀ᶠ t in atTop, c ≤ a t

/-- CDF convergence at every continuity point, the paper's convergence in law. -/
def InDistribution (S : Study) (X : (t : ℕ) → Assignment (S.N t) → ℝ)
    (G : ℝ → ℝ) : Prop :=
  ∀ x, ContinuousAt G x → Tendsto
    (fun t => prob (S.experiment t).design (fun z => X t z ≤ x)) atTop (nhds (G x))

/-- The standard normal distribution function, with true variance one. -/
def normalCDF (x : ℝ) : ℝ :=
  (ProbabilityTheory.gaussianReal 0 1 (Set.Iic x)).toReal

/-- Section 6.3's natural plug-in Chebyshev interval (not a printed interval
formula): |T-theta|≤sqrt(Vhat/alpha). -/
def Covered (T θ Vhat α : ℝ) : Prop := |T - θ| ≤ Real.sqrt (Vhat / α)

/-- Supplement B p. 2: "bal(G_i)=sum_(j in G_i)(2Z_j-1)". -/
def balance {n : ℕ} (G : Finset (Fin n)) (z : Assignment n) : ℝ :=
  ∑ j ∈ G, (2 * bit (z j) - 1)

/-- Supplement B p. 2: multiplier 2 at positive balance, 1 at zero, 0 at negative. -/
def multiplier (b : ℝ) : ℝ := if 0 < b then 2 else if b = 0 then 1 else 0

/-- Supplement B pp. 2 and 6: complete-interference outcome schedule with
fixed baseline b_i=X_i+epsilon_i. -/
def fullOutcome {n : ℕ} (b : Fin n → ℝ) (i : Fin n) (z : Assignment n) : ℝ :=
  multiplier (balance (Finset.univ.erase i) z) * bit (z i) + b i

/-- Supplement B pp. 6–8: one-source outcome schedule, b affected units
including the source. The source is Lean unit 0. -/
def oneSourceOutcome {n : ℕ} (h : ℕ) (c : Fin n → ℝ)
    (i : Fin n) (z : Assignment n) : ℝ :=
  if 0 < i.val ∧ i.val < h then 2 * bit (z ⟨0, by have := i.isLt; omega⟩) * bit (z i) + c i
  else bit (z i) + c i

/-- A sum over the full binary assignment cube splits into the two values of
the first coordinate. Finite computational support for the counterexamples. -/
theorem sum_cube_succ (n : ℕ) (f : Assignment (n+1) → ℝ) :
    (∑ z, f z) = ∑ b : Bool, ∑ z : Assignment n, f (Fin.cons b z) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

/-- The zero-coordinate cube consists of its unique empty assignment. -/
theorem sum_cube_zero (f : Assignment 0 → ℝ) :
    (∑ z, f z) = f (fun i => Fin.elim0 i) := by
  simp only [Fintype.sum_unique]
  congr 1

/-- Coordinate two of a binary cons vector; explicit numeral reduction for
the finite certificates (Fin.cons_succ alone matches constructor indices). -/
theorem cons_at_two {n : ℕ} (b : Bool) (z : Assignment (n+2)) :
    (Fin.cons (α := fun _ : Fin (n+3) => Bool) b z) (2 : Fin (n+3)) = z 1 := by rfl

/-- Coordinate three of a binary cons vector, used for four-unit enumeration. -/
theorem cons_at_three {n : ℕ} (b : Bool) (z : Assignment (n+3)) :
    (Fin.cons (α := fun _ : Fin (n+4) => Bool) b z) (3 : Fin (n+4)) = z 2 := by rfl

/-- Independent fair assignments: each vector has mass 2^-n, p. 683. -/
def fairLaw (n : ℕ) : Law (Assignment n) where
  mass := fun _ => 1 / (2 : ℝ) ^ n
  nonneg := fun _ => by positivity
  total := by simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- The fair Bernoulli experiment with the specified full outcome schedule. -/
def fairExperiment (n : ℕ) (y : Fin n → Assignment n → ℝ) : Experiment n :=
  ⟨fairLaw n, y⟩

/-- T1/T7 finite calculation: under fair product assignments, any function
of the first coordinate has the mean of its two values. -/
theorem fair_first_coordinate (n : ℕ) (f : Bool → ℝ) :
    mean (fairLaw (n+1)) (fun z => f (z 0)) = (f true+f false)/2 := by
  simp only [mean, fairLaw, sum_cube_succ, Fintype.sum_bool, Fin.cons_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  field_simp

/-- T1 and T7, P009-E002/P009-E001: only paper unit 1 has outcome z_1. -/
def sparseExperiment (n : ℕ) : Experiment n :=
  fairExperiment n (fun i z => if i.val = 0 then bit (z i) else 0)

/-- The same explicit sparse experiment for every positive sample size. -/
def sparseStudy : Study where
  N := fun t => t+1
  positive := by intro t; omega
  grows := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop b] with t ht
    omega
  experiment := fun t => sparseExperiment (t+1)

/-- T1/T7 exact finite estimator identities for every positive sample size:
HT=2Z1/n and VhatBER=4Z1/n² for the sparse outcome schedule. -/
theorem sparse_estimators_finite (t : ℕ) (z : Assignment (t+1)) :
    ht (sparseExperiment (t+1)) z = 2*bit (z 0)/(t+1:ℕ) ∧
    vBER (sparseExperiment (t+1)) z = 4*bit (z 0)/(t+1:ℕ)^2 := by
  classical
  have hm (b : Bool) : marginal (sparseExperiment (t+1)) 0 b = 1/2 := by
    dsimp only [marginal, prob, sparseExperiment, fairExperiment]
    calc
      _ = mean (fairLaw (t+1))
          (fun z => (fun q : Bool => if q = b then (1:ℝ) else 0) (z 0)) := by
        congr 1
        funext z
        by_cases hb : z 0 = b <;> simp [hb]
      _ = ((if true = b then (1:ℝ) else 0)+(if false = b then 1 else 0))/2 :=
        fair_first_coordinate t (fun q => if q = b then (1:ℝ) else 0)
      _ = 1/2 := by cases b <;> norm_num
  have hy : ∀ i : Fin t, (sparseExperiment (t+1)).outcome i.succ z = 0 := by
    intro i
    simp [sparseExperiment, fairExperiment]
  simp only [ht, muHat, vBER, Fin.sum_univ_succ, hy, zero_div,
    sq, ite_self, Finset.sum_const_zero, add_zero, hm]
  cases hb : z 0 <;>
    norm_num [sparseExperiment, fairExperiment, bit, hb, Fin.sum_univ_succ] <;> ring

/-- T1/T7 finite mean and true variance of the sparse HT estimator, together
with the strictly larger expected conventional variance estimate. -/
theorem sparse_moments_finite (t : ℕ) :
    mean (sparseExperiment (t+1)).design (ht (sparseExperiment (t+1))) = 1/(t+1:ℕ) ∧
    var (sparseExperiment (t+1)).design (ht (sparseExperiment (t+1))) = 1/(t+1:ℕ)^2 ∧
    mean (sparseExperiment (t+1)).design (vBER (sparseExperiment (t+1))) = 2/(t+1:ℕ)^2 := by
  have htn : ((t+1:ℕ):ℝ) ≠ 0 := by positivity
  have hm : mean (sparseExperiment (t+1)).design (ht (sparseExperiment (t+1))) =
      1/(t+1:ℕ) := by
    change mean (fairLaw (t+1)) (fun z => ht (sparseExperiment (t+1)) z) = _
    simp_rw [(sparse_estimators_finite t _).1]
    rw [fair_first_coordinate t (fun b => 2*bit b/(t+1:ℕ))]
    simp only [bit, Bool.false_eq_true, ite_false, ite_true] <;> field_simp [htn] <;> ring
  refine ⟨hm, ?_, ?_⟩
  · unfold var cov
    rw [hm]
    change mean (fairLaw (t+1)) (fun z =>
      (ht (sparseExperiment (t+1)) z-1/(t+1:ℕ))*
      (ht (sparseExperiment (t+1)) z-1/(t+1:ℕ))) = _
    simp_rw [(sparse_estimators_finite t _).1]
    rw [fair_first_coordinate t (fun b =>
      (2*bit b/(t+1:ℕ)-1/(t+1:ℕ))*(2*bit b/(t+1:ℕ)-1/(t+1:ℕ)))]
    simp only [bit, Bool.false_eq_true, ite_false, ite_true] <;> field_simp [htn] <;> ring
  · change mean (fairLaw (t+1)) (fun z => vBER (sparseExperiment (t+1)) z) = _
    simp_rw [(sparse_estimators_finite t _).2]
    rw [fair_first_coordinate t (fun b => 4*bit b/(t+1:ℕ)^2)]
    simp only [bit, Bool.false_eq_true, ite_false, ite_true] <;> field_simp [htn] <;> ring


/-- T2 finite event inclusion: a lower bound c on the scaled true variance
turns relative underestimation into an additive negative-error event. -/
theorem relative_underestimate_inclusion (a V Vhat η c : ℝ)
    (ha : 0 < a) (hη : 0 < η) (hc : c ≤ a * V)
    (hunder : Vhat < (1-η) * V) : a * (Vhat - V) ≤ -η*c := by
  have h := mul_lt_mul_of_pos_left hunder ha
  have h' := mul_le_mul_of_nonneg_left hc (le_of_lt hη)
  nlinarith

/-! General probability and limit arguments for corrected plug-in coverage. -/
section GeneralCoverageCompletion
open MeasureTheory Topology

/-- Chebyshev for a square-integrable unbiased real statistic, in real-valued probability. -/
theorem measure_chebyshev_unbiased {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℝ) (θ V ε : ℝ)
    (hT : Measurable T) (hT2 : MeasureTheory.Integrable (fun ω => T ω^2) P)
    (hMean : (∫ ω, T ω ∂P) = θ) (hVar : V = ∫ ω, (T ω-θ)^2 ∂P)
    (hε : 0 < ε) : P.real {ω | ε ≤ |T ω-θ|} ≤ V/ε^2 := by
  have hLp := (memLp_two_iff_integrable_sq hT.aestronglyMeasurable).mpr hT2
  have h := ProbabilityTheory.meas_ge_le_variance_div_sq hLp hε
  rw [ProbabilityTheory.variance_eq_integral hT.aemeasurable, hMean, ← hVar] at h
  have hV0 : 0 ≤ V := by rw [hVar]; exact integral_nonneg (fun ω => sq_nonneg _)
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hV0 (sq_nonneg ε)) (by simpa [hMean] using h)

/-- Finite-sample plug-in Chebyshev bound on an arbitrary probability space. -/
theorem measure_plugin_coverage_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T Vhat : Ω → ℝ) (θ V α η : ℝ)
    (hT : Measurable T) (hT2 : MeasureTheory.Integrable (fun ω => T ω^2) P)
    (hMean : (∫ ω, T ω ∂P) = θ) (hVar : V = ∫ ω, (T ω-θ)^2 ∂P)
    (hV : 0 < V) (hα : 0 < α) (hη : 0 < η ∧ η < 1) :
    P.real {ω | ¬ Covered (T ω) θ (Vhat ω) α} ≤
      P.real {ω | Vhat ω < (1-η)*V} + α/(1-η) := by
  let ε := Real.sqrt ((1-η)*V/α)
  have hden : 0 < 1-η := sub_pos.mpr hη.2
  have hrad : 0 < (1-η)*V/α := div_pos (mul_pos hden hV) hα
  have hε : 0 < ε := Real.sqrt_pos.2 hrad
  have hinc : {ω | ¬ Covered (T ω) θ (Vhat ω) α} ⊆
      {ω | Vhat ω < (1-η)*V} ∪ {ω | ε ≤ |T ω-θ|} := by
    intro ω hn
    by_cases hu : Vhat ω < (1-η)*V
    · exact Or.inl hu
    · right
      have hv : (1-η)*V/α ≤ Vhat ω/α :=
        div_le_div_of_nonneg_right (le_of_not_gt hu) hα.le
      exact (Real.sqrt_le_sqrt hv).trans (le_of_lt (lt_of_not_ge hn))
  calc
    _ ≤ P.real ({ω | Vhat ω < (1-η)*V} ∪ {ω | ε ≤ |T ω-θ|}) := measureReal_mono hinc
    _ ≤ P.real {ω | Vhat ω < (1-η)*V} + P.real {ω | ε ≤ |T ω-θ|} := measureReal_union_le _ _
    _ ≤ P.real {ω | Vhat ω < (1-η)*V} + V/ε^2 :=
      add_le_add_right (measure_chebyshev_unbiased P T θ V ε hT hT2 hMean hVar hε) _
    _ = _ := by
      dsimp [ε]
      rw [Real.sq_sqrt hrad.le]
      field_simp [hV.ne', hα.ne', hden.ne']

/-- The probability lower bound supplied by plug-in Chebyshev gives asymptotic
coverage after relative underestimation becomes negligible. -/
theorem liminf_coverage_of_relative_control (coverage : ℕ → ℝ)
    (under : ℝ → ℕ → ℝ) (α : ℝ) (hα : 0 < α)
    (hprob : ∀ t, 0 ≤ coverage t ∧ coverage t ≤ 1)
    (hbound : ∀ η, 0 < η → η < 1 → ∀ᶠ t in atTop,
      1-coverage t ≤ under η t+α/(1-η))
    (hunder : ∀ η, 0 < η → η < 1 → Tendsto (under η) atTop (𝓝 0)) :
    1-α ≤ Filter.liminf coverage atTop := by
  have hbelow : atTop.IsBoundedUnder (· ≥ ·) coverage :=
    isBoundedUnder_of ⟨0, fun t => (hprob t).1⟩
  have habove : atTop.IsBoundedUnder (· ≤ ·) coverage :=
    isBoundedUnder_of ⟨1, fun t => (hprob t).2⟩
  apply (le_liminf_iff habove.isCoboundedUnder_flip hbelow).mpr
  intro y hy
  have hlim : Tendsto (fun η : ℝ => 1-α/(1-η)) (𝓝 0) (𝓝 (1-α)) := by
    have h1 : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝 0) (𝓝 1) := tendsto_const_nhds
    have ha : Tendsto (fun _ : ℝ => α) (𝓝 0) (𝓝 α) := tendsto_const_nhds
    simpa only [sub_zero, div_one, Pi.div_apply, Pi.sub_apply, id_eq] using h1.sub (ha.div (h1.sub tendsto_id) (by norm_num))
  have hgood : ∀ᶠ η : ℝ in 𝓝[>] (0:ℝ), 0 < η ∧ η < 1 ∧ y < 1-α/(1-η) := by
    filter_upwards [self_mem_nhdsWithin,
      (hlim.eventually_const_lt hy).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with η hη hgap hη1
    exact ⟨hη, hη1, hgap⟩
  obtain ⟨η, hη0, hη1, hgap⟩ := hgood.exists
  have hlow : Tendsto (fun t => 1-(under η t+α/(1-η))) atTop (𝓝 (1-α/(1-η))) := by
    simpa only [zero_add] using tendsto_const_nhds.sub ((hunder η hη0 hη1).add_const (α/(1-η)))
  filter_upwards [hlow.eventually_const_lt hgap, hbound η hη0 hη1] with t ht hboundt
  linarith


/-- Positive scaled true variance turns additive lower-tail control into
relative lower-tail control, on changing probability spaces. -/
theorem relative_control_of_additive_control
    (Ω : ℕ → Type) [∀ t, MeasurableSpace (Ω t)]
    (P : (t : ℕ) → Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (Vhat : (t : ℕ) → Ω t → ℝ) (V a : ℕ → ℝ)
    (ha : ∀ t, 0 < a t)
    (hadd : ∀ ε > 0, Tendsto (fun t => (P t).real
      {ω | a t*(Vhat t ω-V t) ≤ -ε}) atTop (𝓝 0))
    (hscale : PositiveLiminf (fun t => a t*V t)) :
    ∀ η, 0 < η → η < 1 → Tendsto (fun t => (P t).real
      {ω | Vhat t ω < (1-η)*V t}) atTop (𝓝 0) := by
  obtain ⟨c, hc, hscale⟩ := hscale
  intro η hη hη1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hadd (η*c) (mul_pos hη hc)) (Eventually.of_forall (fun t => measureReal_nonneg))
  filter_upwards [hscale] with t ht
  apply measureReal_mono ?_ (measure_ne_top (P t) _)
  intro ω hω
  simpa only [neg_mul, Set.mem_ofPred_eq] using relative_underestimate_inclusion (a t) (V t) (Vhat t ω) η c (ha t) hη ht hω


/-- The iterated monotone-tail argument depends only on real probabilities,
so it also applies directly to the paper's finite law model. -/
theorem iterated_monotone_tail_zero (tail : ℝ → ℕ → ℝ) (L : ℝ → ℝ)
    (hnonneg : ∀ ε t, 0 ≤ tail ε t)
    (hmono : ∀ ε δ, 0 < δ → δ < ε → ∀ t, tail ε t ≤ tail δ t)
    (hinner : ∀ ε > 0, Tendsto (tail ε) atTop (𝓝 (L ε)))
    (houter : Tendsto L (𝓝[>] (0:ℝ)) (𝓝 0)) :
    ∀ ε > 0, Tendsto (tail ε) atTop (𝓝 0) := by
  intro ε hε
  have hnonnegative : 0 ≤ L ε := ge_of_tendsto (hinner ε hε)
    (Eventually.of_forall (hnonneg ε))
  have hLle : ∀ᶠ δ : ℝ in 𝓝[>] (0:ℝ), L ε ≤ L δ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with δ hδ hδε
    exact le_of_tendsto_of_tendsto (hinner ε hε) (hinner δ hδ)
      (Eventually.of_forall (hmono ε δ hδ hδε))
  have hnonpositive : L ε ≤ 0 := ge_of_tendsto houter hLle
  simpa only [le_antisymm hnonpositive hnonnegative] using hinner ε hε


end GeneralCoverageCompletion

section CorrectedCoverageProof
open MeasureTheory Topology

/-- T2: corrected plug-in coverage theorem on arbitrary
probability spaces, with unbiased square-integrable T and nonnegative Vhat.
It includes the finite union/Chebyshev bound and the relative-control limit. -/
theorem corrected_coverage
    (Ω : ℕ → Type) [∀ t, MeasurableSpace (Ω t)]
    (P : (t : ℕ) → MeasureTheory.Measure (Ω t))
    [∀ t, MeasureTheory.IsProbabilityMeasure (P t)]
    (T Vhat : (t : ℕ) → Ω t → ℝ) (θ V δ : ℕ → ℝ)
    (hT : ∀ t, MeasureTheory.Integrable (T t) (P t))
    (hT2 : ∀ t, MeasureTheory.Integrable (fun ω => T t ω ^ 2) (P t))
    (hMeas : ∀ t, Measurable (T t) ∧ Measurable (Vhat t))
    (hMean : ∀ t, (∫ ω, T t ω ∂P t) = θ t)
    (hVar : ∀ t, V t = ∫ ω, (T t ω - θ t) ^ 2 ∂P t)
    (hV : ∀ t, 0 < V t) (hVhat : ∀ t ω, 0 ≤ Vhat t ω)
    (hδ : ∀ t, 0 < δ t) (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (∀ t η, 0 < η → η < 1 →
      ((P t) {ω | ¬ Covered (T t ω) (θ t) (Vhat t ω) α}).toReal ≤
      ((P t) {ω | Vhat t ω < (1-η) * V t}).toReal + α/(1-η)) ∧
    ((∀ η, 0 < η → η < 1 → Tendsto
      (fun t => ((P t) {ω | Vhat t ω < (1-η) * V t}).toReal) atTop (nhds 0)) →
      1-α ≤ Filter.liminf (fun t =>
        ((P t) {ω | Covered (T t ω) (θ t) (Vhat t ω) α}).toReal) atTop) ∧
    ((∀ ε > 0, Tendsto (fun t => ((P t) {ω |
      ((t+1 : ℕ) : ℝ) / δ t * (Vhat t ω - V t) ≤ -ε}).toReal) atTop (nhds 0)) →
      PositiveLiminf (fun t => ((t+1 : ℕ) : ℝ) / δ t * V t) →
      ∀ η, 0 < η → η < 1 → Tendsto
        (fun t => ((P t) {ω | Vhat t ω < (1-η) * V t}).toReal) atTop (nhds 0)) := by
  have hbound (t : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
      (P t).real {ω | ¬ Covered (T t ω) (θ t) (Vhat t ω) α} ≤
        (P t).real {ω | Vhat t ω < (1-η)*V t}+α/(1-η) :=
    measure_plugin_coverage_bound (P t) (T t) (Vhat t) (θ t) (V t) α η
      (hMeas t).1 (hT2 t) (hMean t) (hVar t) (hV t) hα.1 ⟨hη, hη1⟩
  refine ⟨hbound, ?_, ?_⟩
  · intro hrelative
    apply liminf_coverage_of_relative_control
      (fun t => (P t).real {ω | Covered (T t ω) (θ t) (Vhat t ω) α})
      (fun η t => (P t).real {ω | Vhat t ω < (1-η)*V t}) α hα.1
      (fun t => ⟨measureReal_nonneg, measureReal_le_one⟩) _ hrelative
    intro η hη hη1
    apply Eventually.of_forall
    intro t
    have hmeas : MeasurableSet {ω | Covered (T t ω) (θ t) (Vhat t ω) α} := by
      unfold Covered
      exact measurableSet_le (((hMeas t).1.sub_const _).abs)
        (((hMeas t).2.div_const α).sqrt)
    have hcompl := measureReal_add_measureReal_compl (μ := P t) hmeas
    have hsum : (P t).real {ω | Covered (T t ω) (θ t) (Vhat t ω) α} +
        (P t).real {ω | ¬ Covered (T t ω) (θ t) (Vhat t ω) α} = 1 := by
      simpa only [probReal_univ, Set.compl_setOf] using hcompl
    linarith [hbound t η hη hη1]
  · intro hadd hscale
    exact relative_control_of_additive_control Ω P Vhat V
      (fun t => ((t+1:ℕ):ℝ)/δ t)
      (fun t => div_pos (by positivity) (hδ t)) hadd hscale

end CorrectedCoverageProof

/-- T2 finite Chebyshev inequality: an unbiased variable on any finite design
has Pr(|T-theta|≥epsilon)≤Var(T)/epsilon². -/
theorem finite_chebyshev {Ω : Type*} [Fintype Ω] (P : Law Ω) (T : Ω → ℝ)
    (θ ε : ℝ) (hMean : mean P T = θ) (hε : 0 < ε) :
    prob P (fun ω => ε ≤ |T ω-θ|) ≤ var P T/ε^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  unfold var cov
  rw [hMean]
  simp only [prob, mean, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : ε ≤ |T ω-θ|
  · simp only [hω, if_true, mul_one]
    have hs : ε^2 ≤ (T ω-θ)^2 := by
      have hsq := mul_self_le_mul_self (le_of_lt hε) hω
      simpa only [← pow_two, sq_abs] using hsq
    simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hs (P.nonneg ω)
  · simp only [hω, if_false, mul_zero, zero_mul]
    exact mul_nonneg (P.nonneg ω) (mul_self_nonneg _)

/-- T2's corrected finite plug-in interval bound, specialized to the finite
design model: noncoverage is at most the relative-underestimation probability
plus alpha/(1-eta). Positivity and unbiasedness are explicit. -/
theorem finite_plugin_coverage_bound {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (T Vhat : Ω → ℝ) (θ α η : ℝ) (hMean : mean P T = θ)
    (hVar : 0 < var P T) (hVhat : ∀ ω, 0 ≤ Vhat ω)
    (hα : 0 < α ∧ α < 1) (hη : 0 < η ∧ η < 1) :
    prob P (fun ω => ¬ Covered (T ω) θ (Vhat ω) α) ≤
      prob P (fun ω => Vhat ω < (1-η)*var P T)+α/(1-η) := by
  let ε := Real.sqrt ((1-η)*var P T/α)
  have hden : 0 < 1-η := sub_pos.mpr hη.2
  have hrad : 0 < (1-η)*var P T/α := div_pos (mul_pos hden hVar) hα.1
  have hε : 0 < ε := Real.sqrt_pos.2 hrad
  have hinc : ∀ ω, ¬ Covered (T ω) θ (Vhat ω) α →
      Vhat ω < (1-η)*var P T ∨ ε ≤ |T ω-θ| := by
    intro ω hn
    by_cases hu : Vhat ω < (1-η)*var P T
    · exact Or.inl hu
    · right
      have hv : (1-η)*var P T/α ≤ Vhat ω/α :=
        div_le_div_of_nonneg_right (le_of_not_gt hu) (le_of_lt hα.1)
      have hs := Real.sqrt_le_sqrt hv
      exact le_trans hs (le_of_lt (lt_of_not_ge hn))
  calc
    _ ≤ prob P (fun ω => Vhat ω < (1-η)*var P T)+
        prob P (fun ω => ε ≤ |T ω-θ|) := probability_union_bound P _ _ _ hinc
    _ ≤ prob P (fun ω => Vhat ω < (1-η)*var P T)+var P T/ε^2 :=
      add_le_add_right (finite_chebyshev P T θ ε hMean hε) _
    _ = _ := by
      dsimp [ε]
      rw [Real.sq_sqrt (le_of_lt hrad)]
      field_simp [ne_of_gt hVar, ne_of_gt hα.1, ne_of_gt hden]

section FiniteCoverageCompletion
open MeasureTheory Topology

/-- Monotonicity of finite-design probabilities. -/
theorem finite_probability_mono {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : prob P A ≤ prob P B := by
  classical
  unfold prob mean
  apply Finset.sum_le_sum
  intro ω hω
  by_cases ha : A ω
  · simp [ha, hAB ω ha]
  · by_cases hb : B ω <;> simp [ha, hb, P.nonneg]

/-- Every nonempty population includes its diagonal interference edges;
therefore average dependence degree is at least one. -/
theorem average_degree_at_least_one {n : ℕ} (E : Experiment n) (hn : 0 < n) :
    1 ≤ dAvg E := by
  have hdnonneg (i j : Fin n) : 0 ≤ d E i j := by unfold d; split_ifs <;> norm_num
  have hdiag (i : Fin n) : d E i i = 1 := by
    apply if_pos
    exact ⟨i, Or.inl rfl, Or.inl rfl⟩
  have hdegree (i : Fin n) : 1 ≤ degree E i := by
    rw [← hdiag i]
    exact Finset.single_le_sum (fun j hj => hdnonneg i j) (Finset.mem_univ i)
  have hsum := Finset.sum_le_sum (fun (i : Fin n) (hi : i ∈ Finset.univ) => hdegree i)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [dAvg, le_div_iff₀ hnR, one_mul]
  simpa using hsum

/-- Definition 10's literal iterated condition supplies every fixed additive
lower-tail limit on the finite randomization sequence. -/
theorem conservative_additive_lower_tails (S : Study)
    (Vhat : (t : ℕ) → Assignment (S.N t) → ℝ) (hCons : Conservative S Vhat) :
    ∀ ε > 0, Tendsto (fun t => prob (S.experiment t).design (fun z =>
      size S t/dAvg (S.experiment t)*
        (Vhat t z-var (S.experiment t).design (ht (S.experiment t))) ≤ -ε))
      atTop (𝓝 0) := by
  obtain ⟨L, hinner, houter⟩ := hCons
  apply iterated_monotone_tail_zero _ L _ _ hinner houter
  · intro ε t
    exact probability_nonnegative _ _
  · intro ε δ hδ hδε t
    apply finite_probability_mono
    intro z hz
    linarith

/-- Positive true variance on the interference scale upgrades Definition 10
to the relative control needed by the corrected coverage theorem. -/
theorem conservative_relative_control (S : Study)
    (Vhat : (t : ℕ) → Assignment (S.N t) → ℝ) (hCons : Conservative S Vhat)
    (hScale : PositiveLiminf (fun t => size S t/dAvg (S.experiment t)*
      var (S.experiment t).design (ht (S.experiment t)))) :
    (∀ η, 0 < η → η < 1 → Tendsto (fun t => prob (S.experiment t).design
      (fun z => Vhat t z < (1-η)*var (S.experiment t).design (ht (S.experiment t))))
      atTop (𝓝 0)) ∧
    (∀ᶠ t in atTop, 0 < var (S.experiment t).design (ht (S.experiment t))) := by
  have ha (t : ℕ) : 0 < size S t/dAvg (S.experiment t) := by
    apply div_pos
    · dsimp [size]
      exact_mod_cast S.positive t
    · exact lt_of_lt_of_le zero_lt_one (average_degree_at_least_one _ (S.positive t))
  obtain ⟨c, hc, hscale⟩ := hScale
  refine ⟨?_, ?_⟩
  · intro η hη hη1
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (conservative_additive_lower_tails S Vhat hCons (η*c) (mul_pos hη hc))
      (Eventually.of_forall (fun t => probability_nonnegative _ _))
    filter_upwards [hscale] with t hscalet
    apply finite_probability_mono
    intro z hz
    simpa only [neg_mul] using relative_underestimate_inclusion
      (size S t/dAvg (S.experiment t))
      (var (S.experiment t).design (ht (S.experiment t))) (Vhat t z) η c (ha t) hη hscalet hz
  · filter_upwards [hscale] with t hscalet
    have hap := ha t
    nlinarith

/-- Coverage under any sequence of finite designs with unbiased statistics.
Only eventual positivity of the true variances is necessary. -/
theorem finite_asymptotic_plugin_coverage
    (S : Study) (T Vhat : (t : ℕ) → Assignment (S.N t) → ℝ) (θ : ℕ → ℝ)
    (hMean : ∀ t, mean (S.experiment t).design (T t) = θ t)
    (hvar : ∀ᶠ t in atTop, 0 < var (S.experiment t).design (T t))
    (hVhat : ∀ t z, 0 ≤ Vhat t z) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (hrelative : ∀ η, 0 < η → η < 1 → Tendsto (fun t => prob (S.experiment t).design
      (fun z => Vhat t z < (1-η)*var (S.experiment t).design (T t))) atTop (𝓝 0)) :
    1-α ≤ Filter.liminf (fun t => prob (S.experiment t).design
      (fun z => Covered (T t z) (θ t) (Vhat t z) α)) atTop := by
  apply liminf_coverage_of_relative_control _ _ α hα.1 _ _ hrelative
  · intro t
    refine ⟨probability_nonnegative _ _, ?_⟩
    have hn := probability_nonnegative (S.experiment t).design
      (fun z => ¬Covered (T t z) (θ t) (Vhat t z) α)
    rw [probability_complement] at hn
    linarith
  · intro η hη hη1
    filter_upwards [hvar] with t ht
    have hb := finite_plugin_coverage_bound (S.experiment t).design
      (T t) (Vhat t) (θ t) α η (hMean t) ht (hVhat t) hα ⟨hη, hη1⟩
    simpa only [probability_complement] using hb


end FiniteCoverageCompletion

/-- Unequal independent assignment probabilities (1/4,3/4), P009-E009. -/
def unequalLaw : Law (Assignment 2) where
  mass := fun z => (if z 0 then 1/4 else 3/4) * (if z 1 then 3/4 else 1/4)
  nonneg := by intro z; split_ifs <;> norm_num
  total := by norm_num [sum_cube_succ, sum_cube_zero, Fintype.sum_bool]

/-- P009-E009's anti-correlated two-unit design, supported at 10 and 01. -/
def anticorrelatedLaw : Law (Assignment 2) where
  mass := fun z => if z 0 ∧ ¬ z 1 then 1/4 else if ¬ z 0 ∧ z 1 then 3/4 else 0
  nonneg := by intro z; split_ifs <;> norm_num
  total := by norm_num [sum_cube_succ, sum_cube_zero, Fintype.sum_bool]

/-- T3(i): y_1=z_2, y_2=-z_1, the full outcome schedule in P009-E009. -/
def signedExperiment : Experiment 2 :=
  ⟨unequalLaw, fun i z => if i = 0 then bit (z 1) else -bit (z 0)⟩

/-- T3(ii): every potential outcome is one under the anti-correlated design. -/
def countExperiment : Experiment 2 := ⟨anticorrelatedLaw, fun _ _ => 1⟩

/-- T3(iii): y_1=1 and y_2=1-z_1 under the unequal Bernoulli design. -/
def squareExperiment : Experiment 2 :=
  ⟨unequalLaw, fun i z => if i = 0 then 1 else 1-bit (z 0)⟩

/-- The unweighted variable 1[Z_i=b]Y_i^a in Lemmas A3/A9/A22/A25. -/
def armVariable {n : ℕ} (E : Experiment n) (b : Bool) (a : ℕ) (i : Fin n)
    (z : Assignment n) : ℝ := if z i = b then E.outcome i z ^ a else 0

/-- T3, Supplement A pp. 8,22,23,25: three explicit two-unit experiments
satisfy Assumption 1 and strictly violate all four signed-covariance bounds.
The conclusions of the four lemmas are not asserted false. -/
theorem signed_weight_counterexamples :
    Regular signedExperiment 4 4 1 ∧ Bernoulli signedExperiment ∧
    Regular countExperiment 4 4 1 ∧
    Regular squareExperiment 4 4 1 ∧ Bernoulli squareExperiment ∧
    var signedExperiment.design (muHat signedExperiment true) = 13/48 ∧
    (∑ i, ∑ j, cov signedExperiment.design
      (armVariable signedExperiment true 1 i) (armVariable signedExperiment true 1 j)) = 0 ∧
    var countExperiment.design (fun z => nHat countExperiment true z / 2) = 1/3 ∧
    (∑ i, ∑ j, cov countExperiment.design (fun z => bit (z i)) (fun z => bit (z j))) = 0 ∧
    var squareExperiment.design (fun z => ∑ i,
      armVariable squareExperiment true 2 i z / marginal squareExperiment i true ^ 2) = 367/9 ∧
    (4:ℝ)^4 * (∑ i, ∑ j, cov squareExperiment.design
      (armVariable squareExperiment true 2 i) (armVariable squareExperiment true 2 j)) = 39 ∧
    (0:ℝ) < 13/48 ∧ (0:ℝ) < 1/3 ∧ (39:ℝ) < 367/9 := by
  norm_num [Regular, Bernoulli, signedExperiment, countExperiment, squareExperiment,
    unequalLaw, anticorrelatedLaw, marginal, prob, mean, potential, bit,
    armVariable, var, cov, muHat, nHat, Real.rpow_natCast, Real.rpow_one,
    Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.prod_univ_succ, Bool.forall_bool,
    sum_cube_succ, sum_cube_zero, Fintype.sum_bool, Function.update]

/-- T4's corrected finite bound: the covariance expansion and the upper bound
with ABSOLUTE covariances for all positive weights w_i≤K. -/
theorem weighted_variance_absolute {Ω U : Type*} [Fintype Ω] [Fintype U]
    (P : Law Ω) (X : U → Ω → ℝ) (w : U → ℝ) (K : ℝ)
    (hw : ∀ i, 0 < w i ∧ w i ≤ K) :
    var P (fun ω => ∑ i, w i * X i ω) =
      ∑ i, ∑ j, w i * w j * cov P (X i) (X j) ∧
    var P (fun ω => ∑ i, w i * X i ω) ≤
      K^2 * (∑ i, ∑ j, |cov P (X i) (X j)|) := by
  have hm : mean P (fun ω => ∑ i, w i * X i ω) = ∑ i, w i * mean P (X i) := by
    simp_rw [mean_sum, mean_const_mul]
  have hc (ω) : (∑ i, w i * X i ω) - mean P (fun ω => ∑ i, w i * X i ω) =
      ∑ i, w i * (X i ω - mean P (X i)) := by
    rw [hm]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hex : var P (fun ω => ∑ i, w i * X i ω) =
      ∑ i, ∑ j, w i * w j * cov P (X i) (X j) := by
    calc
      _ = mean P (fun ω => (∑ i, w i * (X i ω - mean P (X i))) *
          (∑ j, w j * (X j ω - mean P (X j)))) := by
        simp only [var, cov, hc]
      _ = mean P (fun ω => ∑ i, ∑ j, w i * w j *
          ((X i ω - mean P (X i)) * (X j ω - mean P (X j)))) := by
        congr 1
        funext ω
        rw [Fintype.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by simp_rw [mean_sum, mean_const_mul]; rfl
  refine ⟨hex, ?_⟩
  rw [hex]
  have hb : ∀ i j, w i * w j * cov P (X i) (X j) ≤ K^2*|cov P (X i) (X j)| := by
    intro i j
    have hprod : w i * w j ≤ K^2 := by
      calc
        _ ≤ K * K := mul_le_mul (hw i).2 (hw j).2 (le_of_lt (hw j).1)
          (le_trans (le_of_lt (hw i).1) (hw i).2)
        _ = K^2 := by ring
    calc
      _ ≤ w i * w j * |cov P (X i) (X j)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (le_of_lt (hw i).1)
          (le_of_lt (hw j).1))
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
  simpa only [Finset.mul_sum] using
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb i j)))


/-- P009-E014: h_n=max(1,floor(n/2)-1), with natural truncated subtraction. -/
def limsupCluster (n : ℕ) : ℕ := max 1 (n/2-1)

/-- P009-E014: the interference density generated by the explicit cluster. -/
def limsupDensity (n : ℕ) : ℝ :=
  ((limsupCluster n : ℝ)^2 + n - limsupCluster n) / (n:ℝ)^2

/-- A finite real limsup, stated through its upper-eventual and lower-frequent
characterization; avoids Lean's arbitrary conditional limsup on unbounded input. -/
def HasLimsup (a : ℕ → ℝ) (L : ℝ) : Prop :=
  (∀ ε > 0, ∀ᶠ t in atTop, a t < L+ε) ∧
  (∀ ε > 0, ∃ᶠ t in atTop, L-ε < a t)

theorem limsup_density_even (m : ℕ) (hm : 3 ≤ m) :
    1/4-limsupDensity (2*m) = ((m:ℝ)-2)/(4*(m:ℝ)^2) := by
  have hm1 : 1 ≤ m := by omega
  have hmax : max 1 (m-1) = m-1 := max_eq_right (by omega)
  have hdiv : (2*m)/2 = m := by omega
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  simp only [limsupDensity, limsupCluster, hdiv, hmax, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_sub hm1, Nat.cast_one]
  field_simp <;> ring

 theorem limsup_density_odd (m : ℕ) (hm : 2 ≤ m) :
    1/4-limsupDensity (2*m+1) = (8*(m:ℝ)-11)/(4*(2*(m:ℝ)+1)^2) := by
  have hm1 : 1 ≤ m := by omega
  have hmax : max 1 (m-1) = m-1 := max_eq_right (by omega)
  have hdiv : (2*m+1)/2 = m := by omega
  have hd : 2*(m:ℝ)+1 ≠ 0 := by positivity
  simp only [limsupDensity, limsupCluster, hdiv, hmax, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_sub hm1, Nat.cast_one]
  field_simp <;> ring

 theorem limsup_density_below (n : ℕ) (hn : 4 < n) : limsupDensity n < 1/4 := by
  have hm : 2 ≤ n/2 := by omega
  by_cases he : n % 2 = 0
  · have hEq : n = 2*(n/2) := by omega
    have hme : 3 ≤ n/2 := by omega
    have hh := limsup_density_even (n/2) hme
    rw [← hEq] at hh
    have hp : (0:ℝ) < ((n/2:ℕ):ℝ)-2 := by
      have hmr : (2:ℝ) < ((n/2:ℕ):ℝ) := by exact_mod_cast (by omega : 2 < n/2)
      linarith
    have hd : (0:ℝ) < 4*(((n/2:ℕ):ℝ))^2 := by positivity
    linarith [div_pos hp hd]
  · have hEq : n = 2*(n/2)+1 := by omega
    have hh := limsup_density_odd (n/2) hm
    rw [← hEq] at hh
    have hmr : (2:ℝ) ≤ ((n/2:ℕ):ℝ) := by exact_mod_cast hm
    have hp : (0:ℝ) < 8*((n/2:ℕ):ℝ)-11 := by linarith
    have hd : (0:ℝ) < 4*(2*((n/2:ℕ):ℝ)+1)^2 := by positivity
    linarith [div_pos hp hd]

 theorem limsup_density_limit :
    Tendsto (fun t => limsupDensity (t+1)) atTop (nhds (1/4)) := by
  have hN : Tendsto (fun t : ℕ => ((t+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun t : ℕ => 1/((t+1:ℕ):ℝ)) atTop (nhds 0) := by
    simpa [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hN
  have hr : Tendsto (fun t : ℕ => (limsupCluster (t+1):ℝ)/((t+1:ℕ):ℝ)) atTop (nhds (1/2)) := by
    have hl : Tendsto (fun t : ℕ => (1/2:ℝ)-2*(1/((t+1:ℕ):ℝ))) atTop (nhds (1/2)) := by
      simpa using tendsto_const_nhds.sub (hi.const_mul 2)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 3] with t ht
      have h0 : (0:ℝ) < ((t+1:ℕ):ℝ) := by positivity
      have hb : t+1 ≤ 2*limsupCluster (t+1)+4 := by dsimp [limsupCluster]; omega
      have hbr : ((t+1:ℕ):ℝ) ≤ 2*(limsupCluster (t+1):ℝ)+4 := by exact_mod_cast hb
      apply (le_div_iff₀ h0).mpr
      field_simp
      nlinarith only [hbr]
    · filter_upwards [eventually_ge_atTop 3] with t ht
      have h0 : (0:ℝ) < ((t+1:ℕ):ℝ) := by positivity
      have hb : 2*limsupCluster (t+1) ≤ t+1 := by dsimp [limsupCluster]; omega
      have hbr : 2*(limsupCluster (t+1):ℝ) ≤ ((t+1:ℕ):ℝ) := by exact_mod_cast hb
      apply (div_le_iff₀ h0).mpr
      linarith
  have hh := (hr.pow 2).add (((tendsto_const_nhds (x := (1:ℝ))).sub hr).mul hi)
  apply (show Tendsto (fun t : ℕ => ((limsupCluster (t+1):ℝ)/((t+1:ℕ):ℝ))^2+
    (1-(limsupCluster (t+1):ℝ)/((t+1:ℕ):ℝ))*(1/((t+1:ℕ):ℝ))) atTop (nhds (1/4))
    from by convert hh using 1 <;> norm_num).congr'
  filter_upwards [] with t
  have h0 : ((t+1:ℕ):ℝ) ≠ 0 := by positivity
  dsimp [limsupDensity]
  field_simp <;> ring


/-- T5, Supplement A p. 6: P009-E014's explicit density tends to 1/4, but
meets or exceeds 1/4 only at n=1,2,3,4. Positive limsup need not be attained
infinitely often. The exact even and odd deficiencies are also included. -/
theorem limsup_threshold_counterexample :
    Tendsto (fun t => limsupDensity (t+1)) atTop (nhds (1/4)) ∧
    (∀ n, 0 < n → (1/4 ≤ limsupDensity n ↔ n ≤ 4)) ∧
    (∀ m, 3 ≤ m → 1/4-limsupDensity (2*m) = ((m:ℝ)-2)/(4*(m:ℝ)^2)) ∧
    (∀ m, 2 ≤ m → 1/4-limsupDensity (2*m+1) =
      (8*(m:ℝ)-11)/(4*(2*(m:ℝ)+1)^2)) := by
  refine ⟨limsup_density_limit,?_,limsup_density_even,limsup_density_odd⟩
  intro n hn
  by_cases hs : n ≤ 4
  · interval_cases n <;> norm_num [limsupDensity,limsupCluster] at *
  · have hh := limsup_density_below n (by omega)
    exact iff_of_false (by linarith) hs

/-- T6, corrected subsequence selection in Proposition 1's proof: every
strictly smaller positive threshold than a finite positive limsup is met
infinitely often. -/
theorem corrected_limsup_subsequence (a : ℕ → ℝ) (L c : ℝ)
    (hL : HasLimsup a L) (hc : 0 < c) (hcL : c < L) :
    Set.Infinite {t | c ≤ a t} := by
  apply Nat.frequently_atTop_iff_infinite.mp
  exact (hL.2 (L-c) (sub_pos.mpr hcL)).mono (fun t ht => by linarith)


/-- T7 supporting limit obstruction: a uniform upper bound on all finite-design
draws rules out a limiting CDF with positive upper-tail mass at a continuity
point beyond that bound. The sparse schedule and the normal-CDF facts are
separate obligations in the full counterexample at p. 693. -/
theorem bounded_support_limit_obstruction (S : Study)
    (X : (t : ℕ) → Assignment (S.N t) → ℝ) (G : ℝ → ℝ) (b x : ℝ)
    (hX : ∀ t z, X t z ≤ b) (hbx : b ≤ x)
    (hGcont : ContinuousAt G x) (hGlt : G x < 1) :
    ¬ InDistribution S X G := by
  classical
  intro hLimit
  have hp (t : ℕ) : prob (S.experiment t).design (fun z => X t z ≤ x) = 1 := by
    unfold prob
    calc
      _ = mean (S.experiment t).design (fun _ => 1) := by
        congr 1
        funext z
        simp [(hX t z).trans hbx]
      _ = 1 := mean_const (S.experiment t).design 1
  have h := hLimit x hGcont
  simp_rw [hp] at h
  have he : (1:ℝ) = G x := tendsto_nhds_unique tendsto_const_nhds h
  linarith


/-- The half-population consisting of unit 0 and every unit with index
2 ≤ i ≤ 2r+1, containing the first exceptional unit in P009-E005's
`n=4r+2` counterexample; its complement contains the second. -/
def halfA (r : ℕ) : Finset (Fin (4*r+2)) :=
  Finset.univ.filter (fun i => i.val = 0 ∨ (2 ≤ i.val ∧ i.val ≤ 2*r+1))

/-- P009-E005: bounded outcomes averaging assignments in disjoint half-populations. -/
def halfOutcome (r : ℕ) (i : Fin (4*r+2)) (z : Assignment (4*r+2)) : ℝ :=
  if i.val = 0 then (∑ j ∈ halfA r, bit (z j)) / (2*r+1:ℕ)
  else if i.val = 1 then (∑ j ∈ Finset.univ \ halfA r, bit (z j)) / (2*r+1:ℕ)
  else bit (z i)











/-- P009-E008: m blocks of m units, each with a hub and distinguished leaf. -/
def starOutcome (m : ℕ) (hm : 2 ≤ m) (i : Fin (m*m)) (z : Assignment (m*m)) : ℝ :=
  let hub : Fin (m*m) := ⟨((i.val / m)*m) % (m*m), Nat.mod_lt _ (by nlinarith)⟩
  let leaf : Fin (m*m) := ⟨((i.val / m)*m+1) % (m*m), Nat.mod_lt _ (by nlinarith)⟩
  bit (z i) + if i.val % m = 0 then bit (z leaf) else bit (z hub)


/-- P009-E004, T13: y_2=z_1(2z_3-1), with all other outcomes zero. -/
def cancellationExperiment : Experiment 3 := fairExperiment 3
  (fun i z => if i = 1 then bit (z 0)*(2*bit (z 2)-1) else 0)

/-- T13, p. 691: structural direct interference may average to zero. The
explicit fair three-unit experiment satisfies the regularity conditions and
has I_12=1 but xi_21(0)=xi_21(1)=breve xi_21=0. -/
theorem direct_spillover_counterexample :
    Bernoulli cancellationExperiment ∧ Regular cancellationExperiment 2 4 1 ∧
    Interferes cancellationExperiment 0 1 ∧
    xi cancellationExperiment 1 0 false = 0 ∧
    xi cancellationExperiment 1 0 true = 0 ∧
    xiBreve cancellationExperiment 1 0 = 0 := by
  have hnum : Bernoulli cancellationExperiment ∧ Regular cancellationExperiment 2 4 1 ∧
      xi cancellationExperiment 1 0 false = 0 ∧ xi cancellationExperiment 1 0 true = 0 ∧
      xiBreve cancellationExperiment 1 0 = 0 := by
    norm_num [Bernoulli, Regular, cancellationExperiment, fairExperiment, fairLaw,
      marginal, prob, mean, potential, bit, xi, xiBreve, Real.rpow_natCast,
      Real.rpow_one, Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Bool.forall_bool, sum_cube_succ, sum_cube_zero, Fintype.sum_bool, Function.update, cons_at_two, cons_at_three]
  refine ⟨hnum.1, hnum.2.1, ?_, hnum.2.2⟩
  refine Or.inr ⟨(fun _ => false), Function.update (fun _ => false) 0 true, ?_, ?_⟩
  · intro ℓ hℓ
    simp [Function.update_of_ne hℓ]
  · norm_num [cancellationExperiment, fairExperiment, bit, Function.update]

/-- T14, corrected direct-spillover implication (p. 691): absence of structural
interference gives zero assignment-specific and expected spillovers. The
converse fails in direct_spillover_counterexample. -/
theorem no_interference_zero_spillover {n : ℕ} (E : Experiment n) (i j : Fin n)
    (hij : i ≠ j) (hI : ¬ Interferes E i j) :
    (∀ a z, E.outcome j (Function.update (Function.update z j a) i true) =
      E.outcome j (Function.update (Function.update z j a) i false)) ∧
    xi E j i false = 0 ∧ xi E j i true = 0 ∧ xiBreve E j i = 0 := by
  have hp : ∀ a z, E.outcome j (Function.update (Function.update z j a) i true) =
      E.outcome j (Function.update (Function.update z j a) i false) := by
    intro a z
    by_contra hne
    apply hI
    refine Or.inr ⟨_, _, ?_, hne⟩
    intro ℓ hℓ
    simp [Function.update_of_ne hℓ]
  have hx : ∀ a, xi E j i a = 0 := by
    intro a
    simp only [xi, hp, sub_self]
    exact mean_const E.design 0
  exact ⟨hp, hx false, hx true, by simp [xiBreve, hx]⟩

/-- T14's last printed sentence: no interference makes all distinct spillover
coefficients and the full B1 term zero. Positive arm probabilities retain the
paper's domain for the conditional means in B1. -/
theorem no_interference_B1_zero {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (h : NoInterference E)
    (hp : ∀ i, 0 < marginal E i true ∧ 0 < marginal E i false) :
    (∀ i j, i ≠ j → xi E i j false = 0 ∧ xi E i j true = 0) ∧ B1 E = 0 := by
  have hx : ∀ i j, i ≠ j → ∀ a, xi E i j a = 0 := by
    intro i j hij a
    have hp : ∀ z, E.outcome i (Function.update (Function.update z i a) j true) =
        E.outcome i (Function.update (Function.update z i a) j false) := by
      intro z
      apply h i
      simp [Function.update_of_ne hij]
    simp only [xi, hp, sub_self]
    exact mean_const E.design 0
  refine ⟨fun i j hij => ⟨hx i j hij false, hx i j hij true⟩, ?_⟩
  unfold B1
  have hsum : (∑ i, ∑ j, if j = i then 0 else
      xiBreve E i j * xiBreve E j i +
      2 * yBreve E j * (xi E i j true - xi E i j false)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, xiBreve, hx i j (Ne.symm hji), hx j i hji]
  rw [hsum, zero_div]

/-- T15: n=1 is already a concrete counterexample to dropping the diagonal
mixing terms in Supplement A p. 23. The fair no-interference experiment has
four times its full covariance sum equal to one, whereas four times its
off-diagonal alpha sum is zero. It satisfies the regularity hypotheses. -/
theorem diagonal_omission_counterexample :
    Regular (sparseExperiment 1) 2 4 1 ∧ Bernoulli (sparseExperiment 1) ∧
    (4:ℝ) * (∑ i : Fin 1, ∑ j : Fin 1, cov (fairLaw 1)
      (fun z => bit (z i)) (fun z => bit (z j))) = 1 ∧
    (4:ℝ) * (∑ i : Fin 1, ∑ j : Fin 1, if j = i then 0 else
      alpha (fairLaw 1) (fun z => z i) (fun z => z j)) = 0 ∧ (0:ℝ) < 1 := by
  norm_num [Regular, Bernoulli, sparseExperiment, fairExperiment, fairLaw,
    marginal, prob, mean, potential, bit, var, cov, Real.rpow_natCast, Real.rpow_one,
    Fin.forall_fin_succ, Fin.sum_univ_succ, Fin.prod_univ_succ, Bool.forall_bool,
    sum_cube_succ, sum_cube_zero, Fintype.sum_bool, Function.update]




/-- Complete randomization of two of four units, each supported assignment mass 1/6. -/
def completeFourLaw : Law (Assignment 4) where
  mass := fun z => if (∑ i, if z i then (1:ℕ) else 0) = 2 then 1/6 else 0
  nonneg := by intro z; split_ifs <;> norm_num
  total := by
    simp only [sum_cube_succ, sum_cube_zero, Fintype.sum_bool, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ]
    norm_num

/-- P009-E012: y_1=z_1+z_2 and y_j=z_j otherwise, under complete randomization. -/
def hypergeomExperiment : Experiment 4 :=
  ⟨completeFourLaw, fun i z => bit (z i) + if i = 0 then bit (z 1) else 0⟩

/-- Definition A3 and Lemma A12 proof, Supplement A p. 9: T_i counts treated
INCOMING interfering units other than i. -/
def treatedIncoming {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) : ℕ :=
  ∑ j, if j ≠ i ∧ Interferes E j i ∧ z j = true then 1 else 0

/-- The printed hypergeometric expression with the specified draw count. -/
def hypergeomMass (n m draws t : ℕ) : ℝ :=
  (m.choose t : ℝ) * ((n-m).choose (draws-t) : ℝ) / (n.choose draws : ℝ)

/-- T17 finite structural certificate: precisely treatments 1 and 2 in paper
labels affect outcome 1 in P009-E012's four-unit experiment. -/
theorem hypergeom_interferes_zero (j : Fin 4) :
    Interferes hypergeomExperiment j 0 ↔ j = 0 ∨ j = 1 := by
  constructor
  · intro h
    rcases h with h | ⟨z, z', hagree, hne⟩
    · exact Or.inl h
    · by_contra hnot
      have h0 : (0 : Fin 4) ≠ j := by tauto
      have h1 : (1 : Fin 4) ≠ j := by tauto
      apply hne
      simp [hypergeomExperiment, hagree 0 h0, hagree 1 h1]
  · intro h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr ⟨(fun _ => false), Function.update (fun _ => false) 1 true, ?_, ?_⟩
      · intro ℓ hℓ
        simp [Function.update_of_ne hℓ]
      · norm_num [hypergeomExperiment, bit, Function.update]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
/-- T17, Supplement A p. 10: the explicit four-unit complete-randomization
experiment has incoming count 2 but only ONE other interfering treatment.
Its true mass and conditional mass at T=0 are 1/2 and 2/3; the printed
two-draw law gives 1/6 and 1/3, and the likelihood ratios also disagree. -/
theorem hypergeometric_draw_counterexample :
    Complete hypergeomExperiment 2 ∧ Regular hypergeomExperiment 2 4 1 ∧
    incoming hypergeomExperiment 0 = 2 ∧
    prob hypergeomExperiment.design (fun z => treatedIncoming hypergeomExperiment 0 z = 0) = 1/2 ∧
    cmean hypergeomExperiment.design (fun z => z 0 = true)
      (fun z => if treatedIncoming hypergeomExperiment 0 z = 0 then 1 else 0) = 2/3 ∧
    hypergeomMass 4 2 2 0 = 1/6 ∧ hypergeomMass 3 1 2 0 = 1/3 ∧
    (1/2:ℝ) ≠ 1/6 ∧ (2/3:ℝ)/(1/2) ≠ (1/3)/(1/6) := by
  classical
  have hchoose : Nat.choose 4 2 = 6 := by norm_num [Nat.choose]
  have hComplete : Complete hypergeomExperiment 2 := by
    refine ⟨by decide, by decide, ?_⟩
    intro z
    simp only [hypergeomExperiment, completeFourLaw, hchoose, Nat.cast_ofNat]
  have h2 (b : Bool) (z : Assignment 3) :
      (Fin.cons (α := fun _ : Fin 4 => Bool) b z) (2 : Fin 4) = z 1 :=
    cons_at_two (n := 1) b z
  have h3 (b : Bool) (z : Assignment 3) :
      (Fin.cons (α := fun _ : Fin 4 => Bool) b z) (3 : Fin 4) = z 2 :=
    cons_at_three (n := 0) b z
  have h23 (b : Bool) (z : Assignment 2) :
      (Fin.cons (α := fun _ : Fin 3 => Bool) b z) (2 : Fin 3) = z 1 :=
    cons_at_two (n := 0) b z
  have hm (i : Fin 4) (b : Bool) : marginal hypergeomExperiment i b = 1/2 := by
    fin_cases i <;> cases b <;>
      simp only [marginal, prob, mean, hypergeomExperiment, completeFourLaw,
        sum_cube_succ, sum_cube_zero, Fintype.sum_bool, Fin.sum_univ_succ,
        Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ, h2, h3, h23] <;>
      norm_num [h2, h3, h23, Fin.cons_zero, Fin.cons_succ]
  have hy (i : Fin 4) (z : Assignment 4) :
      0 ≤ hypergeomExperiment.outcome i z ∧ hypergeomExperiment.outcome i z ≤ 2 := by
    by_cases hi : i = 0
    · subst i
      cases h0 : z 0 <;> cases h1 : z 1 <;>
        norm_num [hypergeomExperiment, bit, h0, h1]
    · cases hb : z i <;> norm_num [hypergeomExperiment, bit, hi, hb]
  have hmean (F : Assignment 4 → ℝ) (c : ℝ) (hF : ∀ z, F z ≤ c) :
      mean hypergeomExperiment.design F ≤ c := by
    calc
      _ ≤ mean hypergeomExperiment.design (fun _ => c) := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (hF z) (hypergeomExperiment.design.nonneg z)
      _ = c := mean_const _ c
  have hReg : Regular hypergeomExperiment 2 4 1 := by
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      rw [hm i true]
      norm_num
    · intro i
      apply hmean
      intro z
      apply Real.rpow_le_rpow (abs_nonneg _)
      · rw [abs_of_nonneg (hy i z).1]
        exact (hy i z).2
      · norm_num
    · intro i b
      apply hmean
      intro z
      apply Real.rpow_le_rpow (abs_nonneg _)
      · have hp : 0 ≤ potential hypergeomExperiment i b z ∧
            potential hypergeomExperiment i b z ≤ 2 := hy i _
        rw [abs_of_nonneg hp.1]
        exact hp.2
      · norm_num
  have hc : incoming hypergeomExperiment 0 = 2 := by
    have he : Finset.univ.filter (fun j => Interferes hypergeomExperiment j 0) =
        ({0,1} : Finset (Fin 4)) := by
      ext j
      simp [hypergeom_interferes_zero]
    unfold incoming
    rw [he]
    norm_num
  have hT (z : Assignment 4) :
      treatedIncoming hypergeomExperiment 0 z = if z 1 then 1 else 0 := by
    have hPred (j : Fin 4) :
        (j ≠ 0 ∧ Interferes hypergeomExperiment j 0 ∧ z j = true) ↔
          (j = 1 ∧ z 1 = true) := by
      by_cases hj1 : j = 1
      · subst j
        norm_num [hypergeom_interferes_zero]
      · by_cases hj0 : j = 0
        · subst j
          simp
        · simp [hypergeom_interferes_zero, hj0, hj1]
    unfold treatedIncoming
    simp_rw [hPred]
    by_cases hz : z 1 = true <;> simp [hz]
  refine ⟨hComplete, hReg, hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp_rw [hT]
    simp only [prob, mean, hypergeomExperiment, completeFourLaw, sum_cube_succ,
      sum_cube_zero, Fintype.sum_bool, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Fin.cons_zero, Fin.cons_succ, h2, h3]
    norm_num
  · simp_rw [hT]
    simp only [cmean, prob, mean, hypergeomExperiment, completeFourLaw, sum_cube_succ,
      sum_cube_zero, Fintype.sum_bool, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Fin.cons_zero, Fin.cons_succ, h2, h3]
    norm_num
  all_goals norm_num [hypergeomMass, Nat.choose]


/-- P009-E013's explicit six-unit linear outcome schedule realizes its interference
indicators on the full cube; no on-support notion of interference is substituted. -/
def sixOutcome (i : Fin 6) (z : Assignment 6) : ℝ :=
  if i = 0 then bit (z 0)+bit (z 2)+bit (z 4)
  else if i = 1 then bit (z 1)+bit (z 3)+bit (z 5) else bit (z i)

/-- P009-E013's six-unit pairing, (1,2),(3,4),(5,6) in paper labels. -/
def sixPartner : Fin 6 → Fin 6 := ![1,0,3,2,5,4]

/-- Involution of the explicit pairing, finite certificate. -/
theorem sixPartner_involution : Function.Involutive sixPartner := by
  intro i; fin_cases i <;> rfl

/-- P009-E013's symmetric pairing, with no fixed points. -/
def sixPairing : Pairing 6 where
  partner := { toFun := sixPartner, invFun := sixPartner, left_inv := sixPartner_involution, right_inv := sixPartner_involution }
  involution := sixPartner_involution
  no_fixed := by intro i; fin_cases i <;> decide

/-- T19's full-cube interference indicators for the two relevant outcomes. -/
theorem six_incoming_certificate (j : Fin 6) :
    (Interferes (fairExperiment 6 sixOutcome) j 0 ↔ j = 0 ∨ j = 2 ∨ j = 4) ∧
    (Interferes (fairExperiment 6 sixOutcome) j 1 ↔ j = 1 ∨ j = 3 ∨ j = 5) := by
  have h0 := interferes_sum_bit (fairExperiment 6 sixOutcome) 0 j {0,2,4}
    (by intro z; simp [fairExperiment, sixOutcome]; ring)
  have h1 := interferes_sum_bit (fairExperiment 6 sixOutcome) 1 j {1,3,5}
    (by intro z; simp [fairExperiment, sixOutcome]; ring)
  constructor
  · simpa only [Finset.mem_insert, Finset.mem_singleton, or_self_left] using h0
  · simpa only [Finset.mem_insert, Finset.mem_singleton, or_self_left] using h1

/-- T19, Supplement A pp. 5–6: the six-unit outcome and pairing instance has
e_12=1 but THREE witnesses, refuting the printed equality to their count. -/
theorem pair_witness_counterexample :
    let E := fairExperiment 6 sixOutcome
    d E 0 1 = 0 ∧ e E sixPairing 0 1 = 1 ∧
    (∑ ℓ, (1-d E 0 1)*I E ℓ 0*I E (sixPairing.partner ℓ) 1) = 3 ∧ (1:ℝ) ≠ 3 := by
  dsimp only
  have hd : d (fairExperiment 6 sixOutcome) 0 1 = 0 := by
    norm_num [d, Dependent, (six_incoming_certificate _).1,
      (six_incoming_certificate _).2, Fin.exists_fin_succ]
  have he : e (fairExperiment 6 sixOutcome) sixPairing 0 1 = 1 := by
    have hn : ¬ Dependent (fairExperiment 6 sixOutcome) 0 1 := by
      simpa [d] using hd
    unfold e
    simp only [hn, not_false_eq_true, true_and]
    have hw : ∃ ℓ, Interferes (fairExperiment 6 sixOutcome) ℓ 0 ∧
        Interferes (fairExperiment 6 sixOutcome) (sixPairing.partner ℓ) 1 :=
      ⟨0, Or.inl rfl, by simp [sixPairing, sixPartner, (six_incoming_certificate _).2]⟩
    simp [hw]
  refine ⟨hd, he, ?_, by norm_num⟩
  norm_num [hd, I, (six_incoming_certificate _).1, (six_incoming_certificate _).2,
    sixPairing, sixPartner, Fin.sum_univ_succ]

/-- T20, corrected Lemma A7 proof and conclusion, Supplement A pp. 5–6:
the existence indicator is bounded by its witness count, and summing then
using the pairing permutation yields e_AVG≤C2². -/
theorem corrected_pair_dependence {n : ℕ} (hn : 0 < n) (E : Experiment n) (ρ : Pairing n) :
    (∀ i j, e E ρ i j ≤ ∑ ℓ, (1-d E i j)*I E ℓ i*I E (ρ.partner ℓ) j) ∧
    (∀ i j, (∑ ℓ, (1-d E i j)*I E ℓ i*I E (ρ.partner ℓ) j) ≤
      ∑ ℓ, I E ℓ i*I E (ρ.partner ℓ) j) ∧
    eAvg E ρ ≤ C2 E ^ 2 := by
  have hI : ∀ i j, 0 ≤ I E i j := by
    intro i j
    unfold I
    split_ifs <;> norm_num
  have hp : ∀ i j ℓ, 0 ≤ I E ℓ i*I E (ρ.partner ℓ) j :=
    fun i j ℓ => mul_nonneg (hI ℓ i) (hI (ρ.partner ℓ) j)
  have h1 : ∀ i j, e E ρ i j ≤ ∑ ℓ, (1-d E i j)*I E ℓ i*I E (ρ.partner ℓ) j := by
    intro i j
    by_cases hd : Dependent E i j
    · simp [e, d, hd]
    · simp only [e, d, hd, if_false, not_false_eq_true, true_and, sub_zero, one_mul]
      by_cases hw : ∃ ℓ, Interferes E ℓ i ∧ Interferes E (ρ.partner ℓ) j
      · obtain ⟨ℓ, hi, hj⟩ := hw
        have hw' : ∃ k, Interferes E k i ∧ Interferes E (ρ.partner k) j := ⟨ℓ, hi, hj⟩
        simp only [if_pos hw']
        have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hp i j k)
          (Finset.mem_univ ℓ)
        simpa [I, hi, hj] using hs
      · simp only [hw, if_false]
        exact Finset.sum_nonneg (fun ℓ _ => hp i j ℓ)
  have h2 : ∀ i j, (∑ ℓ, (1-d E i j)*I E ℓ i*I E (ρ.partner ℓ) j) ≤
      ∑ ℓ, I E ℓ i*I E (ρ.partner ℓ) j := by
    intro i j
    by_cases hd : Dependent E i j
    · simp only [d, hd, if_true, sub_self, zero_mul, Finset.sum_const_zero]
      exact Finset.sum_nonneg (fun ℓ _ => hp i j ℓ)
    · simp [d, hd]
  refine ⟨h1, h2, ?_⟩
  have ht : (∑ i, ∑ j, ∑ ℓ, I E ℓ i*I E (ρ.partner ℓ) j) =
      ∑ ℓ, outgoing E ℓ*outgoing E (ρ.partner ℓ) := by
    calc
      _ = ∑ i, ∑ ℓ, ∑ j, I E ℓ i*I E (ρ.partner ℓ) j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ ℓ, ∑ i, ∑ j, I E ℓ i*I E (ρ.partner ℓ) j := Finset.sum_comm
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul, outgoing]
  have hperm : (∑ ℓ, outgoing E (ρ.partner ℓ)^2) = ∑ ℓ, outgoing E ℓ^2 :=
    ρ.partner.sum_comp (fun ℓ => outgoing E ℓ^2)
  have hs : (∑ ℓ, outgoing E ℓ*outgoing E (ρ.partner ℓ)) ≤ ∑ ℓ, outgoing E ℓ^2 := by
    have hs' : (∑ ℓ, 2*(outgoing E ℓ*outgoing E (ρ.partner ℓ))) ≤
        ∑ ℓ, (outgoing E ℓ^2+outgoing E (ρ.partner ℓ)^2) := by
      apply Finset.sum_le_sum
      intro ℓ _
      nlinarith [sq_nonneg (outgoing E ℓ-outgoing E (ρ.partner ℓ))]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hperm] at hs'
    linarith
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hsum : (∑ i, ∑ j, e E ρ i j) ≤ ∑ ℓ, outgoing E ℓ^2 := by
    calc
      _ ≤ ∑ i, ∑ j, ∑ ℓ, I E ℓ i*I E (ρ.partner ℓ) j :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (h1 i j).trans (h2 i j)))
      _ = _ := ht
      _ ≤ _ := hs
  unfold eAvg C2
  rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hnR)]
  exact div_le_div_of_nonneg_right hsum hnR

/-- P009-E024's six-unit one-source illustration, with c_1=-1/4 and other c_i=1. -/
def illustrationExperiment : Experiment 6 :=
  fairExperiment 6 (oneSourceOutcome 4 (fun i => if i = 0 then -1/4 else 1))











/-- T25: signed Monte Carlo mean error, the unqualified "Bias" caption would
ordinarily denote this statistic (Supplement B Tables B1/B3/B5/B7). -/
def empiricalBias (R : ℕ) (estimates : Fin R → ℝ) : ℝ :=
  (∑ r, estimates r-1)/(R:ℝ)

/-- T25: the statistic actually reported, |mean error|, not mean absolute error. -/
def reportedBias (R : ℕ) (estimates : Fin R → ℝ) : ℝ := |empiricalBias R estimates|

/-- T25, corrected "Absolute bias" caption: the reported statistic is
nonnegative, is the magnitude of signed mean error, and loses its sign. -/
theorem absolute_bias_caption (R : ℕ) (hR : 0 < R) (estimates : Fin R → ℝ) :
    0 ≤ reportedBias R estimates ∧ reportedBias R estimates = |empiricalBias R estimates| ∧
    |(-1:ℝ)| = 1 ∧ (-1:ℝ) ≠ 1 := by
  exact ⟨abs_nonneg _, rfl, by norm_num, by norm_num⟩




/-- T23, Supplement B p. 2: independent uniform X_i on [0,3] and epsilon_i
on [0,7]. Product restricted Lebesgue measures represent sampling, separately
from the finite assignment laws. -/
def uniformBaselines (n : ℕ) : MeasureTheory.Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (MeasureTheory.Measure.pi (fun _ : Fin n =>
    (3:ENNReal)⁻¹ • MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 3))).prod
  (MeasureTheory.Measure.pi (fun _ : Fin n =>
    (7:ENNReal)⁻¹ • MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 7)))

/-- T23, Supplement B p. 2: "pairs are formed as adjacent units" after
ranking by X_i. A sorting permutation specifies the order; ties may be broken
arbitrarily and have sampling probability zero. -/
def AdjacentRanks {n : ℕ} (x : Fin n → ℝ) (ρ : Pairing n) : Prop :=
  ∃ order : Fin n ≃ Fin n, Monotone (fun i => x (order i)) ∧
    ∀ i j, i.val/2 = j.val/2 → i ≠ j → ρ.partner (order i) = order j









/-- T27, objective used to choose f_n* (Supplement A p. 36). -/
def approximationError {Ω : Type*} [Fintype Ω] (P : Law Ω) (α : ℝ) (f : Ω → ℝ) : ℝ :=
  |prob P (fun ω => f ω = 1)-α/2| + |prob P (fun ω => f ω = -1)-α/2|




/-- T28: the distance from a fixed real threshold to the three support points. -/
def threePointDistance (x : ℝ) : ℝ := min |x+1| (min |x| |x-1|)

/-- T28 finite corrected comparison: if the ABSOLUTE centering shift is less
than the distance to the support, centering cannot change any CDF event. -/
theorem three_point_centering {Ω : Type*} [Fintype Ω] (P : Law Ω) (F : Ω → ℝ)
    (hF : ∀ ω, F ω = -1 ∨ F ω = 0 ∨ F ω = 1)
    (x : ℝ) (hx : x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1)
    (hshift : |mean P F| < threePointDistance x) :
    prob P (fun ω => F ω-mean P F ≤ x) = prob P (fun ω => F ω ≤ x) := by
  have hd := lt_min_iff.mp hshift
  have hd' := lt_min_iff.mp hd.2
  have hcmp : ∀ y : ℝ, |mean P F| < |x-y| → (y-mean P F ≤ x ↔ y ≤ x) := by
    intro y hy
    by_cases hxy : 0 ≤ x-y
    · rw [abs_of_nonneg hxy] at hy
      have hb := abs_lt.mp hy
      have hleft : y-mean P F ≤ x := by linarith
      have hright : y ≤ x := by linarith
      simp [hleft, hright]
    · rw [abs_of_neg (lt_of_not_ge hxy)] at hy
      have hb := abs_lt.mp hy
      have hleft : ¬ y-mean P F ≤ x := by linarith
      have hright : ¬ y ≤ x := by linarith
      simp [hleft, hright]
  apply congrArg (prob P)
  funext ω
  apply propext
  apply hcmp
  rcases hF ω with hω | hω | hω
  · simpa [hω] using hd.1
  · simpa [hω] using hd'.1
  · simpa [hω] using hd'.2

/-- T28's eventual condition: for x outside {-1,0,1}, a shift tending to zero
eventually has magnitude smaller than its positive distance to those atoms. -/
theorem centering_shift_eventually (μ : ℕ → ℝ) (hμ : Tendsto μ atTop (nhds 0))
    (x : ℝ) (hx : x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1) :
    ∀ᶠ t in atTop, |μ t| < threePointDistance x := by
  have hd : 0 < threePointDistance x := by
    simp only [threePointDistance, lt_min_iff, abs_pos]
    constructor
    · intro hzero
      apply hx.1
      linarith
    · exact ⟨hx.2.1, sub_ne_zero.mpr hx.2.2⟩
  have hab : Tendsto (fun t => |μ t|) atTop (nhds 0) := by
    simpa using hμ.abs
  exact hab.eventually_lt tendsto_const_nhds hd

/-- T29 finite variance identity behind Lemma A3, Supplement A p. 3:
variance equals the second moment minus the square of the first moment,
for every finite randomization law. -/
theorem variance_second_moment {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (X : Ω → ℝ) :
    var P X = mean P (fun ω => X ω^2) - (mean P X)^2 := by
  unfold var cov
  calc
    _ = mean P (fun ω => X ω^2-(2*mean P X)*X ω+(mean P X)^2) := by
      congr 1
      funext ω
      ring
    _ = mean P (fun ω => X ω^2)-(2*mean P X)*mean P X+(mean P X)^2 := by
      rw [mean_add, mean_sub, mean_const_mul, mean_const]
    _ = _ := by ring

/-- T29 finite Jensen step from the proof of Lemma A3, Supplement A p. 3:
the m-th absolute moment is bounded by the q-th absolute moment to power
m/q, for positive integer m and real q≥m. -/
theorem finite_moment_interpolation {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (X : Ω → ℝ) (m : ℕ) (hm : 0 < m) (q : ℝ) (hq : (m:ℝ) ≤ q) :
    mean P (fun ω => |X ω|^m) ≤
      Real.rpow (mean P (fun ω => Real.rpow |X ω| q)) ((m:ℝ)/q) := by
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hqpos : 0 < q := hmR.trans_le hq
  have hθ0 : 0 ≤ (m:ℝ)/q := div_nonneg (le_of_lt hmR) (le_of_lt hqpos)
  have hθ1 : (m:ℝ)/q ≤ 1 := (div_le_one hqpos).2 hq
  have hid (ω : Ω) :
      ((|X ω|:ℝ)^q)^((m:ℝ)/q) = |X ω|^m := by
    have he : q*((m:ℝ)/q) = (m:ℝ) := by
      field_simp [ne_of_gt hqpos]
    simpa only [he, Real.rpow_natCast] using
      (Real.rpow_mul (abs_nonneg (X ω)) q ((m:ℝ)/q)).symm
  have hJ := (Real.concaveOn_rpow hθ0 hθ1).le_map_sum
    (t := Finset.univ) (w := P.mass) (p := fun ω => Real.rpow |X ω| q)
    (fun ω _ => P.nonneg ω) P.total
    (fun ω _ => Real.rpow_nonneg (abs_nonneg (X ω)) q)
  simpa only [Real.rpow_eq_pow, smul_eq_mul, hid, mean] using hJ

/-- T29, corrected Cauchy–Schwarz line and full moment chain from Lemma A3,
Supplement A p. 3: the second variable uses Y_j. The absolute form strengthens
the printed signed inequality and supplies the covariance bound for T4. -/
theorem corrected_moment_covariance {n : ℕ} (E : Experiment n) (k q : ℝ)
    (hk : 0 < k) (hq : 2 ≤ q)
    (hMoment : ∀ ℓ, mean E.design (fun z => Real.rpow |E.outcome ℓ z| q) ≤ Real.rpow k q)
    (a : ℕ) (hqa : 2*a ≤ q)
    (i j : Fin n) (b : Bool) :
    |cov E.design (armVariable E b a i) (armVariable E b a j)| ≤
      Real.sqrt (var E.design (armVariable E b a i)*var E.design (armVariable E b a j)) ∧
    Real.sqrt (var E.design (armVariable E b a i)*var E.design (armVariable E b a j)) ≤
      Real.sqrt (mean E.design (fun z => |E.outcome i z|^(2*a)) *
        mean E.design (fun z => |E.outcome j z|^(2*a))) ∧
    Real.sqrt (mean E.design (fun z => |E.outcome i z|^(2*a)) *
        mean E.design (fun z => |E.outcome j z|^(2*a))) ≤
      Real.sqrt (Real.rpow (mean E.design (fun z => Real.rpow |E.outcome i z| q))
        (2*(a:ℝ)/q) * Real.rpow
        (mean E.design (fun z => Real.rpow |E.outcome j z| q)) (2*(a:ℝ)/q)) ∧
    Real.sqrt (Real.rpow (mean E.design (fun z => Real.rpow |E.outcome i z| q))
        (2*(a:ℝ)/q) * Real.rpow
        (mean E.design (fun z => Real.rpow |E.outcome j z| q)) (2*(a:ℝ)/q)) ≤
      Real.sqrt (Real.rpow (Real.rpow k q) (2*(a:ℝ)/q) *
        Real.rpow (Real.rpow k q) (2*(a:ℝ)/q)) ∧
    Real.sqrt (Real.rpow (Real.rpow k q) (2*(a:ℝ)/q) *
        Real.rpow (Real.rpow k q) (2*(a:ℝ)/q)) = Real.sqrt (k^(4*a)) ∧
    Real.sqrt (k^(4*a)) = k^(2*a) ∧
    |cov E.design (armVariable E b a i) (armVariable E b a j)| ≤ k^(2*a) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqa' : ((2*a:ℕ):ℝ) ≤ q := by exact_mod_cast hqa
  let M := fun ℓ => mean E.design (fun z => |E.outcome ℓ z|^(2*a))
  let Q := fun ℓ => Real.rpow
    (mean E.design (fun z => Real.rpow |E.outcome ℓ z| q)) (2*(a:ℝ)/q)
  let K := Real.rpow (Real.rpow k q) (2*(a:ℝ)/q)
  have hM (ℓ : Fin n) : 0 ≤ M ℓ :=
    Finset.sum_nonneg (fun z _ =>
      mul_nonneg (E.design.nonneg z) (pow_nonneg (abs_nonneg _) _))
  have hY (ℓ : Fin n) : 0 ≤ mean E.design (fun z => Real.rpow |E.outcome ℓ z| q) :=
    Finset.sum_nonneg (fun z _ =>
      mul_nonneg (E.design.nonneg z) (Real.rpow_nonneg (abs_nonneg _) q))
  have hQ (ℓ : Fin n) : 0 ≤ Q ℓ := Real.rpow_nonneg (hY ℓ) _
  have hK : 0 ≤ K := Real.rpow_nonneg (Real.rpow_nonneg (le_of_lt hk) q) _
  have hMQ (ℓ : Fin n) : M ℓ ≤ Q ℓ := by
    by_cases ha0 : a = 0
    · norm_num [M, Q, ha0, mean_const]
    · have h := finite_moment_interpolation E.design (E.outcome ℓ)
        (2*a) (by omega) q hqa'
      simpa only [M, Q, Nat.cast_mul, Nat.cast_ofNat] using h
  have hQK (ℓ : Fin n) : Q ℓ ≤ K :=
    Real.rpow_le_rpow (hY ℓ) (hMoment ℓ)
      (div_nonneg (by positivity) (le_of_lt hqpos))
  have hKpow : K = k^(2*a) := by
    dsimp [K]
    rw [← Real.rpow_mul (le_of_lt hk)]
    have he : q*(2*(a:ℝ)/q) = ((2*a:ℕ):ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      field_simp [ne_of_gt hqpos] <;> ring
    rw [he, Real.rpow_natCast]
  have hv (ℓ : Fin n) : var E.design (armVariable E b a ℓ) ≤ M ℓ := by
    calc
      _ ≤ mean E.design (fun z => armVariable E b a ℓ z^2) := by
        rw [variance_second_moment]
        exact sub_le_self _ (sq_nonneg _)
      _ ≤ M ℓ := by
        dsimp only [M, mean]
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ (E.design.nonneg z)
        by_cases hz : z ℓ = b
        · simp only [armVariable, hz, if_true]
          simp only [mul_comm 2 a, pow_mul, ← abs_pow]
          exact le_abs_self _
        · simp [armVariable, hz] <;> positivity
  have hAB := Real.sqrt_le_sqrt (mul_le_mul (hv i) (hv j)
    (variance_nonnegative E.design (armVariable E b a j)) (hM i))
  have hBC := Real.sqrt_le_sqrt (mul_le_mul (hMQ i) (hMQ j) (hM j) (hQ i))
  have hCD := Real.sqrt_le_sqrt (mul_le_mul (hQK i) (hQK j) (hQ j) hK)
  have hD : Real.sqrt (K*K) = Real.sqrt (k^(4*a)) := by
    rw [hKpow]
    congr 1
    rw [← pow_add]
    congr 1
    omega
  have hsqrt : Real.sqrt (k^(4*a)) = k^(2*a) := by
    calc
      _ = Real.sqrt ((k^(2*a))^2) := by
        congr 1
        rw [← pow_mul]
        congr 1
        omega
      _ = k^(2*a) := Real.sqrt_sq (pow_nonneg (le_of_lt hk) _)
  have hCS := covariance_cauchy_schwarz E.design
    (armVariable E b a i) (armVariable E b a j)
  exact ⟨hCS, hAB, hBC, hCD, hD, hsqrt,
    hCS.trans (hAB.trans (hBC.trans (hCD.trans (le_of_eq (hD.trans hsqrt)))))⟩

/-- T30, corrected estimator names in Propositions 9 and 10's proofs,
Supplement A pp. 34–35. These are exactly the printed MAX and SR definitions. -/
theorem corrected_inflated_estimator_names {n : ℕ} (E : Experiment n) (z : Assignment n) :
    vMAX E z = dMax E*vBER E z ∧ vSR E z = lambdaMax E*vBER E z ∧
    (vAVG E z = dMax E*vBER E z ↔ dAvg E = dMax E ∨ vBER E z = 0) ∧
    (vAVG E z = lambdaMax E*vBER E z ↔ dAvg E = lambdaMax E ∨ vBER E z = 0) := by
  dsimp [vMAX, vSR, vAVG]
  exact ⟨rfl, rfl, mul_eq_mul_right_iff, mul_eq_mul_right_iff⟩

/-- Definition A4, Supplement A p. 36: masses alpha/2,1-alpha,alpha/2
at -1,0,1. The atom type is Fin 3, not an approximation by a normal law. -/
def sharpLaw (α : ℝ) (hα : 0 < α ∧ α < 1) : Law (Fin 3) where
  mass := ![α/2, 1-α, α/2]
  nonneg := by intro i; fin_cases i <;> simp <;> linarith [hα.1, hα.2]
  total := by simp [Fin.sum_univ_succ]; ring

/-- Definition A4's three-point random variable X(alpha). -/
def sharpValue : Fin 3 → ℝ := ![-1,0,1]

/-- T31's corrected distribution function, with the argument s in disjoint
case conditions, including its values at all three jumps. -/
def sharpCDF (α x : ℝ) : ℝ :=
  if x < -1 then 0 else if x < 0 then α/2 else if x < 1 then 1-α/2 else 1

/-- T31 finite correction: the CDF of Definition A4 equals the corrected
case expression for EVERY real threshold, Supplement A p. 38. -/
theorem corrected_three_point_CDF (α : ℝ) (hα : 0 < α ∧ α < 1) (x : ℝ) :
    prob (sharpLaw α hα) (fun i => sharpValue i ≤ x) = sharpCDF α x := by
  simp only [prob, mean, sharpLaw, sharpValue, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  by_cases hm : x < -1
  · have h0 : ¬ 0 ≤ x := by linarith
    have h1 : ¬ 1 ≤ x := by linarith
    simp [sharpCDF, hm, not_le.mpr hm, h0, h1]
  by_cases h0 : x < 0
  · have h1 : ¬ 1 ≤ x := by linarith
    simp [sharpCDF, hm, h0, le_of_not_gt hm, not_le.mpr h0, h1]
  by_cases h1 : x < 1
  · simp [sharpCDF, hm, h0, h1, le_of_not_gt hm, le_of_not_gt h0, not_le.mpr h1]
    ring
  · simp [sharpCDF, hm, h0, h1, le_of_not_gt hm, le_of_not_gt h0, le_of_not_gt h1]
    ring

/-- T31's finite CDF identity for any random variable supported on {-1,0,1}.
Only the two outer atom probabilities are needed for the corrected expression. -/
theorem three_point_CDF_formula {Ω : Type*} [Fintype Ω] (P : Law Ω) (F : Ω → ℝ)
    (hF : ∀ ω, F ω = -1 ∨ F ω = 0 ∨ F ω = 1) (x : ℝ) :
    prob P (fun ω => F ω ≤ x) =
      if x < -1 then 0 else if x < 0 then prob P (fun ω => F ω = -1)
      else if x < 1 then 1-prob P (fun ω => F ω = 1) else 1 := by
  by_cases hm : x < -1
  · simp only [hm, if_true]
    have he : (fun ω => F ω ≤ x) = (fun _ => False) := by
      funext ω
      apply propext
      have hlow : (-1:ℝ) ≤ F ω := by
        rcases hF ω with hf | hf | hf <;> norm_num [hf]
      exact iff_of_false (not_le.mpr (hm.trans_le hlow)) (by simp)
    rw [he]
    simpa [prob] using mean_const P (0:ℝ)
  by_cases h0 : x < 0
  · simp only [hm, h0, if_false, if_true]
    apply congrArg (prob P)
    funext ω
    apply propext
    rcases hF ω with hf | hf | hf
    · simpa only [hf] using
        (iff_of_true (le_of_not_gt hm) (show (-1:ℝ) = -1 from rfl))
    · simpa only [hf] using
        (iff_of_false (not_le.mpr h0) (by norm_num : ¬ (0:ℝ) = -1))
    · simpa only [hf] using
        (iff_of_false (not_le.mpr (h0.trans (by norm_num : (0:ℝ) < 1)))
          (by norm_num : ¬ (1:ℝ) = -1))
  by_cases h1 : x < 1
  · simp only [hm, h0, h1, if_false, if_true]
    have he : (fun ω => F ω ≤ x) = (fun ω => ¬ F ω = 1) := by
      funext ω
      apply propext
      rcases hF ω with hf | hf | hf
      · simpa only [hf] using
          (iff_of_true (le_of_not_gt hm) (by norm_num : ¬ (-1:ℝ) = 1))
      · simpa only [hf] using
          (iff_of_true (le_of_not_gt h0) (by norm_num : ¬ (0:ℝ) = 1))
      · simpa only [hf] using
          (iff_of_false (not_le.mpr h1) (by simp : ¬ (¬ (1:ℝ) = 1)))
    rw [he]
    exact probability_complement P _
  · simp only [hm, h0, h1, if_false]
    have he : (fun ω => F ω ≤ x) = (fun _ => True) := by
      funext ω
      apply propext
      have hupp : F ω ≤ (1:ℝ) := by
        rcases hF ω with hf | hf | hf <;> norm_num [hf]
      exact iff_of_true (hupp.trans (le_of_not_gt h1)) True.intro
    rw [he]
    simpa [prob] using mean_const P (1:ℝ)

/-- T31 limiting correction (Supplement A p. 38): convergence of the two
outer atom probabilities implies CDF convergence at every real threshold, even
at jumps of the limit. Arbitrary finite laws include the three-atom distribution
representing any {-1,0,1}-valued random variable. -/
theorem three_point_CDF_limit (Ω : ℕ → Type*) [∀ t, Fintype (Ω t)]
    (P : (t : ℕ) → Law (Ω t)) (F : (t : ℕ) → Ω t → ℝ)
    (hF : ∀ t ω, F t ω = -1 ∨ F t ω = 0 ∨ F t ω = 1) (α : ℝ)
    (hα : 0 < α ∧ α < 1)
    (hminus : Tendsto (fun t => prob (P t) (fun ω => F t ω = -1))
      atTop (nhds (α/2)))
    (hplus : Tendsto (fun t => prob (P t) (fun ω => F t ω = 1))
      atTop (nhds (α/2))) :
    ∀ x, Tendsto (fun t => prob (P t) (fun ω => F t ω ≤ x))
      atTop (nhds (sharpCDF α x)) := by
  intro x
  have hid (t : ℕ) := three_point_CDF_formula (P t) (F t) (hF t) x
  simp_rw [hid]
  by_cases hm : x < -1
  · simp only [sharpCDF, hm, if_true]
    exact tendsto_const_nhds
  by_cases h0 : x < 0
  · simp only [sharpCDF, hm, h0, if_false, if_true]
    exact hminus
  by_cases h1 : x < 1
  · simp only [sharpCDF, hm, h0, h1, if_false, if_true]
    exact tendsto_const_nhds.sub hplus
  · simp only [sharpCDF, hm, h0, h1, if_false]
    exact tendsto_const_nhds

/-- T32 corrected single-flip arithmetic: a control-to-treatment update adds
TWO to an interference set's unweighted balance, Supplement B p. 6. -/
theorem balance_update {n : ℕ} (G : Finset (Fin n)) (i : Fin n)
    (z : Assignment n) (b : Bool) :
    balance G (Function.update z i b)-balance G z =
      if i ∈ G then 2*(bit b-bit (z i)) else 0 := by
  unfold balance
  rw [← Finset.sum_sub_distrib]
  have ht : ∀ j, (2*bit (Function.update z i b j)-1)-(2*bit (z j)-1) =
      if j = i then 2*(bit b-bit (z i)) else 0 := by
    intro j
    by_cases hji : j = i
    · simp [hji]; ring
    · simp [hji, Function.update_of_ne hji]
  simp_rw [ht]
  simp

/-- T32, the specified control-to-treatment flip is the +2 case of balance_update. -/
theorem balance_flip {n : ℕ} (G : Finset (Fin n)) (i : Fin n) (hi : i ∈ G)
    (z : Assignment n) (hz : z i = false) :
    balance G (Function.update z i true) - balance G z = 2 := by
  simpa [hi, hz, bit] using balance_update G i z true

/-- T32's corrected branch crossings: for integer starting balances, upward
and downward changes affect the multiplier exactly at the stated three values. -/
theorem multiplier_crossings (b : ℤ) :
    (multiplier ((b:ℝ)+2) ≠ multiplier b ↔ b = -2 ∨ b = -1 ∨ b = 0) ∧
    (multiplier ((b:ℝ)-2) ≠ multiplier b ↔ b = 0 ∨ b = 1 ∨ b = 2) := by
  unfold multiplier
  split_ifs <;> norm_num at * <;> norm_cast at * <;> omega

/-- T32's paired-flip correction: the net change is +2, -2 or zero according
to membership of the two distinct flipped units in the interference set. -/
theorem balance_paired_flip {n : ℕ} (G : Finset (Fin n)) (i j : Fin n)
    (hij : i ≠ j) (z : Assignment n) (hi : z i = false) (hj : z j = true) :
    balance G (Function.update (Function.update z i true) j false) - balance G z =
      (if i ∈ G then 2 else 0) - (if j ∈ G then 2 else 0) := by
  have h1 := balance_update G i z true
  have h2 := balance_update G j (Function.update z i true) false
  simp only [hi, hj, Function.update_of_ne (Ne.symm hij), bit, Bool.false_eq_true,
    if_false, if_true, mul_zero, sub_zero, zero_sub, mul_one] at h1 h2
  by_cases hIG : i ∈ G <;> by_cases hJG : j ∈ G <;>
    simp [hIG, hJG] at h1 h2 ⊢ <;> linarith

/-- T33 finite potential-outcome calculation, Supplement B p. 8:
every untreated unit has its fixed baseline c_i, for any assignments of
other units and any integer cutoff. -/
theorem one_source_control_outcome {n : ℕ} (b : ℕ) (c : Fin n → ℝ)
    (i : Fin n) (z : Assignment n) :
    oneSourceOutcome b c i (Function.update z i false) = c i := by
  unfold oneSourceOutcome
  split_ifs <;> simp [bit]

/-- T33's corrected zero spillover for every distinct ordered pair in the
one-source schedule, Supplement B p. 8. No averaging cancellation is needed:
the outcome difference vanishes at each full-cube assignment. -/
theorem one_source_untreated_spillover {n : ℕ} (b : ℕ) (c : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    xi (fairExperiment n (oneSourceOutcome b c)) i j false = 0 := by
  unfold xi
  have hs (z : Assignment n) (a : Bool) :
      (fairExperiment n (oneSourceOutcome b c)).outcome i
        (Function.update (Function.update z i false) j a) = c i := by
    dsimp only [fairExperiment]
    rw [Function.update_comm hij false a z]
    exact one_source_control_outcome b c i _
  simp_rw [hs, sub_self]
  exact mean_const _ 0




/-- Definition 9, p. 687: moment indices may be finite real numbers or infinity
under the paper's bounded-outcome convention. -/
abbrev MomentIndex := WithTop ℝ

/-- Uniform q-moment bound. For q=infinity this is essential boundedness on
the finite randomization support, the limit-moment convention used by the paper. -/
def MomentBound {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ)
    (k : ℝ) (q : MomentIndex) : Prop :=
  if q = ⊤ then ∀ ω, 0 < P.mass ω → |X ω| ≤ k
  else mean P (fun ω => Real.rpow |X ω| (q.untopD 0)) ≤ Real.rpow k (q.untopD 0)

/-- Assumption 1 with the extended moment convention used in Definition 9. -/
def RegularMix (S : Study) (k : ℝ) (q s : MomentIndex) : Prop :=
  0 < k ∧ 2 ≤ q ∧ 1 ≤ s ∧
  (∀ t i, k⁻¹ ≤ marginal (S.experiment t) i true ∧
    marginal (S.experiment t) i true ≤ 1-k⁻¹) ∧
  (∀ t i, MomentBound (S.experiment t).design ((S.experiment t).outcome i) k q) ∧
  (∀ t i b, MomentBound (S.experiment t).design (potential (S.experiment t) i b) k s)

/-- Definition 9's observed moment admissibility along the whole sequence. -/
def AdmissibleObserved (S : Study) (q : MomentIndex) : Prop :=
  2 ≤ q ∧ ∃ k > 0, ∀ t i,
    MomentBound (S.experiment t).design ((S.experiment t).outcome i) k q

/-- Definition 9's potential moment admissibility along the whole sequence. -/
def AdmissiblePotential (S : Study) (s : MomentIndex) : Prop :=
  1 ≤ s ∧ ∃ k > 0, ∀ t i b,
    MomentBound (S.experiment t).design (potential (S.experiment t) i b) k s

/-- Literal Definition 9, p. 687: "the maximum values of q and s".
These explicit premises require maxima to EXIST and to be admissible. They are
not automatically supplied by Assumption 1 when a finite supremum is unattained.
Infinity handles the bounded case. -/
def MaximalMoments (S : Study) (q s : MomentIndex) : Prop :=
  AdmissibleObserved S q ∧ (∀ r, AdmissibleObserved S r → r ≤ q) ∧
  AdmissiblePotential S s ∧ (∀ r, AdmissiblePotential S r → r ≤ s)

/-- Definition 9's external power (q-2)/q, with value one at infinity. -/
def extExponent (q : MomentIndex) : ℝ :=
  if q = ⊤ then 1 else (q.untopD 0-2)/(q.untopD 0)

/-- Definition 9's internal power (s-1)/s, with value one at infinity. -/
def intExponent (s : MomentIndex) : ℝ :=
  if s = ⊤ then 1 else (s.untopD 0-1)/(s.untopD 0)

/-- p. 684: the complete randomization SEQUENCE uses a fixed fraction p and
m_n=floor(p n), not an arbitrary sequence of treatment fractions. -/
def CompleteSequence (S : Study) : Prop :=
  ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ t, Complete (S.experiment t) ⌊p*size S t⌋₊

/-- Propositions 2–6: the HT/Hájek errors for a given deterministic estimand. -/
def EstimatorClaims (S : Study) (θ a : ℕ → ℝ) : Prop :=
  InProbability S (fun t z => ht (S.experiment t) z-θ t) ∧
  InProbability S (fun t z => hajek (S.experiment t) z-θ t) ∧
  Op S (fun t z => ht (S.experiment t) z-θ t) a ∧
  Op S (fun t z => hajek (S.experiment t) z-θ t) a

/-- The Bernoulli rate n^-1/2 d_AVG^1/2. -/
def bernoulliRate (S : Study) (t : ℕ) : ℝ :=
  Real.sqrt (dAvg (S.experiment t)) / Real.sqrt (size S t)

/-- T41/T46 finite Lemma A1 (Supplement A p. 3): the IPW arm mean has
expectation equal to the average conditional observed outcome, for any design. -/
theorem expected_arm_mean {n : ℕ} (E : Experiment n) (b : Bool)
    (hp : ∀ i, 0 < marginal E i b) :
    mean E.design (muHat E b) =
      (∑ i, cmean E.design (fun z => z i = b) (E.outcome i))/(n:ℝ) := by
  classical
  unfold muHat
  rw [mean_div, mean_sum]
  simp_rw [mean_div]
  simp only [cmean, marginal, prob]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1 <;> apply congrArg (mean E.design) <;> funext z <;>
    by_cases hz : z i = b <;> simp [hz]

/-- T41/T46 finite unbiasedness (Lemma A1 and Definition 4): HT estimates
ADSE without bias under any design with the paper's conditional means defined. -/
theorem ht_unbiased_ADSE {n : ℕ} (E : Experiment n)
    (hp : ∀ i, 0 < marginal E i true ∧ 0 < marginal E i false) :
    mean E.design (ht E) = adse E := by
  change mean E.design (fun z => muHat E true z-muHat E false z) = _
  rw [mean_sub, expected_arm_mean E true (fun i => (hp i).1),
    expected_arm_mean E false (fun i => (hp i).2)]
  simp only [adse, Finset.sum_sub_distrib, sub_div]

/-- T41/T46 finite Lemma A2 (Supplement A p. 3): with positive arm inclusion
probabilities, the expected IPW arm population size is exactly n. -/
theorem expected_arm_count {n : ℕ} (E : Experiment n) (b : Bool)
    (hp : ∀ i, 0 < marginal E i b) :
    mean E.design (nHat E b) = n := by
  classical
  unfold nHat
  rw [mean_sum]
  simp_rw [mean_div]
  have hm : ∀ i, mean E.design (fun z => if z i = b then (1:ℝ) else 0)/
      marginal E i b = 1 := by
    intro i
    have he : mean E.design (fun z => if z i = b then (1:ℝ) else 0) =
        marginal E i b := by
      unfold marginal prob
      congr 1
      funext z
      by_cases hz : z i = b <;> simp [hz]
    rw [he]
    exact div_self (ne_of_gt (hp i))
  simp [hm]

/-- T35, the finite displayed EATE identity in Definition 3 (p. 677), valid
for any finite design and any full-cube outcome schedule. -/
theorem eate_finite_identity {n : ℕ} (E : Experiment n) :
    eate E = (∑ i, (mean E.design (potential E i true) -
      mean E.design (potential E i false))) / n := by
  change mean E.design (fun z => (∑ i, (potential E i true z-potential E i false z))/(n:ℝ)) = _
  rw [mean_div, mean_sum]
  simp_rw [mean_sub]

namespace BernoulliCompletion
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 theorem sum_split_coordinate {n : ℕ} (i : Fin n) (F : Assignment n → ℝ) :
    (∑ z, F z) = ∑ w : ({j : Fin n // j ≠ i} → Bool),
      (F ((Equiv.piSplitAt i (fun _ => Bool)).symm (false,w)) +
       F ((Equiv.piSplitAt i (fun _ => Bool)).symm (true,w))) := by
  rw [← (Equiv.piSplitAt i (fun _ => Bool)).symm.sum_comp F]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  simp only [add_comm]

def join {n : ℕ} (i : Fin n) (a : Bool) (w : {j : Fin n // j ≠ i} → Bool) : Assignment n :=
  (Equiv.piSplitAt i (fun _ => Bool)).symm (a,w)

 theorem join_self {n : ℕ} (i : Fin n) (a : Bool) (w : {j : Fin n // j ≠ i} → Bool) :
    join i a w i = a := by simp [join, Equiv.piSplitAt]

 theorem join_update {n : ℕ} (i : Fin n) (a b : Bool)
    (w : {j : Fin n // j ≠ i} → Bool) :
    Function.update (join i a w) i b = join i b w := by
  funext j
  by_cases hj : j = i
  · subst j; simp [join_self]
  · simp [Function.update_of_ne hj, join, Equiv.piSplitAt, hj]

def withoutMass {n : ℕ} (E : Experiment n) (i : Fin n)
    (w : {j : Fin n // j ≠ i} → Bool) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, if join i false w j then
    marginal E j true else 1-marginal E j true

 theorem mass_split {n : ℕ} (E : Experiment n) (hBER : Bernoulli E) (i : Fin n)
    (a : Bool) (w : {j : Fin n // j ≠ i} → Bool) :
    E.design.mass (join i a w) =
      (if a then marginal E i true else 1-marginal E i true) * withoutMass E i w := by
  rw [hBER.2]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if join i a w j then marginal E j true else 1-marginal E j true)
    (Finset.mem_univ i)]
  rw [join_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [join, Equiv.piSplitAt, hji]

 theorem potential_mean_split {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (i : Fin n) (b : Bool) :
    mean E.design (potential E i b) =
      ∑ w : ({j : Fin n // j ≠ i} → Bool),
        withoutMass E i w * E.outcome i (join i b w) := by
  unfold mean
  rw [sum_split_coordinate i]
  change (∑ w, (E.design.mass (join i false w) * potential E i b (join i false w) +
    E.design.mass (join i true w) * potential E i b (join i true w))) = _
  apply Finset.sum_congr rfl
  intro w _
  rw [mass_split E hBER, mass_split E hBER]
  simp only [Bool.false_eq_true, if_false, if_true, potential, join_update]
  ring

 theorem conditional_numerator_split {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (i : Fin n) (b : Bool) :
    mean E.design (fun z => if z i = b then E.outcome i z else 0) =
      (if b then marginal E i true else 1-marginal E i true) *
      ∑ w : ({j : Fin n // j ≠ i} → Bool),
        withoutMass E i w * E.outcome i (join i b w) := by
  unfold mean
  rw [sum_split_coordinate i, Finset.mul_sum]
  change (∑ w, (E.design.mass (join i false w) *
      (if join i false w i = b then E.outcome i (join i false w) else 0) +
    E.design.mass (join i true w) *
      (if join i true w i = b then E.outcome i (join i true w) else 0))) = _
  apply Finset.sum_congr rfl
  intro w _
  rw [mass_split E hBER, mass_split E hBER, join_self, join_self]
  cases b <;> simp <;> ring

 theorem marginal_pos {n : ℕ} (E : Experiment n) (hBER : Bernoulli E)
    (i : Fin n) (b : Bool) : 0 < marginal E i b := by
  cases b
  · linarith [(marginal_partition E i), (hBER.1 i).2]
  · exact (hBER.1 i).1

/-- A unit's potential outcome with its own treatment fixed depends only on
all other assignments. Under the actual finite Bernoulli product law, its
unconditional mean equals the observed conditional mean. -/
 theorem conditional_observed_eq_potential_mean {n : ℕ} (E : Experiment n)
    (hBER : Bernoulli E) (i : Fin n) (b : Bool) :
    cmean E.design (fun z => z i = b) (E.outcome i) =
      mean E.design (potential E i b) := by
  unfold cmean
  have hnum : mean E.design (fun z => @ite ℝ (z i = b)
      (Classical.propDecidable _) (E.outcome i z) 0) =
      mean E.design (fun z => if z i = b then E.outcome i z else 0) := by
    congr 1
    funext z
    by_cases h : z i = b <;> simp [h]
  rw [hnum]
  change mean E.design (fun z => if z i = b then E.outcome i z else 0) /
    marginal E i b = _
  apply (div_eq_iff (ne_of_gt (marginal_pos E hBER i b))).2
  rw [conditional_numerator_split E hBER, potential_mean_split E hBER]
  have hq : (if b then marginal E i true else 1-marginal E i true) =
      marginal E i b := by
    cases b
    · simp only [Bool.false_eq_true, if_false]
      linarith [marginal_partition E i]
    · simp
  rw [hq]
  ring

 theorem eate_eq_adse {n : ℕ} (E : Experiment n) (hBER : Bernoulli E) :
    eate E = adse E := by
  rw [eate_finite_identity]
  unfold adse
  simp_rw [conditional_observed_eq_potential_mean E hBER]

 theorem ht_unbiased {n : ℕ} (E : Experiment n) (hBER : Bernoulli E) :
    mean E.design (ht E) = eate E := by
  rw [ht_unbiased_ADSE E (fun i => ⟨marginal_pos E hBER i true,
    marginal_pos E hBER i false⟩), eate_eq_adse E hBER]


end
end BernoulliCompletion


/-- T2's Bernoulli specialization: Definition 10 becomes a coverage guarantee
after a positive lower bound on (n/d_AVG)Var(HT) is imposed. The interval is
centered on the unbiased HT estimator for EATE, with nonnegative estimated variance. -/
theorem bernoulli_corrected_coverage (S : Study) (k q s α : ℝ)
    (hReg : RegularSequence S k q s) (hBER : ∀ t, Bernoulli (S.experiment t))
    (Vhat : (t : ℕ) → Assignment (S.N t) → ℝ)
    (hVhat : ∀ t z, 0 ≤ Vhat t z) (hα : 0 < α ∧ α < 1)
    (hCons : Conservative S Vhat)
    (hScale : PositiveLiminf (fun t => size S t/dAvg (S.experiment t)*
      var (S.experiment t).design (ht (S.experiment t)))) :
    (∀ η, 0 < η → η < 1 → Tendsto (fun t => prob (S.experiment t).design
      (fun z => Vhat t z < (1-η)*var (S.experiment t).design (ht (S.experiment t))))
      atTop (nhds 0)) ∧
    1-α ≤ Filter.liminf (fun t => prob (S.experiment t).design
      (fun z => Covered (ht (S.experiment t) z) (eate (S.experiment t)) (Vhat t z) α)) atTop := by
  have hcontrol := conservative_relative_control S Vhat hCons hScale
  refine ⟨hcontrol.1, ?_⟩
  exact finite_asymptotic_plugin_coverage S (fun t => ht (S.experiment t)) Vhat
    (fun t => eate (S.experiment t))
    (fun t => BernoulliCompletion.ht_unbiased (S.experiment t) (hBER t))
    hcontrol.2 hVhat α hα hcontrol.1


/-- T35, under no interference every assignment-conditional ATE equals the
usual ATE, and averaging under any design preserves this value (Definitions 1–3). -/
theorem no_interference_eate {n : ℕ} (E : Experiment n) (h : NoInterference E) :
    (∀ z, ateAt E z = ate E) ∧ eate E = ate E := by
  have hp : ∀ i b z, potential E i b z = potential E i b (fun _ => false) := by
    intro i b z
    apply h i
    simp [Function.update]
  have ha : ∀ z, ateAt E z = ate E := by
    intro z
    simp only [ateAt, ate, effect, hp]
  refine ⟨ha, ?_⟩
  change mean E.design (fun z => ateAt E z) = ate E
  simp_rw [ha]
  exact mean_const E.design (ate E)

/-- T35, Definitions 1–4 and Lemma A8: EATE reduces to ATE under no
interference, the two displayed finite-sum forms hold, and Bernoulli
randomization makes EATE=ADSE. Every design is permitted in the first parts. -/
theorem estimand_identities {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    (NoInterference E → (∀ z, ateAt E z = ate E) ∧ eate E = ate E) ∧
    eate E = (∑ i, (mean E.design (potential E i true) -
      mean E.design (potential E i false))) / n ∧
    ((∀ i, 0 < marginal E i true ∧ marginal E i true < 1) →
      adse E = (∑ i, (cmean E.design (fun z => z i = true) (potential E i true) -
        cmean E.design (fun z => z i = false) (potential E i false))) / n) ∧
    (Bernoulli E → eate E = adse E) := by
  have hunit (i : Fin n) (b : Bool) :
      cmean E.design (fun z => z i = b) (E.outcome i) =
        cmean E.design (fun z => z i = b) (potential E i b) := by
    unfold cmean
    congr 1
    apply congrArg (mean E.design)
    funext z
    by_cases hz : z i = b
    · simp only [hz, if_true]
      unfold potential
      rw [← hz, Function.update_eq_self]
    · simp only [hz, if_false]
  refine ⟨no_interference_eate E, eate_finite_identity E, ?_,
    BernoulliCompletion.eate_eq_adse E⟩
  intro hp
  unfold adse
  simp_rw [hunit]

/-- T36, Lemma 1 (p. 681): the full finite chain relating the average
interference dependence to C1, C2 and C_infinity, without design assumptions. -/
theorem interference_count_bounds {n : ℕ} (hn : 0 < n) (E : Experiment n) :
    max (C1 E) (Cinf E ^ 2/(n:ℝ)) ≤ dAvg E ∧
    dAvg E ≤ C2 E ^ 2 ∧ C2 E ^ 2 ≤ Cinf E ^ 2 := by
  classical
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hI (i j : Fin n) : 0 ≤ I E i j := by
    unfold I
    split_ifs <;> norm_num
  have hd (i j : Fin n) : 0 ≤ d E i j := by
    unfold d
    split_ifs <;> norm_num
  have hout (i : Fin n) : 0 ≤ outgoing E i :=
    Finset.sum_nonneg (fun j _ => hI i j)
  have hId (i j : Fin n) : I E i j ≤ d E i j := by
    by_cases h : Interferes E i j
    · have hD : Dependent E i j := ⟨i, Or.inl rfl, h⟩
      simp [I, d, h, hD]
    · simpa [I, h] using hd i j
  have hprod (i j ℓ : Fin n) : I E ℓ i*I E ℓ j ≤ d E i j := by
    by_cases hi : Interferes E ℓ i
    · by_cases hj : Interferes E ℓ j
      · have hD : Dependent E i j := ⟨ℓ, hi, hj⟩
        simp [I, d, hi, hj, hD]
      · simpa [I, hj] using hd i j
    · simpa [I, hi] using hd i j
  have hdu (i j : Fin n) : d E i j ≤ ∑ ℓ, I E ℓ i*I E ℓ j := by
    by_cases hD : Dependent E i j
    · obtain ⟨ℓ, hi, hj⟩ := hD
      have hs := Finset.single_le_sum
        (fun k (_ : k ∈ Finset.univ) => mul_nonneg (hI k i) (hI k j))
        (Finset.mem_univ ℓ)
      have hD' : Dependent E i j := ⟨ℓ, hi, hj⟩
      simpa [I, d, hi, hj, hD'] using hs
    · simpa [d, hD] using
        Finset.sum_nonneg (fun ℓ (_ : ℓ ∈ Finset.univ) =>
          mul_nonneg (hI ℓ i) (hI ℓ j))
  have hid (ℓ : Fin n) :
      (∑ i, ∑ j, I E ℓ i*I E ℓ j) = outgoing E ℓ^2 := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, outgoing, pow_two]
  have hsq (ℓ : Fin n) : outgoing E ℓ^2 ≤ ∑ i, degree E i := by
    rw [← hid ℓ]
    exact Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ => hprod i j ℓ))
  have ht : (∑ i, ∑ j, ∑ ℓ, I E ℓ i*I E ℓ j) =
      ∑ ℓ, outgoing E ℓ^2 := by
    calc
      _ = ∑ i, ∑ ℓ, ∑ j, I E ℓ i*I E ℓ j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ ℓ, ∑ i, ∑ j, I E ℓ i*I E ℓ j := Finset.sum_comm
      _ = _ := by simp only [hid]
  have hC2 : C2 E^2 = (∑ ℓ, outgoing E ℓ^2)/(n:ℝ) := by
    exact Real.sq_sqrt (div_nonneg
      (Finset.sum_nonneg (fun ℓ _ => sq_nonneg _)) (le_of_lt hnR))
  have hfin := Set.finite_range (outgoing E)
  have hne : (Set.range (outgoing E)).Nonempty :=
    ⟨outgoing E ⟨0, hn⟩, Set.mem_range_self _⟩
  obtain ⟨ℓ, hℓ⟩ := hne.csSup_mem hfin
  have hmax (i : Fin n) : outgoing E i ≤ Cinf E :=
    le_csSup hfin.bddAbove (Set.mem_range_self i)
  have hCinf : 0 ≤ Cinf E := (hout ⟨0, hn⟩).trans (hmax ⟨0, hn⟩)
  refine ⟨max_le ?_ ?_, ?_, ?_⟩
  · unfold C1 dAvg
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hId i j)))
      (le_of_lt hnR)
  · unfold dAvg
    have hℓ' : outgoing E ℓ = Cinf E := hℓ
    rw [← hℓ']
    exact div_le_div_of_nonneg_right (hsq ℓ) (le_of_lt hnR)
  · rw [hC2]
    unfold dAvg degree
    apply div_le_div_of_nonneg_right _ (le_of_lt hnR)
    calc
      _ ≤ ∑ i, ∑ j, ∑ ℓ, I E ℓ i*I E ℓ j :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hdu i j))
      _ = _ := ht
  · rw [hC2]
    calc
      _ ≤ (∑ _ : Fin n, Cinf E^2)/(n:ℝ) :=
        div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun i _ => (sq_le_sq₀ (hout i) hCinf).2 (hmax i)))
          (le_of_lt hnR)
      _ = Cinf E^2 := by simp [ne_of_gt hnR]

/-- T37, Proposition 12 (p. 695): for any two designs with the same outcomes,
bounded unit-level effects give |EATE_P-EATE_Q|≤2 k_tau δ(P,Q). -/
theorem external_validity_total_variation {n : ℕ} (hn : 0 < n)
    (E : Experiment n) (Q : Law (Assignment n)) (K : ℝ) (hK : BoundedEffects E K) :
    |eate E-eate {E with design := Q}| ≤ 2*K*totalVariation E.design Q := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hab : ∀ z, |ateAt E z| ≤ K := by
    intro z
    calc
      |ateAt E z| = |∑ i, effect E i z| / (n:ℝ) := by
        simp [ateAt, abs_div, abs_of_pos hnR]
      _ ≤ (∑ i, |effect E i z|)/(n:ℝ) :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (le_of_lt hnR)
      _ ≤ (∑ _ : Fin n, K)/(n:ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hK i z)) (le_of_lt hnR)
      _ = K := by simp [ne_of_gt hnR]
  have he : eate E-eate {E with design := Q} =
      ∑ z, (E.design.mass z-Q.mass z)*ateAt E z := by
    change (∑ z, E.design.mass z*ateAt E z)-(∑ z, Q.mass z*ateAt E z) = _
    rw [← Finset.sum_sub_distrib]
    simp only [sub_mul]
  rw [he]
  calc
    _ ≤ ∑ z, |(E.design.mass z-Q.mass z)*ateAt E z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, |E.design.mass z-Q.mass z| *K := by
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hab z) (abs_nonneg _)
    _ = 2*K*totalVariation E.design Q := by
      simp only [totalVariation, ← Finset.sum_mul]
      ring


/-- T6/T40: the outcome construction on the selected subsequence, Supplement A
p. 6, using a reference design to determine its marginal assignment probabilities. -/
def p1Outcome {n : ℕ} (hn : 0 < n) (E : Experiment n) (M : ℕ)
    (i : Fin n) (z : Assignment n) : ℝ :=
  if i.val < M then (n:ℝ)/(M:ℝ)*bit (z ⟨0,hn⟩)*
    (bit (z i)*marginal E i true - (1-bit (z i))*marginal E i false) else 0


/-- T51 finite Lemma A30, Supplement A p. 36: the three-point law has mean
zero, variance alpha and exactly alpha mass at the Chebyshev cutoff. -/
theorem chebyshev_three_point_sharp (α : ℝ) (hα : 0 < α ∧ α < 1) :
    mean (sharpLaw α hα) sharpValue = 0 ∧ var (sharpLaw α hα) sharpValue = α ∧
    prob (sharpLaw α hα) (fun i => |sharpValue i| ≥ 1) = α ∧
    prob (sharpLaw α hα) (fun i => |sharpValue i-mean (sharpLaw α hα) sharpValue| ≥
      Real.sqrt (var (sharpLaw α hα) sharpValue/α)) = α := by
  have hm : mean (sharpLaw α hα) sharpValue = 0 := by
    simp [mean, sharpLaw, sharpValue, Fin.sum_univ_succ]
  have hv : var (sharpLaw α hα) sharpValue = α := by
    simp [var, cov, hm, mean, sharpLaw, sharpValue, Fin.sum_univ_succ]
  have ht : prob (sharpLaw α hα) (fun i => |sharpValue i| ≥ 1) = α := by
    norm_num [prob, mean, sharpLaw, sharpValue, Fin.sum_univ_succ]
  refine ⟨hm, hv, ht, ?_⟩
  simpa [hm, hv, div_self (ne_of_gt hα.1)] using ht




/-- T5, P009-E014's full-cube cluster outcomes, here with fair Bernoulli
design (also allowed by the arbitrary-design proof step). Paper unit 1 affects
the first h_n units; all other outcomes are zero. -/
def limsupExperiment (n : ℕ) (hn : 0 < n) : Experiment n :=
  fairExperiment n (fun i z => if i.val < limsupCluster n then bit (z ⟨0,hn⟩) else 0)

/-- The explicit growing cluster family for the limsup-selection counterexample. -/
def limsupStudy : Study :=
  { sparseStudy with
    experiment := fun t => limsupExperiment (t+1) (by omega) }




/-- T15, P009-E010: every unit has the no-interference outcome z_i. -/
def identityExperiment (n : ℕ) : Experiment n := fairExperiment n (fun i z => bit (z i))

/-- T15's growing fair no-interference family, with all coordinates included. -/
def identityStudy : Study := {sparseStudy with experiment := fun t => identityExperiment (t+1)}








end
end AronowAudit.P009

