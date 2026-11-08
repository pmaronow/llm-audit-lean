import Mathlib
import SAP.P025b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

/-- The normalized total weight of the observations with the indicated binary outcome. -/
def binaryClassSum {n : ℕ} (y w : Fin n → ℝ) (β b : ℝ) : ℝ :=
  ∑ i with y i = b, β * w i

/-- The derivation of the binary formula, including the boundary cases of the sample. -/
def BinaryDerivation : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i = 0 ∨ y i = 1) →
    ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
    let p := populationMean y
    let γ := β / α
    ((Finset.univ.filter (fun i => y i = 1)).card : ℝ) = n * p ∧
    ((Finset.univ.filter (fun i => y i = 0)).card : ℝ) = n * (1-p) ∧
    (∀ w : Fin n → ℝ, weightBox α β w →
      let A := binaryClassSum y w β 1
      let C := binaryClassSum y w β 0
      normBox γ (fun i => β*w i) ∧
      ratio y (fun _ => 1) w = A/(A+C) ∧
      (n*p ≤ A ∧ A ≤ γ*(n*p)) ∧
      (n*(1-p) ≤ C ∧ C ≤ γ*(n*(1-p))) ∧
      (n : ℝ) ≤ A+C ∧ 0 < A+C) ∧
    (∀ a c : ℝ, a ∈ Set.Icc (n*p) (γ*(n*p)) →
      c ∈ Set.Icc (n*(1-p)) (γ*(n*(1-p))) → 0 < a+c) ∧
    (∀ a a' c : ℝ, a ∈ Set.Icc (n*p) (γ*(n*p)) →
      a' ∈ Set.Icc (n*p) (γ*(n*p)) →
      c ∈ Set.Icc (n*(1-p)) (γ*(n*(1-p))) →
      a ≤ a' → a/(a+c) ≤ a'/(a'+c)) ∧
    (∀ a c c' : ℝ, a ∈ Set.Icc (n*p) (γ*(n*p)) →
      c ∈ Set.Icc (n*(1-p)) (γ*(n*(1-p))) →
      c' ∈ Set.Icc (n*(1-p)) (γ*(n*(1-p))) →
      c ≤ c' → a/(a+c') ≤ a/(a+c))

/-- P025-T20; p. 237 (PDF p. 3).
Every nonempty binary sample has exactly the displayed attainable interval and
optimization endpoints, including zero, one, and equal probability cases. The
classes have counts np and n(1-p); their normalized weight sums A and C give
the ratio A/(A+C), satisfy the stated bounds, and make that ratio nondecreasing
in A and nonincreasing in C.
-/
def T20WholeStatement : Prop := T20Statement ∧ BinaryDerivation

/-- The Supplement's two-coordinate objective, with its other coordinates fixed. -/
def twoCoordinateMean (c₁ c₂ p q u v x z : ℝ) : ℝ :=
  (c₁+x*p*u+z*q*v)/(c₂+x*p+z*q)

/-- P025-T12; pp. 239-240 (PDF pp. 5-6); Supplement p. 2.
The printed claim is false: the two-unit census with outcomes (0,1) and equal
probability bounds has threshold values 1/2 and different least stopping indices.
It refutes the Appendix implication and cut equivalence and both Supplement
equivalences. Its feasible box is a single
point; all sample and class endpoints and both means are 1/2. The first upper
cut is one and its physical optimizer and displayed value still give 1/2.
-/
def T12WholeStatement : Prop :=
  T12Statement ∧
  (∀ w : Fin 2 → ℝ, weightBox 1 1 w ↔ w = ![1,1]) ∧
  attainable binaryTwo (fun _ => 1) 1 1 = {(1/2 : ℝ)} ∧
  populationMean binaryTwo = 1/2 ∧
  classMean binaryTwo ![1,1] = 1/2 ∧
  (∀ j : Fin 2, classTotal censusDesign id j = 1) ∧
  (∀ j : Fin 2, ∀ ω : Fin 1, classCount censusDesign id j ω = 1) ∧
  (∀ j : Fin 2, (1 : ℝ)/classTotal censusDesign id j = 1) ∧
  lowerEndpoint binaryTwo (fun _ => 1) 1 1 = 1/2 ∧
  upperEndpoint binaryTwo (fun _ => 1) 1 1 = 1/2 ∧
  lowerEndpoint binaryTwo (classTotal censusDesign id) 1 1 = 1/2 ∧
  upperEndpoint binaryTwo (classTotal censusDesign id) 1 1 = 1/2 ∧
  (fun i : Fin 2 => (1 : ℝ)/1 * upperWeights 1 1 i) = ![1,1] ∧
  ((0 : ℝ)+1*1)/(1+1) = 1/2 ∧
  twoCoordinateMean 0 0 1 1 0 1 1 1 = 1/2 ∧
  ¬ (twoCoordinateMean 0 0 1 1 0 1 (1/1) (1/1) >
       twoCoordinateMean 0 0 1 1 0 1 (1/1) (1/1) ↔
       (0 : ℝ)*0-0+1*1*(0-1) < 0) ∧
  ¬ (twoCoordinateMean 0 0 1 1 0 1 (1/1) (1/1) >
       twoCoordinateMean 0 0 1 1 0 1 (1/1) (1/1) ↔
       (0 : ℝ)-0*1+1*1*(0-1) < 0)

/-- Assumption 1 as the independence and marginal laws of the replicated draws. -/
def ReplicationsIID {ι κ : Type*} [Fintype κ] [MeasurableSpace κ]
    (d : FiniteDesign ι κ) : Prop :=
  iIndepFun (fun r : ℕ => fun ω : ℕ → κ => ω r) (jointLaw d) ∧
  ∀ r : ℕ, (jointLaw d).map (fun ω : ℕ → κ => ω r) = (designPMF d).toMeasure

/-- The physical sum of selected weights in a class in the six-unit example. -/
def pairClassWeightSum (h : ℕ) (ω : ℕ → Fin 2 × Fin 2 × Fin 2)
    (w : Fin h × (Fin 3 × Fin 2) → ℝ) (j : Fin 3) : ℝ :=
  ∑ r : Fin h, w (r, (j, pairChoice (ω r.val) j))

/-- The two polynomial certificates and the three specified optimizer evaluations. -/
def PairPolynomialCertificates : Prop :=
  (∀ W : Fin 3 → ℝ, weightBox (1/4) (1/2) W →
    let N := 2*W 1+3*W 2
    let D := W 0+W 1+W 2
    0 < D ∧
    4*N-5*D = 3*(W 1-2)+7*(W 2-2)+5*(4-W 0) ∧ 0 ≤ 4*N-5*D ∧
    2*D-N = 2*(W 0-2)+(4-W 2) ∧ 0 ≤ 2*D-N ∧
    5/4 ≤ N/D ∧ N/D ≤ 2) ∧
  ratio threeOutcomes (fun _ => 1) ![4,2,2] = 5/4 ∧
  ratio threeOutcomes (fun _ => 1) ![2,4,4] = 2 ∧
  ratio threeOutcomes (fun _ => 1) ![2,2,4] = 2

/-- P025-T14; p. 238 (PDF p. 4).
The printed claim is false: the six-unit random pair design satisfies independent
Brewer replication and violates Assumption 2, yet every nonempty pooled sample
has endpoints 5/4 and 2 on every path. Both polynomial certificates and all three
optimizer evaluations hold. Pooled class sums lie in [2h,4h], give the displayed
ratio and its normalization by h, and map onto the entire class weight box.
-/
def T14WholeStatement : Prop :=
  T14Statement ∧ ReplicationsIID pairDesign ∧ PairPolynomialCertificates ∧
  (∀ j : Fin 3, ((Finset.univ.filter (fun i : Fin 3 × Fin 2 => i.1 = j)).card) = 2) ∧
  (∀ h : ℕ, 0 < h → ∀ ω : ℕ → Fin 2 × Fin 2 × Fin 2,
    (∀ j : Fin 3, (∑ r : Fin h, classCount pairDesign Prod.fst j (ω r.val)) = h) ∧
    (∀ w : Fin h × (Fin 3 × Fin 2) → ℝ, weightBox (1/4) (1/2) w →
      let A := pairClassWeightSum h ω w
      (∀ j, 2*(h : ℝ) ≤ A j ∧ A j ≤ 4*(h : ℝ)) ∧
      0 < A 0+A 1+A 2 ∧
      ratio (fun ri => threeOutcomes ri.2.1) (pooledIndicator pairDesign h ω) w =
        (2*A 1+3*A 2)/(A 0+A 1+A 2) ∧
      (2*A 1+3*A 2)/(A 0+A 1+A 2) =
        ratio threeOutcomes (fun _ => 1) (fun j => A j/h) ∧
      weightBox (1/4) (1/2) (fun j => A j/h)) ∧
    (∀ W : Fin 3 → ℝ, weightBox (1/4) (1/2) W →
      ∃ w : Fin h × (Fin 3 × Fin 2) → ℝ, weightBox (1/4) (1/2) w ∧
        ∀ j, pairClassWeightSum h ω w j / h = W j))

/-- Counts compatible with shares and a known original population size. -/
def sharesKnownSizeMeans {J : ℕ} (y q : Fin J → ℝ) (α β : ℝ) (N : ℕ) : Set ℝ :=
  {v | ∃ m : Fin J → ℕ, sharesCompatible α β q m ∧ (∑ j, m j) = N ∧ classMean y m = v}

/-- Compatibility parentheticals, independent of the existence premise of sharpness. -/
def CompatibilityExistence : Prop :=
  ∀ {J : ℕ}, 0 < J → ∀ q : Fin J → ℝ, (∀ j, 0 < q j) → (∑ j, q j) = 1 →
    ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
    (1 < β/α → ∃ m : Fin J → ℕ, sharesCompatible α β q m) ∧
    (β/α = 1 → ((∃ m : Fin J → ℕ, sharesCompatible α β q m) ↔ rationalVector q))

/-- Finite designs realize exactly the bounded class-total constraints. -/
def ClassDesignRealization : Prop :=
  ∀ {J : ℕ} (α β : ℝ), 0 < α → α ≤ β → β ≤ 1 →
    ∀ (mass : Fin J → ℝ) (m : Fin J → ℕ), absoluteCompatible α β mass m ↔
      (∀ j, 0 < m j) ∧
      ∃ d : FiniteDesign (Σ j : Fin J, Fin (m j)) ((Σ j : Fin J, Fin (m j)) → Bool),
        (∀ i, α ≤ inclusion d i ∧ inclusion d i ≤ β) ∧
        ∀ j, classTotal d Sigma.fst j = mass j

/-- The richer information can prevent sharpness, even with shares and size alone. -/
def RetainedInformationFailure : Prop :=
  absoluteCompatibleMeans binaryTwo ![2/3,4/3] (1/2) (3/4) = {(2/3 : ℝ)} ∧
  lowerEndpoint binaryTwo ![2/3,4/3] (1/2) (3/4) = 4/7 ∧
  upperEndpoint binaryTwo ![2/3,4/3] (1/2) (3/4) = 3/4 ∧
  sharesKnownSizeMeans binaryTwo ![1/3,2/3] (1/2) (3/4) 3 = {(2/3 : ℝ)} ∧
  lowerEndpoint binaryTwo ![1/3,2/3] (1/2) (3/4) = 4/7 ∧
  upperEndpoint binaryTwo ![1/3,2/3] (1/2) (3/4) = 3/4 ∧
  (4/7 : ℝ) < 2/3 ∧ (2/3 : ℝ) < 3/4

/-- P025-T15; p. 237 (PDF p. 3), echoed on pp. 235 and 238;
Supplement pp. 1-2.
Conditional only on positive limiting shares and with population size unrestricted,
the class box endpoints are the sharp infimum and supremum of compatible finite
population means. The box maps onto the proportion region; its rational points
are precisely finite population proportions, with the stated endpoint attainment
criteria. Compatibility is automatic at ratio greater than one and is equivalent
to rational shares at ratio one. Positive scaling preserves the objectives and
endpoints. Bounded class marginals are realized by finite sampling designs.
Absolute totals and known size give the stated integer calibration and outer
bounds; sharpness can fail with totals retained or with shares and size retained.
-/
def T15WholeStatement : Prop :=
  T15Statement ∧ CompatibilityExistence ∧ ClassDesignRealization ∧
  (∀ {J : ℕ}, 0 < J → ∀ (y q : Fin J → ℝ), (∀ j, 0 < q j) →
    ∀ (α β T : ℝ), 0 < α → α ≤ β → β ≤ 1 → 0 < T →
    (∀ W : Fin J → ℝ, weightBox α β W →
      ratio y (fun j => T*q j) W = ratio y q W) ∧
    attainable y (fun j => T*q j) α β = attainable y q α β ∧
    lowerEndpoint y (fun j => T*q j) α β = lowerEndpoint y q α β ∧
    upperEndpoint y (fun j => T*q j) α β = upperEndpoint y q α β) ∧
  RetainedInformationFailure

/-- The finite type of all subsets of the specified size, with no ordering of draws. -/
def QuotaDraw (N s : ℕ) := {t : Finset (Fin N) // t.card = s}

instance quotaDrawFintype (N s : ℕ) : Fintype (QuotaDraw N s) :=
  inferInstanceAs (Fintype {t : Finset (Fin N) // t.card = s})

instance quotaDrawMeasurableSpace (N s : ℕ) : MeasurableSpace (QuotaDraw N s) := ⊤

/-- The independent product of two finite sampling designs on disjoint populations. -/
def sumDesign {n₀ n₁ : ℕ} {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (d : FiniteDesign (Fin n₀) κ) (e : FiniteDesign (Fin n₁) κ') :
    FiniteDesign (Fin n₀ ⊕ Fin n₁) (κ × κ') where
  sample := fun ω => (d.sample ω.1).map Function.Embedding.inl ∪
    (e.sample ω.2).map Function.Embedding.inr
  probability := fun ω => d.probability ω.1 * e.probability ω.2
  nonnegative := fun ω => mul_nonneg (d.nonnegative ω.1) (e.nonnegative ω.2)
  total := by
    simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, e.total, mul_one]
    exact d.total

/-- Class zero is the left summand and class one the right summand. -/
def sumClass {n₀ n₁ : ℕ} : Fin n₀ ⊕ Fin n₁ → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

/-- Uniform, independent draws of exactly fifty zeros and one hundred ones. -/
def KnownSizeQuotaRealization (k : ℕ) : Prop :=
  ∃ d : FiniteDesign (Fin (1000-k) ⊕ Fin k)
      (QuotaDraw (1000-k) 50 × QuotaDraw k 100),
    (∀ ω, d.sample ω = ω.1.val.map Function.Embedding.inl ∪
      ω.2.val.map Function.Embedding.inr) ∧
    (∀ ω, d.probability ω =
      (1 / (Fintype.card (QuotaDraw (1000-k) 50) : ℝ)) *
      (1 / (Fintype.card (QuotaDraw k 100) : ℝ))) ∧
    (∀ i : Fin (1000-k), inclusion d (Sum.inl i) = 50 / ((1000-k : ℕ) : ℝ)) ∧
    (∀ i : Fin k, inclusion d (Sum.inr i) = 100 / (k : ℝ)) ∧
    (∀ i, (1/10 : ℝ) ≤ inclusion d i ∧ inclusion d i ≤ 1/5) ∧
    (∀ j : Fin 2, classTotal d sumClass j = (![50,100] : Fin 2 → ℝ) j) ∧
    (∀ ω, (d.sample ω).card = 150) ∧ ReplicationsIID d

/-- The positive statements preserved by the two sharpness counterexamples. -/
def CounterexamplePreservation : Prop :=
  (∀ m : Fin 2 → ℕ, absoluteCompatible (1/2) (3/4) ![2/3,4/3] m →
    (4/7 : ℝ) ≤ classMean binaryTwo m ∧ classMean binaryTwo m ≤ 3/4) ∧
  (∀ m : Fin 2 → ℕ, absoluteCompatible (1/10) (1/5) ![50,100] m →
    (1/2 : ℝ) ≤ classMean binaryTwo m ∧ classMean binaryTwo m ≤ 4/5) ∧
  IsGLB (compatibleMeans binaryTwo ![1/3,2/3] (1/2) (3/4)) (4/7) ∧
  IsLUB (compatibleMeans binaryTwo ![1/3,2/3] (1/2) (3/4)) (3/4) ∧
  IsGLB (compatibleMeans binaryTwo ![1/3,2/3] (1/10) (1/5)) (1/2) ∧
  IsLUB (compatibleMeans binaryTwo ![1/3,2/3] (1/10) (1/5)) (4/5)

/-- P025-T16; p. 237 (PDF p. 3); Supplement p. 2.
These examples refute the reading of the printed sharpness assertion that retains
absolute class totals, with population size also retained in the second example:
retained absolute totals can force the singleton mean
set {2/3} strictly within [4/7,3/4], even when Assumption 2 holds. With totals
(50,100) and size 1000 the exact means are k/1000 for 500 ≤ k ≤ 750, whose
maximum 3/4 is below the continuous upper endpoint 4/5. All four specified
weight vectors give the stated endpoints. Every such integer k is realized by
independent uniform quota sampling with the specified probabilities and totals;
the 500-zero, 500-one example has mean 1/2 and probabilities 1/10 and 1/5.
Independent replication holds, outer bounds remain valid, and shares alone
with unrestricted size have the corrected sharp endpoints.
-/
def T16WholeStatement : Prop :=
  T16Statement ∧ ReplicationsIID omitOneDesign ∧
  ratio binaryTwo ![2/3,4/3] ![4/3,2] = 3/4 ∧
  ratio binaryTwo ![2/3,4/3] ![2,4/3] = 4/7 ∧
  ratio binaryTwo ![50,100] ![5,10] = 4/5 ∧
  ratio binaryTwo ![50,100] ![10,5] = 1/2 ∧
  upperValue binaryTwo ![2/3,4/3] (3/2) 0 = 2/3 ∧
  lowerValue binaryTwo ![2/3,4/3] (3/2) 0 = 2/3 ∧
  (∀ m : Fin 2 → ℕ, absoluteCompatible (1/2) (3/4) ![2/3,4/3] m ↔
    (∀ j, 0 < m j) ∧
    (8/9 : ℝ) ≤ m 0 ∧ (m 0 : ℝ) ≤ 4/3 ∧
    (16/9 : ℝ) ≤ m 1 ∧ (m 1 : ℝ) ≤ 8/3) ∧
  (∀ m : Fin 2 → ℕ, absoluteCompatible (1/10) (1/5) ![50,100] m ↔
    (∀ j, 0 < m j) ∧ 250 ≤ m 0 ∧ m 0 ≤ 500 ∧ 500 ≤ m 1 ∧ m 1 ≤ 1000) ∧
  (∀ k : ℕ, 500 ≤ k → k ≤ 750 → KnownSizeQuotaRealization k) ∧
  classMean binaryTwo ![500,500] = 1/2 ∧
  CounterexamplePreservation

end
end SAP.P025b
