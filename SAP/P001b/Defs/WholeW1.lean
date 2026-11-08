import Mathlib
import SAP.P001b.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Classical Topology

noncomputable section

universe u v

/-- Uniform probability on the unit interval, used in nonvacuity checks. -/
def W1Uniform : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- A fair binary treatment. -/
def W1Fair : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

def W1BinaryValue (b : Bool) : ℝ := if b then 1 else 0

/-- Conditional independence by conditional-expectation factorization of measurable
events. This is the usual version-invariant definition. -/
def W1CI {Ω E F G : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace G] (μ : Measure Ω)
    (X : Ω → E) (_hX : Measurable X) (Y : Ω → F) (Z : Ω → G) : Prop :=
  ∀ (A : Set F) (B : Set G), MeasurableSet A → MeasurableSet B →
    (μ[(fun ω => if Y ω ∈ A ∧ Z ω ∈ B then (1 : ℝ) else 0) |
      MeasurableSpace.comap X inferInstance]) =ᵐ[μ]
    (fun ω => (μ[(fun ω => if Y ω ∈ A then (1 : ℝ) else 0) |
      MeasurableSpace.comap X inferInstance]) ω *
      (μ[(fun ω => if Z ω ∈ B then (1 : ℝ) else 0) |
        MeasurableSpace.comap X inferInstance]) ω)

/-- A measurable, integrable version of a conditional expectation function. -/
def W1CEF {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (Y : Ω → ℝ) (m : E → ℝ) : Prop :=
  Measurable m ∧ Integrable Y μ ∧ Integrable (m ∘ X) μ ∧
    ∀ A : Set E, MeasurableSet A →
      (∫ ω in X ⁻¹' A, Y ω ∂μ) = ∫ ω in X ⁻¹' A, m (X ω) ∂μ

def W1JointMass {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → E) (D : Ω → ℝ) (d : ℝ) (x : E) : ℝ :=
  probability μ {ω | X ω = x ∧ D ω = d}

/-- Propensity on positive-mass covariate cells; the arbitrary version on null cells
is fixed to one half. It is not interpreted as a conditional ratio on a null cell. -/
def W1CellPropensity {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → E) (D : Ω → ℝ) (x : E) : ℝ :=
  if 0 < probability μ {ω | X ω = x} then
    W1JointMass μ X D 1 x / probability μ {ω | X ω = x}
  else 1 / 2

/-- Conditional PMF in an arm. Every use of this definition assumes both arms have
positive mass, as presupposed by Supp[D] = {0,1}. -/
def W1ArmPMF {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → E) (D : Ω → ℝ) (d : ℝ) (x : E) : ℝ :=
  W1JointMass μ X D d x / probability μ {ω | D ω = d}

/-- Conditional covariate law in a positive-mass arm. -/
def W1ArmLaw {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (D : Ω → ℝ) (d : ℝ) : Measure E :=
  (μ {ω | D ω = d})⁻¹ • ((μ.restrict {ω | D ω = d}).map X)

/-- General overlap of covariate laws. In the usual measure-theoretic convention,
continuous density supports are understood modulo null sets. Thus complete overlap
means that the two conditional laws and the marginal law have the same null sets.
The positive-probability zero/one-region assertions do not assume uniform positivity. -/
def W1GeneralOverlap : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ),
    Measurable X → Measurable D → (∀ ω, D ω = 0 ∨ D ω = 1) →
    0 < probability μ {ω | D ω = 0} → 0 < probability μ {ω | D ω = 1} →
    ∀ p : E → ℝ, W1CEF μ X D p →
      ((∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1 - ε) →
        (W1ArmLaw μ X D 1 ≪ μ.map X) ∧ (μ.map X ≪ W1ArmLaw μ X D 1) ∧
        (W1ArmLaw μ X D 0 ≪ μ.map X) ∧ (μ.map X ≪ W1ArmLaw μ X D 0)) ∧
      (∀ A : Set E, MeasurableSet A → 0 < probability μ (X ⁻¹' A) →
        ((∀ᵐ ω ∂μ.restrict (X ⁻¹' A), p (X ω) = 0) →
          probability μ {ω | X ω ∈ A ∧ D ω = 1} = 0 ∧
          0 < probability μ {ω | X ω ∈ A ∧ D ω = 0}) ∧
        ((∀ᵐ ω ∂μ.restrict (X ⁻¹' A), p (X ω) = 1) →
          probability μ {ω | X ω ∈ A ∧ D ω = 0} = 0 ∧
          0 < probability μ {ω | X ω ∈ A ∧ D ω = 1}))

/-- All discrete support identities and both directions that are actually valid. -/
def W1DiscreteOverlap : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ),
    Measurable X → Measurable D → (∀ ω, D ω = 0 ∨ D ω = 1) →
    0 < probability μ {ω | D ω = 0} → 0 < probability μ {ω | D ω = 1} →
    let S := {x | 0 < probability μ {ω | X ω = x}}
    let p := W1CellPropensity μ X D
    let S1 := {x | 0 < W1ArmPMF μ X D 1 x}
    let S0 := {x | 0 < W1ArmPMF μ X D 0 x}
    S1 = {x | x ∈ S ∧ 0 < p x} ∧ S0 = {x | x ∈ S ∧ p x < 1} ∧
    (S1 = S0 ↔ ∀ x ∈ S, 0 < p x ∧ p x < 1) ∧
    ((∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, ε < p x ∧ p x < 1 - ε) → S1 = S0) ∧
    (S.Finite → S1 = S0 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, ε < p x ∧ p x < 1 - ε)

/-- Coherently normalized density versions have the literal support identity too.
The reference space may be continuous: this algebra does not require countability.
Here a,b are the strictly positive normalizers of the two joint arm densities. -/
def W1CoherentOverlap : Prop :=
  ∀ {E : Type v} (t c : E → ℝ) (a b : ℝ),
    (∀ x, 0 ≤ t x) → (∀ x, 0 ≤ c x) → 0 < a → 0 < b →
    ({x | 0 < t x / a} = {x | 0 < c x / b} ↔
      ∀ x, 0 < t x + c x → 0 < t x / (t x + c x) ∧ t x / (t x + c x) < 1) ∧
    ((∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < t x + c x →
      ε < t x / (t x + c x) ∧ t x / (t x + c x) < 1 - ε) →
      {x | 0 < t x / a} = {x | 0 < c x / b})

def W1OverlapT (k : ℕ) : ℝ := (1 / 3 : ℝ) ^ (k + 1)
def W1OverlapC (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 2)

local instance : MeasurableSpace (ℕ × Bool) := ⊤

/-- The normalized infinite joint law used in the nonconverse example. -/
def W1GeometricLaw : Measure (ℕ × Bool) :=
  Measure.sum (fun z => ENNReal.ofReal (if z.2 then W1OverlapT z.1 else W1OverlapC z.1) •
    Measure.dirac z)

def W1InfiniteOverlap : Prop :=
  Summable W1OverlapT ∧ Summable W1OverlapC ∧
  (∑' k, W1OverlapT k) = 1 / 2 ∧ (∑' k, W1OverlapC k) = 1 / 2 ∧
  IsProbabilityMeasure W1GeometricLaw ∧
  (∀ s : Set (ℕ × Bool), MeasurableSet s) ∧
  (∀ k, W1JointMass W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) 1 k = W1OverlapT k ∧
    W1JointMass W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) 0 k = W1OverlapC k) ∧
  probability W1GeometricLaw {z | W1BinaryValue z.2 = 0} = 1 / 2 ∧
  probability W1GeometricLaw {z | W1BinaryValue z.2 = 1} = 1 / 2 ∧
  {k | 0 < probability W1GeometricLaw {z | z.1 = k}} = Set.univ ∧
  {k | 0 < W1ArmPMF W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) 1 k} = Set.univ ∧
  {k | 0 < W1ArmPMF W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) 0 k} = Set.univ ∧
  ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ k,
    ε < W1CellPropensity W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) k ∧
    W1CellPropensity W1GeometricLaw Prod.fst (fun z => W1BinaryValue z.2) k < 1 - ε

/-- P001-T20. Location: pp. 271–272 (PDF pp. 289–290), Definition 7.3.1,
Theorem 7.3.2 and the surrounding corrected discussion.
The usual measure-theoretic conditions are assumed. Uniform propensity positivity
implies complete overlap of the conditional covariate laws; positive-probability
zero/one propensity regions prevent overlap. For discrete covariates the two arm
PMF supports have the stated propensity descriptions, overlap is equivalent to
pointwise positivity, and finite support yields a uniform bound. The specified
infinite geometric joint law has complete overlap without a uniform bound.
Density supports are version-invariant modulo null sets; coherently normalized
joint-density versions also satisfy the exact pointwise support identity. -/
def T20WholeStatement : Prop :=
  W1GeneralOverlap.{u, v} ∧ W1DiscreteOverlap.{u, v} ∧ W1InfiniteOverlap ∧ W1CoherentOverlap.{v}

/-- Conditional observed mean on a covariate cell within an arm. The ratio is used
only on a positive-mass cell; its version at null cells is zero. -/
def W1ArmMean {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → E)
    (Y0 Y1 D : Ω → ℝ) (d : ℝ) (x : E) : ℝ :=
  let C := {ω | X ω = x ∧ D ω = d}
  if 0 < probability μ C then
    (∫ ω in C, Y1 ω * D ω + Y0 ω * (1 - D ω) ∂μ) / probability μ C
  else 0

/-- P001-T22. Location: p. 278 (PDF p. 296), corrected ignorability discussion;
Theorem 7.1.13, p. 248 (PDF p. 266).
The usual measure-theoretic conditions are assumed, including measurable response
sections on the covariate space and integrability where expectations are used.
(i) Complete coding can coexist with failure of ignorability in the stated four-atom
electorate model, with constant covariates and positivity.
(ii) A fixed measurable response to description and treatment alone implies
conditional independence of the potential-outcome pair and treatment given X.
(iii) Under explicit conditional independence and uniform positivity, discrete
covariates give the ATE as the difference of the two absolutely convergent
population-weighted observed-arm conditional-mean sums. The arm means are actual
positive-cell ratios, not extra model assumptions.
All three canonical clauses are stated in full under these conditions. -/
def T22WholeStatement : Prop :=
  (T21Statement ∧ (∃ response : ℝ → ℝ → ℝ → ℝ,
    ∀ i d, potentialVoteShare d i = response 0 d (electorateType i)) ∧
    (1 / 4 : ℝ) < finiteConditionalMean voterMass displayedGender (fun _ => 0) 0 ∧
    finiteConditionalMean voterMass displayedGender (fun _ => 0) 0 < 1 - (1 / 4 : ℝ)) ∧
  (∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (D : Ω → ℝ), Measurable D → ∀ response : E → ℝ → ℝ,
      Measurable (fun x => response x 0) → Measurable (fun x => response x 1) →
      W1CI μ X hX (fun ω => (response (X ω) 0, response (X ω) 1)) D) ∧
  (∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y0 Y1 D : Ω → ℝ), Measurable Y0 → Measurable Y1 → Measurable D →
    Integrable Y0 μ → Integrable Y1 μ → (∀ ω, D ω = 0 ∨ D ω = 1) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ x, 0 < probability μ {ω | X ω = x} →
      ε < W1CellPropensity μ X D x ∧ W1CellPropensity μ X D x < 1 - ε) →
    W1CI μ X hX (fun ω => (Y0 ω, Y1 ω)) D →
    let m0 := W1ArmMean μ X Y0 Y1 D 0
    let m1 := W1ArmMean μ X Y0 Y1 D 1
    Summable (fun x => m0 x * probability μ {ω | X ω = x}) ∧
    Summable (fun x => m1 x * probability μ {ω | X ω = x}) ∧
    (∫ ω, Y1 ω - Y0 ω ∂μ) =
      (∑' x, m1 x * probability μ {ω | X ω = x}) -
      (∑' x, m0 x * probability μ {ω | X ω = x}))

/-- P001-T26. Location: p. 20 (PDF p. 38), first bulleted list, third bullet.
For every discrete real random variable whose PMF vanishes off the integers, the
probability below four is the sum of all integer masses through three. Its excess
over the masses at one, two and three is exactly the probability of a nonpositive
value, and the printed equality holds exactly when that probability is zero.
For the fair die, the displayed specialization is three sixths, equal to one half.
The usual measure-theoretic conditions are assumed. Null sample points with noninteger values are allowed. -/
def T26WholeStatement : Prop :=
  (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → (Set.range X).Countable →
    (∀ x : ℝ, (¬ ∃ k : ℤ, (k : ℝ) = x) → probability μ {ω | X ω = x} = 0) →
    let q : ℤ → ℝ := fun k => probability μ {ω | X ω = (k : ℝ)}
    Summable q ∧ (∑' k, q k) = 1 ∧
    probability μ {ω | X ω < 4} = integerCDF q 3 ∧
    probability μ {ω | X ω < 4} - (∑ k ∈ Finset.Icc (1 : ℤ) 3, q k) =
      probability μ {ω | X ω ≤ 0} ∧
    (probability μ {ω | X ω < 4} = (∑ k ∈ Finset.Icc (1 : ℤ) 3, q k) ↔
      probability μ {ω | X ω ≤ 0} = 0)) ∧
  ((∀ i, 0 ≤ dieMass i) ∧ (∑ i, dieMass i) = 1 ∧
    (∀ x : ℝ, finiteProbability dieMass (fun i => dieValue i = x) =
      if x ∈ ({1, 2, 3, 4, 5, 6} : Set ℝ) then 1 / 6 else 0) ∧
    finiteProbability dieMass (fun i => dieValue i < 4) =
      (∑ k ∈ Finset.Icc (1 : ℤ) 3,
        finiteProbability dieMass (fun i => dieValue i = (k : ℝ))) ∧
    finiteProbability dieMass (fun i => dieValue i < 4) = 3 / 6 ∧
    (3 / 6 : ℝ) = 1 / 2)

local instance : MeasurableSpace DyadicIndex := ⊤

/-- The explicit law on the countable atom space; its sigma-algebra contains every subset. -/
def W1DyadicLaw : Measure DyadicIndex :=
  Measure.sum (fun i => ENNReal.ofReal (dyadicWeight i) • Measure.dirac i)

def W1DyadicRationals : Set ℝ :=
  {x | 0 < x ∧ x < 1 ∧ ∃ a n : ℕ, x = (a : ℝ) / (2 : ℝ) ^ n}

/-- P001-T27. Location: p. 23 (PDF p. 41), Example 1.2.13; Definition 1.2.4,
p. 18 (PDF p. 36).
The specified dyadic atom law has level masses 2^(-(m+1)) summing to one, all
subsets measurable, and an injective random variable with exactly the dyadic
rationals in (0,1) as its countable range. Each value has its stated positive mass.
Its CDF is the stated mass sum, strictly increases on (0,1), and is constant on no
nonempty open subinterval there. It gives one third mass zero and is continuous
there, while constant on no neighborhood of one third. This supplies all parts
of the canonical counterexample to local flatness at every non-jump point.
The usual measure-theoretic conditions are assumed. -/
def T27WholeStatement : Prop :=
  (∀ m : ℕ, (∑ k : Fin (2 ^ m), dyadicWeight ⟨m, k⟩) = (1 / 2 : ℝ) ^ (m + 1)) ∧
  (∑' m : ℕ, ∑ k : Fin (2 ^ m), dyadicWeight ⟨m, k⟩) =
    (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 1)) ∧
  (∑' m : ℕ, (1 / 2 : ℝ) ^ (m + 1)) = 1 ∧
  Summable dyadicWeight ∧ (∑' i, dyadicWeight i) = 1 ∧
  (∀ i, 0 < dyadicWeight i) ∧
  (∀ s : Set DyadicIndex, MeasurableSet s) ∧ IsProbabilityMeasure W1DyadicLaw ∧
  Measurable dyadicLocation ∧ Function.Injective dyadicLocation ∧
  Set.range dyadicLocation = W1DyadicRationals ∧ (Set.range dyadicLocation).Countable ∧
  (∀ i, W1DyadicLaw {i} = ENNReal.ofReal (dyadicWeight i) ∧
    probability W1DyadicLaw {j | dyadicLocation j = dyadicLocation i} = dyadicWeight i ∧
    0 < probability W1DyadicLaw {j | dyadicLocation j = dyadicLocation i}) ∧
  (∀ x : ℝ, distributionFunction W1DyadicLaw dyadicLocation x = dyadicDistributionFunction x) ∧
  (∀ a b : ℝ, 0 < a → a < b → b < 1 →
    dyadicDistributionFunction a < dyadicDistributionFunction b) ∧
  (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    ¬ ∃ c : ℝ, ∀ x ∈ Set.Ioo a b, dyadicDistributionFunction x = c) ∧
  W1DyadicLaw {i | dyadicLocation i = (1 / 3 : ℝ)} = 0 ∧
  ContinuousAt dyadicDistributionFunction (1 / 3) ∧
  ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x - 1 / 3| < ε →
    dyadicDistributionFunction x = dyadicDistributionFunction (1 / 3)

/-- P001-T37. Location: p. 37 (PDF p. 55), Theorem 1.3.13, and p. 38
(PDF p. 56), Definition 1.3.14.
The extended nonnegative marginal slice integral is finite almost everywhere.
Every finite nonnegative version agreeing with it almost everywhere is a marginal
PDF and gives the CDF at every threshold, without a Borel measurability premise
on the version. At every selected integrable slice with strictly positive integral,
the conditional ratio is integrable, nonnegative and normalized. This last assertion
needs no global measurability assumption on the joint function beyond the existence
of that selected integral. The usual measure-theoretic conditions are assumed. -/
def T37WholeStatement : Prop :=
  (∀ (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (f : ℝ × ℝ → ℝ), JointDensity ν f →
    (∀ᵐ y ∂volume, (∫⁻ x : ℝ, ENNReal.ofReal (f (x, y))) < ∞) ∧
    ∀ g : ℝ → ℝ, (∀ y, 0 ≤ g y) →
      (∀ᵐ y ∂volume, ENNReal.ofReal (g y) = (∫⁻ x : ℝ, ENNReal.ofReal (f (x, y)))) →
      Density (ν.map Prod.snd) g ∧
      ∀ y : ℝ, probability (ν.map Prod.snd) (Set.Iic y) = ∫ v in Set.Iic y, g v) ∧
  (∀ f : ℝ × ℝ → ℝ, (∀ xy, 0 ≤ f xy) →
    ∀ x : ℝ, Integrable (fun y => f (x, y)) volume → (0 < ∫ y, f (x, y)) →
    Integrable (fun y => f (x, y) / (∫ t, f (x, t))) volume ∧
    (∀ y, 0 ≤ f (x, y) / (∫ t, f (x, t))) ∧
    (∫ y, f (x, y) / (∫ t, f (x, t))) = 1)

end
end SAP.P001b
