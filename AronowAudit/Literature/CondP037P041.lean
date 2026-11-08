import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.Basic
import AronowAudit.P037.P037_Bootstrap
import AronowAudit.P045.P045_Spillover

/-!
Statement-only assessment for cond-P037P041. No literature result is asserted
as a theorem. The additional inputs are the closed propositions `DevroyeGammaDirichlet`,
`HHDirectWithin`, and `HHDirectBetween`. The other seven records have no
validated conditional proposal; see the accompanying condmap.json.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal

namespace AronowAudit.Literature
universe u

/-- The open simplex in its ordinary free coordinates, independent of any
application. Devroye (1986), XI.4.1, p. 593. -/
def dirichletSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {p | (∀ i, 0 < p i) ∧ ∑ i, p i < 1}

/-- Append the dependent coordinate to free simplex coordinates. -/
noncomputable def simplexCompletion (k : ℕ) (p : Fin k → ℝ) : Fin (k+1) → ℝ :=
  fun i => if hi : i.val < k then p ⟨i.val, hi⟩ else 1 - ∑ j, p j

/-- The usual Dirichlet density relative to k-dimensional coordinate
Lebesgue measure. The last coordinate is 1-sum(p), not an additional
integration variable. Devroye (1986), XI.4.1, p. 593; explicit normalizer
cross-checked with DasGupta, Graduate Probability, Theorem 1.68 and
Definition 1.59, manuscript p. 139 (author-hosted gradprob.pdf). -/
noncomputable def dirichletFreeDensity (k : ℕ) (a : Fin (k+1) → ℝ)
    (p : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.Gamma (∑ i, a i) / ∏ i, Real.Gamma (a i)) *
    (∏ i : Fin k, Real.rpow (p i) (a i.castSucc - 1)) *
    Real.rpow (1 - ∑ i, p i) (a (Fin.last k) - 1))

/-- Dirichlet law on free coordinates. Restriction removes the Lebesgue-null
boundary; powers at boundary points therefore impose no extra convention. -/
noncomputable def dirichletFreeLaw (k : ℕ) (a : Fin (k+1) → ℝ) :
    Measure (Fin k → ℝ) :=
  (volume.restrict (dirichletSimplex k)).withDensity (dirichletFreeDensity k a)

/-- Luc Devroye, Non-Uniform Random Variate Generation, Springer-Verlag,
1986, Chapter XI, Theorem 4.1, p. 594, with the Dirichlet definition on
p. 593. Both directions are included. Gamma parameters are arbitrary
positive real shapes, with rate ONE as in the source. All probability spaces,
measurable random variables and positive dimensions are quantified here.
The forward conclusion is the free-coordinate Dirichlet law and independence
from the total. The converse reconstructs independent gammas. No forward
claim about the total's law is added to the printed theorem.

Source: https://numerical.recipes/devroye/Devroye_files/chapter_eleven.pdf
printed pp. 593-594, PDF pp. 40-41. -/
def DevroyeGammaDirichlet : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω),
    IsProbabilityMeasure μ →
    ∀ (k : ℕ), 0 < k → ∀ (a : Fin (k+1) → ℝ), (∀ i, 0 < a i) →
    (∀ (Y : Fin (k+1) → Ω → ℝ),
      (∀ i, Measurable (Y i)) →
      ProbabilityTheory.iIndepFun Y μ →
      (∀ i, Measure.map (Y i) μ = ProbabilityTheory.gammaMeasure (a i) 1) →
      let T : Ω → ℝ := fun ω => ∑ i, Y i ω
      let X : Ω → (Fin k → ℝ) := fun ω i => Y i.castSucc ω / T ω
      Measure.map X μ = dirichletFreeLaw k a ∧
        ProbabilityTheory.IndepFun X T μ) ∧
    (∀ (T : Ω → ℝ) (X : Ω → (Fin k → ℝ)),
      Measurable T → Measurable X →
      Measure.map T μ = ProbabilityTheory.gammaMeasure (∑ i, a i) 1 →
      Measure.map X μ = dirichletFreeLaw k a →
      ProbabilityTheory.IndepFun X T μ →
      let Y : Fin (k+1) → Ω → ℝ :=
        fun i ω => T ω * simplexCompletion k (X ω) i
      ProbabilityTheory.iIndepFun Y μ ∧
        ∀ i, Measure.map (Y i) μ = ProbabilityTheory.gammaMeasure (a i) 1)

namespace HH

/-- Finite mass expectations; no statistical conclusion is built in. -/
noncomputable def expectation {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, p ω * X ω

noncomputable def variance {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  expectation p (fun ω => (X ω - expectation p X)^2)

noncomputable def mean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

noncomputable def populationVariance {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - mean x)^2) / (n - 1 : ℕ)

/-- Uniform fixed-count binary assignments, the mixed strategy on p. 834. -/
noncomputable def assignmentMass (n m : ℕ) (z : Fin n → Bool) : ℝ :=
  if (Finset.univ.filter (fun i => z i = true)).card = m
  then (Nat.choose n m : ℝ)⁻¹ else 0

noncomputable def sampleVariance {n : ℕ} (T : Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  (∑ i ∈ T, (x i - (∑ j ∈ T, x j) / T.card)^2) / (T.card - 1 : ℕ)

/-- Source sign convention: control a minus treated b. -/
noncomputable def direct {n : ℕ} (a b : Fin n → ℝ) (z : Fin n → Bool) : ℝ :=
  (∑ i, if z i = false then a i else 0) /
    (Finset.univ.filter (fun i => z i = false)).card -
  (∑ i, if z i = true then b i else 0) /
    (Finset.univ.filter (fun i => z i = true)).card

noncomputable def within {n : ℕ} (a b : Fin n → ℝ) (z : Fin n → Bool) : ℝ :=
  let T := Finset.univ.filter (fun i => z i = true)
  let U := Finset.univ.filter (fun i => z i = false)
  sampleVariance T b / T.card + sampleVariance U a / U.card

/-- First-stage fixed-count law and independent second-stage draws.
Unselected groups' auxiliary draws integrate to one and are unused by the
statistics. This is the marginal experiment at one fixed strategy ψ. -/
noncomputable def trialMass {G : ℕ} (n m : Fin G → ℕ) (C : ℕ)
    (w : Finset (Fin G) × ((g : Fin G) → (Fin (n g) → Bool))) : ℝ :=
  (if w.1.card = C then (Nat.choose G C : ℝ)⁻¹ else 0) *
    ∏ g, assignmentMass (n g) (m g) (w.2 g)

noncomputable def point {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (a b : (g : Fin G) → Fin (n g) → ℝ)
    (w : Finset (Fin G) × ((g : Fin G) → (Fin (n g) → Bool))) : ℝ :=
  (∑ g ∈ w.1, direct (a g) (b g) (w.2 g)) / C

noncomputable def estimate {G : ℕ} {n : Fin G → ℕ} (C : ℕ)
    (a b : (g : Fin G) → Fin (n g) → ℝ)
    (w : Finset (Fin G) × ((g : Fin G) → (Fin (n g) → Bool))) : ℝ :=
  ((1 - (C : ℝ) / G) / C) *
    sampleVariance w.1 (fun g => direct (a g) (b g) (w.2 g)) +
    (∑ g ∈ w.1, within (a g) (b g) (w.2 g)) / ((C : ℝ) * G)

end HH

/-- Michael G. Hudgens and M. Elizabeth Halloran, “Toward Causal Inference
With Interference”, JASA 103(482), 2008, 832-842, Theorem 5 and corollary,
p. 837; its displayed direct variance calculation in Appendix A.5, p. 841.
The fixed-stratum values a=Y(0;ψ), b=Y(1;ψ) are arbitrary real arrays: this
parameterizes every potential-outcome schedule satisfying stratified
interference at the fixed treatment count. Mixed assignment is encoded by
assignmentMass. Both sample variances require at least two observations.
No additivity, equal group sizes or constant outcomes are assumed. -/
def HHDirectWithin : Prop :=
  ∀ (n m : ℕ), 2 ≤ m → m + 2 ≤ n → ∀ (a b : Fin n → ℝ),
    let q := HH.assignmentMass n m
    let D := HH.direct a b
    let W := HH.within a b
    HH.variance q D = HH.populationVariance b / m +
      HH.populationVariance a / (n-m : ℕ) -
      HH.populationVariance (fun i => a i - b i) / n ∧
    HH.expectation q W = HH.variance q D +
      HH.populationVariance (fun i => a i - b i) / n ∧
    HH.variance q D ≤ HH.expectation q W ∧
    (HH.expectation q W = HH.variance q D ↔
      ∃ η : ℝ, ∀ i, a i = b i + η)

/-- Hudgens and Halloran (2008), same article, Theorem 6 and corollary,
p. 837, together with the exact variance identity (A.4), Appendix A.6,
p. 841. The full population of G groups and all sizes, counts and fixed
stratum outcome arrays are quantified. The source's mixed first stage has
STRICT C<G (p. 834); the formula is not strengthened to C=G. Finite laws
encode uniform selection, independent local randomization, and partial
interference. Arbitrary arrays describe all stratified-interference values
at ψ; other strategies' potential outcomes are irrelevant after marginalizing.
The source sign is control minus treatment. -/
def HHDirectBetween : Prop :=
  ∀ (G C : ℕ), 2 ≤ C → C < G → ∀ (n m : Fin G → ℕ),
    (∀ g, 2 ≤ m g ∧ m g + 2 ≤ n g) →
    ∀ (a b : (g : Fin G) → Fin (n g) → ℝ),
    let q := fun g => HH.assignmentMass (n g) (m g)
    let θ := fun g => HH.mean (a g) - HH.mean (b g)
    let V := fun g => HH.variance (q g) (HH.direct (a g) (b g))
    let p := HH.trialMass n m C
    let D := HH.point C a b
    let W := HH.estimate C a b
    HH.variance p D = ((1 - (C : ℝ)/G)/C) * HH.populationVariance θ +
      (∑ g, V g)/((C : ℝ)*G) ∧
    HH.expectation p W = HH.variance p D +
      (∑ g, HH.populationVariance (fun i => a g i - b g i)/(n g))/(G : ℝ)^2 ∧
    HH.variance p D ≤ HH.expectation p W ∧
    (HH.expectation p W = HH.variance p D ↔
      ∀ g, ∃ η : ℝ, ∀ i, a g i = b g i + η)

end AronowAudit.Literature

namespace AronowAudit.P037

/-- The complete held P037-T5(b) proposition, with only an independent
published general theorem added as a hypothesis. Application uses universe 0. -/
def exponentials_give_bayesian_bootstrap_conditional_statement : Prop :=
  AronowAudit.Literature.DevroyeGammaDirichlet.{0} →
    ∀ (n : ℕ), normalizedExponentialLaw n = bayesianBootstrapLaw (n+1)

end AronowAudit.P037

#print AronowAudit.Literature.DevroyeGammaDirichlet
#check @AronowAudit.Literature.DevroyeGammaDirichlet
#print AronowAudit.P037.exponentials_give_bayesian_bootstrap_conditional_statement
#check @AronowAudit.P037.exponentials_give_bayesian_bootstrap_conditional_statement

namespace AronowAudit.P045

/-- Unchanged held P045-T4 type, including C=G. The literature input for
C<G is not an assumption that the held C itself is strictly below G. -/
def direct_variance_correction_conditional_statement : Prop :=
  AronowAudit.Literature.HHDirectWithin →
  AronowAudit.Literature.HHDirectBetween →
  ∀ {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (n m : Fin G → ℕ) (hm : ∀ g, 2 ≤ m g ∧ m g + 2 ≤ n g)
    (a b : (g : Fin G) → Fin (n g) → ℝ),
    let q := fun g => crMass (n g) (m g)
    let law := selectedLaw n C q
    let θ := fun g => mean (a g) - mean (b g)
    let V := fun g => popVar (a g)/(m g) + popVar (b g)/((n g-m g : ℕ) : ℝ) -
      popVar (fun i => a g i-b g i)/(n g)
    let point := selectedMean C (fun g => directGroup (a g) (b g))
    let vest := directVarianceEstimate C a b
    (∀ g, expect (q g) (directGroup (a g) (b g)) = θ g ∧
      variance (q g) (directGroup (a g) (b g)) = V g) ∧
    expect law point = mean θ ∧
    variance law point = ((1-(C : ℝ)/G)/C)*popVar θ + (∑ g, V g)/((C : ℝ)*G) ∧
    expect law vest - variance law point =
      (∑ g, popVar (fun i => a g i-b g i)/(n g))/(G : ℝ)^2 ∧
    0 ≤ expect law vest - variance law point ∧
    (expect law vest = variance law point ↔ ∀ g, ∀ i j, a g i-b g i = a g j-b g j)

end AronowAudit.P045

#print AronowAudit.Literature.HHDirectWithin
#check @AronowAudit.Literature.HHDirectWithin
#print AronowAudit.Literature.HHDirectBetween
#check @AronowAudit.Literature.HHDirectBetween
#print AronowAudit.P045.direct_variance_correction_conditional_statement
#check @AronowAudit.P045.direct_variance_correction_conditional_statement

#print axioms AronowAudit.Literature.DevroyeGammaDirichlet
#print axioms AronowAudit.Literature.HHDirectWithin
#print axioms AronowAudit.Literature.HHDirectBetween
#print axioms AronowAudit.P037.exponentials_give_bayesian_bootstrap_conditional_statement
#print axioms AronowAudit.P045.direct_variance_correction_conditional_statement
