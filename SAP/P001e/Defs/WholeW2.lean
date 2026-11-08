import Mathlib
import SAP.P001e.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v
noncomputable section

/-- The fair two-point law used to test the population assertion in T93. -/
def wholeCoinLaw : Measure (Fin 2) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

def wholeCoinD (i : Fin 2) : ℝ := if i = 0 then 0 else 1

/-- The printed claim is false: p. 258 (PDF p. 276), the population assertion
included in P001-T93 (the corrected imputation tables are on p. 259).
With a fair binary treatment, constant covariates and both potential outcomes equal
to treatment, the observed CEF is exactly D, with treatment coefficient one.
Both conditional and unconditional causal effects are zero. Both arms have positive
mass and propensity one half, so overlap and finite moments do not repair the
missing ignorability assumption. -/
def T93WholeStatement : Prop :=
  IsProbabilityMeasure wholeCoinLaw ∧
  Measurable wholeCoinD ∧ Integrable wholeCoinD wholeCoinLaw ∧
  (∀ i, wholeCoinD i = 0 ∨ wholeCoinD i = 1) ∧
  probability wholeCoinLaw {i | wholeCoinD i = 0} = 1/2 ∧
  probability wholeCoinLaw {i | wholeCoinD i = 1} = 1/2 ∧
  (∀ i, realizedOutcome (wholeCoinD i) (wholeCoinD i) (wholeCoinD i) = wholeCoinD i) ∧
  IsConditionalMean wholeCoinLaw (fun _ : Fin 2 => (0 : ℝ)) wholeCoinD (fun _ => 1/2) ∧
  (∀ i : Fin 2, (1/4 : ℝ) < (fun _ : ℝ => (1/2 : ℝ)) 0 ∧
    (fun _ : ℝ => (1/2 : ℝ)) 0 < 1-1/4) ∧
  IsConditionalMean wholeCoinLaw (fun i => (wholeCoinD i, (0 : ℝ)))
    (fun i => realizedOutcome (wholeCoinD i) (wholeCoinD i) (wholeCoinD i))
    (fun dx => (0 : ℝ) + 1*dx.1 + 0*dx.2) ∧
  IsConditionalMean wholeCoinLaw (fun _ : Fin 2 => (0 : ℝ))
    (fun i => wholeCoinD i-wholeCoinD i) (fun _ => 0) ∧
  expectation wholeCoinLaw (fun i => wholeCoinD i-wholeCoinD i) = 0 ∧
  (0 : ℝ) ≠ 1

/-- The observed, nonempty covariate fibers; no ambient finite support is required. -/
def wholeCells {n : ℕ} {E : Type v} [DecidableEq E] (X : Fin n → E) : Finset E :=
  Finset.univ.image X

def wholeCellN {n : ℕ} {E : Type v} [DecidableEq E] (X : Fin n → E) (x : E) : ℝ :=
  ∑ i, if X i=x then 1 else 0

def wholeCellR {n : ℕ} {E : Type v} [DecidableEq E]
    (X : Fin n → E) (R : Fin n → ℝ) (x : E) : ℝ := ∑ i, if X i=x then R i else 0

def wholeCellS {n : ℕ} {E : Type v} [DecidableEq E]
    (X : Fin n → E) (R Y : Fin n → ℝ) (x : E) : ℝ :=
  ∑ i, if X i=x then recordedOutcome (Y i) (R i)*R i else 0

def wholeSampleIPW {n : ℕ} {E : Type v} (X : Fin n → E)
    (R Y : Fin n → ℝ) (q : E → ℝ) : ℝ :=
  (∑ i, recordedOutcome (Y i) (R i)*R i/q (X i))/(n : ℝ)

def wholeSamplePlugIn {n : ℕ} {E : Type v} [DecidableEq E]
    (X : Fin n → E) (R Y : Fin n → ℝ) : ℝ :=
  ∑ x ∈ wholeCells X, (wholeCellS X R Y x/wholeCellR X R x)*(wholeCellN X x/(n : ℝ))

def wholeSampleWeight {n : ℕ} {E : Type v} (X : Fin n → E)
    (R : Fin n → ℝ) (q : E → ℝ) : ℝ := (∑ i, R i/q (X i))/(n : ℝ)

def wholeSampleStabilized {n : ℕ} {E : Type v} (X : Fin n → E)
    (R Y : Fin n → ℝ) (q : E → ℝ) : ℝ :=
  ((∑ i, Y i*R i/q (X i))/(n : ℝ))/wholeSampleWeight X R q

/-- P001-T85; p. 228 (PDF p. 246), first paragraph.
For every positive finite sample with binary responses, a respondent in each
observed cell and positive fitted probabilities, grouping gives both cell formulas
and their difference. Equality for every outcome vector is equivalent to fitting
the observed response fraction in every cell. Under this saturation condition the
mean weight is one and the stabilized, ordinary IPW and plug-in estimates agree. -/
def T85WholeStatement : Prop :=
  ∀ {n : ℕ} {E : Type v} [DecidableEq E] (hn : 0 < n)
    (X : Fin n → E) (R : Fin n → ℝ) (q : E → ℝ)
    (hbinary : ∀ i, R i=0 ∨ R i=1)
    (hr : ∀ x ∈ wholeCells X, 0 < wholeCellR X R x)
    (hq : ∀ x ∈ wholeCells X, 0 < q x),
  (∀ Y : Fin n → ℝ,
    wholeSampleIPW X R Y q = (∑ x ∈ wholeCells X, wholeCellS X R Y x/q x)/(n : ℝ) ∧
    wholeSamplePlugIn X R Y =
      (∑ x ∈ wholeCells X, wholeCellN X x*wholeCellS X R Y x/wholeCellR X R x)/(n : ℝ) ∧
    wholeSampleIPW X R Y q-wholeSamplePlugIn X R Y =
      (∑ x ∈ wholeCells X, wholeCellS X R Y x*(1/q x-wholeCellN X x/wholeCellR X R x))/(n : ℝ)) ∧
  ((∀ Y : Fin n → ℝ, wholeSampleIPW X R Y q=wholeSamplePlugIn X R Y) ↔
    ∀ x ∈ wholeCells X, q x=wholeCellR X R x/wholeCellN X x) ∧
  ((∀ x ∈ wholeCells X, q x=wholeCellR X R x/wholeCellN X x) →
    wholeSampleWeight X R q=(∑ x ∈ wholeCells X, wholeCellN X x)/(n : ℝ) ∧
    wholeSampleWeight X R q=1 ∧
    ∀ Y : Fin n → ℝ, wholeSampleIPW X R Y q=wholeSamplePlugIn X R Y ∧
      wholeSampleStabilized X R Y q=wholeSampleIPW X R Y q)

/-- P001-T87; p. 233 (PDF p. 251), first paragraph below Table 6.3.1.
For integrable outcomes and almost surely binary responses, a measurable respondent
conditional-mean function exists. Every such version is also the respondent CEF
of the recorded outcome. On nonresponse the recorded CEF is minus 99; the full
CEF given (R,X) is R m(X) minus 99(1-R). Under MAR and almost sure uniform
positive propensity every respondent version is integrable in the population and
is its outcome CEF. The linear and squared-covariate working specifications target
this respondent function; no exact approximation or numerical-fit assertion is made. -/
def T87WholeStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Fin K → ℝ) (hX : Measurable X)
    (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
    (hbinary : ∀ᵐ ω ∂μ, R ω=0 ∨ R ω=1),
  (∃ m : (Fin K → ℝ) → ℝ, IsConditionalMean (μ.restrict {ω | R ω=1}) X Y m) ∧
  ∀ m : (Fin K → ℝ) → ℝ, IsConditionalMean (μ.restrict {ω | R ω=1}) X Y m →
    IsConditionalMean (μ.restrict {ω | R ω=1}) X (fun ω => recordedOutcome (Y ω) (R ω)) m ∧
    IsConditionalMean (μ.restrict {ω | R ω=0}) X (fun ω => recordedOutcome (Y ω) (R ω)) (fun _ => -99) ∧
    IsConditionalMean μ (fun ω => (R ω,X ω)) (fun ω => recordedOutcome (Y ω) (R ω))
      (fun rx => rx.1*m rx.2-99*(1-rx.1)) ∧
    (∀ (p : (Fin K → ℝ) → ℝ), IsConditionalMean μ X R p →
      (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) →
      CondIndependent μ X hX Y R →
      Integrable (m ∘ X) μ ∧ IsConditionalMean μ X Y m)

/-- A conditional density is a version of the actual conditional law, rather than
an assumed formula for its mean. Joint measurability and nonnegativity are the
usual density requirements, at the parameter actually being used. -/
def WholeConditionalDensity {Ω : Type u} {E : Type v}
    [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → E) (Y : Ω → ℝ) (f : E → ℝ → ℝ) : Prop :=
  Measurable (fun z : E × ℝ => f z.1 z.2) ∧
  (∀ z y, 0 ≤ f z y) ∧
  ∀ᵐ z ∂μ.map Z, condDistrib Y Z μ z=volume.withDensity (fun y => ENNReal.ofReal (f z y))

/-- Binary strong ignorability with versions and almost sure overlap. -/
structure WholePotentialModel {Ω : Type u} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (X : Ω → Fin K → ℝ) (D Y0 Y1 : Ω → ℝ)
    (p : (Fin K → ℝ) → ℝ) : Prop where
  hX : Measurable X
  hD : Measurable D
  hY0 : Measurable Y0
  hY1 : Measurable Y1
  hi0 : Integrable Y0 μ
  hi1 : Integrable Y1 μ
  binary : ∀ᵐ ω ∂μ, D ω=0 ∨ D ω=1
  propensity : IsConditionalMean μ X D p
  overlap : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1-ε
  independent : CondIndependent μ X hX (fun ω => (Y0 ω,Y1 ω)) D

/-- Only the true parameter is used here. The last two requirements say that the
inner integrals and outer expectations appearing in the claim exist finitely. -/
def WholeCorrectModel {Ω : Type u} [MeasurableSpace Ω] {K τ : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Fin K → ℝ) (D Y0 Y1 : Ω → ℝ)
    (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ) : Prop :=
  WholeConditionalDensity μ (fun ω => (D ω,X ω))
    (fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)) (fun dx y => g y dx.1 dx.2 θ) ∧
  (∀ d ∈ ({0,1} : Set ℝ), ∀ᵐ ω ∂μ, Integrable (fun y => y*g y d (X ω) θ) volume) ∧
  (∀ d ∈ ({0,1} : Set ℝ), Integrable (fun ω => integratedModelMean g d (X ω) θ) μ)

def WholePotentialPopulation : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K τ : ℕ} (X : Ω → Fin K → ℝ) (D Y0 Y1 : Ω → ℝ) (p : (Fin K → ℝ) → ℝ)
    (model : WholePotentialModel μ X D Y0 Y1 p)
    (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
    (correct : WholeCorrectModel μ X D Y0 Y1 g θ),
  ∀ d ∈ ({0,1} : Set ℝ),
    IsConditionalMean μ X (if d=0 then Y0 else Y1) (fun x => integratedModelMean g d x θ) ∧
    expectation μ (if d=0 then Y0 else Y1)=expectation μ (fun ω => integratedModelMean g d (X ω) θ) ∧
    expectation μ (fun ω => integratedModelMean g d (X ω) θ)=
      ∫ x, integratedModelMean g d x θ ∂μ.map X ∧
    (∀ fX : (Fin K → ℝ) → ℝ, Measurable fX → (∀ x, 0 ≤ fX x) →
      μ.map X=volume.withDensity (fun x => ENNReal.ofReal (fX x)) →
      expectation μ (if d=0 then Y0 else Y1)=∫ x, integratedModelMean g d x θ*fX x)

/-- Point identification compares arbitrary models and arbitrary true density
versions with the same joint observable law. -/
def WholePotentialIdentification : Prop :=
  ∀ {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K τ τ' : ℕ} (X : Ω → Fin K → ℝ) (D Y0 Y1 : Ω → ℝ) (p : (Fin K → ℝ) → ℝ)
    (X' : Ω' → Fin K → ℝ) (D' Y0' Y1' : Ω' → ℝ) (p' : (Fin K → ℝ) → ℝ)
    (model : WholePotentialModel μ X D Y0 Y1 p) (model' : WholePotentialModel ν X' D' Y0' Y1' p')
    (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ) (θ : Fin τ → ℝ)
    (g' : ℝ → ℝ → (Fin K → ℝ) → (Fin τ' → ℝ) → ℝ) (θ' : Fin τ' → ℝ)
    (correct : WholeCorrectModel μ X D Y0 Y1 g θ) (correct' : WholeCorrectModel ν X' D' Y0' Y1' g' θ')
    (hlaw : μ.map (fun ω => ((D ω,X ω),realizedOutcome (Y0 ω) (Y1 ω) (D ω)))=
      ν.map (fun ω => ((D' ω,X' ω),realizedOutcome (Y0' ω) (Y1' ω) (D' ω)))),
    expectation μ Y0=expectation ν Y0' ∧ expectation μ Y1=expectation ν Y1'

/-- Empirical covariate law used by the corrected plug-in estimator. -/
def wholeEmpiricalCovariates {n K : ℕ} (X : Fin n → Fin K → ℝ) : Measure (Fin K → ℝ) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (X i)

def WholePotentialEstimator : Prop :=
  ∀ {n K τ : ℕ} (hn : 0 < n)
    (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (Y D : Fin n → ℝ) (X : Fin n → Fin K → ℝ) (Θ : Set (Fin τ → ℝ)) (θhat : Fin τ → ℝ)
    (hfit : θhat ∈ Θ ∧ ∀ t ∈ Θ, (∏ i, g (Y i) (D i) (X i) t) ≤ ∏ i, g (Y i) (D i) (X i) θhat)
    (hi : ∀ d ∈ ({0,1} : Set ℝ), ∀ i, Integrable (fun y => y*g y d (X i) θhat)),
  (∀ d ∈ ({0,1} : Set ℝ),
    fittedPotentialAverage g d X θhat=(∑ i, ∫ y, y*g y d (X i) θhat)/(n : ℝ) ∧
    fittedPotentialAverage g d X θhat=∫ x, integratedModelMean g d x θhat ∂wholeEmpiricalCovariates X ∧
    ∀ x : Fin K → ℝ, Integrable (fun y => y*g y d x θhat) →
      (∑ _i : Fin n, integratedModelMean g d x θhat)/(n : ℝ)=integratedModelMean g d x θhat) ∧
  fittedPotentialAverage g 1 X θhat-fittedPotentialAverage g 0 X θhat=
    (∑ i, (integratedModelMean g 1 (X i) θhat-integratedModelMean g 0 (X i) θhat))/(n : ℝ)

/-- P001-T94; p. 261 (PDF p. 279), the population identity and last display;
the ATE plug-in formula is on p. 262 (PDF p. 280).
Under binary strong ignorability and almost sure overlap, a correct conditional
density identifies both potential-outcome conditional means and their population
means. The latter are integrals over the covariate law, or the printed iterated
Lebesgue integral when that law has a density, and agree across models with the
same observable law. For any existing ML maximizer and finite displayed integrals,
the corrected estimator averages at the observed covariates; the ATE estimator
averages fitted contrasts. The printed free-covariate average collapses to the
single fitted conditional mean at that covariate. -/
def T94WholeStatement : Prop :=
  WholePotentialPopulation.{u} ∧ WholePotentialIdentification.{u} ∧ WholePotentialEstimator

/-- Five distinct observable cells; the repeated printed row denotes one cell. -/
def wholePostCells : Finset (ℝ × ℝ × ℝ) :=
  {(0,0,0),(1,0,0),(1,1,0),(0,0,1),(1,1,1)}

def wholePostPMF (y x d : ℝ) : ℝ :=
  (if 0=y ∧ 0=x ∧ 0=d then 1/6 else 0)+
  (if 1=y ∧ 0=x ∧ 0=d then 1/6 else 0)+
  (if 1=y ∧ 1=x ∧ 0=d then 1/6 else 0)+
  (if 0=y ∧ 0=x ∧ 1=d then 1/6 else 0)+
  (if 1=y ∧ 1=x ∧ 1=d then 1/3 else 0)

/-- P001-T89; pp. 253–254 (PDF pp. 271–272).
The specified uniform six-atom latent law randomizes treatment with respect to all
potential variables. Treatment has zero outcome effect everywhere but changes the
covariate with probability one third. The complete corrected observable PMF has
four masses one sixth and one mass one third, and total one; the printed function
on five distinct cells has total five sixths. The stated covariate marginals,
conditioning-cell masses, four conditional means and contrast minus one quarter
hold. Conditional outcome probabilities one half and zero witness the loss of
conditional independence after adjusting for this post-treatment covariate. -/
def T89WholeStatement : Prop :=
  T89Statement ∧
  (∀ i, 0 ≤ postWeights i) ∧ (∑ i, postWeights i)=1 ∧
  (fun i => (postOutcome i,postOutcome i,postCovariate1 i,postCovariate0 i,postAssignment i))=
    ![(0,0,0,0,0),(1,1,1,0,0),(1,1,1,1,0),(0,0,0,0,1),(1,1,1,0,1),(1,1,1,1,1)] ∧
  (∀ i, realizedOutcome (postOutcome i) (postOutcome i) (postAssignment i)=postOutcome i ∧
    postOutcome i-postOutcome i=0) ∧
  finiteProbability postWeights (fun i => postCovariate1 i-postCovariate0 i=1)=1/3 ∧
  (∀ y x d : ℝ, finiteProbability postWeights
    (fun i => postOutcome i=y ∧ postCovariate i=x ∧ postAssignment i=d)=wholePostPMF y x d) ∧
  wholePostCells.card=5 ∧
  (∑ z ∈ wholePostCells, wholePostPMF z.1 z.2.1 z.2.2)=1 ∧
  (∑ _z ∈ wholePostCells, (1/6 : ℝ))=5/6 ∧
  finiteProbability postWeights (fun i => postCovariate i=0 ∧ postAssignment i=0)=1/3 ∧
  finiteProbability postWeights (fun i => postCovariate i=1 ∧ postAssignment i=0)=1/6 ∧
  finiteProbability postWeights (fun i => postCovariate i=0 ∧ postAssignment i=1)=1/6 ∧
  finiteProbability postWeights (fun i => postCovariate i=1 ∧ postAssignment i=1)=1/3 ∧
  finiteProbability postWeights (fun i => postOutcome i=1 ∧ postCovariate i=0 ∧ postAssignment i=0)/
    finiteProbability postWeights (fun i => postCovariate i=0 ∧ postAssignment i=0)=1/2 ∧
  finiteProbability postWeights (fun i => postOutcome i=1 ∧ postCovariate i=0 ∧ postAssignment i=1)/
    finiteProbability postWeights (fun i => postCovariate i=0 ∧ postAssignment i=1)=0

end
end SAP.P001e
