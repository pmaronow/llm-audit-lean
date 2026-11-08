import SAP.P001e.WH.W2.Glue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W2
universe u v
noncomputable section

/-- T85: derive positive cell sizes, their total and the unit-to-cell grouping
identities. Use Finset.sum_fiberwise_of_maps_to for the map i ↦ X i, then
Finset.sum_div. Distribute the plug-in cell weights by ring. Binary response gives
recordedOutcome(Y,R)*R=Y*R. No probability or asymptotic argument is needed. -/
def T85_L1 : Prop :=
  ∀ {n : ℕ} {E : Type u} [DecidableEq E] (hn : 0 < n)
    (X : Fin n → E) (R : Fin n → ℝ) (q : E → ℝ)
    (hb : ∀ i, R i=0 ∨ R i=1),
    let C := wholeCells X
    let N : C → ℝ := fun x => wholeCellN X x
    let r : C → ℝ := fun x => wholeCellR X R x
    (∀ x, 0 < N x) ∧ (∑ x, N x)=(n : ℝ) ∧
    wholeSampleWeight X R q=cellWeightMean r (fun x : C => q x) n ∧
    (∀ Y : Fin n → ℝ,
      wholeSampleIPW X R Y q=cellIPW (fun x : C => wholeCellS X R Y x) (fun x : C => q x) n ∧
      wholeSamplePlugIn X R Y=cellPlugIn N r (fun x : C => wholeCellS X R Y x) n ∧
      (∑ i, Y i*R i/q (X i))/(n : ℝ)=wholeSampleIPW X R Y q)

/-- T85: every cell outcome-sum vector is realized by actual unit outcomes when
each observed cell has a respondent. Set Y_i=S_(X_i)/r_(X_i). On binary responses
recordedOutcome(Y_i,R_i)*R_i=Y_i R_i; grouping in one fiber gives S_x r_x/r_x.
Use Finset.sum_congr and sum_mul, cancel with the strictly positive r_x. -/
def T85_L2 : Prop :=
  ∀ {n : ℕ} {E : Type u} [DecidableEq E] (X : Fin n → E) (R : Fin n → ℝ)
    (hb : ∀ i, R i=0 ∨ R i=1)
    (hr : ∀ x ∈ wholeCells X, 0 < wholeCellR X R x)
    (S : wholeCells X → ℝ),
    ∃ Y : Fin n → ℝ, ∀ x : wholeCells X, wholeCellS X R Y x=S x

/-- T87: the stable-outcome CEF identities for an almost surely binary response.
Replace R by 1_{R=1}, apply stable_outcomes_respondent_cef_proof, and transport
set-integral CEF identities through almost sure equality. Alternatively adapt its
partition proof, keeping all partitions modulo null sets. The affine predictor
is measurable on all (r,x); its composition agrees a.e. with the donor's if-branch.
The R=0 restricted outcome is exactly -99 a.e., including a null branch. -/
def T87_L1 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hi : Integrable Y μ)
    (hb : ∀ᵐ ω ∂μ, R ω=0 ∨ R ω=1) (m : E → ℝ)
    (hm : IsConditionalMean (μ.restrict {ω | R ω=1}) X Y m),
    IsConditionalMean (μ.restrict {ω | R ω=1}) X (fun ω => recordedOutcome (Y ω) (R ω)) m ∧
    IsConditionalMean (μ.restrict {ω | R ω=0}) X (fun ω => recordedOutcome (Y ω) (R ω)) (fun _ => -99) ∧
    IsConditionalMean μ (fun ω => (R ω,X ω)) (fun ω => recordedOutcome (Y ω) (R ω))
      (fun rx => rx.1*m rx.2-99*(1-rx.1))

/-- T87: uniform positive propensity transfers L1 of any measurable covariate
function from the respondent sublaw to the population. For every covariate event
A, the propensity CEF implies ε Law(X)(A) ≤ Law(X;R=1)(A). Extend the real integral
inequality to measures, and use Integrable.mono_measure and integrable_smul_measure.
There is no MAR premise: only the response propensity and its a.e. lower bound
are used. This is not an additional population-integrability assumption. -/
def T87_L2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (R : Ω → ℝ) (hR : Measurable R) (hb : ∀ᵐ ω ∂μ, R ω=0 ∨ R ω=1)
    (p m : E → ℝ) (hp : IsConditionalMean μ X R p) (hm : Measurable m)
    (hpos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω))
    (hi : Integrable (m ∘ X) (μ.restrict {ω | R ω=1})),
    Integrable (m ∘ X) μ

/-- T94: integrate an actual conditional density to construct the observed CEF.
Use condExp_ae_eq_integral_condDistrib', then rewrite integration against
withDensity via integral_withDensity_eq_integral_toReal_smul. Joint measurability
of f gives measurable parameter integrals (StronglyMeasurable.integral_prod_right').
Integrability and all set-integral identities follow from integrable_condExp and
setIntegral_condExp. No mean-version premise is assumed. -/
def T94_L1 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → E) (hZ : Measurable Z)
    (Y : Ω → ℝ) (hY : Measurable Y) (hi : Integrable Y μ) (f : E → ℝ → ℝ)
    (hf : WholeConditionalDensity μ Z Y f),
    IsConditionalMean μ Z Y (fun z => ∫ y, y*f z y)

/-- T94: restrict a joint (D,X)-CEF to either observed arm. Test its integral
identity on rectangles {d} × A. Joint measurability restricts to x ↦ F(d,x),
and population integrability of this displayed arm mean supplies its restricted
integrability. This lemma needs neither binary treatment nor ignorability. -/
def T94_L2 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (D Y : Ω → ℝ) (hD : Measurable D) (F : ℝ × E → ℝ)
    (hm : IsConditionalMean μ (fun ω => (D ω,X ω)) Y F)
    (d : ℝ) (hi : Integrable (fun ω => F (d,X ω)) μ),
    IsConditionalMean (μ.restrict {ω | D ω=d}) X Y (fun x => F (d,x))

/-- T94: causal CEF transfer for both arms, with almost sure binary treatment
and overlap. Invoke T94_L2 for the observed arm CEFs and MarSelection.n5_proof
(with n1,n4,n3,n2 discharged) using U=(Y0,Y1) and coordinate projections.
For the control arm use 1-D and propensity 1-p; pull its CI back along r ↦ 1-r
and derive its CEF by linearity. Its respondent event is {D=0}. Consistency is
needed only on the appropriate arm. No rank or pointwise positivity is imposed. -/
def T94_L3 : Prop :=
  T94_L2.{u,0} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : ℕ} (X : Ω → Fin K → ℝ) (D Y0 Y1 : Ω → ℝ) (p : (Fin K → ℝ) → ℝ)
    (model : WholePotentialModel μ X D Y0 Y1 p) (F : ℝ × (Fin K → ℝ) → ℝ)
    (hm : IsConditionalMean μ (fun ω => (D ω,X ω))
      (fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)) F)
    (hi : ∀ d ∈ ({0,1} : Set ℝ), Integrable (fun ω => F (d,X ω)) μ),
    ∀ d ∈ ({0,1} : Set ℝ), IsConditionalMean μ X (if d=0 then Y0 else Y1) (fun x => F (d,x))

/-- T94: a.e. equality of two functions on (D,X) extends to either fixed arm
under overlap. The propensity identity gives the arm sublaw density p for d=1
and 1-p for d=0 relative to Law(X). These densities are positive a.e., so each
arm sublaw has the same null sets as Law(X). Use withDensity_absolutelyContinuous'
or prove the zero-set implication directly by integrating a positive propensity.
The functions need only be measurable; no integrals of them are used here. -/
def T94_L4 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (D : Ω → ℝ) (hD : Measurable D) (hb : ∀ᵐ ω ∂μ, D ω=0 ∨ D ω=1)
    (p : E → ℝ) (hp : IsConditionalMean μ X D p)
    (hpos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω) ∧ p (X ω) < 1-ε)
    (F G : ℝ × E → ℝ) (hF : Measurable F) (hG : Measurable G)
    (he : F =ᵐ[μ.map (fun ω => (D ω,X ω))] G),
    ∀ d ∈ ({0,1} : Set ℝ), (fun x => F (d,x)) =ᵐ[μ.map X] (fun x => G (d,x))

/-- T94: common observable laws make integrated conditional-density versions
agree on each arm Law(X)-a.e. The observable joint law determines condDistrib
by its definition through condKernel. Integrating two density versions gives
equal measurable joint mean functions a.e. on Law(D,X); apply T94_L4 to extend
to each arm. Obtain equality of the covariate laws by mapping the joint law
through ((d,x),y) ↦ x. This is the version-independence step, before causal means
are integrated, and uses only the supplied existence guards. -/
def T94_L5 : Prop :=
  T94_L4.{u,0} →
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
    μ.map X=ν.map X' ∧ ∀ d ∈ ({0,1} : Set ℝ),
      (fun x => integratedModelMean g d x θ) =ᵐ[μ.map X] (fun x => integratedModelMean g' d x θ')

end
end SAP.P001e.WH.W2
