import Mathlib
import SAP.P006a.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a
noncomputable section

/-- The marginal baseline condition, imposed only at feasible policies. -/
def MarginalBaselineOnW2 {Ω X U : Type} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (b0 : X → ℝ)
    (PiSet : Set ((X × U) → ℝ)) : Prop :=
  Measurable b0 ∧ Integrable (fun c => b0 c.1) E.PX ∧
    ∀ π ∈ PiSet, ∀ i,
      (E.law π)[(fun ω => E.μ0 (E.X i ω)) |
        MeasurableSpace.comap (fun ω => (E.X i ω).1) inferInstance]
        =ᵐ[E.law π] (fun ω => b0 (E.X i ω).1)

/-- Joint measurability and dependence on the public covariate only, on the feasible class.
There is no integrability requirement on unselected estimator evaluations. -/
def PublicEstimatorOnW2 {Ω X U : Type} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (PiSet : Set ((X × U) → ℝ)) : Prop :=
  ∀ π ∈ PiSet, Measurable (fun z : Ω × (X × U) => E.μhat π z.1 z.2) ∧
    ∀ ω x u u', E.μhat π ω (x, u) = E.μhat π ω (x, u')

/-- The selected residual, whose ordinary conditional expectation is used in Theorem 3. -/
def TreatedResidualW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (a π : C → ℝ) (i : Fin n) : Ω → ℝ :=
  fun ω => bit (E.T π i ω) * (E.μhat π ω (E.X i ω) - a (E.X i ω))

/-- The moment domain of qualified Lemma 2. Only the two weighted evaluations must be L1. -/
def CoinMomentW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) : Prop :=
  ∀ i, Integrable (fun ω => bit (E.T π i ω) * E.μhat π ω (E.X i ω)) (E.law π) ∧
    Integrable (fun ω => π (E.X i ω) * E.μhat π ω (E.X i ω)) (E.law π) ∧
    (E.law π)[(fun ω => (bit (E.T π i ω) - π (E.X i ω)) *
      E.μhat π ω (E.X i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun _ => (0 : ℝ))

/-- The common outcome contribution to one unit's score. -/
def OutcomeMeanW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) : ℝ :=
  ∫ c, π c * E.μ1 c ∂E.PX

/-- A weighted estimator evaluation may have a different mean at each unit. -/
def EvaluationMeanW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) (i : Fin n) : ℝ :=
  ∫ ω, π (E.X i ω) * E.μhat π ω (E.X i ω) ∂E.law π

/-- The corrected main clauses (i)--(iii), without moments at irrelevant policies or
on untreated observations. Maximizers occur only in the regret clause. -/
def InformationBoundW2 : Prop :=
  ∀ {Ω X U : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U]
    {n : ℕ} (E : Experiment Ω (X × U) n) (PiSet : Set ((X × U) → ℝ))
    (hPiSet : ∀ π ∈ PiSet, Admissible π) (hS : ∀ π ∈ PiSet, PolicyDesign E π)
    (b0 : X → ℝ) (hM : MarginalBaselineOnW2 E b0 PiSet)
    (hX : PublicEstimatorOnW2 E PiSet)
    (hR : ∀ π ∈ PiSet, ∀ i, Integrable
      (TreatedResidualW2 E (fun c => b0 c.1) π i) (E.law π))
    (hU : TreatedUnbiased E (fun c => b0 c.1) PiSet),
    (∀ π ∈ PiSet,
      normalizedTT E π = (∫ c, π c * (E.μ1 c - b0 c.1) ∂E.PX) ∧
      |normalizedTT E π - E.V π| = |∫ c, π c * (E.μ0 c - b0 c.1) ∂E.PX| ∧
      |normalizedTT E π - E.V π| ≤ marginalHeterogeneity E b0) ∧
    (∀ γ : ℝ, marginalHeterogeneity E b0 ≤ γ → ∀ b s,
      IsBest PiSet E.expectedTT b → IsBest PiSet E.V s →
      regret PiSet E.V b = E.V s - E.V b ∧ regret PiSet E.V b ≤ 2 * γ)

/-- Conditional unbiasedness among treated units is understood on the treated measure,
or equivalently at covariates of positive propensity. The full H need not be L1. -/
def SelectedEquivalenceW2 : Prop :=
  ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (T : Ω → Bool) (H a p : Ω → ℝ)
    (hT : Measurable T) (hH : Measurable H)
    (ha : Measurable[m] a) (hai : Integrable a μ)
    (hp : Measurable[m] p) (hpb : ∀ ω, 0 ≤ p ω ∧ p ω ≤ 1)
    (hcoin : μ[(fun ω => bit (T ω)) | m] =ᵐ[μ] p)
    (hR : Integrable (fun ω => bit (T ω) * (H ω - a ω)) μ),
    let ν := μ.restrict {ω | T ω = true}
    Integrable H ν ∧
      ((μ[(fun ω => bit (T ω) * (H ω - a ω)) | m] =ᵐ[μ] (fun _ => 0)) ↔
        (ν[H | m] =ᵐ[ν] a)) ∧
      ((ν[H | m] =ᵐ[ν] a) ↔
        (∀ᵐ ω ∂μ, 0 < p ω → ν[H | m] ω = a ω))

/-- Conditional independence supplies the qualified moment on its weighted L1 domain.
For integrable H the same moment is equivalent to the familiar factorization.
The standard Borel assumption is used only for conditional independence/laws. -/
def CoinFactorizationW2 : Prop :=
  ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (T : Ω → Bool) (H p : Ω → ℝ) (hT : Measurable T) (hH : Measurable H)
    (hp : Measurable[m] p) (hpb : ∀ ω, 0 ≤ p ω ∧ p ω ≤ 1)
    (hcoin : μ[(fun ω => bit (T ω)) | m] =ᵐ[μ] p)
    (hTH : Integrable (fun ω => bit (T ω) * H ω) μ)
    (hpH : Integrable (fun ω => p ω * H ω) μ),
    (CondIndepFun m hm T H μ →
      μ[(fun ω => (bit (T ω) - p ω) * H ω) | m] =ᵐ[μ] (fun _ => 0)) ∧
    (Integrable H μ →
      ((μ[(fun ω => (bit (T ω) - p ω) * H ω) | m] =ᵐ[μ] (fun _ => 0)) ↔
        (μ[(fun ω => bit (T ω) * H ω) | m] =ᵐ[μ]
          (fun ω => p ω * μ[H | m] ω))))

/-- Qualified Lemma 2: the sum identity, the exact criterion for the fixed-unit
n-times form, and the sufficient common joint evaluation law. -/
def QualifiedLemma2W2 : Prop :=
  ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (π : C → ℝ) (hπ : Admissible π)
    (hS : PolicyDesign E π) (hI : CoinMomentW2 E π),
    E.expectedTT π = ∑ i, (OutcomeMeanW2 E π - EvaluationMeanW2 E π i) ∧
    ((∀ i, E.expectedTT π = (n : ℝ) * (OutcomeMeanW2 E π - EvaluationMeanW2 E π i)) ↔
      (∀ i j, EvaluationMeanW2 E π i = EvaluationMeanW2 E π j)) ∧
    (∀ D : Measure (C × ℝ),
      (∀ i, IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω)))
        id (E.law π) D) → ∀ i j, EvaluationMeanW2 E π i = EvaluationMeanW2 E π j)

/-- A single auxiliary-data estimator, with a fixed law independent of each feasible
design vector. Private covariates are included in that vector. -/
structure AuxiliaryDataW2 {Ω X U A : Type} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace A] {n : ℕ}
    (E : Experiment Ω (X × U) n) (PiSet : Set ((X × U) → ℝ))
    (Q : Measure A) (Z : Ω → A) (f : A × X → ℝ) : Prop where
  probability : IsProbabilityMeasure Q
  measurable_Z : Measurable Z
  measurable_f : Measurable f
  representation : ∀ π ∈ PiSet, ∀ ω c, E.μhat π ω c = f (Z ω, c.1)
  law_Z : ∀ π ∈ PiSet, IdentDistrib Z id (E.law π) Q
  independent : ∀ π ∈ PiSet,
    IndepFun Z (fun ω => ((fun i => E.X i ω), (fun i => E.T π i ω))) (E.law π)

/-- The common joint law of a covariate pair and its auxiliary-data evaluation. -/
def AuxiliaryLawW2 {Ω X U A : Type} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace A] {n : ℕ}
    (E : Experiment Ω (X × U) n) (Q : Measure A) (f : A × X → ℝ) :
    Measure ((X × U) × ℝ) :=
  (Q.prod E.PX).map (fun z => (z.2, f (z.1, z.2.1)))

/-- Independent pointwise-unbiased estimation suffices for the corrected treated
moment at the marginal baseline, on the selected-residual L1 domain. Independence
is needed only at each feasible policy; no policy-invariant auxiliary law is assumed. -/
def IndependentUnbiasedW2 : Prop :=
  ∀ {Ω X U : Type} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (PiSet : Set ((X × U) → ℝ))
    (hPiSet : ∀ π ∈ PiSet, Admissible π) (hS : ∀ π ∈ PiSet, PolicyDesign E π)
    (b0 : X → ℝ)
    (hb0 : Measurable b0) (hbi : Integrable (fun c => b0 c.1) E.PX)
    (hu : ∀ π ∈ PiSet, ∀ c,
      Integrable (fun ω => E.μhat π ω c) (E.law π) ∧
        (∫ ω, E.μhat π ω c ∂E.law π) = b0 c.1)
    (hI : ∀ π ∈ PiSet, IndependentEstimator E {π})
    (hR : ∀ π ∈ PiSet, ∀ i, Integrable
      (TreatedResidualW2 E (fun c => b0 c.1) π i) (E.law π)),
    TreatedUnbiased E (fun c => b0 c.1) PiSet

/-- The finite error used by qualified Proposition 10. -/
def EvaluationErrorW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (D : Measure (C × ℝ)) : ℝ :=
  ∫ z, |z.2 - E.μ0 z.1| ∂D

/-- Per-policy approximation and every maximizing pair's exact regret/triangle bound. -/
def Proposition10ConclusionW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) (ε : ℝ) : Prop :=
  (∀ π ∈ PiSet, |normalizedTT E π - E.V π| ≤ ε) ∧
    ∀ b s, IsBest PiSet E.expectedTT b → IsBest PiSet E.V s →
      regret PiSet E.V b = E.V s - E.V b ∧
      regret PiSet E.V b ≤ |E.V s - normalizedTT E s| + |normalizedTT E b - E.V b| ∧
      |E.V s - normalizedTT E s| + |normalizedTT E b - E.V b| ≤ 2 * ε

/-- Proposition 10 for a common joint evaluation law, with no unbiasedness premise. -/
def CommonLawProposition10W2 : Prop :=
  ∀ {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (PiSet : Set (C → ℝ))
    (hPiSet : ∀ π ∈ PiSet, Admissible π) (hS : ∀ π ∈ PiSet, PolicyDesign E π)
    (hI : ∀ π ∈ PiSet, CoinMomentW2 E π) (D : Measure (C × ℝ))
    (hD : IsProbabilityMeasure D)
    (hc : ∀ π ∈ PiSet, ∀ i,
      IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω))) id (E.law π) D)
    (he : Integrable (fun z => |z.2 - E.μ0 z.1|) D),
    Proposition10ConclusionW2 E PiSet (EvaluationErrorW2 E D)

/-- Proposition 10 in its independent auxiliary-data setting. The common law and
weighted treatment-estimator moment are conclusions, not extra assumptions. -/
def AuxiliaryProposition10W2 : Prop :=
  ∀ {Ω X U A : Type} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace U] [MeasurableSpace A] {n : ℕ}
    (E : Experiment Ω (X × U) n) (PiSet : Set ((X × U) → ℝ))
    (hPiSet : ∀ π ∈ PiSet, Admissible π) (hS : ∀ π ∈ PiSet, PolicyDesign E π)
    (Q : Measure A) (Z : Ω → A) (f : A × X → ℝ)
    (hA : AuxiliaryDataW2 E PiSet Q Z f)
    (he : Integrable (fun z => |z.2 - E.μ0 z.1|) (AuxiliaryLawW2 E Q f)),
    (∀ π ∈ PiSet, ∀ i,
      IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω)))
        id (E.law π) (AuxiliaryLawW2 E Q f) ∧
      (∫ ω, |E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω)| ∂E.law π) =
        EvaluationErrorW2 E (AuxiliaryLawW2 E Q f)) ∧
    Proposition10ConclusionW2 E PiSet (EvaluationErrorW2 E (AuxiliaryLawW2 E Q f))

/-- P006-T8; PDF p. 7 (Section 5); PDF pp. 21-22 (Appendix D.2:
Lemma 2, Proposition 10, Theorem 3 and proof).
Under the usual measure-theoretic conditions, treated conditional unbiasedness
at the marginal untreated baseline gives the normalized TT identity, the exact
marginal-heterogeneity bias identity and bound, and regret at most twice the
marginal heterogeneity for every reward and welfare maximizing pair in any
feasible class. The selected conditional-mean formulation is equivalent, and
independent pointwise-unbiased auxiliary data suffice on the treated-residual
integrability domain. Qualified Lemma 2 is a sum over units; its n-times form
for every fixed unit is equivalent to equality of weighted evaluation means,
which a common joint evaluation law supplies. Conditional independence implies
the required weighted moment, equivalent to factorization when the full
evaluation is integrable. Qualified Proposition 10 gives the uniform absolute
error and regret/triangle bounds for a common evaluation law, including the
derived independent auxiliary-data case, without unbiasedness. All estimator
moments are confined to feasible policies; the main clauses require no
integrability on untreated observations. Maximizers are needed only for regret.
-/
def T8WholeStatement_W2 : Prop :=
  InformationBoundW2 ∧ SelectedEquivalenceW2 ∧ IndependentUnbiasedW2 ∧
    QualifiedLemma2W2 ∧ CoinFactorizationW2 ∧ CommonLawProposition10W2 ∧
    AuxiliaryProposition10W2

end
end SAP.P006a
