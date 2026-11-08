import SAP.P001e.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v w
noncomputable section

/-- Standardization evaluates a conditional version only in positive-mass cells. -/
def positiveCellAverage {Ω E : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → E) (m : E → ℝ) : ℝ :=
  ∑' x : E, if 0 < probability μ {ω | X ω=x} then
    m x * probability μ {ω | X ω=x} else 0

/-- Continuous-dose identification with an independent measurable curve state. -/
def T91ContinuousIdentification : Prop :=
  ∀ {Ω : Type u} {E : Type v} {V : Type w}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace V]
    [MeasurableSingletonClass E] [Countable E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D)
    (curve : Ω → V) (hcurve : Measurable curve) (eval : ℝ → V → ℝ)
    (heval : Measurable (fun z : ℝ × V => eval z.1 z.2))
    (hfaithful : Function.Injective (fun s : V => fun t : ℝ => eval t s))
    (hind : CondIndependent μ X hX curve D)
    (hi : ∀ t, Integrable (fun ω => eval t (curve ω)) μ)
    (hobs : Integrable (fun ω => eval (D ω) (curve ω)) μ)
    (d d' : ℝ)
    (hm : ∀ x, 0 < probability μ {ω | X ω=x} →
      ContinuousAt (fun t => cellMean μ X (fun ω => eval t (curve ω)) x) d ∧
      ContinuousAt (fun t => cellMean μ X (fun ω => eval t (curve ω)) x) d')
    (hsupp : ∀ x, 0 < probability μ {ω | X ω=x} → ∀ ε : ℝ, 0 < ε →
      0 < μ {ω | X ω=x ∧ D ω ∈ Metric.ball d ε} ∧
      0 < μ {ω | X ω=x ∧ D ω ∈ Metric.ball d' ε}),
    let Y := fun t ω => eval t (curve ω)
    let m := fun x t => cellMean μ X (Y t) x
    (∀ x, 0 < probability μ {ω | X ω=x} →
      IsConditionalMean (μ.restrict {ω | X ω=x}) D (fun ω => Y (D ω) ω) (m x)) ∧
    (∀ t : ℝ, expectation μ (Y t)=positiveCellAverage μ X (fun x => m x t)) ∧
    expectation μ (fun ω => Y d' ω-Y d ω) =
      positiveCellAverage μ X (fun x => m x d') -
      positiveCellAverage μ X (fun x => m x d) ∧
    (∀ mobs : E → ℝ → ℝ,
      (∀ x, 0 < probability μ {ω | X ω=x} →
        IsConditionalMean (μ.restrict {ω | X ω=x}) D (fun ω => Y (D ω) ω) (mobs x) ∧
        ContinuousAt (mobs x) d ∧ ContinuousAt (mobs x) d') →
      (∀ x, 0 < probability μ {ω | X ω=x} →
        mobs x d=m x d ∧ mobs x d'=m x d') ∧
      expectation μ (fun ω => Y d' ω-Y d ω) =
        positiveCellAverage μ X (fun x => mobs x d') -
        positiveCellAverage μ X (fun x => mobs x d))

/-- Positive-mass identification and the restricted evaluation-ready result. -/
def T91IdentificationStatement : Prop :=
  T91Statement.{u,v} ∧ T91ContinuousIdentification.{u,v,w}

end
end SAP.P001e
