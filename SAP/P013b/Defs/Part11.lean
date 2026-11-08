import Mathlib
import SAP.P013b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013b

open MeasureTheory Filter Finset
open scoped BigOperators Topology ENNReal

/-- The measure of the exact finite randomization law used for replicate draws. -/
noncomputable def designMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (P : Design Ω) : Measure Ω :=
  ∑ z, ENNReal.ofReal (P.weight z) • Measure.dirac z

/-- Both simulated matrix limits for mutually independent replicate assignments,
each drawn from the exact design law: almost surely, for every exposure `d` and
every unit pair, the smoothed same-exposure entry converges, and for every
exposure `e ≠ d` the cross-exposure entry converges. -/
def T20Statement : Prop :=
  ∀ {Ω : Type*} {A : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {N K : ℕ}
    (P : Design Ω) (D : Ω → Fin N → Fin K)
    (Z : ℕ → A → Ω), (∀ r, Measurable (Z r)) →
    ProbabilityTheory.iIndepFun Z μ →
    (∀ r, Measure.map (Z r) μ = designMeasure P) →
    ∀ᵐ a ∂μ, ∀ d : Fin K, ∀ i j : Fin N,
      Tendsto (fun R : ℕ => ((∑ r ∈ range R,
        indicator D i d (Z r a) * indicator D j d (Z r a)) +
          (if i = j then 1 else 0)) / (R + 1 : ℝ)) atTop
        (𝓝 (∑ z, P.weight z * (indicator D i d z * indicator D j d z))) ∧
      ∀ e : Fin K, d ≠ e →
      Tendsto (fun R : ℕ => (∑ r ∈ range R,
        indicator D i d (Z r a) * indicator D j e (Z r a)) / (R : ℝ)) atTop
        (𝓝 (∑ z, P.weight z * (indicator D i d z * indicator D j e z)))

end SAP.P013b
