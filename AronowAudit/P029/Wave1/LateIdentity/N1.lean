import AronowAudit.P029.Wave1.LateIdentityBlueprint
import Mathlib.Probability.Independence.Integration

namespace AronowAudit.P029.Wave1.LateIdentity

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
open AronowAudit.P029

universe u v

noncomputable section

/-- Independence factors the integral on a positive-probability assignment arm. -/
theorem n1_proof : N1.{u} := by
  intro Ω _ μ _ Z v hZ hv hind z hz
  have hB : MeasurableSet {ω | Z ω = z} :=
    (measurableSet_singleton z).preimage hZ
  let a : Bool → ℝ := fun b => if b = z then 1 else 0
  have ha : Measurable a := Measurable.of_discrete
  have hI : Measurable (fun ω => if Z ω = z then (1 : ℝ) else 0) :=
    Measurable.ite hB measurable_const measurable_const
  have hind' : IndepFun (fun ω => if Z ω = z then (1 : ℝ) else 0) v μ := by
    simpa only [Function.comp_def, a, id_eq] using
      hind.comp ha (measurable_id : Measurable (id : ℝ → ℝ))
  have hfactor := hind'.integral_fun_mul_eq_mul_integral
    hI.aestronglyMeasurable hv.aestronglyMeasurable
  have hleft :
      (∫ ω, (if Z ω = z then (1 : ℝ) else 0) * v ω ∂μ) =
        ∫ ω in {ω | Z ω = z}, v ω ∂μ := by
    simpa only [Set.indicator, Set.mem_setOf_eq, ite_mul, one_mul, zero_mul] using
      (integral_indicator (μ := μ) (f := v) hB)
  have hmass : (∫ ω, (if Z ω = z then (1 : ℝ) else 0) ∂μ) =
      mP μ {ω | Z ω = z} := by
    simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, mP, measureReal_def] using
      (integral_indicator_one (μ := μ) hB)
  rw [hleft, hmass] at hfactor
  unfold mCE
  rw [hfactor, mul_div_cancel_left₀ _ (ne_of_gt hz)]

end

end AronowAudit.P029.Wave1.LateIdentity
