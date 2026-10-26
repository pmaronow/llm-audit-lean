import AronowAudit.P018.Wave1.PrintedScalarCorollariesBlueprint
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace AronowAudit.P018.Wave1.PrintedScalarCorollaries
open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
noncomputable section

local instance instProbabilityFairN2 : IsProbabilityMeasure fairLaw := by
  unfold fairLaw
  infer_instance

theorem sign_memLp : MemLp signValue 2 fairLaw := by
  apply MemLp.of_bound (by measurability) 1
  filter_upwards [] with b
  cases b <;> norm_num [signValue]

theorem sign_variance : variance signValue fairLaw = 1 := by
  rw [variance_eq_sub sign_memLp]
  norm_num [fairLaw, PMF.integral_eq_sum, Fintype.sum_bool, signValue,
    PMF.uniformOfFintype_apply]
  have he : ({false, true} : Set Bool) = Set.univ := by
    ext b; cases b <;> simp
  rw [he]
  exact probReal_univ

theorem n2_proof : N2 := by
  intro N
  change variance (fun ω : Fin N → Bool => ∑ i, signValue (ω i))
    (Measure.pi (fun _ => fairLaw)) = N
  have h := variance_sum_pi (μ := fun _ : Fin N => fairLaw)
    (X := fun _ => signValue) (fun _ => sign_memLp)
  have he : (∑ i : Fin N, fun ω : Fin N → Bool => signValue (ω i)) =
      (fun ω => ∑ i, signValue (ω i)) := by ext ω; simp
  rw [he] at h
  simpa only [sign_variance, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] using h
end
end AronowAudit.P018.Wave1.PrintedScalarCorollaries
