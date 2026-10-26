import AronowAudit.P018.Wave1.PrintedLemma1Blueprint

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace AronowAudit.P018.Wave1.PrintedLemma1
open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
noncomputable section

local instance instProbabilityNonlinearN3 (N : ℕ) :
    IsProbabilityMeasure (unitSampleLaw nonlinearKernel N) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => uniformUnitLaw))
  infer_instance

theorem epsilon_formula {N : ℕ} (ω : Fin N → ℝ) (d : Dyad N) :
    epsilon nonlinearKernel ω d = (ω (firstUnit d) + ω (secondUnit d)) ^ 2 - 2/3 := by
  unfold epsilon populationResidual
  rw [nonlinear_population_projection.2.2.2]
  simp [nonlinearKernel, dot, Fin.sum_univ_two]

theorem design_measurable {N : ℕ} :
    Measurable (design (N := N) nonlinearKernel) := by
  unfold design nonlinearKernel
  apply measurable_pi_lambda
  intro d
  apply measurable_pi_lambda
  intro a
  fin_cases a <;> simp <;> fun_prop

theorem epsilon_design_measurable {N : ℕ} (d : Dyad N) :
    Measurable[designSigma (N := N) nonlinearKernel] (fun ω => epsilon nonlinearKernel ω d) := by
  have hdesign : Measurable[designSigma (N := N) nonlinearKernel]
      (design (N := N) nonlinearKernel) := comap_measurable _
  have hd := (measurable_pi_apply 1).comp ((measurable_pi_apply d).comp hdesign)
  convert (hd.sub_const 2).pow_const 2 |>.sub_const (2/3 : ℝ) using 1
  funext ω
  rw [epsilon_formula]
  simp [design, nonlinearKernel]
  <;> ring

theorem epsilon_integrable {N : ℕ} (d : Dyad N) :
    Integrable (fun ω => epsilon nonlinearKernel ω d) (unitSampleLaw nonlinearKernel N) := by
  have hi := (uniform_unit_power_L2 1).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin N => uniformUnitLaw) (firstUnit d))
  have hj := (uniform_unit_power_L2 1).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin N => uniformUnitLaw) (secondUnit d))
  simp only [epsilon_formula]
  change Integrable (fun ω : Fin N → ℝ =>
    (ω (firstUnit d) + ω (secondUnit d))^2 - 2/3)
    (Measure.pi (fun _ : Fin N => uniformUnitLaw))
  have h := (hi.add hj).integrable_sq.sub (integrable_const (2/3 : ℝ))
  apply h.congr
  filter_upwards [] with ω
  simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, pow_one]
  <;> rfl

theorem residual_mean_eq {N : ℕ} (d : Dyad N) :
    conditionalResidualMean nonlinearKernel d = fun ω => epsilon nonlinearKernel ω d := by
  unfold conditionalResidualMean
  exact condExp_of_stronglyMeasurable design_measurable.comap_le
    (epsilon_design_measurable d).stronglyMeasurable (epsilon_integrable d)

theorem residual_cov_zero {N : ℕ} (d f : Dyad N) :
    conditionalResidualCov nonlinearKernel d f = 0 := by
  unfold conditionalResidualCov
  simp only [residual_mean_eq, sub_self, mul_zero]
  exact condExp_zero

theorem n3_proof : N3 := by
  unfold N3 printedSigma
  have ht : ∀ d f : Dyad 3, conditionalTerm nonlinearKernel d f = 0 := by
    intro d f
    ext a b
    simp [conditionalTerm, meanMat, residual_cov_zero]
  simp [ht]
end
end AronowAudit.P018.Wave1.PrintedLemma1
