import AronowAudit.P047.Wave1.ImpossibilityBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-- S2 applied twice gives joint ignorability; armwise ignorability is its projection. -/
theorem n3_proof : N3 := by
  classical
  intro s2 e m he hm heb hmb
  have hJ : JointIgnorableM (genMeasure e m) e := by
    intro a f hf _
    let g₀ : Bool × ℝ × ℝ → ℝ := fun x => f x.2
    let g₁ : Bool × ℝ × ℝ → ℝ := fun x => (if x.1 = a then 1 else 0) * f x.2
    have hg₀ : Measurable g₀ := hf.comp measurable_snd
    have hg₁ : Measurable g₁ := by
      exact (Measurable.ite ((measurable_fst : Measurable
        (fun x : Bool × ℝ × ℝ => x.1)) (measurableSet_singleton a))
        measurable_const measurable_const).mul hg₀
    have h₀ := s2 e m he hm heb hmb g₀ hg₀
    have h₁ := s2 e m he hm heb hmb g₁ hg₁
    change (genMeasure e m)[fun u => (if u.2.1 = a then 1 else 0) * f u.2.2 |
      covariateSigma] =ᵐ[genMeasure e m] fun u => armPropensity e a u *
        ((genMeasure e m)[fun v => f v.2.2 | covariateSigma]) u
    filter_upwards [h₀, h₁] with u hu₀ hu₁
    change ((genMeasure e m)[fun v => f v.2.2 | covariateSigma]) u = _ at hu₀
    change ((genMeasure e m)[fun v => (if v.2.1 = a then 1 else 0) * f v.2.2 |
      covariateSigma]) u = _ at hu₁
    rw [hu₁, hu₀]
    cases a <;> simp only [g₀, g₁, armPropensity, covariate, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte, zero_mul, one_mul] <;> ring
  refine ⟨?_, hJ⟩
  intro a f hf hfi
  let F : ℝ × ℝ → ℝ := fun y => f (if a then y.2 else y.1)
  have hF : Measurable F := by
    cases a
    · exact hf.comp measurable_fst
    · exact hf.comp measurable_snd
  have hFi : Integrable (fun u => F (potential false u, potential true u)) (genMeasure e m) := by
    simpa only [F, potential, Bool.false_eq_true, ↓reduceIte] using hfi
  simpa only [F, potential, Bool.false_eq_true, ↓reduceIte] using hJ a F hF hFi

end

end AronowAudit.P047.Wave1.Impossibility
