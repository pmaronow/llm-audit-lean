import AronowAudit.P018.Wave1.PrintedLemma1Blueprint

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace AronowAudit.P018.Wave1.PrintedLemma1
open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
noncomputable section

theorem uniform_singleton (x : ℝ) : uniformUnitLaw {x} = 0 := by
  unfold uniformUnitLaw
  rw [ProbabilityTheory.cond_apply measurableSet_Icc]
  have h : volume (Set.Icc (-1 : ℝ) 1 ∩ {x}) = 0 :=
    measure_mono_null Set.inter_subset_right (by simp)
  rw [h, mul_zero]

theorem n2_proof : N2 := by
  intro N hN
  let i : Fin N := ⟨1, by omega⟩
  let j : Fin N := ⟨2, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hind := (iIndepFun_pi (μ := fun _ : Fin N => uniformUnitLaw)
    (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).indepFun hij
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simp only [Function.id_def, (measurePreserving_eval _ i).map_eq,
    (measurePreserving_eval _ j).map_eq] at hmap
  have hd : (uniformUnitLaw.prod uniformUnitLaw) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
    have he : ∀ x : ℝ, (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = {x} := by
      intro x
      ext y
      simp [eq_comm]
    simp only [he, uniform_singleton, lintegral_zero]
  rw [← hmap, Measure.map_apply (by fun_prop)
    (measurableSet_eq_fun measurable_fst measurable_snd)] at hd
  exact hd
end
end AronowAudit.P018.Wave1.PrintedLemma1
