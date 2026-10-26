import AronowAudit.P022.Wave1.SharpBounds.N5

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

theorem n7_proof : N7 := by
  intro N _ y1 y0 J h1 h0
  classical
  have hs1 : MeasurableSet (Set.range y1) := (Set.finite_range y1).measurableSet
  have hs0 : MeasurableSet (Set.range y0) := (Set.finite_range y0).measurableSet
  have ha1 : ∀ᵐ p ∂(J : Measure (ℝ × ℝ)), p.1 ∈ Set.range y1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [h1]
    exact ae_map_mem_range hs1 (measurable_of_finite _).aemeasurable
  have ha0 : ∀ᵐ p ∂(J : Measure (ℝ × ℝ)), p.2 ∈ Set.range y0 := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [h0]
    exact ae_map_mem_range hs0 (measurable_of_finite _).aemeasurable
  have hs : ∀ᵐ p ∂(J : Measure (ℝ × ℝ)), p.1 ∈ Set.range y1 ∧ p.2 ∈ Set.range y0 :=
    ha1.and ha0
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    let M : ℝ := ∑ i : Fin N, ∑ j : Fin N, ‖g (y1 i, y0 j)‖
    apply (integrable_const M).mono' hg.aestronglyMeasurable
    filter_upwards [hs] with p hp
    obtain ⟨i, hi⟩ := hp.1
    obtain ⟨j, hj⟩ := hp.2
    have heq : p = (y1 i, y0 j) := Prod.ext hi.symm hj.symm
    rw [heq]
    exact (Finset.single_le_sum (fun j _ => norm_nonneg (g (y1 i, y0 j))) (mem_univ j)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg (g (y1 i, y0 j)))) (mem_univ i))
  · change (∫ p, p.1 ∂(J : Measure (ℝ × ℝ))) = _
    calc
      _ = ∫ x : ℝ, x ∂((J : Measure (ℝ × ℝ)).map Prod.fst) :=
        (integral_map_of_stronglyMeasurable measurable_fst measurable_id'.stronglyMeasurable).symm
      _ = _ := by
        rw [h1, integral_map_of_stronglyMeasurable (measurable_of_finite _) measurable_id'.stronglyMeasurable,
          integral_unitLaw]
  · change (∫ p, p.2 ∂(J : Measure (ℝ × ℝ))) = _
    calc
      _ = ∫ x : ℝ, x ∂((J : Measure (ℝ × ℝ)).map Prod.snd) :=
        (integral_map_of_stronglyMeasurable measurable_snd measurable_id'.stronglyMeasurable).symm
      _ = _ := by
        rw [h0, integral_map_of_stronglyMeasurable (measurable_of_finite _) measurable_id'.stronglyMeasurable,
          integral_unitLaw]
  · intro c
    have hc : MeasurableSet (Set.Ici c) := measurableSet_Ici
    have hmap := congrArg (fun μ : Measure ℝ => (μ (Set.Ici c)).toReal) h1
    rw [Measure.map_apply measurable_fst hc,
      Measure.map_apply (measurable_of_finite _) hc, measure_unitLaw] at hmap
    exact hmap
  · intro e
    have he : MeasurableSet (Set.Ici e) := measurableSet_Ici
    have hmap := congrArg (fun μ : Measure ℝ => (μ (Set.Ici e)).toReal) h0
    rw [Measure.map_apply measurable_snd he,
      Measure.map_apply (measurable_of_finite _) he, measure_unitLaw] at hmap
    exact hmap

end
end AronowAudit.P022.Wave1.SharpBounds
