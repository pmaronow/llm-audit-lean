import AronowAudit.P001.Wave1.GapLawBlueprint
import AronowAudit.P001.Wave1.GapLaw.N1
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.GapLaw

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

theorem n5_proof : N5 := by
  classical
  intro h1 h2 h3
  letI : IsProbabilityMeasure gapJointLaw := h1.1
  letI : IsProbabilityMeasure gapMarginal := gap_marginal_probability
  letI : IsProbabilityMeasure (uniformLaw (-1) 1) := gap_uniform_probability
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hmp : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have hfst : gapJointLaw.map Prod.fst = gapMarginal := by
    change (gapMarginal.prod (uniformLaw (-1) 1)).map Prod.fst = gapMarginal
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hlaw : gapJointLaw.map gapX = gapMarginal.map e.symm := by
    rw [← hfst, Measure.map_map e.symm.measurable measurable_fst]
    rfl
  have hpdf : HasVectorPDF (gapJointLaw.map gapX) (fun x => gapPDF (x 0)) := by
    have hm : Measurable (fun x : Fin 1 → ℝ => gapPDF (x 0)) :=
      gap_pdf_measurable.comp (measurable_pi_apply 0)
    refine ⟨hm.aemeasurable, fun x => gap_pdf_nonneg (x 0), ?_, ?_⟩
    · exact hmp.integrable_comp_of_integrable gap_pdf_integrable
    · rw [hlaw]
      ext A hA
      rw [Measure.map_apply e.symm.measurable hA]
      change volume.withDensity (fun r => ENNReal.ofReal (gapPDF r))
          (e.symm ⁻¹' A) =
        volume.withDensity (fun x : Fin 1 → ℝ => ENNReal.ofReal (gapPDF (x 0))) A
      rw [withDensity_apply _ (e.symm.measurable hA), withDensity_apply _ hA]
      have hchange := (MeasurePreserving.symm e hmp).setLIntegral_comp_preimage_emb
        e.symm.measurableEmbedding
        (fun x : Fin 1 → ℝ => ENNReal.ofReal (gapPDF (x 0))) A
      exact hchange
  obtain ⟨hcef0, hcefb⟩ := h3 h1 h2
  have htransport (m : ℝ → ℝ) (hc : IsCEF gapJointLaw Prod.fst Prod.snd m) :
      IsCEF gapJointLaw gapX Prod.snd (fun x => m (x 0)) := by
    refine ⟨hc.1.comp (measurable_pi_apply 0), hc.2.1, hc.2.2.1, fun A hA => ?_⟩
    have hmA : MeasurableSet (e.symm ⁻¹' A) := e.symm.measurable hA
    have hevent : gapX ⁻¹' A = Prod.fst ⁻¹' (e.symm ⁻¹' A) := rfl
    rw [hevent]
    exact hc.2.2.2 _ hmA
  exact ⟨hpdf, htransport (fun _ => 0) hcef0, htransport pdaBump hcefb⟩

end

end AronowAudit.P001.Wave1.GapLaw
