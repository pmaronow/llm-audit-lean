import AronowAudit.P001.Wave1.SieveRateBlueprint
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The PDF, first moment, and zero CEF of the witness. -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.SieveRate

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem n2_proof : N2 := by
  classical
  intro hN1
  letI : IsProbabilityMeasure sieveMu := hN1.1
  have hZ : Measurable (fun ω => (sieveX 0 ω, sieveY 0 ω)) := hN1.2.1.1 0
  have hYmeas : Measurable (sieveY 0) := measurable_snd.comp hZ
  have hYlaw : sieveMu.map (sieveY 0) = gaussianReal 0 1 := by
    change sieveMu.map (Prod.snd ∘ (fun ω => (sieveX 0 ω, sieveY 0 ω))) = _
    rw [← Measure.map_map measurable_snd hZ, hN1.2.2.1]
    simp only [sieveNu, Measure.map_snd_prod, measure_univ, one_smul]
  have hgauss : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) := by
    apply memLp_one_iff_integrable.mp
    simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) (1 : ℝ≥0))
  have hY : Integrable (sieveY 0) sieveMu := by
    have hid : Integrable (id : ℝ → ℝ) (sieveMu.map (sieveY 0)) := by
      rw [hYlaw]
      exact hgauss
    simpa only [Function.comp_def, id_eq] using hid.comp_measurable hYmeas
  have hF : sieveF = (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp only [sieveF, Set.indicator_apply]
  have hFmeas : Measurable sieveF := by
    rw [hF]
    exact measurable_const.indicator measurableSet_Icc
  have hFint : Integrable sieveF volume := by
    rw [hF]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (by norm_num [Real.volume_Icc])
  have hpdf : HasPDF (sieveMu.map (sieveX 0)) sieveF := by
    refine ⟨hFmeas.aemeasurable, ?_, hFint, ?_⟩
    · intro x
      unfold sieveF
      split_ifs <;> norm_num
    · rw [hN1.2.2.2]
      simp only [uniformLaw, sieveF, sub_zero, inv_one]
  have hprodY : Integrable (Prod.snd : ℝ × ℝ → ℝ) sieveNu := by
    exact hgauss.comp_snd (uniformLaw 0 1)
  have hcef : IsCEF sieveMu (sieveX 0) (sieveY 0) sieveM := by
    refine ⟨measurable_const, hY, ?_, ?_⟩
    · simpa only [sieveM, Function.comp_def] using
        (integrable_const (μ := sieveMu) (0 : ℝ))
    · intro A hA
      have hAfst : MeasurableSet (Prod.fst ⁻¹' A : Set (ℝ × ℝ)) :=
        measurable_fst hA
      have htransport :
          (∫ z in Prod.fst ⁻¹' A, z.2 ∂sieveNu) =
            ∫ ω in sieveX 0 ⁻¹' A, sieveY 0 ω ∂sieveMu := by
        have h := setIntegral_map (μ := sieveMu)
          (g := fun ω => (sieveX 0 ω, sieveY 0 ω))
          (f := Prod.snd) hAfst measurable_snd.aestronglyMeasurable hZ.aemeasurable
        rw [hN1.2.2.1] at h
        exact h
      have hbox : (Prod.fst ⁻¹' A : Set (ℝ × ℝ)) = A ×ˢ Set.univ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
      have hzero : (∫ z in Prod.fst ⁻¹' A, z.2 ∂sieveNu) = 0 := by
        rw [hbox]
        change (∫ z in A ×ˢ Set.univ, z.2
          ∂(uniformLaw 0 1).prod (gaussianReal 0 1)) = 0
        rw [setIntegral_prod (fun z : ℝ × ℝ => z.2) hprodY.integrableOn]
        simp only [setIntegral_univ, integral_id_gaussianReal, integral_zero]
      calc
        (∫ ω in sieveX 0 ⁻¹' A, sieveY 0 ω ∂sieveMu) =
            ∫ z in Prod.fst ⁻¹' A, z.2 ∂sieveNu := htransport.symm
        _ = 0 := hzero
        _ = ∫ ω in sieveX 0 ⁻¹' A, sieveM (sieveX 0 ω) ∂sieveMu := by
          simp only [sieveM, integral_zero]
  exact ⟨hpdf, hY, hcef⟩

end

end AronowAudit.P001.Wave1.SieveRate
