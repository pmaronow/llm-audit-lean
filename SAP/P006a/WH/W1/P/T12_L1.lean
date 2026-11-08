import SAP.P006a.WH.W1.Leaves
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace SAP.P006a.WH.W1.P.T12_L1

noncomputable section

open SAP.P006a

lemma interval_cutoff_integral [IsProbabilityMeasure intervalLaw]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ v : ℝ, (if v ≤ p then (1 : ℝ) else 0) ∂intervalLaw) = p := by
  have hset : Set.Iic p ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 p := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hvp, hv0, hv1⟩
      exact ⟨hv0, hvp⟩
    · rintro ⟨hv0, hvp⟩
      exact ⟨hvp, hv0, hvp.trans hp1⟩
  have hmeasure : intervalLaw (Set.Iic p) = ENNReal.ofReal p := by
    rw [intervalLaw, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc]
    simp
  have hfun : (fun v : ℝ => if v ≤ p then (1 : ℝ) else 0) =
      (Set.Iic p).piecewise (fun _ => (1 : ℝ)) (fun _ => 0) := by
    funext v
    by_cases hv : v ≤ p <;> simp [Set.piecewise, Set.mem_Iic, hv]
  rw [hfun, integral_piecewise measurableSet_Iic (integrable_const _) (integrable_const _)]
  simp only [setIntegral_const, smul_eq_mul, mul_one, mul_zero, add_zero]
  rw [measureReal_def, hmeasure, ENNReal.toReal_ofReal hp0]

theorem T12_L1_proof : SAP.P006a.WH.W1.T12_L1 := by
  classical
  intro ν hν π hπ
  letI : IsProbabilityMeasure ν := hν
  have hinterval : IsProbabilityMeasure intervalLaw := by
    apply isProbabilityMeasure_iff.mpr
    rw [intervalLaw, Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  letI : IsProbabilityMeasure intervalLaw := hinterval
  let μ : Measure (ℝ × ℝ) := ν.prod intervalLaw
  let f : ℝ × ℝ → ℝ := fun ω => bit (decide (ω.2 ≤ π ω.1))
  let g : ℝ × ℝ → ℝ := fun ω => π ω.1
  have hπmeas : @Measurable ℝ ℝ (inferInstance : MeasurableSpace ℝ)
      (inferInstance : MeasurableSpace ℝ) π := hπ.1
  have hfst : @Measurable (ℝ × ℝ) ℝ Prod.instMeasurableSpace
      (inferInstance : MeasurableSpace ℝ)
      (Prod.fst : ℝ × ℝ → ℝ) := by
    exact measurable_fst
  have hsnd : @Measurable (ℝ × ℝ) ℝ Prod.instMeasurableSpace
      (inferInstance : MeasurableSpace ℝ)
      (Prod.snd : ℝ × ℝ → ℝ) := by
    exact measurable_snd
  have hπb (x : ℝ) : 0 ≤ π x ∧ π x ≤ 1 := hπ.2 x
  have hf_eq : f = fun ω : ℝ × ℝ => if ω.2 ≤ π ω.1 then (1 : ℝ) else 0 := by
    funext ω
    simp [f, bit]
  have hfmeas : @Measurable (ℝ × ℝ) ℝ Prod.instMeasurableSpace
      (inferInstance : MeasurableSpace ℝ) f := by
    rw [hf_eq]
    exact Measurable.ite
      (measurableSet_le hsnd (hπmeas.comp hfst))
      measurable_const measurable_const
  have hgmeas : @Measurable (ℝ × ℝ) ℝ Prod.instMeasurableSpace
      (inferInstance : MeasurableSpace ℝ) g :=
    hπmeas.comp hfst
  have hμprob : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hfint : Integrable f μ := by
    apply Integrable.of_bound (μ := μ) hfmeas.aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [hf_eq]
    change ‖(if ω.2 ≤ π ω.1 then (1 : ℝ) else 0)‖ ≤ 1
    split_ifs <;> norm_num
  have hgint : Integrable g μ := by
    apply Integrable.of_bound (μ := μ) hgmeas.aestronglyMeasurable 1
    filter_upwards [] with ω
    change |π ω.1| ≤ 1
    rw [abs_le]
    exact ⟨by linarith [hπb ω.1], (hπb ω.1).2⟩
  have hfstCond : @Measurable (ℝ × ℝ) ℝ
      (MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) (inferInstance : MeasurableSpace ℝ))
      (inferInstance : MeasurableSpace ℝ) (Prod.fst : ℝ × ℝ → ℝ) := by
    exact measurable_iff_comap_le.mpr le_rfl
  have hGm : Measurable[
      MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) (inferInstance : MeasurableSpace ℝ)] g := by
    change Measurable[
      MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) (inferInstance : MeasurableSpace ℝ)]
      (π ∘ Prod.fst)
    exact hπmeas.comp hfstCond
  have hmap : Measure.map (Prod.fst : ℝ × ℝ → ℝ) μ = ν := by
    dsimp [μ]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
  have hmle : MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ)
      (inferInstance : MeasurableSpace ℝ) ≤ Prod.instMeasurableSpace := by
    exact hfst.comap_le
  change μ[f | MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ)
      (inferInstance : MeasurableSpace ℝ)] =ᵐ[μ] g
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hmle hfint
    (fun s hs hfin => hgint.integrableOn)
    _ hGm.aestronglyMeasurable
  intro s hs hfin
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hpre : (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' B = B ×ˢ (Set.univ : Set ℝ) := by
    ext ω
    simp
  have hleft :
      (∫ ω in (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' B, g ω ∂μ) =
        ∫ x in B, π x ∂ν := by
    rw [← hmap]
    symm
    exact setIntegral_map hB hπmeas.aestronglyMeasurable hfst.aemeasurable
  have hfiber (x : ℝ) :
      (∫ v : ℝ, f (x, v) ∂intervalLaw) = π x := by
    rw [hf_eq]
    exact interval_cutoff_integral (π x) (hπb x).1 (hπb x).2
  have hright :
      (∫ ω in (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' B, f ω ∂μ) =
        ∫ x in B, π x ∂ν := by
    change (∫ ω in (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' B, f ω ∂(ν.prod intervalLaw)) = _
    rw [hpre, setIntegral_prod _ hfint.integrableOn]
    simp only [setIntegral_univ, hfiber]
  exact hleft.trans hright.symm

end
end SAP.P006a.WH.W1.P.T12_L1

theorem SAP.P006a.WH.W1.T12_L1_proof : SAP.P006a.WH.W1.T12_L1 :=
  SAP.P006a.WH.W1.P.T12_L1.T12_L1_proof
