import SAP.P001b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b.WH.W2.P.T30_L1

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

theorem rectangle_eq_withDensity
    (ν : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ)
    (hf : SAP.P001b.JointCDFDensity ν f) (x y : ℝ) :
    ν (Set.Iic x ×ˢ Set.Iic y) =
      (volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (f z)))
        (Set.Iic x ×ˢ Set.Iic y) := by
  rw [← hf.2.2 x y, withDensity_apply _ (measurableSet_Iic.prod measurableSet_Iic)]
  exact (setLIntegral_prod (fun z : ℝ × ℝ => ENNReal.ofReal (f z))
    hf.1.ennreal_ofReal.restrict).symm

theorem rectangle_eq_of_lower_rectangles
    (ν ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (hrect : ∀ x y : ℝ, ν (Set.Iic x ×ˢ Set.Iic y) = ρ (Set.Iic x ×ˢ Set.Iic y))
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ν (A ×ˢ B) = ρ (A ×ˢ B) := by
  have hfirst (b : ℝ) :
      (ν.restrict (Set.univ ×ˢ Set.Iic b)).map Prod.fst =
        (ρ.restrict (Set.univ ×ˢ Set.Iic b)).map Prod.fst := by
    apply Measure.ext_of_Iic
    intro a
    have hs : (Prod.fst ⁻¹' Set.Iic a) ∩ (Set.univ ×ˢ Set.Iic b) =
        Set.Iic a ×ˢ Set.Iic b := by
      ext z
      simp [Prod.le_def]
    rw [Measure.map_apply measurable_fst measurableSet_Iic,
      Measure.map_apply measurable_fst measurableSet_Iic]
    rw [Measure.restrict_apply (measurableSet_Iic.preimage measurable_fst),
      Measure.restrict_apply (measurableSet_Iic.preimage measurable_fst)]
    simpa only [hs] using hrect a b
  have hstrip (A : Set ℝ) (hA : MeasurableSet A) (b : ℝ) :
      ν (A ×ˢ Set.Iic b) = ρ (A ×ˢ Set.Iic b) := by
    have heq := congrArg (fun m : Measure ℝ => m A) (hfirst b)
    have hs : (Prod.fst ⁻¹' A) ∩ (Set.univ ×ˢ Set.Iic b) = A ×ˢ Set.Iic b := by
      ext z
      simp
    simp only [Measure.map_apply measurable_fst hA,
      Measure.restrict_apply (hA.preimage measurable_fst)] at heq
    simpa only [hs] using heq
  have hsecond (A : Set ℝ) (hA : MeasurableSet A) :
      (ν.restrict (A ×ˢ Set.univ)).map Prod.snd =
        (ρ.restrict (A ×ˢ Set.univ)).map Prod.snd := by
    apply Measure.ext_of_Iic
    intro b
    have hs : (Prod.snd ⁻¹' Set.Iic b) ∩ (A ×ˢ Set.univ) = A ×ˢ Set.Iic b := by
      ext z
      simp [and_comm]
    rw [Measure.map_apply measurable_snd measurableSet_Iic,
      Measure.map_apply measurable_snd measurableSet_Iic]
    rw [Measure.restrict_apply (measurableSet_Iic.preimage measurable_snd),
      Measure.restrict_apply (measurableSet_Iic.preimage measurable_snd)]
    simpa only [hs] using hstrip A hA b
  have heq := congrArg (fun m : Measure ℝ => m B) (hsecond A hA)
  have hs : (Prod.snd ⁻¹' B) ∩ (A ×ˢ Set.univ) = A ×ˢ B := by
    ext z
    simp [and_comm]
  rw [Measure.map_apply measurable_snd hB,
    Measure.map_apply measurable_snd hB] at heq
  rw [Measure.restrict_apply (hB.preimage measurable_snd),
    Measure.restrict_apply (hB.preimage measurable_snd)] at heq
  simpa only [hs] using heq

end
end SAP.P001b.WH.W2.P.T30_L1

open MeasureTheory
open scoped ENNReal

theorem SAP.P001b.WH.W2.T30_L1_proof : SAP.P001b.WH.W2.T30_L1 := by
  intro ν _ f hf
  let ρ : Measure (ℝ × ℝ) :=
    volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (f z))
  have hrect : ∀ x y : ℝ, ν (Set.Iic x ×ˢ Set.Iic y) = ρ (Set.Iic x ×ˢ Set.Iic y) := by
    intro x y
    exact SAP.P001b.WH.W2.P.T30_L1.rectangle_eq_withDensity ν f hf x y
  have hνρ : ν = ρ := by
    apply Measure.ext_prod
    intro A B hA hB
    exact SAP.P001b.WH.W2.P.T30_L1.rectangle_eq_of_lower_rectangles ν ρ hrect hA hB
  have hmass : (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (f z) ∂volume) = 1 := by
    have h := congrArg (fun μ : Measure (ℝ × ℝ) => μ Set.univ) hνρ
    dsimp [ρ] at h
    rw [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h.symm
  refine ⟨hf.1, hf.2.1, ?_, hνρ⟩
  apply (lintegral_ofReal_ne_top_iff_integrable hf.1.aestronglyMeasurable
    (ae_of_all _ hf.2.1)).mp
  rw [hmass]
  exact ENNReal.one_ne_top
