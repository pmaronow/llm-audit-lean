import SAP.P015b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

noncomputable section

theorem SAP.P015b.WH.W2.T22_L1_proof : SAP.P015b.WH.W2.T22_L1 := by
  intro Ω E B omegaSpace eSpace bSpace P hP T hT x hx f hf hi
  let R : Measure E := P.map T
  let F : Ω → ℝ := fun s => f (T s)
  let H : E → ℝ := condExp (m := MeasurableSpace.comap x bSpace) R f
  let G : Ω → ℝ := H ∘ T
  have hcomp : @Measurable Ω B omegaSpace bSpace (fun s => x (T s)) := hx.comp hT
  have hTa : @AEMeasurable Ω E eSpace omegaSpace T P := hT.aemeasurable
  have hmOmega : MeasurableSpace.comap (fun s => x (T s)) bSpace ≤ omegaSpace := by
    exact hcomp.comap_le
  have hmE : MeasurableSpace.comap x bSpace ≤ eSpace := by
    exact hx.comap_le
  have hT' : @Measurable Ω E (MeasurableSpace.comap (fun s => x (T s)) bSpace)
      (MeasurableSpace.comap x bSpace) T := by
    rw [measurable_comap_iff]
    exact comap_measurable _
  have hce_int : Integrable H R := by
    exact integrable_condExp (m := MeasurableSpace.comap x bSpace)
      (m₀ := eSpace) (μ := R) (f := f)
  have hce_meas : AEStronglyMeasurable[eSpace] H R := by
    exact (stronglyMeasurable_condExp (m := MeasurableSpace.comap x bSpace)
      (m₀ := eSpace) (μ := R) (f := f)).aestronglyMeasurable.mono hmE
  have hG_int : Integrable G P := by
    change Integrable (H ∘ T) P
    exact (@integrable_map_measure Ω ℝ omegaSpace P _ _ E eSpace T H
      hce_meas hTa).mp hce_int
  have hG_meas : AEStronglyMeasurable[MeasurableSpace.comap (fun s => x (T s)) bSpace] G P := by
    change AEStronglyMeasurable[MeasurableSpace.comap (fun s => x (T s)) bSpace] (H ∘ T) P
    exact ((stronglyMeasurable_condExp (m := MeasurableSpace.comap x bSpace)
      (m₀ := eSpace) (μ := R) (f := f)).comp_measurable hT').aestronglyMeasurable
  have hF_int : Integrable F P := by
    change Integrable (f ∘ T) P
    exact (@integrable_map_measure Ω ℝ omegaSpace P _ _ E eSpace T f
      hf.aestronglyMeasurable hTa).mp hi
  have hset : ∀ s : Set Ω,
      MeasurableSet[MeasurableSpace.comap (fun s => x (T s)) bSpace] s → P s < ∞ →
      ∫ ω in s, G ω ∂P = ∫ ω in s, F ω ∂P := by
    intro s hs _hfin
    rcases (MeasurableSpace.measurableSet_comap.mp hs) with ⟨A, hA, hAs⟩
    have hpre : s = T ⁻¹' (x ⁻¹' A) := by
      calc
        s = (fun s => x (T s)) ⁻¹' A := hAs.symm
        _ = T ⁻¹' (x ⁻¹' A) := rfl
    have hEA : @MeasurableSet E eSpace (x ⁻¹' A) := hx hA
    calc
      ∫ ω in s, G ω ∂P = integral (R.restrict (x ⁻¹' A)) H := by
        rw [hpre]
        symm
        exact @setIntegral_map Ω ℝ omegaSpace _ _ P E eSpace T H (x ⁻¹' A) hEA
          hce_meas hTa
      _ = integral (R.restrict (x ⁻¹' A)) f := by
        exact setIntegral_condExp (m := MeasurableSpace.comap x bSpace) (m₀ := eSpace)
          (μ := R) hmE hi (MeasurableSpace.measurableSet_comap.mpr ⟨A, hA, rfl⟩)
      _ = ∫ ω in s, F ω ∂P := by
        rw [hpre]
        exact @setIntegral_map Ω ℝ omegaSpace _ _ P E eSpace T f (x ⁻¹' A) hEA
          hf.aestronglyMeasurable hTa
  have huniq := ae_eq_condExp_of_forall_setIntegral_eq hmOmega hF_int
    (fun s hs hfin => hG_int.integrableOn) hset hG_meas
  exact huniq.symm
