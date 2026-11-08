import SAP.P001f.Bridge.T102PDFSupportPrelim

set_option autoImplicit false

namespace SAP.P001f.Bridge

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001
open AronowAudit.P001.Wave1.GapLaw

noncomputable section

universe u

theorem T102_pdf_support_identification_refuted :
    ¬ SAP.P001f.PDAIdentifiedPDFSupportSaturated.{u} := by
  classical
  intro H
  obtain ⟨hXm, _, _, hcoords, _, hmean0, _⟩ :=
    n4_proof n1_proof n2_proof
  obtain ⟨hpdf, hcef0, hcef1⟩ :=
    n5_proof n1_proof n2_proof n3_proof
  haveI : IsProbabilityMeasure T102RestrictedLaw := T102_restricted_probability
  have hXlaw : T102RestrictedLaw.map T102RestrictedX = gapJointLaw.map gapX := by
    change T102RestrictedLaw.map (gapX ∘ Subtype.val) = gapJointLaw.map gapX
    calc
      T102RestrictedLaw.map (gapX ∘ Subtype.val) =
          (T102RestrictedLaw.map Subtype.val).map gapX := by
        exact (Measure.map_map hXm measurable_subtype_coe).symm
      _ = gapJointLaw.map gapX := by rw [T102_restricted_map_eq]
  have hfR : RealDensity (T102RestrictedLaw.map T102RestrictedX)
      (fun x : Fin 1 → ℝ => gapPDF (x 0)) := by
    change AronowAudit.P001.HasVectorPDF
      (T102RestrictedLaw.map T102RestrictedX) (fun x : Fin 1 → ℝ => gapPDF (x 0))
    rw [hXlaw]
    exact hpdf
  obtain ⟨qv, hqv⟩ := T102_restricted_vector_joint_pdf
  have hmeanR :
      (fun j : Fin 1 => ∫ ω, T102RestrictedX ω j ∂T102RestrictedLaw) =
        (0 : Fin 1 → ℝ) := by
    let hp : MeasurePreserving (Subtype.val : T102RestrictedSample → ℝ × ℝ)
      T102RestrictedLaw gapJointLaw := T102_restricted_preserving
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (∫ ω, gapX ω.val 0 ∂T102RestrictedLaw) = 0
    calc
      (∫ ω, gapX ω.val 0 ∂T102RestrictedLaw) =
          ∫ ω, gapX ω 0 ∂gapJointLaw :=
        hp.integral_comp (MeasurableEmbedding.subtype_coe T102_sample_support_measurable)
          (fun ω => gapX ω 0)
      _ = 0 := hmean0

  let l : ULift.{u} T102RestrictedSample ≃ᵐ T102RestrictedSample := MeasurableEquiv.ulift
  let ν : Measure (ULift.{u} T102RestrictedSample) := T102RestrictedLaw.map l.symm
  have hl : MeasurePreserving l ν T102RestrictedLaw := by
    refine ⟨l.measurable, ?_⟩
    dsimp [ν]
    rw [Measure.map_map l.measurable l.symm.measurable, l.self_comp_symm, Measure.map_id]
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hlaw {E : Type} [MeasurableSpace E]
      (g : T102RestrictedSample → E) (hg : Measurable g) :
      ν.map (g ∘ l) = T102RestrictedLaw.map g := by
    rw [← Measure.map_map hg l.measurable, hl.map_eq]
  have hcef (m : (Fin 1 → ℝ) → ℝ)
      (hc : ConditionalMean T102RestrictedLaw T102RestrictedX T102RestrictedY m) :
      ConditionalMean ν (T102RestrictedX ∘ l) (T102RestrictedY ∘ l) m := by
    refine ⟨hc.1, hl.integrable_comp_of_integrable hc.2.1,
      hl.integrable_comp_of_integrable hc.2.2.1, fun A hA => ?_⟩
    change (∫ ω in l ⁻¹' (T102RestrictedX ⁻¹' A), T102RestrictedY (l ω) ∂ν) =
      ∫ ω in l ⁻¹' (T102RestrictedX ⁻¹' A),
        (m ∘ T102RestrictedX) (l ω) ∂ν
    rw [hl.setIntegral_preimage_emb l.measurableEmbedding,
      hl.setIntegral_preimage_emb l.measurableEmbedding]
    exact hc.2.2.2 A hA
  have hmeanL :
      (fun j : Fin 1 => ∫ ω, (T102RestrictedX ∘ l) ω j ∂ν) =
        (0 : Fin 1 → ℝ) := by
    funext j
    calc
      (∫ ω, (T102RestrictedX ∘ l) ω j ∂ν) =
          ∫ ω, T102RestrictedX ω j ∂T102RestrictedLaw :=
        hl.integral_comp' (fun ω => T102RestrictedX ω j)
      _ = 0 := congrFun hmeanR j
  have hfL : RealDensity (ν.map (T102RestrictedX ∘ l))
      (fun x : Fin 1 → ℝ => gapPDF (x 0)) := by
    rw [hlaw T102RestrictedX T102_restricted_measurable_X]
    exact hfR
  have hqL : RealDensity
      (ν.map (fun ω => ((T102RestrictedX ∘ l) ω, (T102RestrictedY ∘ l) ω))) qv := by
    change RealDensity
      (ν.map ((fun ω => (T102RestrictedX ω, T102RestrictedY ω)) ∘ l)) qv
    rw [hlaw _ (T102_restricted_measurable_X.prodMk T102_restricted_measurable_Y)]
    exact hqv
  have hrange : Set.range (T102RestrictedX ∘ l) =
      {x : Fin 1 → ℝ | 0 < gapPDF (x 0)} := by
    change Set.range (T102RestrictedX ∘ l) = T102PDFSupport
    calc
      Set.range (T102RestrictedX ∘ l) = Set.range T102RestrictedX := by
        ext x
        constructor
        · rintro ⟨ω, rfl⟩
          exact ⟨l ω, rfl⟩
        · rintro ⟨ω, rfl⟩
          exact ⟨l.symm ω, by simp⟩
      _ = T102PDFSupport := T102_restricted_covariate_range
  have hbump : ContDiff ℝ 1 bumpVec :=
    n2_proof.1.comp (contDiff_apply ℝ ℝ (0 : Fin 1))
  have hm0 : ContDiff ℝ 1 (fun (_ : Fin 1 → ℝ) => (0 : ℝ)) := contDiff_const
  have hEq := @H (ULift.{u} T102RestrictedSample) _ ν _ 1
    (T102RestrictedX ∘ l) (T102RestrictedY ∘ l)
    (T102_restricted_measurable_X.comp l.measurable)
    (T102_restricted_measurable_Y.comp l.measurable)
    (fun j => hl.integrable_comp_of_integrable
      (T102_restricted_preserving.integrable_comp_of_integrable (hcoords j)))
    (hl.integrable_comp_of_integrable
      (T102_restricted_preserving.integrable_comp_of_integrable n1_proof.2.2.1))
    (fun x : Fin 1 → ℝ => gapPDF (x 0)) qv hfL hqL hrange
    (fun _ : Fin 1 → ℝ => 0) bumpVec
    (hcef _ (T102_restricted_cef _ hcef0))
    (hcef _ (T102_restricted_cef _ hcef1))
    (hm0.differentiable (by norm_num))
    (hbump.differentiable (by norm_num)) 0
  dsimp only at hEq
  rw [hmeanL] at hEq
  have hzero : coordinateDerivative (fun _ : Fin 1 → ℝ => 0) 0 0 = 0 := by
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).deriv
  have hone : coordinateDerivative bumpVec 0 0 = 1 := by
    simpa [coordinateDerivative, bumpVec] using n2_proof.2.2.deriv
  rw [hzero, hone] at hEq
  exact zero_ne_one hEq

end

end SAP.P001f.Bridge
