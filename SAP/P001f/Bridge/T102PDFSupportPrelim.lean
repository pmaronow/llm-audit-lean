import SAP.P001f.Defs.Part3
import AronowAudit.P001.Wave1.Gap.FidP001

set_option autoImplicit false

namespace SAP.P001f.Bridge

open MeasureTheory ProbabilityTheory Filter
open AronowAudit.P001
open AronowAudit.P001.Wave1.GapLaw

noncomputable section

def T102PDFSupport : Set (Fin 1 → ℝ) :=
  {x | 0 < gapPDF (x 0)}

def T102SampleSupport : Set (ℝ × ℝ) :=
  {ω | gapX ω ∈ T102PDFSupport}

abbrev T102RestrictedSample := {ω : ℝ × ℝ // ω ∈ T102SampleSupport}

def T102RestrictedLaw : Measure T102RestrictedSample :=
  gapJointLaw.comap Subtype.val

def T102RestrictedX (ω : T102RestrictedSample) : Fin 1 → ℝ := gapX ω.val

def T102RestrictedY (ω : T102RestrictedSample) : ℝ := ω.val.2

theorem T102_pdf_positive_set_measurable : MeasurableSet T102PDFSupport := by
  change MeasurableSet {x : Fin 1 → ℝ | 0 < gapPDF (x 0)}
  exact measurableSet_lt measurable_const
    (gap_pdf_measurable.comp (measurable_pi_apply 0))

theorem T102_sample_support_measurable : MeasurableSet T102SampleSupport := by
  change MeasurableSet (gapX ⁻¹' T102PDFSupport)
  exact (measurable_pi_lambda fun _ => measurable_fst)
    T102_pdf_positive_set_measurable

theorem T102_sample_support_conull :
    ∀ᵐ ω ∂gapJointLaw, ω ∈ T102SampleSupport := by
  obtain ⟨_, _, _, _, _, hbound, _⟩ := n1_proof
  filter_upwards [hbound] with ω hw
  have hx : ω.1 ∈ Set.Icc (-2 : ℝ) (-1) ∪ Set.Icc 1 2 := by
    rcases le_total (0 : ℝ) ω.1 with h0 | h0
    · right
      have h1 := hw.1
      have h2 := hw.2
      rw [abs_of_nonneg h0] at h1 h2
      exact ⟨h1, h2⟩
    · left
      have h1 := hw.1
      have h2 := hw.2
      rw [abs_of_nonpos h0] at h1 h2
      constructor <;> linarith
  have hp : 0 < gapPDF ω.1 := by
    simp [gapPDF, hx]
  simpa [T102SampleSupport, T102PDFSupport, gapX] using hp

theorem T102_restricted_map_eq :
    T102RestrictedLaw.map Subtype.val = gapJointLaw := by
  rw [T102RestrictedLaw, map_comap_subtype_coe T102_sample_support_measurable,
    Measure.restrict_eq_self_of_ae_mem T102_sample_support_conull]

theorem T102_restricted_probability : IsProbabilityMeasure T102RestrictedLaw := by
  have hmass : T102RestrictedLaw Set.univ = 1 := by
    calc
      T102RestrictedLaw Set.univ = (T102RestrictedLaw.map Subtype.val) Set.univ := by
        rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
        simp
      _ = gapJointLaw Set.univ := by rw [T102_restricted_map_eq]
      _ = 1 := n1_proof.1.measure_univ
  exact ⟨hmass⟩

theorem T102_restricted_covariate_range :
    Set.range T102RestrictedX = T102PDFSupport := by
  ext x
  constructor
  · rintro ⟨ω, rfl⟩
    change 0 < gapPDF (gapX ω.val 0)
    exact ω.property
  · intro hx
    refine ⟨⟨(x 0, 0), ?_⟩, ?_⟩
    · change gapX (x 0, 0) ∈ T102PDFSupport
      simpa [T102PDFSupport, gapX] using hx
    · funext j
      fin_cases j
      rfl

theorem T102_restricted_preserving :
    MeasurePreserving (Subtype.val : T102RestrictedSample → ℝ × ℝ)
      T102RestrictedLaw gapJointLaw :=
  ⟨measurable_subtype_coe, T102_restricted_map_eq⟩

theorem T102_restricted_measurable_X : Measurable T102RestrictedX :=
  (measurable_pi_lambda fun _ => measurable_fst).comp measurable_subtype_coe

theorem T102_restricted_measurable_Y : Measurable T102RestrictedY :=
  measurable_snd.comp measurable_subtype_coe

theorem T102_restricted_scalar_joint_pdf :
    AronowAudit.P001.HasJointPDF
      (T102RestrictedLaw.map (fun ω => (T102RestrictedX ω 0, T102RestrictedY ω)))
      (fun z => gapPDF z.1 *
        (if z.2 ∈ Set.Icc (-1 : ℝ) 1 then (1 / 2 : ℝ) else 0)) := by
  let g : (ℝ × ℝ) → ℝ × ℝ := fun ω => (gapX ω 0, Prod.snd ω)
  have hg : Measurable g := by
    exact ((measurable_pi_apply 0).comp
      (measurable_pi_lambda fun _ => measurable_fst)).prodMk measurable_snd
  have hpair :
      T102RestrictedLaw.map (fun ω => (T102RestrictedX ω 0, T102RestrictedY ω)) =
        gapJointLaw.map (fun ω => (gapX ω 0, Prod.snd ω)) := by
    change T102RestrictedLaw.map (g ∘ Subtype.val) = gapJointLaw.map g
    calc
      T102RestrictedLaw.map (g ∘ Subtype.val) =
          (T102RestrictedLaw.map Subtype.val).map g := by
        exact (Measure.map_map hg measurable_subtype_coe).symm
      _ = gapJointLaw.map g := by rw [T102_restricted_map_eq]
  rw [hpair]
  exact AronowAudit.P001.Wave1.fidT102_joint_pdf

theorem T102_restricted_cef
    (m : (Fin 1 → ℝ) → ℝ)
    (hc : AronowAudit.P001.IsCEF gapJointLaw gapX Prod.snd m) :
    ConditionalMean T102RestrictedLaw T102RestrictedX T102RestrictedY m := by
  change AronowAudit.P001.IsCEF gapJointLaw gapX Prod.snd m at hc
  change AronowAudit.P001.IsCEF T102RestrictedLaw
    T102RestrictedX T102RestrictedY m
  let hp := T102_restricted_preserving
  refine ⟨hc.1, hp.integrable_comp_of_integrable hc.2.1,
    hp.integrable_comp_of_integrable hc.2.2.1, fun A hA => ?_⟩
  change (∫ ω in Subtype.val ⁻¹' (gapX ⁻¹' A), Prod.snd ω.val ∂T102RestrictedLaw) =
    ∫ ω in Subtype.val ⁻¹' (gapX ⁻¹' A), (m ∘ gapX) ω.val ∂T102RestrictedLaw
  rw [hp.setIntegral_preimage_emb
      (MeasurableEmbedding.subtype_coe T102_sample_support_measurable),
    hp.setIntegral_preimage_emb
      (MeasurableEmbedding.subtype_coe T102_sample_support_measurable)]
  exact hc.2.2.2 A hA

theorem T102_restricted_vector_joint_pdf :
    ∃ qv : ((Fin 1 → ℝ) × ℝ) → ℝ,
      RealDensity
        (T102RestrictedLaw.map (fun ω => (T102RestrictedX ω, T102RestrictedY ω))) qv := by
  let q : (ℝ × ℝ) → ℝ := fun z => gapPDF z.1 *
    (if z.2 ∈ Set.Icc (-1 : ℝ) 1 then (1 / 2 : ℝ) else 0)
  have hq : AronowAudit.P001.HasJointPDF
      (T102RestrictedLaw.map (fun ω => (T102RestrictedX ω 0, T102RestrictedY ω))) q :=
    T102_restricted_scalar_joint_pdf
  let e : ((Fin 1 → ℝ) × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).prodCongr (MeasurableEquiv.refl ℝ)
  have hep : MeasurePreserving e volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).prod (MeasurePreserving.id volume)
  have hqvi : Integrable (q ∘ e) volume :=
    hep.integrable_comp_of_integrable hq.2.2.1
  have hpair :
      T102RestrictedLaw.map (fun ω => (T102RestrictedX ω, T102RestrictedY ω)) =
        (T102RestrictedLaw.map
          (fun ω => (T102RestrictedX ω 0, T102RestrictedY ω))).map e.symm := by
    rw [Measure.map_map
      (f := fun ω : T102RestrictedSample =>
        (T102RestrictedX ω 0, T102RestrictedY ω))
      e.symm.measurable
      (((measurable_pi_apply 0).comp T102_restricted_measurable_X).prodMk
        T102_restricted_measurable_Y)]
    congr 1
  refine ⟨q ∘ e, ?_⟩
  change AEMeasurable (q ∘ e) volume ∧ (∀ z, 0 ≤ (q ∘ e) z) ∧
    Integrable (q ∘ e) volume ∧
    T102RestrictedLaw.map (fun ω => (T102RestrictedX ω, T102RestrictedY ω)) =
      volume.withDensity (fun z => ENNReal.ofReal ((q ∘ e) z))
  refine ⟨hqvi.aestronglyMeasurable.aemeasurable, fun z => hq.2.1 (e z), hqvi, ?_⟩
  rw [hpair, hq.2.2.2]
  ext A hA
  rw [Measure.map_apply e.symm.measurable hA,
    withDensity_apply _ (e.symm.measurable hA), withDensity_apply _ hA]
  exact (MeasurePreserving.symm e hep).setLIntegral_comp_preimage_emb
    e.symm.measurableEmbedding (fun z => ENNReal.ofReal ((q ∘ e) z)) A

end

end SAP.P001f.Bridge
