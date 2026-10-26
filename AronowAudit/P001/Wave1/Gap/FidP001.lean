import AronowAudit.P001.Wave1.GapLaw.N1
import AronowAudit.P001.Wave1.GapLaw.N2
import AronowAudit.P001.Wave1.GapLaw.N3
import AronowAudit.P001.Wave1.GapLaw.N4
import AronowAudit.P001.Wave1.GapLaw.N5
import AronowAudit.P001.Wave1.PdaMeanNotIdentified.N5

/-!
# P001-T37 and P001-T102: marginal densities and CEF derivatives

The marginal-density correction covers every finite nonnegative almost-everywhere version.
The PDA witness retains the joint PDF, the common response and CEF relationship,
and actual derivatives at the covariate mean.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-- P001-T37: almost-everywhere agreement supplies the marginal version's
integrability and almost-everywhere measurability. -/
theorem marginal_pdf_ae_correction_all_versions
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (f : (ℝ × ℝ) → ℝ) (hf : AronowAudit.P001.HasJointPDF ν f) :
    (∀ᵐ y ∂volume,
      (∫⁻ x : ℝ, ENNReal.ofReal (f (x, y))) < ∞) ∧
    ∀ g : ℝ → ℝ, (∀ y, 0 ≤ g y) →
      (∀ᵐ y ∂volume,
        ENNReal.ofReal (g y) = (∫⁻ x : ℝ, ENNReal.ofReal (f (x, y)))) →
      AronowAudit.P001.HasPDF (ν.map Prod.snd) g := by
  have hfi : Integrable f ((volume : Measure ℝ).prod volume) := hf.2.2.1
  have hslice := hfi.prod_left_ae
  constructor
  · filter_upwards [hslice] with y hy
    rw [← ofReal_integral_eq_lintegral_ofReal hy
      (ae_of_all _ (fun x => hf.2.1 (x, y)))]
    simp
  · intro g hgn hge
    have he : g =ᵐ[volume] (fun y => ∫ x, f (x, y)) := by
      filter_upwards [hge, hslice] with y hy hiy
      have hh := congrArg ENNReal.toReal hy
      rw [ENNReal.toReal_ofReal (hgn y)] at hh
      exact hh.trans (integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ (fun x => hf.2.1 (x, y))) hiy.aestronglyMeasurable).symm
    have hgi : Integrable g volume := hfi.integral_prod_right.congr he.symm
    refine ⟨hgi.aestronglyMeasurable.aemeasurable, hgn, hgi, ?_⟩
    apply Measure.ext
    intro B hB
    have hpre : MeasurableSet (Prod.snd ⁻¹' B : Set (ℝ × ℝ)) := measurable_snd hB
    rw [Measure.map_apply measurable_snd hB, hf.2.2.2,
      withDensity_apply _ hpre, withDensity_apply _ hB,
      ← lintegral_indicator hpre, ← lintegral_indicator hB]
    change (∫⁻ z : ℝ × ℝ,
      (Prod.snd ⁻¹' B).indicator (fun z => ENNReal.ofReal (f z)) z
      ∂((volume : Measure ℝ).prod volume)) = _
    rw [lintegral_prod_symm (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      _ (hf.1.ennreal_ofReal.indicator hpre)]
    apply lintegral_congr_ae
    filter_upwards [hge] with y hy
    by_cases hBy : y ∈ B
    · simpa [Set.indicator, hBy] using hy.symm
    · simp [Set.indicator, hBy]

/-- P001-T102: the pair is the identity on the gap-law sample space.
The density proof uses measurable integrable factors and the density of a product measure. -/
lemma fidT102_joint_pdf :
    HasJointPDF
      (gapJointLaw.map (fun ω => (GapLaw.gapX ω 0, Prod.snd ω)))
      (fun z => gapPDF z.1 *
        (if z.2 ∈ Set.Icc (-1 : ℝ) 1 then (1 / 2 : ℝ) else 0)) := by
  change HasJointPDF (gapJointLaw.map id) _
  rw [Measure.map_id]
  exact PdaMeanNotIdentified.n5_proof

/-- P001-T102: a joint-density counterexample with two globally C¹ versions
of one CEF whose actual derivatives at the actual covariate mean differ. -/
theorem printed_pda_continuous_cef_counterexample :
    ∃ (μ : Measure (ℝ × ℝ))
      (X : (ℝ × ℝ) → (Fin 1 → ℝ)) (Y : (ℝ × ℝ) → ℝ)
      (f m₀ m₁ : (Fin 1 → ℝ) → ℝ) (q : (ℝ × ℝ) → ℝ),
      IsProbabilityMeasure μ ∧ Measurable X ∧ Measurable Y ∧
      (∀ j, Integrable (fun ω => X ω j) μ) ∧ Integrable Y μ ∧
      AronowAudit.P001.HasVectorPDF (μ.map X) f ∧
      AronowAudit.P001.HasJointPDF (μ.map (fun ω => (X ω 0, Y ω))) q ∧
      AronowAudit.P001.IsCEF μ X Y m₀ ∧
      AronowAudit.P001.IsCEF μ X Y m₁ ∧
      ContDiff ℝ 1 m₀ ∧ ContDiff ℝ 1 m₁ ∧
      m₀ =ᵐ[μ.map X] m₁ ∧
      (let xbar : Fin 1 → ℝ :=
          fun j => AronowAudit.P001.mean μ (fun ω => X ω j)
       HasDerivAt
         (fun t : ℝ => m₀ (Function.update xbar 0 (xbar 0 + t))) 0 0 ∧
       HasDerivAt
         (fun t : ℝ => m₁ (Function.update xbar 0 (xbar 0 + t))) 1 0) := by
  obtain ⟨hXm, _, _, hcoords, _, hmean0, hae⟩ :=
    GapLaw.n4_proof GapLaw.n1_proof GapLaw.n2_proof
  obtain ⟨hpdf, hcef0, hcef1⟩ :=
    GapLaw.n5_proof GapLaw.n1_proof GapLaw.n2_proof GapLaw.n3_proof
  have hmean : (fun j => mean gapJointLaw (fun ω => GapLaw.gapX ω j)) =
      (0 : Fin 1 → ℝ) := by
    funext j
    exact hmean0
  have hbump : ContDiff ℝ 1 GapLaw.bumpVec :=
    GapLaw.n2_proof.1.comp (contDiff_apply ℝ ℝ (0 : Fin 1))
  refine ⟨gapJointLaw, GapLaw.gapX, Prod.snd, (fun x => gapPDF (x 0)),
    (fun _ => 0), GapLaw.bumpVec,
    (fun z => gapPDF z.1 *
      (if z.2 ∈ Set.Icc (-1 : ℝ) 1 then (1 / 2 : ℝ) else 0)),
    GapLaw.n1_proof.1, hXm, measurable_snd, hcoords, GapLaw.n1_proof.2.2.1,
    hpdf, fidT102_joint_pdf, hcef0, hcef1, contDiff_const, hbump, hae, ?_⟩
  dsimp only
  rw [hmean, hmean0]
  constructor
  · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · simpa [GapLaw.bumpVec] using GapLaw.n2_proof.2.2

end

end AronowAudit.P001.Wave1
