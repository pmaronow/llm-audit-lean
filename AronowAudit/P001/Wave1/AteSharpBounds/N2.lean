import AronowAudit.P001.Wave1.AteSharpBoundsBlueprint

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.AteSharpBounds

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n2_proof : N2.{u} := by
  intro Ω _ μ _ Y0 Y1 D h0 h1 hD a b hbound hbinary
  let y : Ω → ℝ := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
  let l : Ω → ℝ := fun ω => ateLower (y ω) (D ω) a b
  let u : Ω → ℝ := fun ω => ateUpper (y ω) (D ω) a b
  have hint (g : Ω → ℝ) (hgm : Measurable g) (v w : ℝ)
      (hgb : ∀ᵐ ω ∂μ, g ω ∈ Set.Icc v w) : Integrable g μ := by
    apply Integrable.of_bound hgm.aestronglyMeasurable (max |v| |w|)
    filter_upwards [hgb] with ω hω
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hω.1 hω.2
  have hi0 : Integrable Y0 μ := hint Y0 h0 a b (hbound.mono fun _ h => h.1)
  have hi1 : Integrable Y1 μ := hint Y1 h1 a b (hbound.mono fun _ h => h.2)
  have hym : Measurable y := by dsimp [y, observedOutcome]; fun_prop
  have hyb : ∀ᵐ ω ∂μ, y ω ∈ Set.Icc a b := by
    filter_upwards [hbound, hbinary] with ω hb hr
    rcases hr with hr | hr
    · simpa [y, observedOutcome, hr] using hb.1
    · simpa [y, observedOutcome, hr] using hb.2
  have hyi : Integrable y μ := hint y hym a b hyb
  have hlm : Measurable l := by dsimp [l, y, ateLower, observedOutcome]; fun_prop
  have hum : Measurable u := by dsimp [u, y, ateUpper, observedOutcome]; fun_prop
  have hlb : ∀ᵐ ω ∂μ, l ω ∈ Set.Icc (a-b) (b-a) := by
    filter_upwards [hbound, hbinary] with ω hb hr
    rcases hr with hr | hr <;> simp [l, y, ateLower, observedOutcome, hr]
    · constructor <;> linarith [hb.1.1, hb.1.2]
    · constructor <;> linarith [hb.2.1, hb.2.2]
  have hub : ∀ᵐ ω ∂μ, u ω ∈ Set.Icc (a-b) (b-a) := by
    filter_upwards [hbound, hbinary] with ω hb hr
    rcases hr with hr | hr <;> simp [u, y, ateUpper, observedOutcome, hr]
    · constructor <;> linarith [hb.1.1, hb.1.2]
    · constructor <;> linarith [hb.2.1, hb.2.2]
  have hli : Integrable l μ := hint l hlm (a-b) (b-a) hlb
  have hui : Integrable u μ := hint u hum (a-b) (b-a) hub
  have hlτ : ∀ᵐ ω ∂μ, l ω ≤ Y1 ω - Y0 ω := by
    filter_upwards [hbound, hbinary] with ω hb hr
    rcases hr with hr | hr <;> simp [l, y, ateLower, observedOutcome, hr]
    · linarith [hb.2.1]
    · linarith [hb.1.2]
  have hτu : ∀ᵐ ω ∂μ, Y1 ω - Y0 ω ≤ u ω := by
    filter_upwards [hbound, hbinary] with ω hb hr
    rcases hr with hr | hr <;> simp [u, y, ateUpper, observedOutcome, hr]
    · linarith [hb.2.2]
    · linarith [hb.1.1]
  have hw : (fun ω => u ω - l ω) =ᵐ[μ] (fun _ => b-a) := by
    filter_upwards [hbinary] with ω hr
    rcases hr with hr | hr <;>
      simp [u, l, y, ateLower, ateUpper, observedOutcome, hr] <;> ring
  refine ⟨hyi, ⟨?_, ?_⟩, ?_⟩
  · exact integral_mono_ae hli (hi1.sub hi0) hlτ
  · exact integral_mono_ae (hi1.sub hi0) hui hτu
  · change (∫ ω, u ω ∂μ) - (∫ ω, l ω ∂μ) = b-a
    rw [← integral_sub hui hli, integral_congr_ae hw]
    simp

end

end AronowAudit.P001.Wave1.AteSharpBounds
