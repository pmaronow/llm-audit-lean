import AronowAudit.P001.Wave1.AteSharpBoundsBlueprint
import AronowAudit.P001.Wave1.AteSharpBounds.N2

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.AteSharpBounds

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

theorem n3_proof : N3.{u} := by
  intro Ω _ μ _ Y0 Y1 D h0 h1 hD a b hbound hbinary c hc
  let y : Ω → ℝ := fun ω => observedOutcome (Y0 ω) (Y1 ω) (D ω)
  let l : Ω → ℝ := fun ω => ateLower (y ω) (D ω) a b
  let u : Ω → ℝ := fun ω => ateUpper (y ω) (D ω) a b
  have hwidth : (∫ ω, u ω ∂μ) - (∫ ω, l ω ∂μ) = b-a :=
    (n2_proof μ Y0 Y1 D h0 h1 hD a b hbound hbinary).2.2
  change c ∈ Set.Icc (∫ ω, l ω ∂μ) (∫ ω, u ω ∂μ) at hc
  have hlm : Measurable l := by dsimp [l, y, ateLower, observedOutcome]; fun_prop
  have hlb : ∀ᵐ ω ∂μ, l ω ∈ Set.Icc (a-b) (b-a) := by
    filter_upwards [hbound, hbinary] with ω hb hr
    rcases hr with hr | hr <;> simp [l, y, ateLower, observedOutcome, hr]
    · constructor <;> linarith [hb.1.1, hb.1.2]
    · constructor <;> linarith [hb.2.1, hb.2.2]
  have hli : Integrable l μ := by
    apply Integrable.of_bound hlm.aestronglyMeasurable (max |a-b| |b-a|)
    filter_upwards [hlb] with ω hω
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hω.1 hω.2
  let q : ℝ := a+c-(∫ ω, l ω ∂μ)
  have hqa : a ≤ q := by dsimp [q]; linarith [hc.1]
  have hqb : q ≤ b := by dsimp [q]; linarith [hc.2]
  let A0 : Ω → ℝ := fun ω => Y0 ω*(1-D ω)+(a+b-q)*D ω
  let A1 : Ω → ℝ := fun ω => Y1 ω*D ω+q*(1-D ω)
  have hA0 : Measurable A0 := by dsimp [A0]; fun_prop
  have hA1 : Measurable A1 := by dsimp [A1]; fun_prop
  refine ⟨A0, A1, hA0, hA1, ?_, ?_, ?_⟩
  · filter_upwards [hbound, hbinary] with ω hb hr
    rcases hr with hr | hr
    · simpa [A0, A1, hr] using And.intro hb.1 (And.intro hqa hqb)
    · simp only [A0, A1, hr, sub_self, mul_zero, mul_one, zero_add, add_zero]
      exact ⟨⟨by linarith, by linarith⟩, hb.2⟩
  · apply Measure.map_congr
    filter_upwards [hbinary] with ω hr
    apply Prod.ext
    · rcases hr with hr | hr <;> simp [observedOutcome, A0, A1, y, hr]
    · rfl
  · have hid : (fun ω => A1 ω-A0 ω) =ᵐ[μ]
        (fun ω => l ω+(c-(∫ ω, l ω ∂μ))) := by
      filter_upwards [hbinary] with ω hr
      rcases hr with hr | hr <;>
        simp [A0, A1, l, y, ateLower, observedOutcome, q, hr] <;> ring
    change (∫ ω, A1 ω-A0 ω ∂μ) = c
    rw [integral_congr_ae hid, integral_add hli (integrable_const _)]
    simp

end

end AronowAudit.P001.Wave1.AteSharpBounds
