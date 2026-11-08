import AronowAudit.P027.Wave1.CancellationLimitBlueprint

/-! Uniqueness of the normalized limit, and event containment from weights at least one. -/

namespace AronowAudit.P027.Wave1.CancellationLimit

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

theorem n10_proof : N10 := by
  intro Ξ _ μ _ A w c hw hc hlim hdisj
  have hnotzero
      (hzero : TendstoInMeasure μ (fun n ξ => A n ξ / w n) atTop (fun _ => 0)) :
      False := by
    have hae : (fun _ : Ξ => c) =ᵐ[μ] (fun _ => 0) :=
      tendstoInMeasure_ae_unique hlim hzero
    obtain ⟨ξ, hξ⟩ := hae.exists
    exact hc hξ
  rcases hdisj with hraw | hnormalized
  · apply hnotzero
    rw [tendstoInMeasure_iff_dist] at hraw ⊢
    intro δ hδ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hraw δ hδ)
      (fun _ => zero_le)
    intro n
    apply measure_mono
    intro ξ hξ
    change δ ≤ dist (A n ξ / w n) 0 at hξ
    change δ ≤ dist (A n ξ) 0
    simp only [Real.dist_eq, sub_zero] at hξ ⊢
    have hw_nonneg : 0 ≤ w n := le_trans zero_le_one (hw n)
    have hratio : |A n ξ / w n| ≤ |A n ξ| := by
      rw [abs_div, abs_of_nonneg hw_nonneg]
      exact div_le_self (abs_nonneg _) (hw n)
    exact hξ.trans hratio
  · exact hnotzero hnormalized

end
end AronowAudit.P027.Wave1.CancellationLimit
