import SAP.P046.Bridge.Part1
import AronowAudit.P046.Wave1.Gap.GLP046B3
import AronowAudit.P046.Wave1.Gap.GP046B3b

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.Bridge

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- Existing variance identification rules out truncating a negative Gaussian variance. -/
theorem v_nonneg (M : Study) (hM : ValidStudy M) (g : ℝ → ℝ)
    (hg : MemLp (fun o => g (W o)) 2 M.law) : 0 ≤ V M g := by
  have he : variance (fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))) M.law =
      V M g := (AronowAudit.P046.Wave1.fixed_adjusted_variance_proof
        (toStudy M) (valid_to hM) g hg).1
  rw [← he]
  exact variance_nonneg _ _

/-- Package the two project convergence conclusions with their actual variance signs. -/
theorem comparison_from (M : Study) (hM : ValidStudy M) (F : ∀ n, CrossFit n)
    (gstar : ℝ → ℝ) (hg : MemLp (fun o => gstar (W o)) 2 M.law)
    (h : AronowAudit.P046.NormalLimit (toStudy M)
        (fun n => adjusted M (F n)) (V M gstar) ∧
      AronowAudit.P046.NormalLimit (toStudy M) (fun _ => ht M) (V M (fun _ => 0)) ∧
      V M gstar ≤ V M (fun _ => 0)) : EfficiencyComparison M F gstar := by
  exact ⟨normal_from (v_nonneg M hM gstar hg) h.1,
    normal_from (v_nonneg M hM (fun _ => 0) MemLp.zero) h.2.1, h.2.2⟩

/-- Family membership supplies finite prediction moments; no extra family-case premise is added. -/
theorem target5 : T5Statement := by
  constructor
  · intro M hM d family F hbal hG hzero hfit gstar hstar hmin hconv
    have hfits : ∀ n j, ∀ᵐ a ∂sampleLaw M n,
        MemLp (fun o => (F n).g j a (W o)) 2 M.law := by
      apply AronowAudit.P046.fitted_L2_from_membership (toStudy M) d family
        (fun n => toFit (F n)) hG
      intro n j
      exact (hfit n j).mono fun _ h => ⟨h.choose, h.choose_spec.1⟩
    have h := AronowAudit.P046.Wave1.proposition4c_corrected_proof (toStudy M)
      (valid_to hM) d family (fun n => toFit (F n)) hbal hG hzero hfit
      gstar hstar hmin hconv hfits
    obtain ⟨theta, htheta⟩ := hstar
    apply comparison_from M hM F gstar
    · exact htheta ▸ hG theta
    · exact h
  · intro M hM F hbal gstar hg hconv hfits hbetter
    exact comparison_from M hM F gstar hg
      (AronowAudit.P046.Wave1.proposition4c_direct_proof (toStudy M) (valid_to hM)
        (fun n => toFit (F n)) hbal gstar hg hconv hfits hbetter)

end
end SAP.P046.Bridge
