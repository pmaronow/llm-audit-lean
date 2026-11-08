import SAP.P046.Bridge.Part1
import AronowAudit.P046.Wave1.PropositionThree
import AronowAudit.P046.Wave1.Gap.GP046B2
import AronowAudit.P046.Wave1.Gap.GP046B4
import AronowAudit.P046.Wave1.Gap.GP046B5
import AronowAudit.P046.Wave1.Gap.GLP046B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.Bridge

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

/-- A putative SAP proof of the printed assertion would give the refuted project assertion. -/
theorem target6 : T6Statement := by
  intro h
  apply AronowAudit.P046.Wave1.proposition3_printed_refuted
  intro M hM n hn alpha ha
  exact h (fromStudy M) (valid_from hM) n hn alpha ha

/-- The unit-variance formula is a direct rewriting of the exported first two moments. -/
theorem ht_unit_variance (M : Study) (hM : ValidStudy M) :
    variance (fun o => htTerm (M.pi (W o)) (X o) (Y o)) M.law =
      (∫ o, M.m (W o) / M.pi (W o) ∂M.law) - (mu M)^2 := by
  letI := hM.probability
  have hLp : MemLp (fun o => htTerm (M.pi (W o)) (X o) (Y o)) 2 M.law :=
    AronowAudit.P046.ht_unit_memLp (toStudy M) (valid_to hM)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply]
  have hs : (∫ o, htTerm (M.pi (W o)) (X o) (Y o) ^ 2 ∂M.law) =
      ∫ o, M.m (W o) / M.pi (W o) ∂M.law :=
    AronowAudit.P046.ht_second_moment (toStudy M) (valid_to hM)
  have hm : (∫ o, htTerm (M.pi (W o)) (X o) (Y o) ∂M.law) = mu M :=
    (AronowAudit.P046.ht_unit_facts (toStudy M) (valid_to hM)).2
  rw [hs, hm]

theorem target7 : T7Statement := by
  constructor
  · intro delta hd eps heps
    obtain ⟨C, hC, h⟩ := AronowAudit.P046.ht_uniform_root_n delta hd eps heps
    exact ⟨C, hC, fun M hM heq n hn => h (toStudy M) (valid_to hM) heq n hn⟩
  · intro M hM
    letI := hM.probability
    have hv := ht_unit_variance M hM
    refine ⟨?_, hv, normal_from ?_ (AronowAudit.P046.proposition2_asymptotic.2
      (toStudy M) (valid_to hM))⟩
    · intro n hn
      have hlp : MemLp (ht M (n := n)) 2 (sampleLaw M n) :=
        AronowAudit.P046.ht_sample_memLp (toStudy M) (valid_to hM) n
      exact ⟨hlp.integrable (by norm_num),
        AronowAudit.P046.ht_unbiased (toStudy M) (valid_to hM) n hn⟩
    · rw [← hv]
      exact variance_nonneg _ _

theorem target8 : T8Statement := by
  intro M hM n hn F hint
  exact AronowAudit.P046.Wave1.proposition4a_proof (toStudy M) (valid_to hM) n hn
    (toFit F) hint

/-- At the true regression the exported excess-variance identity has zero remainder. -/
theorem hahn_nonneg (M : Study) (hM : ValidStudy M) : 0 ≤ hahnBound M := by
  have hg := AronowAudit.P046.Wave1.p4d_regression_L2 (toStudy M) (valid_to hM)
  have h := AronowAudit.P046.Wave1.fixed_adjusted_variance_proof
    (toStudy M) (valid_to hM) M.m hg
  have he : V M M.m = hahnBound M := by
    have hx : V M M.m = hahnBound M +
        (∫ o, q M (W o) * (M.m (W o) - M.m (W o))^2 ∂M.law) := h.2
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, integral_zero, add_zero]
      using hx
  have hv := h.1.trans he
  rw [← hv]
  exact variance_nonneg _ _

theorem target9 : T9Statement := by
  constructor
  · intro M hM F hbal g hg hconv hfits
    exact AronowAudit.P046.Wave1.proposition4b_proof (toStudy M) (valid_to hM)
      (fun n => toFit (F n)) hbal g hg hconv hfits
  · intro M hM F hbal hconv hfits
    exact normal_from (hahn_nonneg M hM)
      (AronowAudit.P046.Wave1.proposition4d_proof (toStudy M) (valid_to hM)
        (fun n => toFit (F n)) hbal hconv hfits)

theorem target10 : T10Statement := by
  intro est hmeas
  obtain ⟨eps, heps, c, hc, h⟩ := AronowAudit.P046.Wave1.proposition1_proof est hmeas
  refine ⟨eps, heps, c, hc, ?_⟩
  intro N
  obtain ⟨n, hn, hn0, M, hM, ht⟩ := h N
  exact ⟨n, hn, hn0, fromStudy M, valid_from hM, ht⟩

end
end SAP.P046.Bridge
