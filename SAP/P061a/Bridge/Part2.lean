import SAP.P061a.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.Bridge

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

theorem transfer_correspondence : T5Statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S D y d d' estimate estimatedScale s L inst hs _hscalePos hp hm hdom hint hfirst hscale hrate
    exact AronowAudit.P061.corrected_inference_transfer S (fun N => toProject (D N)) y d d'
      estimate estimatedScale s L hs hp hm hdom hint hfirst hscale hrate
  · intro A instA instNe N label hlabel D y H f d d' hN hH hp hy
    exact AronowAudit.P061.local_total_variation_bias_bound label hlabel (toProject D) y H f
      d d' hN hH hp hy
  · exact AronowAudit.P061.rate_bound_suffices
  · intro Ω D estimate estimatedScale T A s L inst c hc hs _hscalePos hfirst hscale hrate
    exact AronowAudit.P061.nonzero_drift_limit (fun N => toProject (D N))
      estimate estimatedScale T A s L c hc hs hfirst hscale hrate

theorem attribution_correspondence : T6Statement := by
  constructor
  · intro Ω inst N D g y d d' hN hp hp'
    refine ⟨?_, rfl, ?_⟩
    · exact AronowAudit.P061.corrected_attribution_general (toProject D) g y d d' hN hp hp'
        (AronowAudit.P061.finite_type_targeted_moment (toProject D) g y d)
        (AronowAudit.P061.finite_type_targeted_moment (toProject D) g y d')
    · exact AronowAudit.P061.PaperDomains.aeed_average_eed_T6 (toProject D) g y d d' hN
        (fun i => ⟨hp i, hp' i⟩)
  · intro N D y hN hp hp'
    exact AronowAudit.P061.binary_adse_identity (toProject D) y hN hp hp'

theorem first_moment_correspondence : T8Statement := by
  constructor
  · intro Ω N D g y d hN hp hm
    have h := AronowAudit.P061.corrected_first_moment (toProject D) g y d hN hp hm
    refine ⟨h, ?_, ?_⟩
    · intro i
      have habs : AronowAudit.P061.Integrable (toProject D)
          (fun z => if g i z=d then |y i z| else 0) := by
        simpa only [AronowAudit.P061.Integrable, HasMean, toProject,
          apply_ite abs, abs_zero, abs_abs] using hm i
      have he := AronowAudit.P061.epo_conditional (toProject D) g (fun j z => |y j z|) i d (hp i) habs
      rw [← show conditionalExposureMean D g (fun j z => |y j z|) i d =
        AronowAudit.P061.conditionalMean (toProject D) g (fun j z => |y j z|) i d from rfl] at he
      rw [← he]
      simp only [AronowAudit.P061.epo, AronowAudit.P061.expectation, mean,
        toProject, apply_ite abs, abs_zero]
      rfl
    · unfold populationExposureMean
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      exact (h.1 i).2.1
  · intro Ω N D g y d hN hp
    constructor
    · exact AronowAudit.P061.PaperDomains.finite_support_targeted_moment_T8
        (toProject D) g y d hN hp
    · exact AronowAudit.P061.PaperDomains.targeted_nurva_moment_T8
        (toProject D) g y d hN hp

theorem positivity_contract_correspondence :
    positivityWellDefined ↔ AronowAudit.P061.PrintedClaims.printed_well_defined_claim := by
  constructor
  · intro h Ω N D g y d d' hN hp hp'
    exact h (fromProject D) g y d d' hN hp hp'
  · intro h Ω N D g y d d' hN hp hp'
    exact h (toProject D) g y d d' hN hp hp'

/-- Auxiliary reading with positivity alone and no existence hypotheses; this is not the packaged T11 assertion. -/
theorem refutation_correspondence : ¬positivityWellDefined := by
  intro h
  exact AronowAudit.P061.Refutations.printed_well_defined_claim_refuted
    (positivity_contract_correspondence.mp h)

/-- The positive finite-support component of the credited T11 declaration. -/
theorem finite_targets_correspondence : T11Statement := by
  intro Ω N D g y d d' hN hp hp' hfin
  have hd (i : Fin N) : 0 < AronowAudit.P061.pi (toProject D) g i d := by
    obtain ⟨c,hc,hci⟩ := hp
    exact hc.trans_le (hci i)
  have hd' (i : Fin N) : 0 < AronowAudit.P061.pi (toProject D) g i d' := by
    obtain ⟨c,hc,hci⟩ := hp'
    exact hc.trans_le (hci i)
  have h := (AronowAudit.P061.PaperDomains.finite_support_targets_T11_resolved
    (toProject D) g y d d' hN hd hd' hfin).2
  refine ⟨h.1, h.2.1, ?_, h.2.2.1, ?_, ?_, rfl, h.2.2.2⟩
  · intro i e _he
    unfold exposureProbability eventProbability
    apply tsum_congr
    intro z
    by_cases hz : supported D z
    · simp only [hz, true_and]
    · have hzero : D.mass z=0 := le_antisymm (le_of_not_gt hz) (D.mass_nonnegative z)
      simp only [hz, false_and, hzero, ite_self]
  · intro e he
    unfold populationExposureMean
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    rcases he with rfl | rfl
    · exact (h.2.2.1 i).1
    · exact (h.2.2.1 i).2
  · intro i
    exact congrArg₂ (fun a b : ℝ => a-b) (h.2.2.1 i).1 (h.2.2.1 i).2

end SAP.P061a.Bridge
