import SAP.P035.Defs
import SAP.P035.Bridge
import AronowAudit.P035.P035_Nonidentification

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SAP.P035 SAP.P035.Bridge

theorem SAP.P035.T1 : SAP.P035.T1Statement := by
  rcases AronowAudit.P035.campaign_nonidentification_counterexample with
    ⟨hSizes, hBounds, hThresholds, hIndependent, hProbability, hObserved,
      hCounts, hCalibrated, hPorch, hD, hC, hCMean, hDOverall, hCOverall,
      hLaws, hNotIdentified, hNotFunction⟩
  have hObservedSAP (y : Year) (z : Bool) (r : ℕ) : C y z true r = D y z true r := by
    simpa only [C_eq, D_eq] using hObserved (toYear y) z r
  refine ⟨?_, ?_, ?_, ?_, ?_, hObservedSAP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro y
    simpa only [latentSize_eq, reducedDenominator_eq] using hSizes (toYear y)
  · intro y
    simpa only [latentSize_eq, threshold_eq] using hBounds (toYear y)
  · intro y z
    simpa only [threshold_eq, latentSize_eq, releasedFrequency_eq] using
      hThresholds (toYear y) z
  · intro y z r
    simpa only [conditionalMass_eq, latentPopulation_eq] using hIndependent (toYear y) z r
  · constructor
    · intro y z r
      simpa only [jointMass_eq] using hProbability.1 (toYear y) z r
    · simpa only [sum_years, jointMass_eq, latentPopulation_eq, to_from] using hProbability.2
  · intro y z
    simpa only [successCount_eq, lower_D, lower_C, threshold_eq, latentSize_eq,
      releasedFrequency_eq] using hCounts (toYear y) z
  · simpa only [calibrated_iff, lower_D, lower_C] using hCalibrated
  · intro y
    simpa only [outcomeMean_eq, lower_D, exactEffect_eq] using hPorch (toYear y)
  · intro y z r
    simpa only [campaignDifference_eq, lower_D] using hD (toYear y) z r
  · intro y r
    simpa only [campaignDifference_eq, lower_C] using hC (toYear y) r
  · intro y
    simpa only [campaignMean_eq, lower_C, exactEffect_eq, threshold_eq, latentSize_eq] using
      hCMean (toYear y)
  · simpa only [overallCampaignEffect_eq, lower_D] using hDOverall
  · simpa only [overallCampaignEffect_eq, lower_C] using hCOverall
  · intro w
    funext y z b
    have h := congrFun (congrFun (congrFun
      (hLaws (fun v z r => w (fromYear v) z r)) (toYear y)) z) b
    simpa only [observedLawWith, AronowAudit.P035.observedLawWith,
      latentPopulation_eq, D_eq, C_eq, from_to] using h
  · intro w
    funext y z b
    simp only [observedRealLawWith, hObservedSAP]
  · exact fun h => hNotIdentified (identified_iff.mp h)
  · rintro ⟨f, hf⟩
    apply hNotFunction
    refine ⟨fun l => f (liftLaw l), ?_⟩
    intro Y hY
    have h := hf (liftOutcome Y) ((calibrated_lift Y).mpr hY)
    simpa only [observedLaw_lift, overallCampaignEffect_eq, lower_lift] using h

theorem SAP.P035.T2 : SAP.P035.T2Statement := by
  rcases AronowAudit.P035.corrected_campaign_interpretation with
    ⟨⟨U, V, hU, hV, hLaw, hZero, hPositive, hAbsent⟩, hNotIdentified⟩
  refine ⟨⟨liftOutcome U, liftOutcome V, (calibrated_lift U).mpr hU,
    (calibrated_lift V).mpr hV, ?_, ?_, ?_, ?_⟩,
    fun h => hNotIdentified (identified_iff.mp h)⟩
  · rw [observedLaw_lift, observedLaw_lift, hLaw]
  · intro y z r
    simpa only [campaignDifference_eq, lower_lift] using hZero (toYear y) z r
  · intro y
    have h := hPositive (toYear y)
    have hExact := h.2.trans (AronowAudit.P035.frequency_contrast (toYear y)).1
    simpa only [campaignMean_eq, lower_lift, releasedFrequency_eq, exactEffect_eq] using
      And.intro h.1 (And.intro h.2 hExact)
  · intro y r
    exact hAbsent (toYear y) r
