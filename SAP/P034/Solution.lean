import SAP.P034.Defs
import SAP.P034.Bridge
import AronowAudit.P034.P034_Attrition
import AronowAudit.P034.P034_Contrasts
import AronowAudit.P034.P034_Rounding

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory

theorem SAP.P034.T1 : SAP.P034.T1Statement := by
  obtain ⟨ha, _hn, hs, ht, hsn, hb⟩ := AronowAudit.P034.missingness_counterexample
  have ha' := SAP.P034.Bridge.worldAFacts_iff.mpr ha
  have hs' := SAP.P034.Bridge.sampleFacts_iff.mpr hs
  have hb' := SAP.P034.Bridge.worldBFacts_iff.mpr hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdet, hsol, _, _⟩ := ha'
  have hdet0 : SAP.P034.witnessGram.det ≠ 0 := by rw [hdet]; norm_num
  have hpopulation := SAP.P034.Bridge.normal_equations_cast
    SAP.P034.witnessGram SAP.P034.witnessRhs SAP.P034.witnessBeta hdet0 hsol
  obtain ⟨_, _, _, _, _, _, _, hg, _⟩ := hs'
  have hsampleDet : SAP.P034.sampleGram.det ≠ 0 := by
    rw [hg, Matrix.det_smul, hdet]
    norm_num
  have hsampleSol : SAP.P034.sampleGram.mulVec SAP.P034.witnessBeta =
      SAP.P034.sampleRhs := (hsn AronowAudit.P034.witnessBeta).mpr rfl
  have hsample := SAP.P034.Bridge.normal_equations_cast
    SAP.P034.sampleGram SAP.P034.sampleRhs SAP.P034.witnessBeta hsampleDet hsampleSol
  exact ⟨SAP.P034.Bridge.worldAFacts_iff.mpr ha, hpopulation,
    SAP.P034.Bridge.sampleFacts_iff.mpr hs, ht, hsample, hb'⟩

theorem SAP.P034.T2 {Ω : Type*} [MeasurableSpace Ω] : SAP.P034.T2Statement Ω := by
  intro k μ hμ M hT hY hR hX hY2 hX2 hH1 hOverlap hH2
  have h := AronowAudit.P034.corrected_complete_case_identification μ
    (SAP.P034.Bridge.toAudit M) hT hY hR hX hY2 hX2 hH1 hOverlap hH2
  exact ⟨(SAP.P034.Bridge.identification_iff μ M).mpr h.1,
    SAP.P034.Bridge.failure_iff.mpr h.2⟩

theorem SAP.P034.T3 : SAP.P034.T3Statement := by
  simpa only [SAP.P034.T3Statement, SAP.P034.Bridge.fittedOutcome_eq,
    SAP.P034.Bridge.factorialCell_eq] using AronowAudit.P034.factorial_counterexample

theorem SAP.P034.T4 : SAP.P034.T4Statement := by
  intro k a b c d γ z
  simpa only [SAP.P034.Bridge.fittedOutcome_eq] using
    AronowAudit.P034.corrected_factorial_contrasts a b c d γ z

theorem SAP.P034.T5 : SAP.P034.T5Statement := by
  simpa only [SAP.P034.T5Statement, SAP.P034.Bridge.oa3Counts_eq,
    SAP.P034.Bridge.oa3Totals_eq, SAP.P034.Bridge.oa3Tenths_eq,
    SAP.P034.Bridge.oa3Percentage_eq, SAP.P034.Bridge.roundsToTenth_eq] using
    AronowAudit.P034.corrected_oa3_table
