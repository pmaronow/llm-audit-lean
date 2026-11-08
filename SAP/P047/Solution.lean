import SAP.P047.WH.W1.Proofs.T3
import SAP.P047.Defs
import SAP.P047.Bridge
import AronowAudit.P047.P047_Identification
import AronowAudit.P047.Wave1.Impossibility

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open SAP.P047 SAP.P047.Bridge MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

theorem SAP.P047.T1 : T1Statement := by
  constructor
  · intro L B ε h
    obtain ⟨hc, hm, hb, hn⟩ :=
      AronowAudit.P047.known_propensity_finite_sample (toProject L) h
    refine ⟨hc, hm, hb, ?_⟩
    intro n hnpos
    obtain ⟨hmean, htail, hinterval⟩ := hn n hnpos
    refine ⟨hmean, htail, ?_⟩
    intro α hα0 hα1
    obtain ⟨hcoverage, hroot⟩ := hinterval α hα0 hα1
    have hroot' : Real.sqrt n * (2 * halfWidth B ε α n) =
        2 * B / ε * Real.sqrt (2 * Real.log (2 / α)) := hroot
    refine ⟨hcoverage, ?_, ?_, hroot'⟩
    · exact mul_nonneg (div_nonneg h.1.le h.2.1.le) (Real.sqrt_nonneg _)
    · intro s
      have hw : intervalWidth L B ε α n s = 2 * halfWidth B ε α n :=
        AronowAudit.P047.confidenceInterval_endpoint_width (toProject L) B ε α n s
      refine ⟨hw, ?_⟩
      rw [hw]
      have hnreal : (0 : ℝ) < n := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnpos)
      exact (eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr hnreal))).2
        (by simpa only [mul_comm] using hroot')
  · intro L ε h
    simpa only [treatedScore_eq, treatedEstimator_eq, sampleLaw_eq, treatedMean_eq,
      treatedHalfWidth_eq, toProject] using
      AronowAudit.P047.treated_mean_finite_sample (toProject L) h

theorem SAP.P047.T2 : T2Statement := by
  intro B ε hB hε hε1
  obtain ⟨htight, hmodel⟩ := AronowAudit.P047.known_propensity_asymptotics hB hε hε1
  refine ⟨?_, ?_⟩
  · simpa only [knownRootRisk_eq] using htight
  · intro L h
    exact hmodel (toProject L) h

theorem SAP.P047.T3 : SAP.P047.T3WholeStatement.{u} :=
  SAP.P047.WH.W1.T3_whole
