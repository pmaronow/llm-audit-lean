import SAP.P003a.WH.W1.Leaves
import AronowAudit.P003.Wave1.Gap.GLP0031B2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open SAP.P003a.Bridge
open scoped BigOperators

theorem SAP.P003a.WH.W1.T1_L2_proof : SAP.P003a.WH.W1.T1_L2 := by
  classical
  change SAP.P003a.w1BadCritical
  dsimp [SAP.P003a.w1BadCritical]
  let α : ℝ := ((109 / 500 : ℚ) : ℝ)
  let o₁ : SAP.P003a.Counts := ⟨0,3,11,6⟩
  let o₂ : SAP.P003a.Counts := ⟨0,3,10,7⟩
  let r : SAP.P003a.Counts := ⟨0,0,1,0⟩
  let z : Finset (Fin 20) := SAP.P003a.w1CriticalAssignment.val
  let y : Fin 20 → Bool := SAP.P003a.w1BadOutcomes z
  have hcert₁ := SAP.P003a.WH.W1.real_interval_certificate (109/500) o₁ (-7/10) (-3/20)
    (by simpa [o₁] using AronowAudit.P003.interval_obs_0_3_11_6)
  have hcert₂ := SAP.P003a.WH.W1.real_interval_certificate (109/500) o₂ (-13/20) (-1/5)
    (by simpa [o₂] using AronowAudit.P003.interval_obs_0_3_10_7)
  rcases hcert₁ with ⟨hne₁, hlo₁, hhi₁, hI₁⟩
  rcases hcert₂ with ⟨hne₂, hlo₂, hhi₂, hI₂⟩
  have hneLo : (SAP.P003a.accepted α (SAP.P003a.minusCompletion o₁ r)).Nonempty := by
    simpa [α, o₁, r, SAP.P003a.minusCompletion] using hne₁
  have hneHi : (SAP.P003a.accepted α (SAP.P003a.plusCompletion o₁ r)).Nonempty := by
    simpa [α, o₁, r, SAP.P003a.plusCompletion] using hne₂
  have hloLo : SAP.P003a.lower α (SAP.P003a.minusCompletion o₁ r) = (-7/10 : ℝ) := by
    simpa [α, o₁, r, SAP.P003a.minusCompletion] using hlo₁
  have hhiHi : SAP.P003a.upper α (SAP.P003a.plusCompletion o₁ r) = (-1/5 : ℝ) := by
    simpa [α, o₁, r, SAP.P003a.plusCompletion] using hhi₂
  have hmiss : SAP.P003a.missingInterval α o₁ r = Set.Icc (-7/10) (-1/5) := by
    dsimp [SAP.P003a.missingInterval]
    rw [if_pos hneLo, if_pos hneHi, hloLo, hhiHi]
    norm_num [α, o₁, o₂, r, SAP.P003a.minusCompletion,
      SAP.P003a.plusCompletion, SAP.P003a.estimate, SAP.P003a.estimateQ]
  have hobs₁ : SAP.P003a.unitObserved y z = o₁ := by
    decide +kernel
  have hobs₂ : SAP.P003a.unitObserved
      (SAP.P003a.unitPlus y z (SAP.P003a.w1BadMissing z)) z = o₂ := by
    decide +kernel
  have hbin : SAP.P003a.w1BinaryCompletion
      (SAP.P003a.w1BadM z) y := by
    intro i hi
    by_cases hm : i ∈ SAP.P003a.w1BadMissing z
    · simp [SAP.P003a.w1BadM, hm] at hi
    · simp [SAP.P003a.w1BadM, hm, SAP.P003a.w1BadOutcomes, y, z]
      rfl
  have hcrit : (-3/20 : ℝ) ∈ SAP.P003a.exactInterval α
      (SAP.P003a.unitObserved y z) := by
    rw [hobs₁, hI₁]
    norm_num
  have hsubset : SAP.P003a.exactInterval α (SAP.P003a.unitObserved y z) ⊆
      SAP.P003a.w1LabeledCompletionUnion α
        (SAP.P003a.w1BadM z) z := by
    intro t ht
    exact ⟨y, hbin, by simpa [hobs₁] using ht⟩
  have hmissout : (-3/20 : ℝ) ∉ SAP.P003a.missingInterval α o₁ r := by
    rw [hmiss]
    norm_num
  have hD5 : max (SAP.P003a.upper α o₂) (SAP.P003a.estimate o₂) < (-3/20 : ℝ) := by
    rw [hhi₂]
    norm_num [α, o₂, SAP.P003a.estimate, SAP.P003a.estimateQ]
  have hpopτ : SAP.P003a.tau SAP.P003a.badPopulation = (-3/20 : ℝ) := by
    norm_num [SAP.P003a.tau, SAP.P003a.tauQ, SAP.P003a.badPopulation,
      SAP.P003a.Counts.effect, SAP.P003a.Counts.total]
  have hw : AronowAudit.P003.tableCounts SAP.P003a.w1BadTable =
      toAudit SAP.P003a.badPopulation := by
    simpa using (show SAP.P003a.tableCounts SAP.P003a.w1BadTable =
      SAP.P003a.badPopulation by decide +kernel)
  have hpush₁ := AronowAudit.P003.Wave1.neyman_pValue_pushforward
    (toAudit SAP.P003a.badPopulation) (toAudit o₁) 3
    SAP.P003a.w1BadTable hw
    (by norm_num [o₁, SAP.P003a.badPopulation, SAP.P003a.Counts.total])
    (by norm_num [o₁])
    (by norm_num)
    (by norm_num [SAP.P003a.badPopulation, SAP.P003a.Counts.total])
  have hpush₂ := AronowAudit.P003.Wave1.neyman_pValue_pushforward
    (toAudit SAP.P003a.badPopulation) (toAudit o₂) 3
    SAP.P003a.w1BadTable hw
    (by norm_num [o₂, SAP.P003a.badPopulation, SAP.P003a.Counts.total])
    (by norm_num [o₂])
    (by norm_num)
    (by norm_num [SAP.P003a.badPopulation, SAP.P003a.Counts.total])
  have hest₁ : SAP.P003a.outcomeEstimator y z = SAP.P003a.estimate o₁ := by
    simpa [hobs₁] using AronowAudit.P003.Wave1.couplingB2_outcome_estimate y z
  have hest₂ : SAP.P003a.outcomeEstimator
      (SAP.P003a.unitPlus y z (SAP.P003a.w1BadMissing z)) z = SAP.P003a.estimate o₂ := by
    simpa [hobs₂] using AronowAudit.P003.Wave1.couplingB2_outcome_estimate
      (SAP.P003a.unitPlus y z (SAP.P003a.w1BadMissing z)) z
  have htableEq (u : Finset (Fin 20)) :
      AronowAudit.P003.tableEstimator (n := 20) SAP.P003a.w1BadTable u =
        SAP.P003a.tableEstimator SAP.P003a.w1BadTable u := by
    exact SAP.P003a.Bridge.to_tableEstimator SAP.P003a.w1BadTable u
  have htail₁ : SAP.P003a.uniformProb (fun q : SAP.P003a.Assignment 20 3 =>
      |SAP.P003a.tableEstimator SAP.P003a.w1BadTable q.val - (-3/20)| ≥
        |SAP.P003a.outcomeEstimator y z - (-3/20)|) =
      (SAP.P003a.pValue SAP.P003a.badPopulation o₁ : ℝ) := by
    have hp := hpush₁
    change AronowAudit.P003.uniformProb (fun q : AronowAudit.P003.Assignment 20 3 =>
      |AronowAudit.P003.tableEstimator (n := 20) SAP.P003a.w1BadTable q.val -
          AronowAudit.P003.tau (toAudit SAP.P003a.badPopulation)| ≥
        |AronowAudit.P003.estimate (toAudit o₁) -
          AronowAudit.P003.tau (toAudit SAP.P003a.badPopulation)|) = _ at hp
    rw [SAP.P003a.Bridge.uniformProb_eq] at hp
    simp_rw [htableEq] at hp
    simpa [hpopτ, hest₁, SAP.P003a.Bridge.to_pValue,
      SAP.P003a.Bridge.to_tableEstimator, SAP.P003a.Bridge.to_tau,
      SAP.P003a.Bridge.to_estimate] using hp
  have htail₂ : SAP.P003a.uniformProb (fun q : SAP.P003a.Assignment 20 3 =>
      |SAP.P003a.tableEstimator SAP.P003a.w1BadTable q.val - (-3/20)| ≥
        |SAP.P003a.outcomeEstimator
          (SAP.P003a.unitPlus y z (SAP.P003a.w1BadMissing z)) z - (-3/20)|) =
      (SAP.P003a.pValue SAP.P003a.badPopulation o₂ : ℝ) := by
    have hp := hpush₂
    change AronowAudit.P003.uniformProb (fun q : AronowAudit.P003.Assignment 20 3 =>
      |AronowAudit.P003.tableEstimator (n := 20) SAP.P003a.w1BadTable q.val -
          AronowAudit.P003.tau (toAudit SAP.P003a.badPopulation)| ≥
        |AronowAudit.P003.estimate (toAudit o₂) -
          AronowAudit.P003.tau (toAudit SAP.P003a.badPopulation)|) = _ at hp
    rw [SAP.P003a.Bridge.uniformProb_eq] at hp
    simp_rw [htableEq] at hp
    simpa [hpopτ, hest₂, SAP.P003a.Bridge.to_pValue,
      SAP.P003a.Bridge.to_tableEstimator, SAP.P003a.Bridge.to_tau,
      SAP.P003a.Bridge.to_estimate] using hp
  have hpv := AronowAudit.P003.missing_critical_tail_counterexample
  have hpv₁ : SAP.P003a.pValue SAP.P003a.badPopulation o₁ = 83/380 := by
    simpa [o₁] using hpv.1
  have hpv₂ : SAP.P003a.pValue SAP.P003a.badPopulation o₂ = 83/380 := by
    simpa [o₂] using hpv.2.1
  have hpvr₁ : (SAP.P003a.pValue SAP.P003a.badPopulation o₁ : ℝ) = (83/380 : ℝ) := by
    simpa using congrArg (fun q : ℚ => (q : ℝ)) hpv₁
  have hpvr₂ : (SAP.P003a.pValue SAP.P003a.badPopulation o₂ : ℝ) = (83/380 : ℝ) := by
    simpa using congrArg (fun q : ℚ => (q : ℝ)) hpv₂
  refine ⟨?_, ?_, hne₁, hne₂, ?_, ?_, hD5, ?_, ?_⟩
  · simpa [α] using hI₁
  · simpa [α] using hI₂
  · simpa [α] using hmiss
  · refine ⟨?_, ?_, ?_, hmissout⟩
    · simpa [α] using hcrit
    · simpa [α] using hsubset
    · exact hsubset hcrit
  · exact htail₁.trans hpvr₁
  · exact htail₂.trans hpvr₂

