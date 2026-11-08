import SAP.P003a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SAP.P003a.WH.W1.P.T4_L1

open SAP.P003a
open SAP.P003a.Bridge

private def v : Counts := ⟨0,15,0,1⟩
private def q₁ : Counts := ⟨0,7,0,1⟩
private def q₂ : Counts := ⟨0,8,0,0⟩
private def w : PotentialTable 16 := fun i => canonicalPair v i.val

private theorem table_counts : tableCounts w = v := by
  decide +kernel

private theorem audit_counts : AronowAudit.P003.tableCounts w = toAudit v := by
  rw [to_tableCounts, table_counts]

private theorem audit_states : AronowAudit.P003.randomStates (toAudit v) 8 =
    [toAudit q₁, toAudit q₂] := by
  decide +kernel

private theorem estimator_bridge (z : Assignment 16 8) :
    tableEstimator w z.val =
      estimate (observed v (fromAudit (AronowAudit.P003.Wave1.neyman_treated w z.val))) := by
  calc
    _ = AronowAudit.P003.tableEstimator w z.val := (to_tableEstimator w z.val).symm
    _ = AronowAudit.P003.estimate
        (AronowAudit.P003.observed (toAudit v)
          (AronowAudit.P003.Wave1.neyman_treated w z.val)) :=
      AronowAudit.P003.Wave1.neyman_estimator_eq w (toAudit v) audit_counts 8 z
    _ = _ := by simp [decode_estimate, decode_observed]

private theorem state_estimate₁ (z : Assignment 16 8)
    (hz : AronowAudit.P003.Wave1.neyman_treated w z.val = toAudit q₁) :
    tableEstimator w z.val = 7/8 := by
  rw [estimator_bridge z, hz]
  norm_num [q₁, v, observed, estimate, estimateQ]

private theorem state_estimate₂ (z : Assignment 16 8)
    (hz : AronowAudit.P003.Wave1.neyman_treated w z.val = toAudit q₂) :
    tableEstimator w z.val = 1 := by
  rw [estimator_bridge z, hz]
  norm_num [q₂, v, observed, estimate, estimateQ]

private theorem state_support (z : Assignment 16 8) :
    AronowAudit.P003.Wave1.neyman_treated w z.val = toAudit q₁ ∨
    AronowAudit.P003.Wave1.neyman_treated w z.val = toAudit q₂ := by
  have hm := AronowAudit.P003.Wave1.neyman_treated_mem w (toAudit v) audit_counts 8 z
  rw [audit_states] at hm
  simpa using hm

private theorem estimator_fiber₁ :
    (Finset.univ.filter fun z : Assignment 16 8 => tableEstimator w z.val = (7/8 : ℝ)).card =
    (Finset.univ.filter fun z : Assignment 16 8 =>
      AronowAudit.P003.Wave1.neyman_treated w z.val = toAudit q₁).card := by
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    rcases state_support z with hq | hq
    · exact hq
    · have h := state_estimate₂ z hq
      rw [h] at hz
      norm_num at hz
  · intro hz
    exact state_estimate₁ z hz

private theorem estimator_fiber₂ :
    (Finset.univ.filter fun z : Assignment 16 8 => tableEstimator w z.val = (1 : ℝ)).card =
    (Finset.univ.filter fun z : Assignment 16 8 =>
      AronowAudit.P003.Wave1.neyman_treated w z.val = toAudit q₂).card := by
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    rcases state_support z with hq | hq
    · have h := state_estimate₁ z hq
      rw [h] at hz
      norm_num at hz
    · exact hq
  · intro hz
    exact state_estimate₂ z hz

private theorem fiber₁ :
    (Finset.univ.filter fun z : Assignment 16 8 => tableEstimator w z.val = (7/8 : ℝ)).card = 6435 := by
  rw [estimator_fiber₁,
    AronowAudit.P003.Wave1.neyman_fiber_card w (toAudit v) (toAudit q₁)
      audit_counts 8 (by norm_num [q₁, v, toAudit, AronowAudit.P003.Counts.total])]
  norm_num [AronowAudit.P003.multiplicity,
    AronowAudit.P003.binomial_eq_choose, q₁, v, toAudit] <;> decide +kernel

private theorem fiber₂ :
    (Finset.univ.filter fun z : Assignment 16 8 => tableEstimator w z.val = (1 : ℝ)).card = 6435 := by
  rw [estimator_fiber₂,
    AronowAudit.P003.Wave1.neyman_fiber_card w (toAudit v) (toAudit q₂)
      audit_counts 8 (by norm_num [q₂, v, toAudit, AronowAudit.P003.Counts.total])]
  norm_num [AronowAudit.P003.multiplicity,
    AronowAudit.P003.binomial_eq_choose, q₂, v, toAudit] <;> decide +kernel

end SAP.P003a.WH.W1.P.T4_L1

theorem SAP.P003a.WH.W1.T4_L1_proof : SAP.P003a.WH.W1.T4_L1 := by
  classical
  unfold SAP.P003a.WH.W1.T4_L1
  dsimp only
  refine ⟨SAP.P003a.WH.W1.P.T4_L1.table_counts, ?_, ?_,
    SAP.P003a.WH.W1.P.T4_L1.fiber₁, SAP.P003a.WH.W1.P.T4_L1.fiber₂, ?_, ?_, ?_⟩
  · calc
      tableTau SAP.P003a.WH.W1.P.T4_L1.w = AronowAudit.P003.tableTau SAP.P003a.WH.W1.P.T4_L1.w :=
        (SAP.P003a.Bridge.to_tableTau _).symm
      _ = AronowAudit.P003.tau (SAP.P003a.Bridge.toAudit SAP.P003a.WH.W1.P.T4_L1.v) := by
        have hs := AronowAudit.P003.corrected_sate SAP.P003a.WH.W1.P.T4_L1.w (by norm_num)
        rw [SAP.P003a.Bridge.to_tableCounts,
          SAP.P003a.WH.W1.P.T4_L1.table_counts] at hs
        exact hs.2.2.2
      _ = 15/16 := by norm_num [AronowAudit.P003.tau, AronowAudit.P003.tauQ,
        SAP.P003a.Bridge.toAudit, SAP.P003a.WH.W1.P.T4_L1.v,
        SAP.P003a.Counts.effect, SAP.P003a.Counts.total,
        AronowAudit.P003.Counts.effect, AronowAudit.P003.Counts.total]
  · exact fun z => by
      rcases SAP.P003a.WH.W1.P.T4_L1.state_support z with hq | hq
      · exact Or.inl (SAP.P003a.WH.W1.P.T4_L1.state_estimate₁ z hq)
      · exact Or.inr (SAP.P003a.WH.W1.P.T4_L1.state_estimate₂ z hq)
  · norm_num
  · norm_num
  · norm_num [SAP.P003a.estimate, SAP.P003a.estimateQ]
