import SAP.P003a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SAP.P003a.WH.W1.P.T1_L3

open SAP.P003a
open SAP.P003a.Bridge

private def obs : Counts := ⟨0,3,10,7⟩

private def eligibleTables : List Counts :=
  (possibleTables obs).filter fun v => decide (-3 ≤ v.effect)

private theorem tail_certificate : ∀ v ∈ eligibleTables,
    tailCount v obs ≤ 248 ∧
      (tailCount v obs = 248 ↔ v = ⟨8,0,3,9⟩ ∨ v = ⟨9,0,3,8⟩) := by
  decide +kernel

end SAP.P003a.WH.W1.P.T1_L3

theorem SAP.P003a.WH.W1.T1_L3_proof : SAP.P003a.WH.W1.T1_L3 := by
  classical
  intro v hv hτ
  have htot : v.total = 20 := by
    have h := (AronowAudit.P003.possible_table_facts
      (SAP.P003a.Bridge.toAudit ⟨0,3,10,7⟩) (SAP.P003a.Bridge.toAudit v)
      ((SAP.P003a.Bridge.to_possible ⟨0,3,10,7⟩ v).mpr hv)).1
    simpa [SAP.P003a.Counts.total] using h
  have heff : -3 ≤ v.effect := by
    have hh : (-3 / 20 : ℚ) ≤ (v.effect : ℚ) / 20 := by
      simpa [SAP.P003a.tauQ, htot] using hτ
    have hh' : (-3 : ℚ) ≤ v.effect := by
      rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 20)] at hh
      exact hh
    exact_mod_cast hh'
  have hcert := SAP.P003a.WH.W1.P.T1_L3.tail_certificate v (by
    simp only [SAP.P003a.WH.W1.P.T1_L3.eligibleTables, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨hv, heff⟩)
  have hden : SAP.P003a.binomial 20 3 = 1140 := by
    change Nat.fast_choose 20 3 = 1140
    decide
  have hpv : SAP.P003a.pValue v ⟨0,3,10,7⟩ =
      (SAP.P003a.tailCount v ⟨0,3,10,7⟩ : ℚ) / 1140 := by
    simp [SAP.P003a.pValue, htot, hden]
  have hnum : (SAP.P003a.tailCount v ⟨0,3,10,7⟩ : ℚ) ≤ 248 := by
    exact_mod_cast hcert.1
  have hbound : (SAP.P003a.tailCount v ⟨0,3,10,7⟩ : ℚ) / 1140 ≤ 248 / 1140 :=
    (div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 1140)).2 hnum
  have heqnum : (SAP.P003a.tailCount v ⟨0,3,10,7⟩ : ℚ) / 1140 = 248 / 1140 ↔
      SAP.P003a.tailCount v ⟨0,3,10,7⟩ = 248 := by
    constructor
    · intro h
      have hm := congrArg (fun x : ℚ => x * 1140) h
      have hm' : (SAP.P003a.tailCount v ⟨0,3,10,7⟩ : ℚ) = 248 := by
        have hn : (1140 : ℚ) ≠ 0 := by norm_num
        field_simp [hn] at hm
        linarith
      exact_mod_cast hm'
    · intro h
      have hn : (SAP.P003a.tailCount v ⟨0,3,10,7⟩ : ℚ) = 248 := by exact_mod_cast h
      rw [hn]
  refine ⟨?_, ?_⟩
  · rw [hpv]
    exact hbound
  · rw [hpv, heqnum]
    simpa [SAP.P003a.WH.W1.P.T1_L3.obs] using hcert.2
