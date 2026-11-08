import SAP.P003a.WH.W1.Leaves
import AronowAudit.P003.Wave1.Gap.GLP0031B2
import AronowAudit.P003.Wave1.Gap.GLP0032B4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 250000

namespace SAP.P003a.WH.W1.P.T1_L5

open SAP.P003a
open SAP.P003a.Bridge

theorem bad_table_canonical :
    w1BadTable = fun i => canonicalPair badPopulation i.val := by
  funext i
  by_cases h11 : i.val < 11
  · simp [w1BadTable, canonicalPair, badPopulation, h11]
  · by_cases h14 : i.val < 14
    · simp [w1BadTable, canonicalPair, badPopulation, h11, h14]
    · simp [w1BadTable, canonicalPair, badPopulation, h11, h14]

theorem bad_observed_eq (z : Finset (Fin 20)) :
    unitObserved (w1BadOutcomes z) z =
      observed badPopulation (treatedCounts badPopulation z) := by
  have hcan : unitObserved
      (unitOutcomes (fun i : Fin 20 => canonicalPair badPopulation i.val) z) z =
      canonicalObserved badPopulation z := by
    have h := AronowAudit.P003.Wave1.shuffleB2_canonical_observed
      (toAudit badPopulation) z
    have hY : (fun i : Fin 20 => AronowAudit.P003.canonicalPair
        (toAudit badPopulation) i.val) =
        (fun i : Fin 20 => canonicalPair badPopulation i.val) := by
      funext i
      rfl
    have hU : AronowAudit.P003.unitObserved
        (AronowAudit.P003.unitOutcomes
          (fun i : Fin 20 => AronowAudit.P003.canonicalPair
            (toAudit badPopulation) i.val) z) z =
        toAudit (unitObserved
          (unitOutcomes (fun i : Fin 20 => canonicalPair badPopulation i.val) z) z) := by
      rw [hY]
      exact to_unitObserved _ _
    have hC : AronowAudit.P003.canonicalObserved (toAudit badPopulation) z =
        toAudit (canonicalObserved badPopulation z) := to_canonicalObserved _ _
    have h' := congrArg fromAudit h.symm
    rw [hU, hC] at h'
    simpa only [from_to] using h'
  have hobs : canonicalObserved badPopulation z =
      observed badPopulation (treatedCounts badPopulation z) := by
    have h := AronowAudit.P003.Wave1.monte_rank_valid_observed_bridge
      (toAudit badPopulation) z
    have hC : AronowAudit.P003.canonicalObserved (toAudit badPopulation) z =
        toAudit (canonicalObserved badPopulation z) := to_canonicalObserved _ _
    have hT : AronowAudit.P003.treatedCounts (toAudit badPopulation) z =
        toAudit (treatedCounts badPopulation z) := to_treatedCounts _ _
    have hO : AronowAudit.P003.observed (toAudit badPopulation)
        (toAudit (treatedCounts badPopulation z)) =
        toAudit (observed badPopulation (treatedCounts badPopulation z)) :=
      to_observed _ _
    apply (to_inj _ _).mp
    calc
      toAudit (canonicalObserved badPopulation z) =
          AronowAudit.P003.canonicalObserved (toAudit badPopulation) z := hC.symm
      _ = AronowAudit.P003.observed (toAudit badPopulation)
          (AronowAudit.P003.treatedCounts (toAudit badPopulation) z) := h.symm
      _ = AronowAudit.P003.observed (toAudit badPopulation)
          (toAudit (treatedCounts badPopulation z)) :=
            congrArg (AronowAudit.P003.observed (toAudit badPopulation)) hT
      _ = toAudit (observed badPopulation (treatedCounts badPopulation z)) := hO
  rw [w1BadOutcomes, bad_table_canonical]
  exact hcan.trans hobs

theorem bad_treated_mem (z : Assignment 20 3) :
    treatedCounts badPopulation z.val ∈ randomStates badPopulation 3 := by
  have h := AronowAudit.P003.Wave1.glp0032b4_gmc_treated_legal
    (toAudit badPopulation) 3 z
  rw [to_treatedCounts, to_randomStates] at h
  rcases List.mem_map.mp h with ⟨q, hq, heq⟩
  have hq' : q = treatedCounts badPopulation z.val := (to_inj _ _).mp heq
  simpa [hq'] using hq

theorem bad_states :
    randomStates badPopulation 3 =
      [⟨0,0,0,3⟩,⟨0,0,1,2⟩,⟨0,0,2,1⟩,⟨0,0,3,0⟩,
       ⟨1,0,0,2⟩,⟨1,0,1,1⟩,⟨1,0,2,0⟩,⟨2,0,0,1⟩,
       ⟨2,0,1,0⟩,⟨3,0,0,0⟩] := by
  have hA := AronowAudit.P003.bad_random_states_certificate
  rw [to_badPopulation] at hA
  have h := congrArg (List.map fromAudit) hA
  rw [to_randomStates] at h
  simp only [List.map_map, Function.comp_def, from_to] at h
  change randomStates badPopulation 3 = _ at h
  simpa [fromAudit] using h

theorem bad_observed_cases (z : Assignment 20 3) :
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨0,3,14,3⟩ ∨
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨0,3,13,4⟩ ∨
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨0,3,12,5⟩ ∨
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨0,3,11,6⟩ ∨
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨1,2,13,4⟩ ∨
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨1,2,12,5⟩ ∨
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨1,2,11,6⟩ ∨
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨2,1,12,5⟩ ∨
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨2,1,11,6⟩ ∨
    observed badPopulation (treatedCounts badPopulation z.val) = ⟨3,0,11,6⟩ := by
  have h := bad_treated_mem z
  rw [bad_states] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  all_goals rw [h] <;> norm_num [observed, badPopulation]

theorem int_0_3_14_3 : exactInterval ((109/500 : ℚ) : ℝ) ⟨0,3,14,3⟩ =
    Set.Icc (-17/20 : ℝ) (-2/5 : ℝ) := by
  have h : intervalQ (109/500) (⟨0,3,14,3⟩ : Counts) = some (-17/20,-2/5) := by
    simpa using AronowAudit.P003.interval_obs_0_3_14_3
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem int_0_3_13_4 : exactInterval ((109/500 : ℚ) : ℝ) ⟨0,3,13,4⟩ =
    Set.Icc (-4/5 : ℝ) (-7/20 : ℝ) := by
  have h : intervalQ (109/500) (⟨0,3,13,4⟩ : Counts) = some (-4/5,-7/20) := by
    simpa using AronowAudit.P003.interval_obs_0_3_13_4
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem int_0_3_12_5 : exactInterval ((109/500 : ℚ) : ℝ) ⟨0,3,12,5⟩ =
    Set.Icc (-3/4 : ℝ) (-3/10 : ℝ) := by
  have h : intervalQ (109/500) (⟨0,3,12,5⟩ : Counts) = some (-3/4,-3/10) := by
    simpa using AronowAudit.P003.interval_obs_0_3_12_5
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem int_0_3_11_6 : exactInterval ((109/500 : ℚ) : ℝ) ⟨0,3,11,6⟩ =
    Set.Icc (-7/10 : ℝ) (-3/20 : ℝ) := by
  have h : intervalQ (109/500) (⟨0,3,11,6⟩ : Counts) = some (-7/10,-3/20) := by
    simpa using AronowAudit.P003.interval_obs_0_3_11_6
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem int_1_2_13_4 : exactInterval ((109/500 : ℚ) : ℝ) ⟨1,2,13,4⟩ =
    Set.Icc (-13/20 : ℝ) (-1/20 : ℝ) := by
  have h : intervalQ (109/500) (⟨1,2,13,4⟩ : Counts) = some (-13/20,-1/20) := by
    simpa using AronowAudit.P003.interval_obs_1_2_13_4
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem int_1_2_12_5 : exactInterval ((109/500 : ℚ) : ℝ) ⟨1,2,12,5⟩ =
    Set.Icc (-3/5 : ℝ) 0 := by
  have h : intervalQ (109/500) (⟨1,2,12,5⟩ : Counts) = some (-3/5,0) := by
    simpa using AronowAudit.P003.interval_obs_1_2_12_5
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem int_1_2_11_6 : exactInterval ((109/500 : ℚ) : ℝ) ⟨1,2,11,6⟩ =
    Set.Icc (-11/20 : ℝ) (1/20 : ℝ) := by
  have h : intervalQ (109/500) (⟨1,2,11,6⟩ : Counts) = some (-11/20,1/20) := by
    simpa using AronowAudit.P003.interval_obs_1_2_11_6
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem int_2_1_12_5 : exactInterval ((109/500 : ℚ) : ℝ) ⟨2,1,12,5⟩ =
    Set.Icc (-2/5 : ℝ) (1/5 : ℝ) := by
  have h : intervalQ (109/500) (⟨2,1,12,5⟩ : Counts) = some (-2/5,1/5) := by
    simpa using AronowAudit.P003.interval_obs_2_1_12_5
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem int_2_1_11_6 : exactInterval ((109/500 : ℚ) : ℝ) ⟨2,1,11,6⟩ =
    Set.Icc (-7/20 : ℝ) (1/4 : ℝ) := by
  have h : intervalQ (109/500) (⟨2,1,11,6⟩ : Counts) = some (-7/20,1/4) := by
    simpa using AronowAudit.P003.interval_obs_2_1_11_6
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem int_3_0_11_6 : exactInterval ((109/500 : ℚ) : ℝ) ⟨3,0,11,6⟩ =
    Set.Icc (-1/10 : ℝ) (2/5 : ℝ) := by
  have h : intervalQ (109/500) (⟨3,0,11,6⟩ : Counts) = some (-1/10,2/5) := by
    simpa using AronowAudit.P003.interval_obs_3_0_11_6
  simpa using (SAP.P003a.WH.W1.real_interval_certificate (109/500) _ _ _ h).2.2.2

theorem zero_mask_eq_of_cert (o : Counts)
    (hne : (accepted ((109/500 : ℚ) : ℝ) o).Nonempty)
    (hest : estimate o ∈ exactInterval ((109/500 : ℚ) : ℝ) o) :
    missingInterval ((109/500 : ℚ) : ℝ) o ⟨0,0,0,0⟩ =
      exactInterval ((109/500 : ℚ) : ℝ) o := by
  have hI := SAP.P003a.WH.W1.interval_eq_Icc ((109/500 : ℚ) : ℝ) o hne
  have hb : lower ((109/500 : ℚ) : ℝ) o ≤ estimate o ∧
      estimate o ≤ upper ((109/500 : ℚ) : ℝ) o := by
    simpa only [hI, Set.mem_Icc] using hest
  have hm : minusCompletion o ⟨0,0,0,0⟩ = o := by
    cases o
    rfl
  have hp : plusCompletion o ⟨0,0,0,0⟩ = o := by
    cases o
    rfl
  simp only [missingInterval, hm, hp, if_pos hne]
  rw [min_eq_left hb.1, max_eq_left hb.2]
  exact hI.symm

end SAP.P003a.WH.W1.P.T1_L5
