import SAP.P003a.WH.W1.P.T1_L5.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 250000

namespace SAP.P003a.WH.W1.P.T1_L5

open SAP.P003a
open SAP.P003a.Bridge

theorem zero_mask_eq_row (o : Counts)
    (ho : o = ⟨0,3,14,3⟩ ∨ o = ⟨0,3,13,4⟩ ∨ o = ⟨0,3,12,5⟩ ∨
      o = ⟨0,3,11,6⟩ ∨ o = ⟨1,2,13,4⟩ ∨ o = ⟨1,2,12,5⟩ ∨
      o = ⟨1,2,11,6⟩ ∨ o = ⟨2,1,12,5⟩ ∨ o = ⟨2,1,11,6⟩ ∨
      o = ⟨3,0,11,6⟩) :
    missingInterval ((109/500 : ℚ) : ℝ) o ⟨0,0,0,0⟩ =
      exactInterval ((109/500 : ℚ) : ℝ) o := by
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨0,3,14,3⟩ (-17/20) (-2/5) (by
      simpa using AronowAudit.P003.interval_obs_0_3_14_3)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_0_3_14_3]
    norm_num [estimate, estimateQ]
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨0,3,13,4⟩ (-4/5) (-7/20) (by
      simpa using AronowAudit.P003.interval_obs_0_3_13_4)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_0_3_13_4]
    norm_num [estimate, estimateQ]
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨0,3,12,5⟩ (-3/4) (-3/10) (by
      simpa using AronowAudit.P003.interval_obs_0_3_12_5)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_0_3_12_5]
    norm_num [estimate, estimateQ]
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨0,3,11,6⟩ (-7/10) (-3/20) (by
      simpa using AronowAudit.P003.interval_obs_0_3_11_6)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_0_3_11_6]
    norm_num [estimate, estimateQ]
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨1,2,13,4⟩ (-13/20) (-1/20) (by
      simpa using AronowAudit.P003.interval_obs_1_2_13_4)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_1_2_13_4]
    norm_num [estimate, estimateQ]
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨1,2,12,5⟩ (-3/5) 0 (by
      simpa using AronowAudit.P003.interval_obs_1_2_12_5)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_1_2_12_5]
    norm_num [estimate, estimateQ]
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨1,2,11,6⟩ (-11/20) (1/20) (by
      simpa using AronowAudit.P003.interval_obs_1_2_11_6)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_1_2_11_6]
    norm_num [estimate, estimateQ]
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨2,1,12,5⟩ (-2/5) (1/5) (by
      simpa using AronowAudit.P003.interval_obs_2_1_12_5)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_2_1_12_5]
    norm_num [estimate, estimateQ]
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨2,1,11,6⟩ (-7/20) (1/4) (by
      simpa using AronowAudit.P003.interval_obs_2_1_11_6)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_2_1_11_6]
    norm_num [estimate, estimateQ]
  · have hc := SAP.P003a.WH.W1.real_interval_certificate (109/500) ⟨3,0,11,6⟩ (-1/10) (2/5) (by
      simpa using AronowAudit.P003.interval_obs_3_0_11_6)
    apply zero_mask_eq_of_cert _ hc.1
    rw [int_3_0_11_6]
    norm_num [estimate, estimateQ]

theorem uniform_bad_pushforward (E : Counts → Prop) :
    uniformProb (fun z : Assignment 20 3 =>
      E (treatedCounts badPopulation z.val)) =
      designProb badPopulation 3 E := by
  let vA : AronowAudit.P003.Counts := toAudit badPopulation
  let wA : AronowAudit.P003.PotentialTable vA.total :=
    fun i => AronowAudit.P003.canonicalPair vA i.val
  have hw : AronowAudit.P003.tableCounts wA = vA := by
    change AronowAudit.P003.tableCounts
      (fun i : Fin vA.total => AronowAudit.P003.canonicalPair vA i.val) = vA
    exact AronowAudit.P003.Wave1.glp0032b4_gmc_canonical_counts vA
  have hnt (z : AronowAudit.P003.Assignment vA.total 3) :
      AronowAudit.P003.Wave1.neyman_treated wA z.val =
        AronowAudit.P003.treatedCounts vA z.val := by
    ext <;> rfl
  have hp := AronowAudit.P003.Wave1.neyman_event_pushforward wA vA hw 3
    (fun q => E (fromAudit q))
  have hp' : AronowAudit.P003.uniformProb (fun z : AronowAudit.P003.Assignment vA.total 3 =>
      E (fromAudit (AronowAudit.P003.treatedCounts vA z.val))) =
      AronowAudit.P003.designProb vA 3 (fun q => E (fromAudit q)) := by
    simpa only [hnt] using hp
  have hfun : (fun z : Assignment 20 3 =>
      E (fromAudit (AronowAudit.P003.treatedCounts vA z.val))) =
      (fun z : Assignment 20 3 => E (treatedCounts badPopulation z.val)) := by
    funext z
    have ht : AronowAudit.P003.treatedCounts vA z.val =
        toAudit (treatedCounts badPopulation z.val) := by
      change AronowAudit.P003.treatedCounts (toAudit badPopulation) z.val = _
      exact to_treatedCounts badPopulation z.val
    rw [ht]
    rfl
  have hu : AronowAudit.P003.uniformProb
      (fun z : AronowAudit.P003.Assignment vA.total 3 =>
        E (fromAudit (AronowAudit.P003.treatedCounts vA z.val))) =
      uniformProb (fun z : Assignment 20 3 => E (treatedCounts badPopulation z.val)) := by
    change uniformProb
      (fun z : Assignment 20 3 =>
        E (fromAudit (AronowAudit.P003.treatedCounts vA z.val))) = _
    rw [hfun]
  have hd : AronowAudit.P003.designProb vA 3 (fun q => E (fromAudit q)) =
      designProb badPopulation 3 E := by
    change AronowAudit.P003.designProb (toAudit badPopulation) 3
      (fun q => E (fromAudit q)) = _
    exact to_designProb badPopulation 3 E
  exact hu.trans (hp'.trans hd)

theorem complete_design_coverage :
    designProb badPopulation 3 (fun q =>
      (-3/20 : ℝ) ∈ exactInterval ((109/500 : ℚ) : ℝ)
        (observed badPopulation q)) = (892/1140 : ℝ) := by
  unfold designProb
  rw [show randomStates badPopulation 3 =
      [⟨0,0,0,3⟩,⟨0,0,1,2⟩,⟨0,0,2,1⟩,⟨0,0,3,0⟩,
       ⟨1,0,0,2⟩,⟨1,0,1,1⟩,⟨1,0,2,0⟩,⟨2,0,0,1⟩,
       ⟨2,0,1,0⟩,⟨3,0,0,0⟩] by exact bad_states]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  dsimp [observed, badPopulation]
  simp only [int_0_3_14_3, int_0_3_13_4, int_0_3_12_5, int_0_3_11_6,
    int_1_2_13_4, int_1_2_12_5, int_1_2_11_6, int_2_1_12_5,
    int_2_1_11_6, int_3_0_11_6, Set.mem_Icc]
  dsimp [Counts.total]
  rw [show (20 : ℕ).choose 3 = 1140 by decide +kernel]
  norm_num [multiplicity, binomial, Nat.fast_choose, Counts.total]

theorem imputation_design_coverage :
    designProb badPopulation 3 (fun q =>
      (-3/20 : ℝ) ∈ missingInterval ((109/500 : ℚ) : ℝ)
        (observed badPopulation q) (badMask q)) = (297/380 : ℝ) := by
  have hA : AronowAudit.P003.designProb AronowAudit.P003.badPopulation 3
      (fun q => AronowAudit.P003.tau AronowAudit.P003.badPopulation ∈
        AronowAudit.P003.missingInterval ((109/500 : ℚ) : ℝ)
          (AronowAudit.P003.observed AronowAudit.P003.badPopulation q)
          (AronowAudit.P003.badMask q)) = (297/380 : ℝ) := by
    calc
      AronowAudit.P003.designProb AronowAudit.P003.badPopulation 3
          (fun q => AronowAudit.P003.tau AronowAudit.P003.badPopulation ∈
            AronowAudit.P003.missingInterval ((109/500 : ℚ) : ℝ)
              (AronowAudit.P003.observed AronowAudit.P003.badPopulation q)
              (AronowAudit.P003.badMask q)) =
          AronowAudit.P003.missingProb AronowAudit.P003.badPopulation 3
            AronowAudit.P003.ConfidenceFollowup.badJointLaw
            (fun q r => AronowAudit.P003.tau AronowAudit.P003.badPopulation ∈
              AronowAudit.P003.missingInterval ((109/500 : ℚ) : ℝ)
                (AronowAudit.P003.observed AronowAudit.P003.badPopulation q) r) := by
          exact (AronowAudit.P003.ConfidenceFollowup.badJointLaw_probability
            (fun q r => AronowAudit.P003.tau AronowAudit.P003.badPopulation ∈
              AronowAudit.P003.missingInterval ((109/500 : ℚ) : ℝ)
                (AronowAudit.P003.observed AronowAudit.P003.badPopulation q) r)).symm
      _ = (297/380 : ℝ) := AronowAudit.P003.ConfidenceFollowup.badJointLaw_coverage
  have hS : designProb badPopulation 3 (fun q =>
      tau badPopulation ∈ missingInterval ((109/500 : ℚ) : ℝ)
        (observed badPopulation q) (badMask q)) = (297/380 : ℝ) := by
    simpa only [decode_designProb, to_badPopulation, to_tau, to_missingInterval,
      to_observed, to_badMask, to_from, from_to] using hA
  have htau : tau badPopulation = (-3/20 : ℝ) := by
    norm_num [tau, tauQ, badPopulation, Counts.effect, Counts.total]
  rw [htau] at hS
  exact hS

end SAP.P003a.WH.W1.P.T1_L5

open SAP.P003a.WH.W1.P.T1_L5

theorem SAP.P003a.WH.W1.T1_L5_proof : SAP.P003a.WH.W1.T1_L5 := by
  classical
  unfold SAP.P003a.WH.W1.T1_L5 SAP.P003a.w1BadCoverageFacts
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmiss (z : Assignment 20 3) :
        w1BadMissing z.val = ∅ ↔ z ≠ w1CriticalAssignment := by
      have heq : z.val = w1CriticalAssignment.val ↔ z = w1CriticalAssignment := by
        constructor
        · intro h
          exact Subtype.ext h
        · intro h
          exact congrArg Subtype.val h
      simp [w1BadMissing, heq]
    have hset : Finset.univ.filter
        (fun z : Assignment 20 3 => w1BadMissing z.val = ∅) =
        ({w1CriticalAssignment} : Finset (Assignment 20 3))ᶜ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_compl, Finset.mem_singleton]
      exact hmiss z
    rw [hset, Finset.card_compl]
    simp only [Finset.card_singleton]
    have hc : Fintype.card (Assignment 20 3) = (20 : ℕ).choose 3 := by
      simpa [Assignment] using
        (AronowAudit.P003.Wave1.neyman_assignment_card 20 3)
    rw [hc]
    norm_num [Nat.choose]
  · intro z _hne
    rw [bad_observed_eq]
    exact zero_mask_eq_row _ (bad_observed_cases z)
  · have hfun :
        (fun z : Assignment 20 3 =>
          (-3/20 : ℝ) ∈ exactInterval ((109/500 : ℚ) : ℝ)
            (unitObserved (w1BadOutcomes z.val) z.val)) =
        (fun z => (fun q => (-3/20 : ℝ) ∈ exactInterval ((109/500 : ℚ) : ℝ)
          (observed badPopulation q)) (treatedCounts badPopulation z.val)) := by
      funext z
      rw [bad_observed_eq]
    rw [hfun]
    exact (uniform_bad_pushforward (fun q =>
      (-3/20 : ℝ) ∈ exactInterval ((109/500 : ℚ) : ℝ)
        (observed badPopulation q))).trans complete_design_coverage
  · have hfun :
        (fun z : Assignment 20 3 =>
          (-3/20 : ℝ) ∈ missingInterval ((109/500 : ℚ) : ℝ)
            (unitObserved (w1BadOutcomes z.val) z.val)
            (badMask (treatedCounts badPopulation z.val))) =
        (fun z => (fun q => (-3/20 : ℝ) ∈ missingInterval ((109/500 : ℚ) : ℝ)
          (observed badPopulation q) (badMask q)) (treatedCounts badPopulation z.val)) := by
      funext z
      rw [bad_observed_eq]
    rw [hfun]
    exact (uniform_bad_pushforward (fun q =>
      (-3/20 : ℝ) ∈ missingInterval ((109/500 : ℚ) : ℝ)
        (observed badPopulation q) (badMask q))).trans imputation_design_coverage
