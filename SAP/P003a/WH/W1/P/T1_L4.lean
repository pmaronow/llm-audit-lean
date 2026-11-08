import SAP.P003a.WH.W1.Leaves
import AronowAudit.P003.Wave1.Gap.GLP0031B2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000


namespace SAP.P003a.WH.W1.P.T1_L4

open _root_.SAP.P003a
open _root_.SAP.P003a.Bridge

theorem audit_state_observed_injective
    (q q' : _root_.AronowAudit.P003.Counts)
    (hq : q ∈ _root_.AronowAudit.P003.randomStates (toAudit badPopulation) 3)
    (hq' : q' ∈ _root_.AronowAudit.P003.randomStates (toAudit badPopulation) 3)
    (ho : _root_.AronowAudit.P003.observed (toAudit badPopulation) q =
      _root_.AronowAudit.P003.observed (toAudit badPopulation) q') : q = q' := by
  have hstates : q = ⟨0,0,0,3⟩ ∨ q = ⟨0,0,1,2⟩ ∨ q = ⟨0,0,2,1⟩ ∨
      q = ⟨0,0,3,0⟩ ∨ q = ⟨1,0,0,2⟩ ∨ q = ⟨1,0,1,1⟩ ∨
      q = ⟨1,0,2,0⟩ ∨ q = ⟨2,0,0,1⟩ ∨ q = ⟨2,0,1,0⟩ ∨ q = ⟨3,0,0,0⟩ := by
    rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate] at hq
    simpa using hq
  have hstates' : q' = ⟨0,0,0,3⟩ ∨ q' = ⟨0,0,1,2⟩ ∨ q' = ⟨0,0,2,1⟩ ∨
      q' = ⟨0,0,3,0⟩ ∨ q' = ⟨1,0,0,2⟩ ∨ q' = ⟨1,0,1,1⟩ ∨
      q' = ⟨1,0,2,0⟩ ∨ q' = ⟨2,0,0,1⟩ ∨ q' = ⟨2,0,1,0⟩ ∨ q' = ⟨3,0,0,0⟩ := by
    rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate] at hq'
    simpa using hq'
  rcases hstates with h | h | h | h | h | h | h | h | h | h <;> subst q
  all_goals rcases hstates' with h | h | h | h | h | h | h | h | h | h <;> subst q'
  all_goals norm_num [_root_.AronowAudit.P003.observed,
    _root_.AronowAudit.P003.badPopulation, badPopulation] at ho
  all_goals rfl

theorem audit_table_counts :
    _root_.AronowAudit.P003.tableCounts w1BadTable = toAudit badPopulation := by
  decide +kernel

theorem audit_table_eq_canonical :
    w1BadTable = (fun i => _root_.AronowAudit.P003.canonicalPair (toAudit badPopulation) i.val) := by
  funext i
  by_cases h : i.val < 11
  · simp [w1BadTable, _root_.AronowAudit.P003.canonicalPair, badPopulation, toAudit, h]
  · simp [w1BadTable, _root_.AronowAudit.P003.canonicalPair, badPopulation, toAudit, h]

theorem audit_canonicalPair_eq (i : Fin 20) :
    _root_.AronowAudit.P003.canonicalPair (toAudit badPopulation) i.val =
      canonicalPair badPopulation i.val := by
  by_cases h : i.val < 11
  · simp [_root_.AronowAudit.P003.canonicalPair, canonicalPair, badPopulation, toAudit, h]
  · by_cases h' : i.val < 14
    · simp [_root_.AronowAudit.P003.canonicalPair, canonicalPair, badPopulation, toAudit, h, h']
    · simp [_root_.AronowAudit.P003.canonicalPair, canonicalPair, badPopulation, toAudit, h, h']
theorem audit_neyman_eq (z : Assignment 20 3) :
    _root_.AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val =
      _root_.AronowAudit.P003.treatedCounts (toAudit badPopulation) z.val := by
  rw [audit_table_eq_canonical]
  simp [_root_.AronowAudit.P003.Wave1.neyman_treated, _root_.AronowAudit.P003.Wave1.neyman_pack,
    _root_.AronowAudit.P003.treatedCounts, audit_canonicalPair_eq]

theorem unit_observed_eq (z : Assignment 20 3) :
    unitObserved (w1BadOutcomes z.val) z.val =
      observed badPopulation (fromAudit (_root_.AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val)) := by
  have hout : w1BadOutcomes z.val = _root_.AronowAudit.P003.unitOutcomes w1BadTable z.val := rfl
  have haudit : _root_.AronowAudit.P003.unitObserved (_root_.AronowAudit.P003.unitOutcomes w1BadTable z.val) z.val =
      _root_.AronowAudit.P003.observed (toAudit badPopulation) (_root_.AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val) := by
    calc
      _root_.AronowAudit.P003.unitObserved (_root_.AronowAudit.P003.unitOutcomes w1BadTable z.val) z.val =
          _root_.AronowAudit.P003.unitObserved
            (_root_.AronowAudit.P003.unitOutcomes (fun i => _root_.AronowAudit.P003.canonicalPair (toAudit badPopulation) i.val) z.val)
            z.val := by rw [audit_table_eq_canonical]
      _ = _root_.AronowAudit.P003.canonicalObserved (toAudit badPopulation) z.val :=
            (_root_.AronowAudit.P003.Wave1.shuffleB2_canonical_observed (toAudit badPopulation) z.val).symm
      _ = _root_.AronowAudit.P003.observed (toAudit badPopulation)
          (_root_.AronowAudit.P003.treatedCounts (toAudit badPopulation) z.val) :=
            (_root_.AronowAudit.P003.Wave1.monte_rank_valid_observed_bridge (toAudit badPopulation) z.val).symm
      _ = _root_.AronowAudit.P003.observed (toAudit badPopulation)
          (_root_.AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val) := by rw [← audit_neyman_eq]
  have h := congrArg fromAudit haudit
  simpa only [← hout, Bridge.to_unitObserved, Bridge.decode_observed, from_to] using h

theorem audit_row_state (r : W1CoverageRow) (hr : r ∈ w1BadRows) :
    ∃ q : _root_.AronowAudit.P003.Counts,
      q ∈ _root_.AronowAudit.P003.randomStates (toAudit badPopulation) 3 ∧
      _root_.AronowAudit.P003.observed (toAudit badPopulation) q = toAudit r.o ∧
      _root_.AronowAudit.P003.multiplicity (toAudit badPopulation) q = r.weight := by
  have hr' : r = ⟨⟨0,3,11,6⟩,1,-7/10,-3/20,true⟩ ∨
      r = ⟨⟨0,3,12,5⟩,18,-3/4,-3/10,false⟩ ∨
      r = ⟨⟨0,3,13,4⟩,45,-4/5,-7/20,false⟩ ∨
      r = ⟨⟨0,3,14,3⟩,20,-17/20,-2/5,false⟩ ∨
      r = ⟨⟨1,2,11,6⟩,33,-11/20,1/20,true⟩ ∨
      r = ⟨⟨1,2,12,5⟩,198,-3/5,0,true⟩ ∨
      r = ⟨⟨1,2,13,4⟩,165,-13/20,-1/20,true⟩ ∨
      r = ⟨⟨2,1,11,6⟩,165,-7/20,1/4,true⟩ ∨
      r = ⟨⟨2,1,12,5⟩,330,-2/5,1/5,true⟩ ∨
      r = ⟨⟨3,0,11,6⟩,165,-1/10,2/5,false⟩ := by
    simpa [w1BadRows] using hr
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨⟨0,0,3,0⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨0,0,2,1⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨0,0,1,2⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨0,0,0,3⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨1,0,2,0⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨1,0,1,1⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨1,0,0,2⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨2,0,1,0⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨2,0,0,1⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel
  · refine ⟨⟨3,0,0,0⟩, ?_, ?_, ?_⟩
    · rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate]; simp
    · decide +kernel
    · decide +kernel

theorem audit_state_row (q : _root_.AronowAudit.P003.Counts)
    (hq : q ∈ _root_.AronowAudit.P003.randomStates (toAudit badPopulation) 3) :
    ∃ r ∈ w1BadRows, _root_.AronowAudit.P003.observed (toAudit badPopulation) q = toAudit r.o := by
  have hq' : q = ⟨0,0,0,3⟩ ∨ q = ⟨0,0,1,2⟩ ∨ q = ⟨0,0,2,1⟩ ∨
      q = ⟨0,0,3,0⟩ ∨ q = ⟨1,0,0,2⟩ ∨ q = ⟨1,0,1,1⟩ ∨
      q = ⟨1,0,2,0⟩ ∨ q = ⟨2,0,0,1⟩ ∨ q = ⟨2,0,1,0⟩ ∨ q = ⟨3,0,0,0⟩ := by
    rw [← Bridge.to_badPopulation, _root_.AronowAudit.P003.bad_random_states_certificate] at hq
    simpa using hq
  rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨⟨0,3,14,3⟩,20,-17/20,-2/5,false⟩, by simp [w1BadRows], by decide +kernel⟩
  · exact ⟨⟨⟨0,3,13,4⟩,45,-4/5,-7/20,false⟩, by simp [w1BadRows], by decide +kernel⟩
  · exact ⟨⟨⟨0,3,12,5⟩,18,-3/4,-3/10,false⟩, by simp [w1BadRows], by decide +kernel⟩
  · exact ⟨⟨⟨0,3,11,6⟩,1,-7/10,-3/20,true⟩, by simp [w1BadRows], by decide +kernel⟩
  · exact ⟨⟨⟨1,2,13,4⟩,165,-13/20,-1/20,true⟩, by simp [w1BadRows], by decide +kernel⟩
  · exact ⟨⟨⟨1,2,12,5⟩,198,-3/5,0,true⟩, by simp [w1BadRows], by decide +kernel⟩
  · exact ⟨⟨⟨1,2,11,6⟩,33,-11/20,1/20,true⟩, by simp [w1BadRows], by decide +kernel⟩
  · exact ⟨⟨⟨2,1,12,5⟩,330,-2/5,1/5,true⟩, by simp [w1BadRows], by decide +kernel⟩
  · exact ⟨⟨⟨2,1,11,6⟩,165,-7/20,1/4,true⟩, by simp [w1BadRows], by decide +kernel⟩
  · exact ⟨⟨⟨3,0,11,6⟩,165,-1/10,2/5,false⟩, by simp [w1BadRows], by decide +kernel⟩

theorem bad_row_intervalQ (r : W1CoverageRow) (hr : r ∈ w1BadRows) :
    intervalQ (109/500) r.o = some (r.lo,r.hi) := by
  have hr' : r = ⟨⟨0,3,11,6⟩,1,-7/10,-3/20,true⟩ ∨
      r = ⟨⟨0,3,12,5⟩,18,-3/4,-3/10,false⟩ ∨
      r = ⟨⟨0,3,13,4⟩,45,-4/5,-7/20,false⟩ ∨
      r = ⟨⟨0,3,14,3⟩,20,-17/20,-2/5,false⟩ ∨
      r = ⟨⟨1,2,11,6⟩,33,-11/20,1/20,true⟩ ∨
      r = ⟨⟨1,2,12,5⟩,198,-3/5,0,true⟩ ∨
      r = ⟨⟨1,2,13,4⟩,165,-13/20,-1/20,true⟩ ∨
      r = ⟨⟨2,1,11,6⟩,165,-7/20,1/4,true⟩ ∨
      r = ⟨⟨2,1,12,5⟩,330,-2/5,1/5,true⟩ ∨
      r = ⟨⟨3,0,11,6⟩,165,-1/10,2/5,false⟩ := by
    simpa [w1BadRows] using hr
  have hA : _root_.AronowAudit.P003.intervalQ (109/500) (toAudit r.o) =
      some (r.lo,r.hi) := by
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_0_3_11_6
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_0_3_12_5
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_0_3_13_4
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_0_3_14_3
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_1_2_11_6
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_1_2_12_5
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_1_2_13_4
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_2_1_11_6
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_2_1_12_5
    · simpa [Bridge.toAudit] using _root_.AronowAudit.P003.interval_obs_3_0_11_6
  simpa only [Bridge.to_intervalQ] using hA

theorem bad_row_arithmetic (r : W1CoverageRow) (hr : r ∈ w1BadRows) :
    estimate r.o ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ) ∧
    ((-3/20 : ℝ) ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ) ↔ r.covers = true) := by
  have hr' : r = ⟨⟨0,3,11,6⟩,1,-7/10,-3/20,true⟩ ∨
      r = ⟨⟨0,3,12,5⟩,18,-3/4,-3/10,false⟩ ∨
      r = ⟨⟨0,3,13,4⟩,45,-4/5,-7/20,false⟩ ∨
      r = ⟨⟨0,3,14,3⟩,20,-17/20,-2/5,false⟩ ∨
      r = ⟨⟨1,2,11,6⟩,33,-11/20,1/20,true⟩ ∨
      r = ⟨⟨1,2,12,5⟩,198,-3/5,0,true⟩ ∨
      r = ⟨⟨1,2,13,4⟩,165,-13/20,-1/20,true⟩ ∨
      r = ⟨⟨2,1,11,6⟩,165,-7/20,1/4,true⟩ ∨
      r = ⟨⟨2,1,12,5⟩,330,-2/5,1/5,true⟩ ∨
      r = ⟨⟨3,0,11,6⟩,165,-1/10,2/5,false⟩ := by
    simpa [w1BadRows] using hr
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [estimate, estimateQ, Set.mem_Icc]

theorem bad_row_facts (r : W1CoverageRow) (hr : r ∈ w1BadRows) :
    (Finset.univ.filter fun z : Assignment 20 3 =>
      unitObserved (w1BadOutcomes z.val) z.val = r.o).card = r.weight ∧
    intervalQ (109/500) r.o = some (r.lo,r.hi) ∧
    exactInterval ((109/500 : ℚ) : ℝ) r.o = Set.Icc (r.lo : ℝ) (r.hi : ℝ) ∧
    estimate r.o ∈ exactInterval ((109/500 : ℚ) : ℝ) r.o ∧
    ((-3/20 : ℝ) ∈ exactInterval ((109/500 : ℚ) : ℝ) r.o ↔ r.covers = true) := by
  obtain ⟨q,hq,hobs,hmult⟩ := audit_row_state r hr
  have hobs' : observed badPopulation (fromAudit q) = r.o := by
    simpa using congrArg fromAudit hobs
  have hcard_eq :
      (Finset.univ.filter fun z : Assignment 20 3 =>
        unitObserved (w1BadOutcomes z.val) z.val = r.o) =
      (Finset.univ.filter fun z : Assignment 20 3 =>
        _root_.AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val = q) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      have hobsz : observed badPopulation (fromAudit (_root_.AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val)) =
          observed badPopulation (fromAudit q) := (unit_observed_eq z).symm.trans (hz.trans hobs'.symm)
      have hobsAudit : _root_.AronowAudit.P003.observed (toAudit badPopulation)
          (_root_.AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val) =
          _root_.AronowAudit.P003.observed (toAudit badPopulation) q := by
        simpa only [← to_observed, to_from] using congrArg toAudit hobsz
      exact audit_state_observed_injective _ _
        (_root_.AronowAudit.P003.Wave1.neyman_treated_mem w1BadTable (toAudit badPopulation)
          audit_table_counts 3 z) hq hobsAudit
    · intro hz
      calc
        unitObserved (w1BadOutcomes z.val) z.val =
            observed badPopulation (fromAudit (_root_.AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val)) :=
              unit_observed_eq z
        _ = observed badPopulation (fromAudit q) := by rw [hz]
        _ = r.o := hobs'
  have hcard := _root_.AronowAudit.P003.Wave1.neyman_fiber_card w1BadTable (toAudit badPopulation) q
      audit_table_counts 3 (by
        have := _root_.AronowAudit.P003.random_state_facts (toAudit badPopulation) 3 q hq
        exact this.2.2.2.2)
  have hgroup :
      (Finset.univ.filter fun z : Assignment 20 3 =>
        unitObserved (w1BadOutcomes z.val) z.val = r.o).card = r.weight := by
    rw [hcard_eq, hcard, hmult]
  have hqI := bad_row_intervalQ r hr
  have hreal := real_interval_certificate (109/500) r.o r.lo r.hi hqI
  have harith := bad_row_arithmetic r hr
  refine ⟨hgroup, hqI, hreal.2.2.2, ?_, ?_⟩
  · rw [hreal.2.2.2]
    exact harith.1
  · rw [hreal.2.2.2]
    exact harith.2

end SAP.P003a.WH.W1.P.T1_L4

open _root_.SAP.P003a
open _root_.SAP.P003a.WH.W1
open _root_.SAP.P003a.Bridge
open _root_.SAP.P003a.WH.W1.P.T1_L4

theorem SAP.P003a.WH.W1.T1_L4_proof : SAP.P003a.WH.W1.T1_L4 := by
  change (w1BadRows.map W1CoverageRow.o).Nodup ∧
    (∀ z : Assignment 20 3, ∃ r ∈ w1BadRows,
      unitObserved (w1BadOutcomes z.val) z.val = r.o) ∧
    (∀ r ∈ w1BadRows,
      (Finset.univ.filter fun z : Assignment 20 3 =>
        unitObserved (w1BadOutcomes z.val) z.val = r.o).card = r.weight ∧
      intervalQ (109/500) r.o = some (r.lo,r.hi) ∧
      exactInterval ((109/500 : ℚ) : ℝ) r.o = Set.Icc (r.lo : ℝ) (r.hi : ℝ) ∧
      estimate r.o ∈ exactInterval ((109/500 : ℚ) : ℝ) r.o ∧
      ((-3/20 : ℝ) ∈ exactInterval ((109/500 : ℚ) : ℝ) r.o ↔ r.covers = true))
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro z
    let q := _root_.AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val
    have hq : q ∈ _root_.AronowAudit.P003.randomStates (toAudit badPopulation) 3 := by
      exact _root_.AronowAudit.P003.Wave1.neyman_treated_mem w1BadTable (toAudit badPopulation)
        audit_table_counts 3 z
    obtain ⟨r,hr,hobs⟩ := audit_state_row q hq
    refine ⟨r,hr,?_⟩
    have hobs' : observed badPopulation (fromAudit q) = r.o := by
      simpa using congrArg fromAudit hobs
    simpa [q] using (unit_observed_eq z).trans hobs'
  · intro r hr
    exact bad_row_facts r hr

