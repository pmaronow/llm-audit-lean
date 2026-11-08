import SAP.P003a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P003a.WH.W1.P.T1_L1

open SAP.P003a
open SAP.P003a.Bridge

lemma badTable_canonical : ∀ i : Fin 20,
    w1BadTable i = canonicalPair badPopulation i.val := by
  decide +kernel

lemma badExceptional_treated_iff (z : Assignment 20 3) :
    treatedCounts badPopulation z.val = ⟨0,0,3,0⟩ ↔ z = w1CriticalAssignment := by
  constructor
  · intro hz
    have hz' : AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val = ⟨0,0,3,0⟩ := by
      simpa [AronowAudit.P003.Wave1.neyman_treated,
        AronowAudit.P003.Wave1.neyman_pack, treatedCounts, badTable_canonical] using hz
    have hf := (AronowAudit.P003.Wave1.neyman_treated_eq w1BadTable z.val
      ⟨0,0,3,0⟩).mp hz'
    have hsub : z.val ⊆ ({(11 : Fin 20), 12, 13} : Finset (Fin 20)) := by
      intro i hi
      by_contra hnot
      have htype : w1BadTable i ≠ (false,true) := by
        fin_cases i <;> simp_all [w1BadTable, badPopulation]
      rcases hpair : w1BadTable i with ⟨a,b⟩
      have hzero : (z.val.filter fun j => w1BadTable j = (a,b)).card = 0 := by
        have hcount := hf (a,b)
        cases a <;> cases b <;>
          simp_all [AronowAudit.P003.Wave1.neyman_typeCount]
      have hpos : 0 < (z.val.filter fun j => w1BadTable j = (a,b)).card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi,hpair⟩⟩
      omega
    have hcard : z.val.card = ({(11 : Fin 20), 12, 13} : Finset (Fin 20)).card := by
      rw [z.property]
      decide
    have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    apply Subtype.ext
    simpa [w1CriticalAssignment] using heq
  · intro hz
    subst z
    decide +kernel

lemma badObserved_canonical (z : Finset (Fin 20)) :
    unitObserved (w1BadOutcomes z) z = canonicalObserved badPopulation z := by
  apply Counts.ext
  · change (Finset.univ.filter fun i => i ∈ z ∧ w1BadOutcomes z i = true).card =
      (Finset.univ.filter fun i => i ∈ z ∧ (canonicalPair badPopulation i.val).1 = true).card
    apply congrArg Finset.card
    ext i
    by_cases hiz : i ∈ z <;>
      simp [w1BadOutcomes, unitOutcomes, badTable_canonical, hiz]
  · change (Finset.univ.filter fun i => i ∈ z ∧ w1BadOutcomes z i = false).card =
      (Finset.univ.filter fun i => i ∈ z ∧ (canonicalPair badPopulation i.val).1 = false).card
    apply congrArg Finset.card
    ext i
    by_cases hiz : i ∈ z <;>
      simp [w1BadOutcomes, unitOutcomes, badTable_canonical, hiz]
  · change (Finset.univ.filter fun i => i ∉ z ∧ w1BadOutcomes z i = true).card =
      (Finset.univ.filter fun i => i ∉ z ∧ (canonicalPair badPopulation i.val).2 = true).card
    apply congrArg Finset.card
    ext i
    by_cases hiz : i ∈ z <;>
      simp [w1BadOutcomes, unitOutcomes, badTable_canonical, hiz]
  · change (Finset.univ.filter fun i => i ∉ z ∧ w1BadOutcomes z i = false).card =
      (Finset.univ.filter fun i => i ∉ z ∧ (canonicalPair badPopulation i.val).2 = false).card
    apply congrArg Finset.card
    ext i
    by_cases hiz : i ∈ z <;>
      simp [w1BadOutcomes, unitOutcomes, badTable_canonical, hiz]

lemma badBinaryCompletion (z : Finset (Fin 20)) :
    w1BinaryCompletion (w1BadM z) (w1BadOutcomes z) := by
  intro i hi
  by_cases hm : i ∈ w1BadMissing z
  · simp [w1BadM, hm] at hi
  · simp [w1BadM, hm]

end SAP.P003a.WH.W1.P.T1_L1

theorem SAP.P003a.WH.W1.T1_L1_proof : SAP.P003a.WH.W1.T1_L1 := by
  classical
  unfold SAP.P003a.WH.W1.T1_L1 SAP.P003a.w1BadRealization
  have hcounts : tableCounts w1BadTable = badPopulation := by
    decide +kernel
  have hcard : Fintype.card (Assignment 20 3) = 1140 := by
    rw [AronowAudit.P003.Wave1.neyman_assignment_card]
    decide +kernel
  have htableAudit : AronowAudit.P003.tableCounts w1BadTable =
      SAP.P003a.Bridge.toAudit badPopulation := by
    rw [SAP.P003a.Bridge.to_tableCounts, hcounts]
  have hmaskpush := AronowAudit.P003.Wave1.neyman_event_pushforward
    w1BadTable (SAP.P003a.Bridge.toAudit badPopulation) htableAudit 3
  refine ⟨hcounts, ?_, hcard, ?_, ?_, ?_, ?_⟩
  · have hs := AronowAudit.P003.corrected_sate w1BadTable (by omega : 0 < 20)
    have htau := hs.2.2.2
    rw [SAP.P003a.Bridge.to_tableTau, htableAudit] at htau
    calc
      tableTau w1BadTable = tau badPopulation := by simpa only [SAP.P003a.Bridge.to_tau] using htau
      _ = -3/20 := by norm_num [tau, tauQ, badPopulation, Counts.effect, Counts.total]
  · intro z
    refine ⟨SAP.P003a.WH.W1.P.T1_L1.badObserved_canonical z.val,
      SAP.P003a.WH.W1.P.T1_L1.badTable_canonical, ?_, ?_,
      SAP.P003a.WH.W1.P.T1_L1.badBinaryCompletion z.val⟩
    · by_cases hz : z.val = w1CriticalAssignment.val
      · have : z = w1CriticalAssignment := Subtype.ext hz
        simp [w1BadMissing, this]
      · have : z ≠ w1CriticalAssignment := by
          intro he
          exact hz (congrArg Subtype.val he)
        simp [w1BadMissing, hz, this]
    · by_cases hz : z.val = w1CriticalAssignment.val
      · have : z = w1CriticalAssignment := Subtype.ext hz
        simp [w1BadMissing, this]
      · have : z ≠ w1CriticalAssignment := by
          intro he
          exact hz (congrArg Subtype.val he)
        simp [w1BadMissing, hz, this]
  · dsimp
    decide +kernel
  · intro E
    have hobs (z : Assignment 20 3) :
        canonicalObserved badPopulation z.val =
          SAP.P003a.Bridge.fromAudit (AronowAudit.P003.observed
            (SAP.P003a.Bridge.toAudit badPopulation)
            (AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val)) := by
      calc
        canonicalObserved badPopulation z.val =
            SAP.P003a.Bridge.fromAudit (AronowAudit.P003.canonicalObserved
              (SAP.P003a.Bridge.toAudit badPopulation) z.val) := by
                simp [SAP.P003a.Bridge.to_canonicalObserved]
        _ = SAP.P003a.Bridge.fromAudit (AronowAudit.P003.observed
              (SAP.P003a.Bridge.toAudit badPopulation)
              (AronowAudit.P003.treatedCounts (SAP.P003a.Bridge.toAudit badPopulation) z.val)) := by
                exact congrArg SAP.P003a.Bridge.fromAudit
                  (AronowAudit.P003.Wave1.monte_rank_valid_observed_bridge
                    (SAP.P003a.Bridge.toAudit badPopulation) z.val).symm
        _ = SAP.P003a.Bridge.fromAudit (AronowAudit.P003.observed
              (SAP.P003a.Bridge.toAudit badPopulation)
              (AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val)) := by
                congr 2
                simp [AronowAudit.P003.Wave1.neyman_treated,
                  AronowAudit.P003.Wave1.neyman_pack, AronowAudit.P003.treatedCounts,
                  SAP.P003a.WH.W1.P.T1_L1.badTable_canonical,
                  AronowAudit.P003.canonicalPair, SAP.P003a.canonicalPair,
                  SAP.P003a.Bridge.toAudit, badPopulation]
    have hp := hmaskpush (fun q => E (SAP.P003a.Bridge.fromAudit
      (AronowAudit.P003.observed (SAP.P003a.Bridge.toAudit badPopulation) q)))
    calc
      uniformProb (fun z : Assignment 20 3 => E (canonicalObserved badPopulation z.val)) =
          uniformProb (fun z : Assignment 20 3 =>
            E (SAP.P003a.Bridge.fromAudit
              (AronowAudit.P003.observed (SAP.P003a.Bridge.toAudit badPopulation)
                (AronowAudit.P003.Wave1.neyman_treated w1BadTable z.val)))) := by
        congr 1
        funext z
        exact congrArg E (hobs z)
      _ = AronowAudit.P003.designProb (SAP.P003a.Bridge.toAudit badPopulation) 3
          (fun q => E (SAP.P003a.Bridge.fromAudit
            (AronowAudit.P003.observed (SAP.P003a.Bridge.toAudit badPopulation) q))) := hp
      _ = AronowAudit.P003.designProb (SAP.P003a.Bridge.toAudit badPopulation) 3
          (fun q => E (observed badPopulation (SAP.P003a.Bridge.fromAudit q))) := by
        congr 1
      _ = designProb badPopulation 3 (fun q => E (observed badPopulation q)) := by
        exact SAP.P003a.Bridge.to_designProb badPopulation 3
          (fun q => E (observed badPopulation q))
  · intro z
    by_cases hz : z = w1CriticalAssignment
    · subst z
      dsimp [w1CriticalAssignment]
      decide +kernel
    · have hmissing : w1BadMissing z.val = ∅ := by
        have hzval : z.val ≠ w1CriticalAssignment.val := by
          intro hval
          apply hz
          exact Subtype.ext hval
        simp [w1BadMissing, hzval]
      have hstate : treatedCounts badPopulation z.val ≠ ⟨0,0,3,0⟩ := by
        intro he
        exact hz ((SAP.P003a.WH.W1.P.T1_L1.badExceptional_treated_iff z).mp he)
      have hmask : badMask (treatedCounts badPopulation z.val) = ⟨0,0,0,0⟩ := by
        simp [badMask, hstate]
      simp [hmissing, hmask]

