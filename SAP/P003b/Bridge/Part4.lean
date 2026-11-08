import SAP.P003b.Bridge.Part3
import AronowAudit.P003.P003_ConfidenceCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.Bridge
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

@[simp] theorem tauQ_any (v : AronowAudit.P003.Counts) :
    AronowAudit.P003.tauQ v = tauQ (fromCounts v) := rfl
@[simp] theorem tau_any (v : AronowAudit.P003.Counts) :
    AronowAudit.P003.tau v = tau (fromCounts v) := rfl
@[simp] theorem estimateQ_any (v : AronowAudit.P003.Counts) :
    AronowAudit.P003.estimateQ v = estimateQ (fromCounts v) := rfl
@[simp] theorem pValue_any (v o : AronowAudit.P003.Counts) :
    AronowAudit.P003.pValue v o = pValue (fromCounts v) (fromCounts o) := pValue_eq (fromCounts v) (fromCounts o)
@[simp] theorem possible_any (o v : AronowAudit.P003.Counts) :
    AronowAudit.P003.Possible o v ↔ Possible (fromCounts o) (fromCounts v) := possible_eq (fromCounts o) (fromCounts v)
@[simp] theorem acceptedEffects_any (α : ℚ) (o : AronowAudit.P003.Counts) :
    AronowAudit.P003.acceptedEffectsQ α o = acceptedEffectsQ α (fromCounts o) := acceptedEffects_eq α (fromCounts o)
@[simp] theorem intervalQ_any (α : ℚ) (o : AronowAudit.P003.Counts) :
    AronowAudit.P003.intervalQ α o = intervalQ α (fromCounts o) := intervalQ_eq α (fromCounts o)
@[simp] theorem candidateNumerators_any (o : AronowAudit.P003.Counts) :
    AronowAudit.P003.candidateNumerators o = candidateNumerators (fromCounts o) := rfl
@[simp] theorem badPopulation_eq : AronowAudit.P003.badPopulation = toCounts badPopulation := rfl
@[simp] theorem badMask_eq (q : Counts) :
    AronowAudit.P003.badMask (toCounts q) = toCounts (badMask q) := by
  simp only [AronowAudit.P003.badMask, badMask]
  have h : toCounts q = (⟨0,0,3,0⟩ : AronowAudit.P003.Counts) ↔ q = (⟨0,0,3,0⟩ : Counts) := to_inj q (⟨0,0,3,0⟩ : Counts)
  simp only [h]
  split_ifs <;> rfl

@[simp] theorem randomStates_any (v : AronowAudit.P003.Counts) (m : ℕ) :
    AronowAudit.P003.randomStates v m = (randomStates (fromCounts v) m).map toCounts := randomStates_eq (fromCounts v) m
@[simp] theorem multiplicity_any (v q : AronowAudit.P003.Counts) :
    AronowAudit.P003.multiplicity v q = multiplicity (fromCounts v) (fromCounts q) := rfl
@[simp] theorem observed_any (v q : AronowAudit.P003.Counts) :
    AronowAudit.P003.observed v q = toCounts (observed (fromCounts v) (fromCounts q)) := rfl
@[simp] theorem shuffleCost_any {n K : ℕ} (α ε : ℝ) (o : AronowAudit.P003.Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n (n/2)) :
    AronowAudit.P003.upperShuffleCost α ε o pool = upperShuffleCost α ε (fromCounts o) pool := shuffleCost_eq α ε (fromCounts o) pool
@[simp] theorem expectedShuffleCost_any (α ε : ℝ) (n K : ℕ) (o : AronowAudit.P003.Counts) :
    AronowAudit.P003.expectedUpperShuffleCost α ε n K o = expectedUpperShuffleCost α ε n K (fromCounts o) := expectedShuffleCost_eq α ε n K (fromCounts o)

/-- Transfer an already certified rational inversion to a nonempty real accepted set. -/
theorem certified_nonempty (o : AronowAudit.P003.Counts) (l u : ℚ)
    (h : AronowAudit.P003.intervalQ (109/500) o = some (l,u)) :
    (AronowAudit.P003.accepted (109/500) o).Nonempty := by
  simpa only [Rat.cast_div,Rat.cast_ofNat] using
    (AronowAudit.P003.ConfidenceFollowup.real_extrema_of_intervalQ (109/500) o l u h).1

/-- Endpoint existence on the ten already enumerated design states of the counterexample. -/
theorem bad_endpoints_native (q : AronowAudit.P003.Counts)
    (hq : q ∈ AronowAudit.P003.randomStates AronowAudit.P003.badPopulation 3) :
    (AronowAudit.P003.accepted (109/500)
      (AronowAudit.P003.minusCompletion (AronowAudit.P003.observed AronowAudit.P003.badPopulation q)
        (AronowAudit.P003.badMask q))).Nonempty ∧
    (AronowAudit.P003.accepted (109/500)
      (AronowAudit.P003.plusCompletion (AronowAudit.P003.observed AronowAudit.P003.badPopulation q)
        (AronowAudit.P003.badMask q))).Nonempty := by
  rw [AronowAudit.P003.bad_random_states_certificate] at hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (AronowAudit.P003.accepted (109/500) ⟨0,3,14,3⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨0,3,14,3⟩).Nonempty
    exact ⟨certified_nonempty ⟨0,3,14,3⟩ _ _ AronowAudit.P003.interval_obs_0_3_14_3,
      certified_nonempty ⟨0,3,14,3⟩ _ _ AronowAudit.P003.interval_obs_0_3_14_3⟩
  · change (AronowAudit.P003.accepted (109/500) ⟨0,3,13,4⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨0,3,13,4⟩).Nonempty
    exact ⟨certified_nonempty ⟨0,3,13,4⟩ _ _ AronowAudit.P003.interval_obs_0_3_13_4,
      certified_nonempty ⟨0,3,13,4⟩ _ _ AronowAudit.P003.interval_obs_0_3_13_4⟩
  · change (AronowAudit.P003.accepted (109/500) ⟨0,3,12,5⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨0,3,12,5⟩).Nonempty
    exact ⟨certified_nonempty ⟨0,3,12,5⟩ _ _ AronowAudit.P003.interval_obs_0_3_12_5,
      certified_nonempty ⟨0,3,12,5⟩ _ _ AronowAudit.P003.interval_obs_0_3_12_5⟩
  · change (AronowAudit.P003.accepted (109/500) ⟨0,3,11,6⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨0,3,10,7⟩).Nonempty
    exact ⟨certified_nonempty ⟨0,3,11,6⟩ _ _ AronowAudit.P003.interval_obs_0_3_11_6,
      certified_nonempty ⟨0,3,10,7⟩ _ _ AronowAudit.P003.interval_obs_0_3_10_7⟩
  · change (AronowAudit.P003.accepted (109/500) ⟨1,2,13,4⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨1,2,13,4⟩).Nonempty
    exact ⟨certified_nonempty ⟨1,2,13,4⟩ _ _ AronowAudit.P003.interval_obs_1_2_13_4,
      certified_nonempty ⟨1,2,13,4⟩ _ _ AronowAudit.P003.interval_obs_1_2_13_4⟩
  · change (AronowAudit.P003.accepted (109/500) ⟨1,2,12,5⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨1,2,12,5⟩).Nonempty
    exact ⟨certified_nonempty ⟨1,2,12,5⟩ _ _ AronowAudit.P003.interval_obs_1_2_12_5,
      certified_nonempty ⟨1,2,12,5⟩ _ _ AronowAudit.P003.interval_obs_1_2_12_5⟩
  · change (AronowAudit.P003.accepted (109/500) ⟨1,2,11,6⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨1,2,11,6⟩).Nonempty
    exact ⟨certified_nonempty ⟨1,2,11,6⟩ _ _ AronowAudit.P003.interval_obs_1_2_11_6,
      certified_nonempty ⟨1,2,11,6⟩ _ _ AronowAudit.P003.interval_obs_1_2_11_6⟩
  · change (AronowAudit.P003.accepted (109/500) ⟨2,1,12,5⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨2,1,12,5⟩).Nonempty
    exact ⟨certified_nonempty ⟨2,1,12,5⟩ _ _ AronowAudit.P003.interval_obs_2_1_12_5,
      certified_nonempty ⟨2,1,12,5⟩ _ _ AronowAudit.P003.interval_obs_2_1_12_5⟩
  · change (AronowAudit.P003.accepted (109/500) ⟨2,1,11,6⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨2,1,11,6⟩).Nonempty
    exact ⟨certified_nonempty ⟨2,1,11,6⟩ _ _ AronowAudit.P003.interval_obs_2_1_11_6,
      certified_nonempty ⟨2,1,11,6⟩ _ _ AronowAudit.P003.interval_obs_2_1_11_6⟩
  · change (AronowAudit.P003.accepted (109/500) ⟨3,0,11,6⟩).Nonempty ∧
      (AronowAudit.P003.accepted (109/500) ⟨3,0,11,6⟩).Nonempty
    exact ⟨certified_nonempty ⟨3,0,11,6⟩ _ _ AronowAudit.P003.interval_obs_3_0_11_6,
      certified_nonempty ⟨3,0,11,6⟩ _ _ AronowAudit.P003.interval_obs_3_0_11_6⟩

@[simp] theorem traceGet_snd (xs : List (Counts × Bool)) (i : ℕ) :
    ((xs.map toTrace)[i]!).2 = xs[i]!.2 := by
  by_cases h : i < xs.length
  · simp [getElem!_pos, h, toTrace]
  · have h' : ¬ i < (xs.map toTrace).length := by simpa using h
    rw [getElem!_neg xs i h, getElem!_neg _ i h']
    rfl

end
end SAP.P003b.Bridge
