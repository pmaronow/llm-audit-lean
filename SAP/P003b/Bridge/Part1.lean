import SAP.P003b.Defs
import AronowAudit.P003.P003_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.Bridge
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

abbrev toCounts (v : Counts) : AronowAudit.P003.Counts := ⟨v.a,v.b,v.c,v.d⟩
abbrev fromCounts (v : AronowAudit.P003.Counts) : Counts := ⟨v.a,v.b,v.c,v.d⟩
@[simp] theorem from_to (v : Counts) : fromCounts (toCounts v) = v := rfl
@[simp] theorem to_from (v : AronowAudit.P003.Counts) : toCounts (fromCounts v) = v := rfl
@[simp] theorem to_inj (v w : Counts) : toCounts v = toCounts w ↔ v = w := by
  constructor
  · intro h; exact congrArg fromCounts h
  · exact congrArg toCounts
@[simp] theorem total_eq (v : Counts) : (toCounts v).total = v.total := rfl
@[simp] theorem effect_eq (v : Counts) : (toCounts v).effect = v.effect := rfl
@[simp] theorem tauQ_eq (v : Counts) : AronowAudit.P003.tauQ (toCounts v) = tauQ v := rfl
@[simp] theorem tau_eq (v : Counts) : AronowAudit.P003.tau (toCounts v) = tau v := rfl
@[simp] theorem estimateQ_eq (v : Counts) : AronowAudit.P003.estimateQ (toCounts v) = estimateQ v := rfl
@[simp] theorem estimate_eq (v : Counts) : AronowAudit.P003.estimate (toCounts v) = estimate v := rfl
@[simp] theorem randomStates_eq (v : Counts) (m : ℕ) :
    AronowAudit.P003.randomStates (toCounts v) m = (randomStates v m).map toCounts := by
  simp [AronowAudit.P003.randomStates, randomStates, List.map_flatMap,
    List.map_filterMap, Function.comp_def, toCounts]
@[simp] theorem multiplicity_eq (v q : Counts) :
    AronowAudit.P003.multiplicity (toCounts v) (toCounts q) = multiplicity v q := rfl
@[simp] theorem observed_eq (v q : Counts) :
    AronowAudit.P003.observed (toCounts v) (toCounts q) = toCounts (observed v q) := rfl
@[simp] theorem designProb_eq (v : Counts) (m : ℕ) (E : AronowAudit.P003.Counts → Prop) :
    AronowAudit.P003.designProb (toCounts v) m E = designProb v m (fun q => E (toCounts q)) := by
  simp [AronowAudit.P003.designProb, designProb, List.map_map, Function.comp_def]
@[simp] theorem designMean_eq (v : Counts) (m : ℕ) (f : AronowAudit.P003.Counts → ℝ) :
    AronowAudit.P003.designMean (toCounts v) m f = designMean v m (fun q => f (toCounts q)) := by
  simp [AronowAudit.P003.designMean, designMean, List.map_map, Function.comp_def]
@[simp] theorem deviation_eq (v o : Counts) (m : ℕ) :
    AronowAudit.P003.deviationNumerator (toCounts v) (toCounts o) m = deviationNumerator v o m := rfl
@[simp] theorem tail_eq (v o : Counts) : AronowAudit.P003.tailCount (toCounts v) (toCounts o) = tailCount v o := by
  simp [AronowAudit.P003.tailCount, tailCount, List.map_map, Function.comp_def]
  all_goals rfl
@[simp] theorem pValue_eq (v o : Counts) : AronowAudit.P003.pValue (toCounts v) (toCounts o) = pValue v o := by
  simp [AronowAudit.P003.pValue, pValue, AronowAudit.P003.binomial, binomial]
@[simp] theorem level_eq (α : ℚ) (v o : Counts) :
    AronowAudit.P003.levelAccepted α (toCounts v) (toCounts o) = levelAccepted α v o := by
  simp [AronowAudit.P003.levelAccepted, levelAccepted, AronowAudit.P003.binomial, binomial]
  all_goals rfl
@[simp] theorem possibleTables_eq (o : Counts) :
    AronowAudit.P003.possibleTables (toCounts o) = (possibleTables o).map toCounts := by
  simp [AronowAudit.P003.possibleTables, possibleTables, List.map_flatMap,
    List.map_map, Function.comp_def, toCounts]
@[simp] theorem possible_eq (o v : Counts) :
    AronowAudit.P003.Possible (toCounts o) (toCounts v) ↔ Possible o v := by
  rw [AronowAudit.P003.Possible, possibleTables_eq]
  simp only [List.mem_map, to_inj, exists_eq_right]
  all_goals rfl
@[simp] theorem accepted_eq (α : ℝ) (o : Counts) :
    AronowAudit.P003.accepted α (toCounts o) = accepted α o := by
  ext t
  simp [AronowAudit.P003.accepted, accepted, List.filter_map, List.mem_map]
  all_goals rfl
@[simp] theorem interval_eq (α : ℝ) (o : Counts) :
    AronowAudit.P003.exactInterval α (toCounts o) = exactInterval α o := by
  simp [AronowAudit.P003.exactInterval, exactInterval]
@[simp] theorem lower_eq (α : ℝ) (o : Counts) : AronowAudit.P003.lower α (toCounts o) = lower α o := by
  simp [AronowAudit.P003.lower, lower]
@[simp] theorem upper_eq (α : ℝ) (o : Counts) : AronowAudit.P003.upper α (toCounts o) = upper α o := by
  simp [AronowAudit.P003.upper, upper]
@[simp] theorem acceptedEffects_eq (α : ℚ) (o : Counts) :
    AronowAudit.P003.acceptedEffectsQ α (toCounts o) = acceptedEffectsQ α o := by
  simp [AronowAudit.P003.acceptedEffectsQ, acceptedEffectsQ, List.dedup_map_of_injective,
    List.filter_map, List.map_map, Function.comp_def,
    show Function.Injective toCounts from fun _ _ h => congrArg fromCounts h]
@[simp] theorem intervalQ_eq (α : ℚ) (o : Counts) : AronowAudit.P003.intervalQ α (toCounts o) = intervalQ α o := by
  simp [AronowAudit.P003.intervalQ, intervalQ]
  all_goals rfl
@[simp] theorem candidateNumerators_eq (o : Counts) :
    AronowAudit.P003.candidateNumerators (toCounts o) = candidateNumerators o := rfl
@[simp] theorem candidateLattice_eq (o : Counts) :
    AronowAudit.P003.candidateLattice (toCounts o) = candidateLattice o := rfl
@[simp] theorem reuseVector_eq (v : Counts) (k : ℕ) :
    AronowAudit.P003.reuseVector (toCounts v) k = toCounts (reuseVector v k) := rfl
@[simp] theorem tableCounts_eq {n : ℕ} (w : PotentialTable n) :
    AronowAudit.P003.tableCounts w = toCounts (tableCounts w) := rfl
@[simp] theorem tableTau_eq {n : ℕ} (w : PotentialTable n) : AronowAudit.P003.tableTau w = tableTau w := rfl
@[simp] theorem tableEstimator_eq {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) :
    AronowAudit.P003.tableEstimator w z = tableEstimator w z := rfl

end
end SAP.P003b.Bridge
