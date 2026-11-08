import SAP.P003a.Defs
import AronowAudit.P003.P003_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.Bridge
open SAP.P003a
abbrev A := AronowAudit.P003.Counts

def toAudit (v : Counts) : A := ⟨v.a,v.b,v.c,v.d⟩
def fromAudit (v : A) : Counts := ⟨v.a,v.b,v.c,v.d⟩
@[simp] theorem to_a (v : Counts) : (toAudit v).a = v.a := rfl
@[simp] theorem to_b (v : Counts) : (toAudit v).b = v.b := rfl
@[simp] theorem to_c (v : Counts) : (toAudit v).c = v.c := rfl
@[simp] theorem to_d (v : Counts) : (toAudit v).d = v.d := rfl
@[simp] theorem from_to (v : Counts) : fromAudit (toAudit v) = v := rfl
@[simp] theorem to_from (v : A) : toAudit (fromAudit v) = v := rfl
@[simp] theorem to_inj (v w : Counts) : toAudit v = toAudit w ↔ v = w := by
  constructor
  · intro h; exact congrArg fromAudit h
  · exact congrArg toAudit
@[simp] theorem to_total (v : Counts) : (toAudit v).total = v.total := rfl
@[simp] theorem to_effect (v : Counts) : (toAudit v).effect = v.effect := rfl
@[simp] theorem to_observed (v q : Counts) : AronowAudit.P003.observed (toAudit v) (toAudit q) = toAudit (observed v q) := rfl
@[simp] theorem to_randomStates (v : Counts) (m : ℕ) :
    AronowAudit.P003.randomStates (toAudit v) m = (randomStates v m).map toAudit := by
  simp [AronowAudit.P003.randomStates, randomStates, toAudit,
    List.map_flatMap, List.map_filterMap]
@[simp] theorem to_possibleTables (o : Counts) :
    AronowAudit.P003.possibleTables (toAudit o) = (possibleTables o).map toAudit := by
  simp [AronowAudit.P003.possibleTables, possibleTables, toAudit,
    List.map_flatMap, Function.comp_def]


@[simp] theorem to_tauQ (v : Counts) : AronowAudit.P003.tauQ (toAudit v) = tauQ v := rfl
@[simp] theorem to_tau (v : Counts) : AronowAudit.P003.tau (toAudit v) = tau v := rfl
@[simp] theorem to_estimateQ (v : Counts) : AronowAudit.P003.estimateQ (toAudit v) = estimateQ v := rfl
@[simp] theorem to_estimate (v : Counts) : AronowAudit.P003.estimate (toAudit v) = estimate v := rfl
@[simp] theorem to_multiplicity (v q : Counts) : AronowAudit.P003.multiplicity (toAudit v) (toAudit q) = multiplicity v q := rfl
@[simp] theorem to_deviation (v o : Counts) (m : ℕ) : AronowAudit.P003.deviationNumerator (toAudit v) (toAudit o) m = deviationNumerator v o m := rfl

@[simp] theorem to_tailCount (v o : Counts) : AronowAudit.P003.tailCount (toAudit v) (toAudit o) = tailCount v o := by
  simp only [AronowAudit.P003.tailCount, tailCount, to_a, to_b, to_randomStates,
    List.map_map, Function.comp_def, to_observed, to_deviation, to_multiplicity]
  all_goals rfl

@[simp] theorem to_pValue (v o : Counts) : AronowAudit.P003.pValue (toAudit v) (toAudit o) = pValue v o := by
  simp only [AronowAudit.P003.pValue, pValue, to_tailCount, to_total, to_a, to_b, AronowAudit.P003.binomial, binomial]

@[simp] theorem to_levelAccepted (α : ℚ) (v o : Counts) : AronowAudit.P003.levelAccepted α (toAudit v) (toAudit o) = levelAccepted α v o := by
  simp only [AronowAudit.P003.levelAccepted, levelAccepted, to_tailCount, to_total, to_a, to_b, AronowAudit.P003.binomial, binomial]
  all_goals rfl

@[simp] theorem to_possible (o v : Counts) : AronowAudit.P003.Possible (toAudit o) (toAudit v) ↔ Possible o v := by
  simp only [AronowAudit.P003.Possible, Possible, to_possibleTables, List.mem_map]
  simp only [to_inj, exists_eq_right]

@[simp] theorem to_accepted (α : ℝ) (o : Counts) : AronowAudit.P003.accepted α (toAudit o) = accepted α o := by
  classical
  ext t
  simp only [AronowAudit.P003.accepted, accepted, Finset.mem_image, List.mem_toFinset,
    List.mem_filter, decide_eq_true_eq, to_possibleTables, List.mem_map]
  constructor
  · rintro ⟨v, ⟨⟨u, hu, rfl⟩, ha⟩, ht⟩
    exact ⟨u, ⟨hu, by simpa only [to_pValue] using ha⟩, by simpa only [to_tau] using ht⟩
  · rintro ⟨u, ⟨hu, ha⟩, ht⟩
    exact ⟨toAudit u, ⟨⟨u, hu, rfl⟩, by simpa only [to_pValue] using ha⟩,
      by simpa only [to_tau] using ht⟩

@[simp] theorem to_exactInterval (α : ℝ) (o : Counts) : AronowAudit.P003.exactInterval α (toAudit o) = exactInterval α o := by
  simp only [AronowAudit.P003.exactInterval, exactInterval, to_accepted]

@[simp] theorem to_lower (α : ℝ) (o : Counts) : AronowAudit.P003.lower α (toAudit o) = lower α o := by
  simp only [AronowAudit.P003.lower, lower, to_accepted]
@[simp] theorem to_upper (α : ℝ) (o : Counts) : AronowAudit.P003.upper α (toAudit o) = upper α o := by
  simp only [AronowAudit.P003.upper, upper, to_accepted]

@[simp] theorem to_acceptedEffectsQ (α : ℚ) (o : Counts) : AronowAudit.P003.acceptedEffectsQ α (toAudit o) = acceptedEffectsQ α o := by
  classical
  simp only [AronowAudit.P003.acceptedEffectsQ, acceptedEffectsQ, to_possibleTables]
  rw [List.dedup_map_of_injective (by intro v w h; exact (to_inj v w).mp h)]
  simp only [List.filter_map, List.map_map, Function.comp_def, to_levelAccepted, to_effect]

@[simp] theorem to_intervalQ (α : ℚ) (o : Counts) : AronowAudit.P003.intervalQ α (toAudit o) = intervalQ α o := by
  simp only [AronowAudit.P003.intervalQ, intervalQ, to_acceptedEffectsQ, to_total]
  all_goals rfl

@[simp] theorem to_designProb (v : Counts) (m : ℕ) (E : Counts → Prop) :
    AronowAudit.P003.designProb (toAudit v) m (fun q => E (fromAudit q)) = designProb v m E := by
  simp only [AronowAudit.P003.designProb, designProb, to_randomStates,
    List.map_map, Function.comp_def, from_to, to_multiplicity, to_total]
  all_goals rfl

@[simp] theorem to_missingMasks (o : Counts) :
    AronowAudit.P003.missingMasks (toAudit o) = (missingMasks o).map toAudit := by
  simp [AronowAudit.P003.missingMasks, missingMasks, toAudit,
    List.map_flatMap, Function.comp_def]

@[simp] theorem to_plusCompletion (o r : Counts) :
    AronowAudit.P003.plusCompletion (toAudit o) (toAudit r) = toAudit (plusCompletion o r) := rfl
@[simp] theorem to_minusCompletion (o r : Counts) :
    AronowAudit.P003.minusCompletion (toAudit o) (toAudit r) = toAudit (minusCompletion o r) := rfl

@[simp] theorem to_completions (o r : Counts) :
    AronowAudit.P003.completions (toAudit o) (toAudit r) = (completions o r).map toAudit := by
  simp [AronowAudit.P003.completions, completions, toAudit,
    List.map_flatMap, Function.comp_def]

@[simp] theorem to_missingInterval (α : ℝ) (o r : Counts) :
    AronowAudit.P003.missingInterval α (toAudit o) (toAudit r) = missingInterval α o r := by
  simp only [AronowAudit.P003.missingInterval, missingInterval, to_plusCompletion,
    to_minusCompletion, to_accepted, to_lower, to_upper, to_estimate]

@[simp] theorem to_completionUnion (α : ℝ) (o r : Counts) :
    AronowAudit.P003.completionUnion α (toAudit o) (toAudit r) = completionUnion α o r := by
  ext t
  simp only [AronowAudit.P003.completionUnion, completionUnion, Set.mem_ofPred_eq,
    to_completions, List.mem_map]
  constructor
  · rintro ⟨v, ⟨u, hu, rfl⟩, ht⟩
    exact ⟨u, hu, by simpa only [to_exactInterval] using ht⟩
  · rintro ⟨u, hu, ht⟩
    exact ⟨toAudit u, ⟨u, hu, rfl⟩, by simpa only [to_exactInterval] using ht⟩

@[simp] theorem to_completionHull (α : ℝ) (o r : Counts) :
    AronowAudit.P003.completionHull α (toAudit o) (toAudit r) = completionHull α o r := by
  simp only [AronowAudit.P003.completionHull, completionHull, to_completionUnion]

@[simp] theorem to_missingIntervalQ (α : ℚ) (o r : Counts) :
    AronowAudit.P003.missingIntervalQ α (toAudit o) (toAudit r) = missingIntervalQ α o r := by
  simp only [AronowAudit.P003.missingIntervalQ, missingIntervalQ, to_minusCompletion,
    to_plusCompletion, to_intervalQ, to_estimateQ]
  all_goals rfl

@[simp] theorem to_completionHullQ (α : ℚ) (o r : Counts) :
    AronowAudit.P003.completionHullQ α (toAudit o) (toAudit r) = completionHullQ α o r := by
  simp only [AronowAudit.P003.completionHullQ, completionHullQ, to_completions,
    List.filterMap_map, Function.comp_def, to_intervalQ]
  all_goals rfl

end SAP.P003a.Bridge
