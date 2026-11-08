import SAP.P003a.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.Bridge
open SAP.P003a

/-- Pull a joint missingness law back along the four-field correspondence. -/
def liftLaw (μ : Counts → Counts → ℝ) (q r : A) : ℝ := μ (fromAudit q) (fromAudit r)

@[simp] theorem to_IsMissingLaw (v : Counts) (m : ℕ) (μ : Counts → Counts → ℝ) :
    AronowAudit.P003.IsMissingLaw (toAudit v) m (liftLaw μ) ↔ IsMissingLaw v m μ := by
  simp only [AronowAudit.P003.IsMissingLaw, IsMissingLaw, to_randomStates,
    List.forall_mem_map, to_observed, to_missingMasks, List.map_map,
    Function.comp_def, liftLaw, from_to, to_multiplicity, to_total]

@[simp] theorem to_missingProb (v : Counts) (m : ℕ) (μ : Counts → Counts → ℝ)
    (E : Counts → Counts → Prop) :
    AronowAudit.P003.missingProb (toAudit v) m (liftLaw μ)
      (fun q r => E (fromAudit q) (fromAudit r)) = missingProb v m μ E := by
  simp only [AronowAudit.P003.missingProb, missingProb, to_randomStates,
    List.map_map, Function.comp_def, to_observed, to_missingMasks, liftLaw, from_to]
  all_goals rfl

@[simp] theorem to_badPopulation : AronowAudit.P003.badPopulation = toAudit badPopulation := rfl
@[simp] theorem to_badMask (q : Counts) : AronowAudit.P003.badMask (toAudit q) = toAudit (badMask q) := by
  change (if toAudit q = toAudit ⟨0,0,3,0⟩ then toAudit ⟨0,0,1,0⟩ else toAudit ⟨0,0,0,0⟩) = _
  simp only [to_inj, badMask]
  split <;> rfl

@[simp] theorem to_badCoverage : AronowAudit.P003.badCoverage = badCoverage := by
  unfold AronowAudit.P003.badCoverage badCoverage
  simp only [to_badPopulation, to_randomStates, List.map_map, Function.comp_def,
    to_observed, to_badMask, to_missingIntervalQ, to_tauQ, to_multiplicity]

@[simp] theorem to_badHullCoverage : AronowAudit.P003.badHullCoverage = badHullCoverage := by
  unfold AronowAudit.P003.badHullCoverage badHullCoverage
  simp only [to_badPopulation, to_randomStates, List.map_map, Function.comp_def,
    to_observed, to_badMask, to_completionHullQ, to_tauQ, to_multiplicity]
  all_goals rfl

@[simp] theorem to_tableCounts {n : ℕ} (w : PotentialTable n) :
    AronowAudit.P003.tableCounts w = toAudit (tableCounts w) := rfl
@[simp] theorem to_tableTau {n : ℕ} (w : PotentialTable n) :
    AronowAudit.P003.tableTau w = tableTau w := rfl
@[simp] theorem to_tableEstimator {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) :
    AronowAudit.P003.tableEstimator w z = tableEstimator w z := rfl

@[simp] theorem to_varianceEstimate (o : Counts) :
    AronowAudit.P003.varianceEstimate (toAudit o) = varianceEstimate o := rfl
@[simp] theorem to_standardError (o : Counts) :
    AronowAudit.P003.standardError (toAudit o) = standardError o := rfl
@[simp] theorem to_studentized (C : ℝ) (o v : Counts) :
    AronowAudit.P003.studentized C (toAudit o) (toAudit v) = studentized C o v := rfl
@[simp] theorem to_canonicalObserved {n : ℕ} (v : Counts) (z : Finset (Fin n)) :
    AronowAudit.P003.canonicalObserved (toAudit v) z = toAudit (canonicalObserved v z) := rfl
@[simp] theorem to_treatedCounts {n : ℕ} (v : Counts) (z : Finset (Fin n)) :
    AronowAudit.P003.treatedCounts (toAudit v) z = toAudit (treatedCounts v z) := rfl

@[simp] theorem to_scaledEstimatorMass (v : Counts) (m : ℕ) :
    AronowAudit.P003.scaledEstimatorMass (toAudit v) m = scaledEstimatorMass v m := by
  funext j
  unfold AronowAudit.P003.scaledEstimatorMass scaledEstimatorMass
  simp only [AronowAudit.P003.designProb, designProb, to_randomStates, List.map_map,
    Function.comp_def, to_observed, to_estimateQ, to_multiplicity, to_total]
  all_goals rfl

@[simp] theorem to_unitObserved {n : ℕ} (y : Fin n → Bool) (z : Finset (Fin n)) :
    AronowAudit.P003.unitObserved y z = toAudit (unitObserved y z) := rfl

@[simp] theorem to_candidateNumerators (o : Counts) :
    AronowAudit.P003.candidateNumerators (toAudit o) = candidateNumerators o := rfl
@[simp] theorem to_reuseVector (v : Counts) (k : ℕ) :
    AronowAudit.P003.reuseVector (toAudit v) k = toAudit (reuseVector v k) := rfl
@[simp] theorem to_lineGroup (o : Counts) (x : ℤ) (j : ℕ) :
    AronowAudit.P003.lineGroup (toAudit o) x j = (lineGroup o x j).map toAudit := by
  simp only [AronowAudit.P003.lineGroup, lineGroup, to_possibleTables, List.filter_map]
  all_goals rfl

@[simp] theorem to_minimumB (xs : List Counts) :
    AronowAudit.P003.minimumB (xs.map toAudit) = (minimumB xs).map toAudit := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, AronowAudit.P003.minimumB, minimumB, ih]
    cases minimumB vs with
    | none => rfl
    | some u =>
      by_cases h : v.b ≤ u.b <;> simp [h, toAudit]

@[simp] theorem to_firstOnLine (o : Counts) (x : ℤ) (j : ℕ) :
    AronowAudit.P003.firstOnLine (toAudit o) x j = (firstOnLine o x j).map toAudit := by
  simp only [AronowAudit.P003.firstOnLine, firstOnLine, to_lineGroup, to_minimumB]

end SAP.P003a.Bridge
