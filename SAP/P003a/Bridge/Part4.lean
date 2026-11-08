import SAP.P003a.Bridge.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.Bridge
open SAP.P003a

/-- The two four-field types represent exactly the same data. -/
theorem forall_audit (P : A → Prop) : (∀ v, P v) ↔ ∀ v : Counts, P (toAudit v) := by
  constructor
  · intro h v; exact h (toAudit v)
  · intro h v; simpa only [to_from] using h (fromAudit v)

@[simp] theorem decode_tauQ (v : A) :
    AronowAudit.P003.tauQ v = tauQ (fromAudit v) := by
  simpa only [to_from] using to_tauQ (fromAudit v)

@[simp] theorem decode_tau (v : A) :
    AronowAudit.P003.tau v = tau (fromAudit v) := by
  simpa only [to_from] using to_tau (fromAudit v)

@[simp] theorem decode_estimateQ (o : A) :
    AronowAudit.P003.estimateQ o = estimateQ (fromAudit o) := by
  simpa only [to_from] using to_estimateQ (fromAudit o)

@[simp] theorem decode_estimate (o : A) :
    AronowAudit.P003.estimate o = estimate (fromAudit o) := by
  simpa only [to_from] using to_estimate (fromAudit o)

@[simp] theorem decode_pValue (v o : A) :
    AronowAudit.P003.pValue v o = pValue (fromAudit v) (fromAudit o) := by
  simpa only [to_from] using to_pValue (fromAudit v) (fromAudit o)

@[simp] theorem decode_levelAccepted (α : ℚ) (v o : A) :
    AronowAudit.P003.levelAccepted α v o = levelAccepted α (fromAudit v) (fromAudit o) := by
  simpa only [to_from] using to_levelAccepted α (fromAudit v) (fromAudit o)

@[simp] theorem decode_intervalQ (α : ℚ) (o : A) :
    AronowAudit.P003.intervalQ α o = intervalQ α (fromAudit o) := by
  simpa only [to_from] using to_intervalQ α (fromAudit o)

@[simp] theorem decode_acceptedEffectsQ (α : ℚ) (o : A) :
    AronowAudit.P003.acceptedEffectsQ α o = acceptedEffectsQ α (fromAudit o) := by
  simpa only [to_from] using to_acceptedEffectsQ α (fromAudit o)

@[simp] theorem decode_Possible (o v : A) :
    AronowAudit.P003.Possible o v ↔ Possible (fromAudit o) (fromAudit v) := by
  simpa only [to_from] using to_possible (fromAudit o) (fromAudit v)

@[simp] theorem decode_exactInterval (α : ℝ) (o : A) :
    AronowAudit.P003.exactInterval α o = exactInterval α (fromAudit o) := by
  simpa only [to_from] using to_exactInterval α (fromAudit o)

@[simp] theorem decode_missingIntervalQ (α : ℚ) (o r : A) :
    AronowAudit.P003.missingIntervalQ α o r = missingIntervalQ α (fromAudit o) (fromAudit r) := by
  simpa only [to_from] using to_missingIntervalQ α (fromAudit o) (fromAudit r)

@[simp] theorem decode_completionHullQ (α : ℚ) (o r : A) :
    AronowAudit.P003.completionHullQ α o r = completionHullQ α (fromAudit o) (fromAudit r) := by
  simpa only [to_from] using to_completionHullQ α (fromAudit o) (fromAudit r)

@[simp] theorem decode_varianceEstimate (o : A) :
    AronowAudit.P003.varianceEstimate o = varianceEstimate (fromAudit o) := by
  simpa only [to_from] using to_varianceEstimate (fromAudit o)

@[simp] theorem decode_standardError (o : A) :
    AronowAudit.P003.standardError o = standardError (fromAudit o) := by
  simpa only [to_from] using to_standardError (fromAudit o)

@[simp] theorem decode_studentized (C : ℝ) (o v : A) :
    AronowAudit.P003.studentized C o v = studentized C (fromAudit o) (fromAudit v) := by
  simpa only [to_from] using to_studentized C (fromAudit o) (fromAudit v)

@[simp] theorem decode_observed (v q : A) :
    fromAudit (AronowAudit.P003.observed v q) = observed (fromAudit v) (fromAudit q) := by
  have h := congrArg fromAudit (to_observed (fromAudit v) (fromAudit q))
  simpa only [to_from, from_to] using h

@[simp] theorem decode_tableCounts {n : ℕ} (w : PotentialTable n) :
    fromAudit (AronowAudit.P003.tableCounts w) = tableCounts w := rfl

@[simp] theorem decode_designProb (v : A) (m : ℕ) (E : A → Prop) :
    AronowAudit.P003.designProb v m E = designProb (fromAudit v) m (fun q => E (toAudit q)) := by
  simpa only [to_from] using to_designProb (fromAudit v) m (fun q => E (toAudit q))

@[simp] theorem decode_missingProb (v : Counts) (m : ℕ) (μ : Counts → Counts → ℝ)
    (E : A → A → Prop) :
    AronowAudit.P003.missingProb (toAudit v) m (liftLaw μ) E =
      missingProb v m μ (fun q r => E (toAudit q) (toAudit r)) := by
  simpa only [to_from] using to_missingProb v m μ (fun q r => E (toAudit q) (toAudit r))

@[simp] theorem decode_firstOnLine (o : A) (x : ℤ) (j : ℕ) :
    (AronowAudit.P003.firstOnLine o x j).map fromAudit = firstOnLine (fromAudit o) x j := by
  have h := congrArg (Option.map fromAudit) (to_firstOnLine (fromAudit o) x j)
  simpa [Option.map_map, Function.comp_def] using h

@[simp] theorem decode_reuseVector (v : A) (k : ℕ) :
    fromAudit (AronowAudit.P003.reuseVector v k) = reuseVector (fromAudit v) k := by
  have h := congrArg fromAudit (to_reuseVector (fromAudit v) k)
  simpa only [to_from, from_to] using h

@[simp] theorem decode_possibleTablesFinset (o : A) :
    (AronowAudit.P003.possibleTables o).toFinset.image fromAudit = (possibleTables (fromAudit o)).toFinset := by
  have he := to_possibleTables (fromAudit o)
  rw [to_from] at he
  rw [he]
  ext v
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact hb
  · intro hv
    exact ⟨toAudit v, ⟨v, hv, rfl⟩, rfl⟩

@[simp] theorem decode_upperRun (corrected : Bool) (o : A) (α : ℚ) :
    (AronowAudit.P003.upperRun corrected o (AronowAudit.P003.exactRejectQ α o)).value =
      (upperRun corrected (fromAudit o) (exactRejectQ α (fromAudit o))).value := by
  have he : (fun v i => exactRejectQ α (fromAudit o) (fromAudit v) i) =
      AronowAudit.P003.exactRejectQ α o := by
    funext v i
    simp only [AronowAudit.P003.exactRejectQ, exactRejectQ, decode_levelAccepted]
  have h := to_upperRun corrected (fromAudit o) (exactRejectQ α (fromAudit o)) 0
  simpa only [to_from, he, mapEndpoint] using h

@[simp] theorem decode_mk (a b c d : ℕ) :
    fromAudit (AronowAudit.P003.Counts.mk a b c d) = Counts.mk a b c d := rfl
@[simp] theorem bit_eq (b : Bool) : AronowAudit.P003.bit b = bit b := rfl
@[simp] theorem logTwo_eq (x : ℝ) : AronowAudit.P003.logTwo x = logTwo x := rfl
@[simp] theorem searchStep_eq (f : ℤ → Bool) (a b : ℤ) :
    AronowAudit.P003.searchStep f a b = searchStep f a b := rfl
@[simp] theorem isSD_eq (f : ℤ → ℝ) : AronowAudit.P003.IsSD f ↔ IsSD f := Iff.rfl
@[simp] theorem uniformProb_eq {Ω : Type*} [Fintype Ω] (E : Ω → Prop) :
    AronowAudit.P003.uniformProb E = uniformProb E := rfl
@[simp] theorem unitPlus_eq {n : ℕ} (y : Fin n → Bool) (z r : Finset (Fin n)) :
    AronowAudit.P003.unitPlus y z r = unitPlus y z r := rfl
@[simp] theorem coupledPlus_eq {n : ℕ} (w : PotentialTable n) (y : Fin n → Bool)
    (z : Finset (Fin n)) : AronowAudit.P003.coupledPlus w y z = coupledPlus w y z := rfl
@[simp] theorem PossibleTable_eq {n : ℕ} (y : Fin n → Bool) (z : Finset (Fin n))
    (w : PotentialTable n) : AronowAudit.P003.PossibleTable y z w ↔ PossibleTable y z w := Iff.rfl
@[simp] theorem outcomeEstimator_eq {n : ℕ} (y : Fin n → Bool) (z : Finset (Fin n)) :
    AronowAudit.P003.outcomeEstimator y z = outcomeEstimator y z := rfl
@[simp] theorem unitPValue_eq {n : ℕ} (w : PotentialTable n) (y : Fin n → Bool)
    (z : Finset (Fin n)) : AronowAudit.P003.unitPValue w y z = unitPValue w y z := rfl

end SAP.P003a.Bridge
