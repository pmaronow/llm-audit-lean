import SAP.P003b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.Bridge
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

@[simp] theorem lineGroup_eq (o : Counts) (x : ℤ) (j : ℕ) :
    AronowAudit.P003.lineGroup (toCounts o) x j = (lineGroup o x j).map toCounts := by
  simp [AronowAudit.P003.lineGroup, lineGroup, List.filter_map, Function.comp_def]
  all_goals rfl
@[simp] theorem minimumB_eq (xs : List Counts) :
    AronowAudit.P003.minimumB (xs.map toCounts) = (minimumB xs).map toCounts := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, AronowAudit.P003.minimumB, minimumB, ih]
    cases minimumB vs with
    | none => rfl
    | some u =>
      simp only [Option.map_some]
      split_ifs <;> rfl
@[simp] theorem firstOnLine_eq (o : Counts) (x : ℤ) (j : ℕ) :
    AronowAudit.P003.firstOnLine (toCounts o) x j = (firstOnLine o x j).map toCounts := by
  simp [AronowAudit.P003.firstOnLine, firstOnLine]
@[simp] theorem candidates_eq (o : Counts) (x : ℤ) :
    AronowAudit.P003.candidates (toCounts o) x = (candidates o x).map toCounts := by
  simp only [AronowAudit.P003.candidates, candidates, total_eq, List.map_flatMap]
  congr 1
  funext j
  rw [firstOnLine_eq]
  cases firstOnLine o x j with
  | none => rfl
  | some v =>
    simp only [Option.map_some]
    have hp := possible_eq o ⟨v.a-1,1,1,v.d-1⟩
    simp only [toCounts] at hp ⊢
    simp only [hp]
    split_ifs <;> rfl

abbrev toTrace (p : Counts × Bool) : AronowAudit.P003.Counts × Bool := (toCounts p.1,p.2)
abbrev toQuery (r : QueryResult) : AronowAudit.P003.QueryResult :=
  ⟨r.compatible,r.idx,r.trace.map toTrace⟩
abbrev toEndpoint (r : EndpointResult) : AronowAudit.P003.EndpointResult :=
  ⟨r.value,r.trace.map toTrace⟩

@[simp] theorem runTests_eq (reject : AronowAudit.P003.Counts → ℕ → Bool)
    (idx : ℕ) (xs : List Counts) :
    AronowAudit.P003.runTests reject idx (xs.map toCounts) =
      toQuery (runTests (fun v => reject (toCounts v)) idx xs) := by
  induction xs generalizing idx with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, AronowAudit.P003.runTests, runTests]
    split_ifs <;> simp [ih, toQuery, toTrace]
@[simp] theorem adaptiveSearch_eq (fuel : ℕ) (corrected : Bool) (o : Counts)
    (k₁ k₂ : ℤ) (reject : AronowAudit.P003.Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) :
    AronowAudit.P003.adaptiveSearch fuel corrected (toCounts o) k₁ k₂ reject a b idx =
      toEndpoint (adaptiveSearch fuel corrected o k₁ k₂
        (fun v => reject (toCounts v)) a b idx) := by
  induction fuel generalizing a b idx with
  | zero =>
    simp only [AronowAudit.P003.adaptiveSearch, adaptiveSearch]
    split_ifs <;> rfl
  | succ fuel ih =>
    simp only [AronowAudit.P003.adaptiveSearch, adaptiveSearch, candidates_eq, runTests_eq]
    split_ifs <;> simp [ih, toEndpoint, toQuery, toTrace, List.map_append]
@[simp] theorem upperRun_eq (corrected : Bool) (o : Counts)
    (reject : AronowAudit.P003.Counts → ℕ → Bool) (idx : ℕ) :
    AronowAudit.P003.upperRun corrected (toCounts o) reject idx =
      toEndpoint (upperRun corrected o (fun v => reject (toCounts v)) idx) := by
  simp [AronowAudit.P003.upperRun, upperRun]
@[simp] theorem canonicalPair_eq (v : Counts) (i : ℕ) :
    AronowAudit.P003.canonicalPair (toCounts v) i = canonicalPair v i := rfl
@[simp] theorem canonicalObserved_eq {n : ℕ} (v : Counts) (z : Finset (Fin n)) :
    AronowAudit.P003.canonicalObserved (toCounts v) z = toCounts (canonicalObserved v z) := rfl
@[simp] theorem complement_eq (o : Counts) :
    AronowAudit.P003.complementObserved (toCounts o) = toCounts (complementObserved o) := rfl
@[simp] theorem exactRejectQ_eq (α : ℚ) (o v : Counts) (idx : ℕ) :
    AronowAudit.P003.exactRejectQ α (toCounts o) (toCounts v) idx = exactRejectQ α o v idx := by
  simp [AronowAudit.P003.exactRejectQ, exactRejectQ]
@[simp] theorem exactRejectQ_fn (α : ℚ) (o : Counts) :
    (fun v => AronowAudit.P003.exactRejectQ α (toCounts o) (toCounts v)) = exactRejectQ α o := by
  funext v idx
  exact exactRejectQ_eq α o v idx
@[simp] theorem exactUpperRun_eq (α : ℝ) (o : Counts) :
    AronowAudit.P003.exactUpperRun α (toCounts o) = toEndpoint (exactUpperRun α o) := by
  simp [AronowAudit.P003.exactUpperRun, exactUpperRun]
@[simp] theorem monteMean_eq {n K : ℕ} (v o : Counts) (draws : Fin K → Finset (Fin n)) :
    AronowAudit.P003.monteMean (toCounts v) (toCounts o) draws = monteMean v o draws := by
  simp [AronowAudit.P003.monteMean, monteMean]
  all_goals rfl
@[simp] theorem testBudget_eq (n : ℕ) : AronowAudit.P003.testBudget n = testBudget n := rfl
@[simp] theorem uniformProb_eq {Ω : Type*} [Fintype Ω] (E : Ω → Prop) :
    AronowAudit.P003.uniformProb E = uniformProb E := rfl
@[simp] theorem approximateReject_eq {n m K : ℕ} (α ε : ℝ) (o v : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) (idx : ℕ) :
    AronowAudit.P003.approximateReject α ε (toCounts o) pool (toCounts v) idx =
      approximateReject α ε o pool v idx := by
  simp [AronowAudit.P003.approximateReject, approximateReject,
    AronowAudit.P003.batch, batch]
  all_goals rfl
@[simp] theorem approximateReject_fn {n m K : ℕ} (α ε : ℝ) (o : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) :
    (fun v => AronowAudit.P003.approximateReject α ε (toCounts o) pool (toCounts v)) =
      approximateReject α ε o pool := by
  funext v idx
  exact approximateReject_eq α ε o v pool idx
@[simp] theorem monteEndpoints_eq {n m K : ℕ} (corrected : Bool) (α ε : ℝ) (o : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) :
    AronowAudit.P003.monteEndpoints corrected α ε (toCounts o) pool =
      (toEndpoint (monteEndpoints corrected α ε o pool).1,
       toEndpoint (monteEndpoints corrected α ε o pool).2) := by
  simp [AronowAudit.P003.monteEndpoints, monteEndpoints, toEndpoint, List.length_map]
@[simp] theorem monteInterval_eq {n m K : ℕ} (corrected : Bool) (α ε : ℝ) (o : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n m) :
    AronowAudit.P003.monteInterval corrected α ε (toCounts o) pool = monteInterval corrected α ε o pool := by
  simp [AronowAudit.P003.monteInterval, monteInterval, toEndpoint]
  all_goals rfl
@[simp] theorem traceProbability_eq (o : Counts) (xs : List (Counts × Bool)) :
    AronowAudit.P003.traceProbabilityQ (toCounts o) (xs.map toTrace) = traceProbabilityQ o xs := by
  simp [AronowAudit.P003.traceProbabilityQ, traceProbabilityQ, List.map_map, Function.comp_def, toTrace]
  all_goals rfl
@[simp] theorem adaptiveData_eq : AronowAudit.P003.adaptiveData = toCounts adaptiveData := rfl
@[simp] theorem firstMismatch_eq (a b : List (Counts × Bool)) :
    AronowAudit.P003.firstMismatch (a.map toTrace) (b.map toTrace) = firstMismatch a b := by
  simp [AronowAudit.P003.firstMismatch, firstMismatch, List.zip_map, Function.comp_def, toTrace]
  all_goals rfl
@[simp] theorem shuffleCost_eq {n K : ℕ} (α ε : ℝ) (o : Counts)
    (pool : Fin (2*testBudget n+1) → Fin K → Assignment n (n/2)) :
    AronowAudit.P003.upperShuffleCost α ε (toCounts o) pool = upperShuffleCost α ε o pool := by
  simp [AronowAudit.P003.upperShuffleCost, upperShuffleCost, toEndpoint]
@[simp] theorem expectedShuffleCost_eq (α ε : ℝ) (n K : ℕ) (o : Counts) :
    AronowAudit.P003.expectedUpperShuffleCost α ε n K (toCounts o) = expectedUpperShuffleCost α ε n K o := by
  unfold AronowAudit.P003.expectedUpperShuffleCost expectedUpperShuffleCost
  congr 1
  apply Finset.sum_congr rfl
  intro pool hp
  exact congrArg (fun k : ℕ => (k : ℝ)) (shuffleCost_eq α ε o pool)

end
end SAP.P003b.Bridge
