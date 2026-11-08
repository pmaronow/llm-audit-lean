import SAP.P003a.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace SAP.P003a.Bridge
open SAP.P003a

@[simp] theorem sentinelSearch_eq (fuel : ℕ) (f : ℤ → Bool) (a b : ℤ) :
    AronowAudit.P003.sentinelSearch fuel f a b = sentinelSearch fuel f a b := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ fuel ih =>
    simp only [AronowAudit.P003.sentinelSearch, sentinelSearch, ih]

@[simp] theorem printedSearch_eq (fuel : ℕ) (k₁ k₂ : ℤ) (f : ℤ → Bool) (a b : ℤ) :
    AronowAudit.P003.printedSearch fuel k₁ k₂ f a b = printedSearch fuel k₁ k₂ f a b := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ fuel ih =>
    simp only [AronowAudit.P003.printedSearch, printedSearch, ih]
    rfl

/-- Four-field conversion preserves every Boolean branch of the candidate scan. -/
@[simp] theorem to_candidates (o : Counts) (x : ℤ) :
    AronowAudit.P003.candidates (toAudit o) x = (candidates o x).map toAudit := by
  simp only [AronowAudit.P003.candidates, candidates, to_total, List.map_flatMap]
  congr 1
  funext j
  rw [to_firstOnLine]
  cases h : firstOnLine o x j with
  | none => rfl
  | some v =>
    simp only [Option.map_some, to_a, to_b, to_c, to_d]
    change (if v.b = 0 ∧ v.c = 0 ∧ 1 ≤ v.a ∧ 1 ≤ v.d ∧
      AronowAudit.P003.Possible (toAudit o) (toAudit ⟨v.a-1,1,1,v.d-1⟩)
      then [toAudit v,toAudit ⟨v.a-1,1,1,v.d-1⟩] else [toAudit v]) = _
    simp only [to_possible]
    split <;> simp_all

def mapQuery (r : QueryResult) : AronowAudit.P003.QueryResult :=
  ⟨r.compatible,r.idx,r.trace.map fun x => (toAudit x.1,x.2)⟩

def mapEndpoint (r : EndpointResult) : AronowAudit.P003.EndpointResult :=
  ⟨r.value,r.trace.map fun x => (toAudit x.1,x.2)⟩

@[simp] theorem to_runTests (reject : Counts → ℕ → Bool) (idx : ℕ) (xs : List Counts) :
    AronowAudit.P003.runTests (fun v i => reject (fromAudit v) i) idx (xs.map toAudit) =
      mapQuery (runTests reject idx xs) := by
  induction xs generalizing idx with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, AronowAudit.P003.runTests, runTests, from_to]
    split <;> simp_all [mapQuery]

theorem value_ite (p : Prop) [Decidable p] (x y : EndpointResult) :
    (if p then x else y).value = if p then x.value else y.value := by
  split <;> rfl

theorem audit_value_ite (p : Prop) [Decidable p] (x y : AronowAudit.P003.EndpointResult) :
    (if p then x else y).value = if p then x.value else y.value := by
  split <;> rfl

@[simp] theorem to_adaptiveSearch (fuel : ℕ) (corrected : Bool) (o : Counts)
    (k₁ k₂ : ℤ) (reject : Counts → ℕ → Bool) (a b : ℤ) (idx : ℕ) :
    (AronowAudit.P003.adaptiveSearch fuel corrected (toAudit o) k₁ k₂
      (fun v i => reject (fromAudit v) i) a b idx).value =
      (adaptiveSearch fuel corrected o k₁ k₂ reject a b idx).value := by
  induction fuel generalizing a b idx with
  | zero =>
    rw [AronowAudit.P003.adaptiveSearch, adaptiveSearch]
    split <;> rfl
  | succ fuel ih =>
    rw [AronowAudit.P003.adaptiveSearch, adaptiveSearch]
    simp only [to_candidates, to_runTests, mapQuery, value_ite, audit_value_ite, ih]

@[simp] theorem to_upperRun (corrected : Bool) (o : Counts)
    (reject : Counts → ℕ → Bool) (idx : ℕ) :
    (AronowAudit.P003.upperRun corrected (toAudit o)
      (fun v i => reject (fromAudit v) i) idx).value = (upperRun corrected o reject idx).value := by
  simp only [AronowAudit.P003.upperRun, upperRun, to_total, to_a, to_b, to_c, to_adaptiveSearch]

end SAP.P003a.Bridge
