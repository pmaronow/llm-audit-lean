import SAP.P003b.Bridge.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.Bridge
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

@[simp] theorem logTwo_eq (x : ℝ) : AronowAudit.P003.logTwo x = logTwo x := rfl
@[simp] theorem recommendedK_eq (ε : ℝ) (n : ℕ) :
    AronowAudit.P003.recommendedK ε n = recommendedK ε n := rfl
@[simp] theorem searchStep_eq (f : ℤ → Bool) (a b : ℤ) :
    AronowAudit.P003.searchStep f a b = searchStep f a b := rfl
@[simp] theorem printedExecution_eq (fuel : ℕ) (k₁ k₂ : ℤ) (f : ℤ → Bool) (a b : ℤ) :
    AronowAudit.P003.printedExecution fuel k₁ k₂ f a b = printedExecution fuel k₁ k₂ f a b := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ t ih =>
    simp only [AronowAudit.P003.printedExecution, printedExecution, searchStep_eq]
    split_ifs <;> simp_all [ih]

@[simp] theorem approximateReject_nativePool {n m K : ℕ} (α ε : ℝ) (o : Counts)
    (pool : Fin (2*AronowAudit.P003.testBudget n+1) → Fin K → AronowAudit.P003.Assignment n m) :
    (fun v => AronowAudit.P003.approximateReject α ε (toCounts o) pool (toCounts v)) =
      approximateReject α ε o pool := approximateReject_fn α ε o pool
@[simp] theorem monteInterval_nativePool {n m K : ℕ} (corrected : Bool) (α ε : ℝ) (o : Counts)
    (pool : Fin (2*AronowAudit.P003.testBudget n+1) → Fin K → AronowAudit.P003.Assignment n m) :
    AronowAudit.P003.monteInterval corrected α ε (toCounts o) pool = monteInterval corrected α ε o pool :=
  monteInterval_eq corrected α ε o pool
@[simp] theorem shuffleCost_nativePool {n K : ℕ} (α ε : ℝ) (o : AronowAudit.P003.Counts)
    (pool : Fin (2*AronowAudit.P003.testBudget n+1) → Fin K → AronowAudit.P003.Assignment n (n/2)) :
    AronowAudit.P003.upperShuffleCost α ε o pool = upperShuffleCost α ε (fromCounts o) pool :=
  shuffleCost_any α ε o pool

end
end SAP.P003b.Bridge
