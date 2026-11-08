import SAP.P026a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a
open Finset
open scoped BigOperators
noncomputable section


/-- A probability law on all binary allocations, with positive marginals in both arms. -/
structure UnitLaw (I : Type*) [Fintype I] [DecidableEq I] where
  weight : (I → Bool) → ℝ
  nonnegative : ∀ w, 0 ≤ weight w
  normalized : ∑ w, weight w = 1
  positive : ∀ i, 0 < ∑ w, weight w * (if w i=true then 1 else 0) ∧
    0 < ∑ w, weight w * (if w i=false then 1 else 0)

def UnitLaw.assignmentDesign {I : Type*} [Fintype I] [DecidableEq I]
    (E : UnitLaw I) : AssignmentDesign (I → Bool) I ℝ := ⟨E.weight, fun w => w⟩

/-- A fixed partition into nonempty clusters and a probability law on their allocations. -/
structure ClusterLaw (U C : Type*) [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] where
  cluster : U → C
  covers : Function.Surjective cluster
  assignment : UnitLaw C

def ClusterLaw.clusterAssignmentDesign {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterLaw U C) : AssignmentDesign (C → Bool) C ℝ :=
  E.assignment.assignmentDesign

def ClusterLaw.unitAssignmentDesign {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterLaw U C) : AssignmentDesign (C → Bool) U ℝ :=
  ⟨E.assignment.weight, fun w i => w (E.cluster i)⟩

def ClusterLaw.totals {U C : Type*} [Fintype U] [DecidableEq U]
    [Fintype C] [DecidableEq C] (E : ClusterLaw U C) (y : U → ℝ) (c : C) : ℝ :=
  ∑ i ∈ univ.filter (fun i => E.cluster i=c), y i


end
end SAP.P026a
