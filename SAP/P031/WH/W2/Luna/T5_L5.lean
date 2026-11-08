import SAP.P031.WH.W2.Leaves
import SAP.P031.WH.W3.Proofs.LeafChecks

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter Finset
open SAP.P031 SAP.P031.WH.W2 SAP.P031.WH.W3

noncomputable section
namespace SAP.P031.WH.W2.Luna

theorem boundedFourthMomentsAdapterW2W3 (P : ℕ → Population)
    (h : BoundedFourthMomentsW2 P) : UniformFourthMomentsW3 P := by
  rcases h with ⟨B, hB, hFourth⟩
  refine ⟨B, hB, ?_⟩
  intro n
  constructor
  · simpa [SAP.P031.fourthMomentW3, groupMean] using (hFourth n).1
  · simpa [SAP.P031.fourthMomentW3, groupMean] using (hFourth n).2

theorem T5_L5_solution : T5_L5 := by
  intro P p μ1 μ0 v1 v0 c hReg
  exact armConsistencyW3 GateAudit.first_leaf GateAudit.second_leaf
    P p hReg.growingW2 hReg.pPositiveW2 hReg.pLessOneW2 hReg.allocationW2
    (boundedFourthMomentsAdapterW2W3 P hReg.fourthW2)

example : T5_L5 := T5_L5_solution

#print axioms T5_L5_solution

end SAP.P031.WH.W2.Luna
end
