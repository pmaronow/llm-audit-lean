import AronowAudit.P011.Wave1.PropositionOneBlueprint

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

theorem n4_proof : N4 := by
  classical
  change Nested PF
  constructor
  · intro k l hkl
    change 3 * (k + 1) ≤ 3 * (l + 1)
    omega
  · intro k
    have hk : PF.size k ≤ PF.size (k + 1) := by
      change 3 * (k + 1) ≤ 3 * (k + 1 + 1)
      omega
    refine ⟨⟨Fin.castLE hk, ?_⟩, ?_⟩
    · intro i j hij
      apply Fin.ext
      exact congrArg (fun x : Fin (PF.size (k + 1)) => x.val) hij
    · intro i j
      rfl

end

end AronowAudit.P011.Wave1.PropositionOne
