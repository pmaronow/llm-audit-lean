import SAP.P023.Defs.WholeW2
import SAP.P023.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P023.WH.W2

open scoped BigOperators

/-- Assemble the whole printed Proposition 1 without new leaves.
`close_counts_positive` derives both denominator guards from Condition 1.
`Bridge.propositionOne` supplies the exact printed-design identity for every
normal-equation solution, allowing empty nuisance bins and either tie code.
Its existing proof uses the bin geometry and the bin normal equations.
The target-specific orchestrator ruling identifies the target as this equality
under Conditions 1–3; the separate auxiliary necessity remark is not a premise
or conclusion of this assembly. -/
theorem T11_assembly : T11WholeStatement_W2 := by
  intro ι _ k hk x d y hdata h1
  have hn : (0 < ∑ i ∈ close k x, d i) ∧
      (0 < ∑ i ∈ close k x, (1 - d i)) :=
    AronowAudit.P023.close_counts_positive k x d hdata h1
  refine ⟨hn.1, hn.2, ?_⟩
  intro c hc
  exact Bridge.propositionOne k hk x d y hdata h1 c hc

end SAP.P023.WH.W2
