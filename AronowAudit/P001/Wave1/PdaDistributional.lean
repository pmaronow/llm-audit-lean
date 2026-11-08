import AronowAudit.P001.Wave1.PdaDistributionalBlueprint
import AronowAudit.P001.Wave1.GapLaw.N1
import AronowAudit.P001.Wave1.GapLaw.N2
import AronowAudit.P001.Wave1.GapLaw.N4

set_option autoImplicit false

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 AronowAudit.P001.Wave1.GapLaw MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

theorem printed_pda_distributional_contract_refuted :
    ¬ ∀ {K : ℕ} (ν : Measure (Fin K → ℝ)) [IsProbabilityMeasure ν],
      (∀ k, Integrable (fun x => x k) ν) →
      ∀ (m m' : (Fin K → ℝ) → ℝ), ContDiff ℝ 1 m → ContDiff ℝ 1 m' → m =ᵐ[ν] m' →
      ∀ (k : Fin K),
        partialAt m (fun j => ∫ x, x j ∂ν) k = partialAt m' (fun j => ∫ x, x j ∂ν) k :=
  AronowAudit.P001.Wave1.PdaDistributional.assemble n1_proof n2_proof n4_proof

example : AronowAudit.P001.Wave1.PdaDistributional.Target :=
  printed_pda_distributional_contract_refuted

end

end AronowAudit.P001.Wave1
