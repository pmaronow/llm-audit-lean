import AronowAudit.P001.Wave1.MixtureMaximumBlueprint
import AronowAudit.P001.Wave1.MixtureMaximum.N1

set_option autoImplicit false

namespace AronowAudit.P001.Wave1

open AronowAudit.P001
open scoped BigOperators

noncomputable section

theorem printed_unrestricted_mixture_maximum_refuted :
  ¬ ∀ {n : ℕ}, 0 < n → ∀ (y : Fin n → ℝ), (∀ i, 0 < y i) →
    ∃ θ : Fin 7 → ℝ, MixtureAdmissible θ ∧ ∀ θ', MixtureAdmissible θ' →
      mixtureLikelihood y θ' ≤ mixtureLikelihood y θ :=
  MixtureMaximum.assemble MixtureMaximum.n1_proof

end

end AronowAudit.P001.Wave1
