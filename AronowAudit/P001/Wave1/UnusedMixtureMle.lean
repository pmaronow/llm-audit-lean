import AronowAudit.P001.Wave1.UnusedMixtureMleBlueprint
import AronowAudit.P001.Wave1.UnusedMixtureMle.N1

set_option autoImplicit false

namespace AronowAudit.P001.Wave1

open AronowAudit.P001
open scoped BigOperators

noncomputable section

theorem unused_mixture_attained_mle_inconsistent :
  UnusedMixtureWitness ∧
  ∃ T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ,
    (∀ n (y : Fin n → Fin 4),
      T n y ∈ disjointMixtureParameterSet ∧
      ∀ u ∈ disjointMixtureParameterSet,
        disjointMixtureLikelihood y u ≤ disjointMixtureLikelihood y (T n y)) ∧
    (¬ FiniteMixtureConsistent T (![1, 1/3, 1/4] : Fin 3 → ℝ) ∨
     ¬ FiniteMixtureConsistent T (![1, 1/3, 3/4] : Fin 3 → ℝ)) :=
  UnusedMixtureMle.assemble UnusedMixtureMle.n1_proof

end

end AronowAudit.P001.Wave1
