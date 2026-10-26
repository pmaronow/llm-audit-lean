import AronowAudit.P001.P001_Foundations

/-!
# Attained MLE inconsistency with an unused mixture component (P001-T11)

The compact parameter box is `Θ = [0,1]×[0,1]×[1/4,3/4]`.
Both `θ_A = (1,1/3,1/4)` and `θ_B = (1,1/3,3/4)` are admissible and give the common
PMF `(2/3,1/3,0,0)`, hence equal normalized sample laws. No estimator is consistent
at both truths. Likelihood maxima are attained on the box for every sample.

`Target` combines these properties with a sequence `T` of attained likelihood
maximizers that fails `FiniteMixtureConsistent`, defined under the actual
parameter-indexed product laws `finiteMixtureSampleProb`, at `θ_A` or `θ_B`.

This refutes only the bare full-vector reading of p. 199. The witness does not
satisfy an additional identification or unique-population-maximum premise
(Theorem 5.2.6).
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.UnusedMixtureMle

open AronowAudit.P001
open scoped BigOperators

noncomputable section


def Target : Prop :=
  UnusedMixtureWitness ∧
  ∃ T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ,
    (∀ n (y : Fin n → Fin 4),
      T n y ∈ disjointMixtureParameterSet ∧
      ∀ u ∈ disjointMixtureParameterSet,
        disjointMixtureLikelihood y u ≤ disjointMixtureLikelihood y (T n y)) ∧
    (¬ FiniteMixtureConsistent T (![1, 1/3, 1/4] : Fin 3 → ℝ) ∨
     ¬ FiniteMixtureConsistent T (![1, 1/3, 3/4] : Fin 3 → ℝ))

/-- A sequence of attained likelihood maximizers on the compact parameter box. -/
def N1 : Prop :=
  ∃ T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ,
    ∀ n (y : Fin n → Fin 4),
      T n y ∈ disjointMixtureParameterSet ∧
      ∀ u ∈ disjointMixtureParameterSet,
        disjointMixtureLikelihood y u ≤ disjointMixtureLikelihood y (T n y)

/-- The selected likelihood maximizers fail consistency at at least one of the
two observationally equivalent parameter values. -/
theorem assemble (h1 : N1) : Target := by
  obtain ⟨T, hT⟩ := h1
  exact ⟨unused_component_nonidentification, T, hT,
    not_and_or.mp (finite_mixture_statistical_impossibility T)⟩

end

end AronowAudit.P001.Wave1.UnusedMixtureMle
