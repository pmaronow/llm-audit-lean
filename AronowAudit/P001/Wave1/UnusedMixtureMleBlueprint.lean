import AronowAudit.P001.P001_Foundations

/-!
# Blueprint: attained MLE inconsistency in the actual unused-component experiment (P001-T11)

Records 7, 8 and 9 of group P001a, all P001-T11 (resolution `bridge`), held declarations
`nonidentification_no_two_consistent_targets_supporting` (:6207),
`unused_component_counterexample_full_supporting` (:6861) and
`unused_component_nonidentification_supporting` (:1365). The first two quantify over an
arbitrary measure `μ` unrelated to either sampling experiment; the third stops at PMF
algebra. All three map to **one** shared new declaration (mapper's
`unused_mixture_attained_mle_inconsistent`), to be emitted and credited once.

`Target`: the proved `UnusedMixtureWitness` (compact box, both truths admissible, common PMF
`(2/3,1/3,0,0)`, attained maxima, equal normalized sample laws, impossibility of consistency
at both truths for every estimator) **and** an actual sequence `T` of attained likelihood
maximizers on `Θ = [0,1]×[0,1]×[1/4,3/4]` that fails `FiniteMixtureConsistent` (defined on
the actual parameter-indexed product sample laws `finiteMixtureSampleProb`) at
`θ_A = (1,1/3,1/4)` or at `θ_B = (1,1/3,3/4)`.

This refutes only the bare full-vector reading of p. 199; the witness does not satisfy an
added identification / unique-population-maximum premise (Theorem 5.2.6).

Node `N1` (choice of maximizers from the proved `finite_mixture_compact_attainment`) is one
term and is proved by the blueprint author in `UnusedMixtureMle/N1.lean`. The assembly uses
the proved `unused_component_nonidentification` and
`finite_mixture_statistical_impossibility` (both axiom-clean). Do not use the :6207 / :6861
arbitrary-`μ` statements as the sampling-law bridge.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.UnusedMixtureMle

open AronowAudit.P001
open scoped BigOperators

noncomputable section

/-- The frozen statement the three records are resolved by (mapper's
`AronowAudit.P001.Wave1.unused_mixture_attained_mle_inconsistent`). -/
def Target : Prop :=
  UnusedMixtureWitness ∧
  ∃ T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ,
    (∀ n (y : Fin n → Fin 4),
      T n y ∈ disjointMixtureParameterSet ∧
      ∀ u ∈ disjointMixtureParameterSet,
        disjointMixtureLikelihood y u ≤ disjointMixtureLikelihood y (T n y)) ∧
    (¬ FiniteMixtureConsistent T (![1, 1/3, 1/4] : Fin 3 → ℝ) ∨
     ¬ FiniteMixtureConsistent T (![1, 1/3, 3/4] : Fin 3 → ℝ))

/-- **Node N1** (paper proof, records 7-9, first paragraph: "Θ is nonempty and compact, so
for every n and every sample y an attained maximum exists. This includes n=0 ... Select one
maximizer T_n(y) for each pair (n,y)"). A sequence of attained likelihood maximizers on the
compact box. Proved by `Classical.choose` from `finite_mixture_compact_attainment` in
`UnusedMixtureMle/N1.lean`. -/
def N1 : Prop :=
  ∃ T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ,
    ∀ n (y : Fin n → Fin 4),
      T n y ∈ disjointMixtureParameterSet ∧
      ∀ u ∈ disjointMixtureParameterSet,
        disjointMixtureLikelihood y u ≤ disjointMixtureLikelihood y (T n y)

/-- The nodes suffice: the proved impossibility theorem applies to the selected MLE, and
classical De Morgan turns `¬ (A ∧ B)` into `¬ A ∨ ¬ B`. -/
theorem assemble (h1 : N1) : Target := by
  obtain ⟨T, hT⟩ := h1
  exact ⟨unused_component_nonidentification, T, hT,
    not_and_or.mp (finite_mixture_statistical_impossibility T)⟩

end

end AronowAudit.P001.Wave1.UnusedMixtureMle
