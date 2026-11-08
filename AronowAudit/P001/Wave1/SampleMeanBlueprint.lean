import AronowAudit.P001.P001_Foundations

/-!
# Blueprint: paper contract for the sample mean (P001-T108, bridge)

Record 5 of group P001a: P001-T108 / held `AronowAudit.P001.sample_mean_memLp`; resolution
`bridge`. The held declaration (P001_Foundations.lean:1020) proves only L² closure of the
sample mean; it states none of Theorems 3.2.3-3.2.5 (pp. 97-99). The bridge states the
three printed conclusions at every `n ≥ 1`, each under its own printed moment hypothesis:
unbiasedness under L¹ (finite expectation, footnote 2 p. 45); `V[X̄] = V[X]/n` under L²;
Chebyshev under L² and `V[X] > 0`.

`Target` is the final statement (mapper's `sample_mean_paper_contract`), universe
polymorphic in `Ω`. One node, `N1 = Target`; it is a direct combination of three proved
source theorems (`iid_sample_mean_expectation_integrable` :7356,
`iid_sample_mean_finite_moments` :3036, `iid_sample_mean_chebyshev` :4114; all axiom-clean)
and is proved by the blueprint author in `AronowAudit/P001/Wave1/SampleMean/N1.lean`.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.SampleMean

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The frozen statement the record is resolved by (mapper's
`AronowAudit.P001.Wave1.sample_mean_paper_contract`). -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), IID μ X → Integrable (X 0) μ → ∀ (n : ℕ), 0 < n →
    mean μ (sampleMean X n) = mean μ (X 0) ∧
    (MemLp (X 0) 2 μ →
      var μ (sampleMean X n) = var μ (X 0) / (n : ℝ) ∧
      (0 < var μ (X 0) → ∀ ε : ℝ, 0 < ε →
        prob μ {ω | ε ≤ |sampleMean X n ω - mean μ (X 0)|} ≤
          var μ (X 0) / (ε ^ 2 * (n : ℝ))))

/-- **Node N1** (paper proof, record 5: "These arguments are precisely the three existing
theorem applications listed in reuse; none depends on a drafted result"). Equal to
`Target`; proved (one term) in `SampleMean/N1.lean`. -/
def N1 : Prop := Target.{u}

/-- One-step record: the single node is the target. -/
theorem assemble (h1 : N1.{u}) : Target.{u} := h1

end

end AronowAudit.P001.Wave1.SampleMean
