import AronowAudit.P001.P001_Foundations

/-!
# Blueprint: expected value under MCAR with exact binary support (P001-T111, bridge)

Record 12 of group P001a: P001-T111 / held `AronowAudit.P001.mcar_expected_value`;
resolution `bridge`. Theorem 6.1.6 and Definition 6.1.5 (p. 213). The held theorem (:4279)
is proved but its pointwise-binary domain admits `R ≡ 1`, contrary to `Supp[R] = {0,1}`.
The bridge (mapper's `mcar_paper_support_mean`) states the paper domain (a.e. binary `R`,
both `P(R=0) > 0` and `P(R=1) > 0`) and writes the right side as the respondent
conditional mean `conditionalMeanAt μ R Y* 1 = ∫_{R=1} Y* / P(R=1)`.

One node, `N1 = Target`. Writers prove `theorem n1_proof : N1` in
`AronowAudit/P001/Wave1/McarMean/N1.lean`.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.McarMean

open AronowAudit.P001 MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The frozen statement the record is resolved by (mapper's
`AronowAudit.P001.Wave1.mcar_paper_support_mean`). -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y R : Ω → ℝ), Measurable Y → Measurable R → Integrable Y μ →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    0 < prob μ {ω | R ω = 0} → 0 < prob μ {ω | R ω = 1} → IndepFun Y R μ →
    mean μ Y = conditionalMeanAt μ R (fun ω => censored (Y ω) (R ω)) 1

/-- **Node N1** (paper proof, record 12: "Let A={R=1} ... ∫_A Y=P(A)E[Y] ... At every point
of A, censored(Y,R)=Y·1-99·0=Y, so ∫_A Y*=∫_A Y. Dividing by the strictly positive P(A)
gives E[Y]=∫_A Y*/P(A)=conditionalMeanAt μ R Y* 1"). Equal to `Target`.
Suggested route: copy the (axiom-clean) body of `mcar_expected_value` (:4279-4294), which
never uses its pointwise `hbinary`: `independent_constant_cef μ R Y hR hY hYi hind.symm`
tested at `{1}`, `integral_congr_ae` with `ae_restrict_mem` for `censored y 1 = y`, then
`mul_div_cancel_left₀` with `hR1.ne'`; unfold `conditionalMeanAt` (:690). -/
def N1 : Prop := Target.{u}

/-- One-step record: the single node is the target. -/
theorem assemble (h1 : N1.{u}) : Target.{u} := h1

end

end AronowAudit.P001.Wave1.McarMean
