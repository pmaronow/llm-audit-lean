import AronowAudit.P001.P001_Foundations

/-!
# Variance and standard-error consistency (P001-T55)

Definition 3.2.32 (Consistency of Sampling Variance and Standard Error Estimators),
pp. 113–114 (PDF pp. 131–132), footnote 23, p. 114, and the following
continuous-mapping sentence, with the estimator's hat restored in four places.

The estimator `θhat` has a root-`n` limit law `ν`, any probability law with finite
second moment; normality is not assumed. This identifies the target variance
`V[T] = var ν id`. The sampling-variance estimate `Vhat` is measurable and nonnegative.
The conclusions are both centered forms of footnote 23 and the equivalence of
variance and standard-error consistency. The single intermediate statement `N1`
is `Target`.
-/

namespace AronowAudit.P001.Wave1.VarianceSEContract

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

/-- The premises on
`θhat` and `ν` fix the meaning of the target `var ν id`; they are not used in the proof. -/
def Target : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (θhat Vhat : ℕ → Ω → ℝ) (θ : ℝ),
    (∀ n, Measurable (θhat n)) → (∀ n, Measurable (Vhat n)) →
    (∀ n ω, 0 ≤ Vhat n ω) →
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], MemLp id 2 ν →
    CD μ (fun n ω => Real.sqrt n * (θhat n ω - θ)) ν →
    (VarianceConsistent μ Vhat (var ν id) ↔
      CP μ (fun n ω => (n : ℝ) * Vhat n ω - var ν id) 0) ∧
    (SEConsistent μ Vhat (var ν id) ↔
      CP μ (fun n ω => Real.sqrt n * Real.sqrt (Vhat n ω) -
        Real.sqrt (var ν id)) 0) ∧
    (VarianceConsistent μ Vhat (var ν id) ↔ SEConsistent μ Vhat (var ν id))

/-- N1 = Target (proof outline: centering at a constant leaves
every bad event unchanged; `√(n·Vhat) = √n·√Vhat` by nonnegativity, and continuity of `√·` at
`v` and of `t ↦ t²` at `√v` give the two directions). -/
def N1 : Prop := Target.{u}

/- Satisfiable instance of the hypotheses: `Ω = {-1, 1}` with equal masses
(or `μ = gaussianReal 0 1` on `ℝ`), `θ = 0`, `θhat n ω = ω/√n` and `Vhat n ω = 1/n` for
`n ≥ 1` (both `0` at `n = 0`), `ν` the law of the root-`n` statistic (equal masses on
`{-1, 1}`, resp. `gaussianReal 0 1`), which has finite second moment and variance `1`. -/

end
end AronowAudit.P001.Wave1.VarianceSEContract
