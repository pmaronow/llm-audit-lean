import AronowAudit.P017.P017_Audit

/-!
P017-T9: supporting properties of the uniform-effect IPW counterexample.

Proposition 1 as printed (PDF p. 2) asserts that every realised clipped target
of a root-n normal estimator is a nonnegative finite-ratio weighted mean of the effect.

The witness has `G = ipwPopulation` (`τ = U ~ Uniform(0,1)`, fair
`B = ±1`, fair `T`), `P = iidSamples G`, and `hat = sampleMean ipwSummand`
(the observed-data IPW mean). Its effect mean is `1/2`, `(0,1) ⊆ supp τ`
gives radius `≥ 1/2`, and the IPW summand has mean `1/2` and variance `53/12`,
so Mathlib's iid CLT gives `RootNNormal`. On the positive-probability event
`B_i = -1, T_i = 0`, the estimate is `2` (`ipw_bad_event_estimator`) and clips
to a value `≥ 1`, while `τ < 1` a.s. makes every value `≥ 1` unrepresentable
(`strictly_one_sided_not_representable`).

Only `(0,1) ⊆ supp τ` and `radius ≥ 1/2` are needed for this argument:
with radius `≥ 1/2`, possibly `⊤`, the clipped value of `2` is `≥ 1`.
The exact support `[0,1]` and radius `1/2` are not required.
-/

set_option autoImplicit false

namespace AronowAudit.P017.Wave1.PropositionOne

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section




/-! ## Effect and IPW summand properties -/

/-- The effect is the first coordinate, so it is measurable, integrable, and has
mean μ=1/2: `ipwEffect ω = ω.1` by `ring`; integrate the first coordinate of
the product law (`integral_fun_fst`/`Measure.map_fst_prod`) and use
`∫ x in Ioo 0 1, x = 1/2` (`integral_id` for `∫ x in 0..1, x`, `intervalIntegral.integral_of_le`,
`integral_Ioc_eq_integral_Ioo`). -/
def S1 : Prop :=
  Measurable ipwEffect ∧ Integrable ipwEffect ipwPopulation ∧
    populationMean ipwPopulation ipwEffect = 1 / 2

/-- Every neighborhood of a point in (0,1) intersects it in a positive-length
interval: `(0,1)` lies in the closed support of the effect law.
Use `Measure.mem_support_iff_forall`, `ipwPopulation.map ipwEffect = uniform01`
(`Measure.map_fst_prod`), and `Real.volume_Ioo` on a small open interval inside `U ∩ (0,1)`. -/
def S2 : Prop := Ioo (0 : ℝ) 1 ⊆ effectSupport ipwPopulation ipwEffect


/-- The IPW summand is measurable and square integrable: E Z=1/2, E Z²=14/3,
and Var Z=53/12>0. Also |Z|<4 almost surely, so Z∈L².
Use `MemLp.of_bound` (a.s. bound `4`), `integral_prod` / `integral_fun_fst/snd` with the
`fairPair` integrals (`integral_add_measure`, `integral_smul_measure`, `integral_dirac`), and
`variance_eq_sub`. -/
def S5 : Prop :=
  Measurable ipwSummand ∧ MemLp ipwSummand 2 ipwPopulation ∧
    (∫ ω, ipwSummand ω ∂ipwPopulation) = 1 / 2 ∧ variance ipwSummand ipwPopulation = 53 / 12


/-! ## Equivalent statements -/

/-- N1 is S1. -/
def N1 : Prop := S1
/-- N2 is S2. -/
def N2 : Prop := S2
/-- N5 is S5. -/
def N5 : Prop := S5




end

end AronowAudit.P017.Wave1.PropositionOne
