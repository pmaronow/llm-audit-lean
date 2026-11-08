import AronowAudit.P017.P017_Audit

/-!
# Blueprint: P017-T9, refutation of `proposition1_printed`

Wave 1, group P005-P006-P017-P023-P046-P047. Resolution `refute` (mapper §6, accepted by both
referees with no fixes).

The frozen record `AronowAudit.P017.proposition1_printed` (P017_Audit.lean, line 934) asserts
Proposition 1 as printed (PDF p. 2): every realised clipped target of a root-n normal estimator
is a nonnegative finite-ratio weighted mean of the effect. `Target` is the negation of its
universe-0 instance (checked by `rfl`).

Witness (mapper, existing definitions): `G = ipwPopulation` (`τ = U ~ Uniform(0,1)`, fair
`B = ±1`, fair `T`), `P = iidSamples G`, `hat = sampleMean ipwSummand` (the observed-data IPW
mean). Its effect mean is `1/2`, `(0,1) ⊆ supp τ` gives radius `≥ 1/2`, the IPW summand has
mean `1/2` and variance `53/12`, so Mathlib's iid CLT gives `RootNNormal`. On the
positive-probability bad event `B_i = -1, T_i = 0` the estimate is `2` (proved
`ipw_bad_event_estimator`) and clips to a value `≥ 1`, while `τ < 1` a.s. makes every value
`≥ 1` unrepresentable (proved `strictly_one_sided_not_representable`).

Simplification decided by the blueprint architect (no change of mathematics): only
`(0,1) ⊆ supp τ` and `radius ≥ 1/2` are needed, not the exact support `[0,1]` and radius `= 1/2`
of the mapper's node list (with radius `≥ 1/2`, possibly `⊤`, the clipped value of `2` is
`≥ 1`).

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P017/Wave1/PropositionOne/Nk.lean`.
`Sk` is the statement of node k; `Nk` is `Sk` with, as hypotheses, the statements it may use.
Do not use the admitted `uniform_ipw_counterexample` (its proof is `sorry`).
-/

set_option autoImplicit false

namespace AronowAudit.P017.Wave1.PropositionOne

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-! ## Frozen target -/

/-- **Target (P017-T9).** The exact negation of the frozen printed contract
`proposition1_printed` (Proposition 1 as printed, PDF p. 2), universe-0 instance. -/
def Target : Prop :=
  ¬ ∀ {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (G : Measure Ω) [IsProbabilityMeasure G] (τ : Ω → ℝ)
      (_hτm : Measurable τ) (_hτi : Integrable τ G) (P : Measure Ξ)
      [IsProbabilityMeasure P] (hat : ℕ → Ξ → ℝ)
      (_hh : RootNNormal P hat (populationMean G τ)),
      ∀ n, 1 ≤ n → ∀ ω, Representable G τ
        (clipTarget (populationMean G τ) (effectRadius G τ) (hat n ω))

/-- A sample in the bad event `ipwBadEvent (-1) n` for every `n` (all units `B = -1`, `T = 0`). -/
def badSample : ℕ → ℝ × (ℝ × ℝ) := fun _ => (1 / 2, (-1, 0))

/-! ## Node statements -/

/-- **Statement S1** (mapper §6 step 1, "The effect is the first coordinate, so it is measurable,
integrable, has mean μ=1/2"): `ipwEffect ω = ω.1` by `ring`; integrate the first coordinate of
the product law (`integral_fun_fst`/`Measure.map_fst_prod`) and use
`∫ x in Ioo 0 1, x = 1/2` (`integral_id` for `∫ x in 0..1, x`, `intervalIntegral.integral_of_le`,
`integral_Ioc_eq_integral_Ioo`). -/
def S1 : Prop :=
  Measurable ipwEffect ∧ Integrable ipwEffect ipwPopulation ∧
    populationMean ipwPopulation ipwEffect = 1 / 2

/-- **Statement S2** (mapper §6 step 1, "every neighborhood of a point in that interval
intersects (0,1) in a positive-length interval"): `(0,1)` lies in the closed support of the
effect law. Use `Measure.mem_support_iff_forall`, `ipwPopulation.map ipwEffect = uniform01`
(`Measure.map_fst_prod`), and `Real.volume_Ioo` on a small open interval inside `U ∩ (0,1)`. -/
def S2 : Prop := Ioo (0 : ℝ) 1 ⊆ effectSupport ipwPopulation ipwEffect

/-- **Statement S3** (mapper §6 step 1, "Thus supportInf=0, supportSup=1, and
effectRadius=min(1-1/2,1/2-0)=1/2>0"; only the lower bound is needed): from S2,
`supportSup ≥ 1` and `supportInf ≤ 0` (`le_sSup`/`sSup_le` in `EReal` over the image of `(0,1)`);
then `EReal` subtraction monotonicity and `EReal.toENNReal` monotonicity, using S1 (`μ = 1/2`). -/
def S3 : Prop := (1 / 2 : ℝ≥0∞) ≤ effectRadius ipwPopulation ipwEffect

/-- **Statement S4** (mapper §6 step 4, "Almost surely 0<τ<1"): the effect is a.s. below 1
(`ipwEffect ω = ω.1`, and `uniform01 = volume.restrict (Ioo 0 1)`; use `ae_restrict_mem`
transported through `Measure.prod`, e.g. `Measure.ae_prod_mem_iff_ae_ae_mem` or
`ae_map_iff` with `Measure.map_fst_prod`). -/
def S4 : Prop := ∀ᵐ ω ∂ipwPopulation, ipwEffect ω < 1

/-- **Statement S5** (mapper §6 step 2, "E Z=1/2, E Z²=14/3, Var Z=53/12>0. Also |Z|<4 almost
surely, so Z∈L²"): the IPW summand's measurability, square integrability, mean and variance.
Use `MemLp.of_bound` (a.s. bound `4`), `integral_prod` / `integral_fun_fst/snd` with the
`fairPair` integrals (`integral_add_measure`, `integral_smul_measure`, `integral_dirac`), and
`variance_eq_sub`. -/
def S5 : Prop :=
  Measurable ipwSummand ∧ MemLp ipwSummand 2 ipwPopulation ∧
    (∫ ω, ipwSummand ω ∂ipwPopulation) = 1 / 2 ∧ variance ipwSummand ipwPopulation = 53 / 12

/-- **Statement S6** (mapper §6 step 2, "Apply the ordinary iid L² central limit theorem, in
exactly Mathlib's tendstoInDistribution_inv_sqrt_mul_sum_sub form"): the actual `RootNNormal`
premise for the witness. Follow the proved template `AronowAudit.P047.estimator_central_limit`
(`tendstoInDistribution_inv_sqrt_mul_sum_sub`, `iIndepFun_infinitePi`,
`measurePreserving_eval_infinitePi`, `IdentDistrib.memLp_iff`, `TendstoInDistribution.congr`),
with `v = (53/12).toNNReal > 0` from S5 and the mean `1/2` from S1, S5. -/
def S6 : Prop :=
  RootNNormal (iidSamples ipwPopulation) (sampleMean ipwSummand)
    (populationMean ipwPopulation ipwEffect)

/-- **Statement S7** (mapper §6 step 3, "On A_n every observed pair is (0,-1); every Z_i=2 and
hat_n=2 ... The clipping rule at μ=1/2,c=1/2 returns min(1,max(0,2))=1"): on the bad event the
clipped target is at least `1`. Use `ipw_bad_event_estimator` (`= -2·(-1) = 2`), S1, S3 and the
two branches of `clipTarget` (`c = ⊤` gives `2`; otherwise `c.toReal ≥ 1/2`). -/
def S7 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ s ∈ ipwBadEvent (-1) n,
    1 ≤ clipTarget (populationMean ipwPopulation ipwEffect) (effectRadius ipwPopulation ipwEffect)
      (sampleMean ipwSummand n s)

/-! ## Nodes (`Nk` = statements it may use → `Sk`) -/

/-- Node N1 = S1. -/
def N1 : Prop := S1
/-- Node N2 = S2. -/
def N2 : Prop := S2
/-- Node N3: may use S1, S2. -/
def N3 : Prop := S1 → S2 → S3
/-- Node N4 = S4. -/
def N4 : Prop := S4
/-- Node N5 = S5. -/
def N5 : Prop := S5
/-- Node N6: may use S1, S5. -/
def N6 : Prop := S1 → S5 → S6
/-- Node N7: may use S1, S3. -/
def N7 : Prop := S1 → S3 → S7

/-! ## Assembly -/

/-- **Assembly.** The nodes suffice for the refutation. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7) :
    Target := by
  have s3 : S3 := h3 h1 h2
  have s6 : S6 := h6 h1 h5
  have s7 : S7 := h7 h1 s3
  intro hall
  have hmem : badSample ∈ ipwBadEvent (-1) 1 := fun _ _ => ⟨rfl, rfl⟩
  have hrep := hall ipwPopulation ipwEffect h1.1 h1.2.1 (iidSamples ipwPopulation)
    (sampleMean ipwSummand) s6 1 le_rfl badSample
  exact strictly_one_sided_not_representable ipwPopulation ipwEffect _
    (Or.inl (h4.mono fun ω hω => lt_of_lt_of_le hω (s7 1 le_rfl badSample hmem))) hrep

/-- Fidelity check: `Target` is literally the negation of the universe-0 instance of the frozen
statement `AronowAudit.P017.proposition1_printed` (only its type is read). -/
example : Target = ¬ (type_of% @AronowAudit.P017.proposition1_printed.{0, 0}) := rfl

end

end AronowAudit.P017.Wave1.PropositionOne
