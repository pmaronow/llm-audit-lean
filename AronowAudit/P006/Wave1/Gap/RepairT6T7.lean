import AronowAudit.P006.P006_CounterfactualMetrics
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
P006-T6 with integrability of the treated estimator residual only.

For T7, finiteness of the weighted total does not justify integrating the
weighted conditional moments term by term.
-/

namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance instDecidableRepairT6T7 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The outcome and randomization assumptions at one fixed policy. This is the
part of `Standing` used below, with no assumption on the estimator. The alignment theorem
requires it only on the feasible class. Independence across units and fixed
potential-outcome laws across policies are unnecessary for these conclusions. -/
structure RepairT6T7_Design {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n) (π : C → ℝ) : Prop where
  px_probability : IsProbabilityMeasure E.PX
  means_measurable : Measurable E.μ0 ∧ Measurable E.μ1
  means_integrable : Integrable E.μ0 E.PX ∧ Integrable E.μ1 E.PX
  law_probability : IsProbabilityMeasure (E.law π)
  measurable_units : ∀ i,
    Measurable (E.X i) ∧ Measurable (E.Y0 i) ∧ Measurable (E.Y1 i) ∧
    Measurable (E.T π i)
  integrable_units : ∀ i,
    Integrable (E.Y0 i) (E.law π) ∧ Integrable (E.Y1 i) (E.law π)
  covariate_law : ∀ i,
    IdentDistrib (E.X i) (fun x : C => x) (E.law π) E.PX
  conditional_means : ∀ i,
    (E.law π)[E.Y0 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ0 (E.X i ω)) ∧
    (E.law π)[E.Y1 i | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => E.μ1 (E.X i ω))
  bernoulli : ∀ i,
    (E.law π)[(fun ω => bit (E.T π i ω)) | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => π (E.X i ω))
  ignorability : ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
    (E.law π)[(fun ω => bit (E.T π i ω) *
      B.indicator (fun _ => (1 : ℝ)) (E.Y0 i ω, E.Y1 i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) *
        (E.law π)[(fun η => B.indicator (fun _ => (1 : ℝ))
          (E.Y0 i η, E.Y1 i η)) | E.covariateSigma i] ω)


section ConditionalMoment

variable {Ω Z : Type*} {G : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace Z] {μ : Measure Ω}

lemma RepairT6T7_mul_integrable {b f : Ω → ℝ} (hb : Measurable b)
    (hbnd : ∀ ω, ‖b ω‖ ≤ 1) (hf : Integrable f μ) :
    Integrable (fun ω => b ω * f ω) μ :=
  hf.bdd_mul hb.aestronglyMeasurable (Eventually.of_forall hbnd)

lemma RepairT6T7_simple_moment [IsFiniteMeasure μ] {b p : Ω → ℝ} {z : Ω → Z}
    (hb : Measurable b) (hp : Measurable p)
    (hbnd : ∀ ω, ‖b ω‖ ≤ 1) (hpnd : ∀ ω, ‖p ω‖ ≤ 1)
    (hz : Measurable z)
    (hI : ∀ A : Set Z, MeasurableSet A →
      μ[(fun ω => b ω * A.indicator (fun _ => (1 : ℝ)) (z ω)) | G] =ᵐ[μ]
      μ[(fun ω => p ω * A.indicator (fun _ => (1 : ℝ)) (z ω)) | G])
    (s : SimpleFunc Z ℝ) :
    μ[(fun ω => b ω * s (z ω)) | G] =ᵐ[μ]
      μ[(fun ω => p ω * s (z ω)) | G] := by
  induction s using SimpleFunc.induction with
  | @const c A hA =>
    simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
    have hind (a : Ω → ℝ) :
        (fun ω => a ω * A.piecewise (Function.const Z c) (Function.const Z 0) (z ω)) =
          c • (fun ω => a ω * A.indicator (fun _ => (1 : ℝ)) (z ω)) := by
      ext ω
      by_cases hω : z ω ∈ A <;> simp [hω, mul_comm]
    rw [hind b, hind p]
    have hscaled :
        c • μ[(fun ω => b ω * A.indicator (fun _ => (1 : ℝ)) (z ω)) | G] =ᵐ[μ]
          c • μ[(fun ω => p ω * A.indicator (fun _ => (1 : ℝ)) (z ω)) | G] := by
      filter_upwards [hI A hA] with ω hω using congrArg (c * ·) hω
    exact (condExp_smul c _ G).trans
      (hscaled.trans (condExp_smul c _ G).symm)
  | @add s t _ hs ht =>
    have hi (a : Ω → ℝ) (ha : Measurable a) (ha' : ∀ ω, ‖a ω‖ ≤ 1)
        (v : SimpleFunc Z ℝ) : Integrable (fun ω => a ω * v (z ω)) μ :=
      RepairT6T7_mul_integrable ha ha' ((v.comp z hz).integrable_of_isFiniteMeasure)
    simp only [SimpleFunc.coe_add, Pi.add_apply, mul_add]
    exact (condExp_add (hi b hb hbnd s) (hi b hb hbnd t) G).trans
      ((hs.add ht).trans (condExp_add (hi p hp hpnd s) (hi p hp hpnd t) G).symm)

/-- The indicator conditional moment extends to every integrable measurable mark.
The two multiplied simple approximations share the integrable bound `2 * ‖f ∘ z‖`. -/
lemma RepairT6T7_binary_conditional_moment_extension [IsFiniteMeasure μ]
    {b p : Ω → ℝ} {z : Ω → Z} (hG : G ≤ mΩ)
    (hb : Measurable b) (hp : Measurable[G] p)
    (hbnd : ∀ ω, ‖b ω‖ ≤ 1) (hpnd : ∀ ω, ‖p ω‖ ≤ 1)
    (hz : Measurable z)
    (hI : ∀ A : Set Z, MeasurableSet A →
      μ[(fun ω => b ω * A.indicator (fun _ => (1 : ℝ)) (z ω)) | G] =ᵐ[μ]
        (fun ω => p ω * μ[(fun η => A.indicator (fun _ => (1 : ℝ)) (z η)) | G] ω))
    {f : Z → ℝ} (hf : Measurable f) (hfi : Integrable (fun ω => f (z ω)) μ) :
    μ[(fun ω => b ω * f (z ω)) | G] =ᵐ[μ]
      (fun ω => p ω * μ[(fun η => f (z η)) | G] ω) := by
  have hp' : Measurable p := hp.mono hG le_rfl
  have hsimple (s : SimpleFunc Z ℝ) :
      μ[(fun ω => b ω * s (z ω)) | G] =ᵐ[μ]
        μ[(fun ω => p ω * s (z ω)) | G] := by
    apply RepairT6T7_simple_moment hb hp' hbnd hpnd hz
    intro A hA
    have hi : Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) (z ω)) μ := by
      have hm : Measurable (fun ω => A.indicator (fun _ => (1 : ℝ)) (z ω)) :=
        (measurable_const.indicator hA).comp hz
      refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
      exact Eventually.of_forall fun ω => by
        by_cases hω : z ω ∈ A <;> simp [hω]
    exact (hI A hA).trans
      (condExp_mul_of_stronglyMeasurable_left hp.stronglyMeasurable
        (RepairT6T7_mul_integrable hp' hpnd hi) hi).symm
  let s : ℕ → SimpleFunc Z ℝ := SimpleFunc.approxOn f hf Set.univ 0 (Set.mem_univ 0)
  have hs_bound (n : ℕ) (ω : Ω) : ‖s n (z ω)‖ ≤ ‖f (z ω)‖ + ‖f (z ω)‖ :=
    SimpleFunc.norm_approxOn_zero_le hf (Set.mem_univ 0) (z ω) n
  have hs_tendsto (ω : Ω) : Tendsto (fun n => s n (z ω)) atTop (𝓝 (f (z ω))) :=
    SimpleFunc.tendsto_approxOn hf (Set.mem_univ 0) (by simp)
  have hi (a : Ω → ℝ) (ha : Measurable a) (ha' : ∀ ω, ‖a ω‖ ≤ 1) (n : ℕ) :
      Integrable (fun ω => a ω * s n (z ω)) μ :=
    RepairT6T7_mul_integrable ha ha' (((s n).comp z hz).integrable_of_isFiniteMeasure)
  have hbound (a : Ω → ℝ) (ha : ∀ ω, ‖a ω‖ ≤ 1) (n : ℕ) :
      ∀ᵐ ω ∂μ, ‖a ω * s n (z ω)‖ ≤ ‖f (z ω)‖ + ‖f (z ω)‖ := by
    exact Eventually.of_forall fun ω =>
      (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (ha ω) (norm_nonneg _)).trans
        (by simpa using hs_bound n ω))
  have hlim : μ[(fun ω => b ω * f (z ω)) | G] =ᵐ[μ]
      μ[(fun ω => p ω * f (z ω)) | G] := by
    apply tendsto_condExp_unique (fun n ω => b ω * s n (z ω))
      (fun n ω => p ω * s n (z ω)) _ _ (hi b hb hbnd) (hi p hp' hpnd)
      (Eventually.of_forall fun ω => tendsto_const_nhds.mul (hs_tendsto ω))
      (Eventually.of_forall fun ω => tendsto_const_nhds.mul (hs_tendsto ω))
      (fun ω => ‖f (z ω)‖ + ‖f (z ω)‖) (hfi.norm.add hfi.norm)
      (fun ω => ‖f (z ω)‖ + ‖f (z ω)‖) (hfi.norm.add hfi.norm)
      (hbound b hbnd) (hbound p hpnd) (fun n => hsimple (s n))
  exact hlim.trans (condExp_mul_of_stronglyMeasurable_left hp.stronglyMeasurable
    (RepairT6T7_mul_integrable hp' hpnd hfi) hfi)

end ConditionalMoment

section ExperimentMoments

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}

lemma RepairT6T7_admissible_norm {π : C → ℝ} (hπ : Admissible π) (c : C) : ‖π c‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hπ.2 c).1] using (hπ.2 c).2

lemma RepairT6T7_bit_norm (t : Bool) : ‖bit t‖ ≤ 1 := by
  cases t <;> norm_num [bit]

lemma RepairT6T7_law_transport (E : Experiment Ω C n) {π : C → ℝ} (hS : RepairT6T7_Design E π)
    (_hπ : Admissible π) (i : Fin n)
    {f : C → ℝ} (hf : Measurable f) (hfi : Integrable f E.PX) :
    Integrable (fun ω => f (E.X i ω)) (E.law π) ∧
      (∫ ω, f (E.X i ω) ∂E.law π) = ∫ c, f c ∂E.PX := by
  have h := (hS.covariate_law i).comp hf
  exact ⟨h.integrable_iff.mpr hfi, h.integral_eq⟩

/-- Both potential-outcome coordinates have the required treated conditional mean. -/
lemma RepairT6T7_unit_outcome_moments (E : Experiment Ω C n) {π : C → ℝ} (hS : RepairT6T7_Design E π)
    (hπ : Admissible π) (i : Fin n) :
    (E.law π)[(fun ω => bit (E.T π i ω) * E.Y0 i ω) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) * E.μ0 (E.X i ω)) ∧
    (E.law π)[(fun ω => bit (E.T π i ω) * E.Y1 i ω) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) * E.μ1 (E.X i ω)) := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability
  obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units i
  have hp : Measurable[E.covariateSigma i] (fun ω => π (E.X i ω)) :=
    hπ.1.comp (comap_measurable (E.X i))
  have hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hb : Measurable (fun ω => bit (E.T π i ω)) :=
    (measurable_of_countable bit).comp hT
  have h0 := RepairT6T7_binary_conditional_moment_extension hG hb hp
    (fun ω => RepairT6T7_bit_norm (E.T π i ω)) (fun ω => RepairT6T7_admissible_norm hπ (E.X i ω))
    (hY0.prodMk hY1) (hS.ignorability i) measurable_fst
    (hS.integrable_units i).1
  have h1 := RepairT6T7_binary_conditional_moment_extension hG hb hp
    (fun ω => RepairT6T7_bit_norm (E.T π i ω)) (fun ω => RepairT6T7_admissible_norm hπ (E.X i ω))
    (hY0.prodMk hY1) (hS.ignorability i) measurable_snd
    (hS.integrable_units i).2
  exact ⟨h0.trans (by
    filter_upwards [(hS.conditional_means i).1] with ω hω using congrArg (π (E.X i ω) * ·) hω),
    h1.trans (by
    filter_upwards [(hS.conditional_means i).2] with ω hω using congrArg (π (E.X i ω) * ·) hω)⟩

lemma RepairT6T7_actual_welfare (E : Experiment Ω C n) {π : C → ℝ} (hS : RepairT6T7_Design E π)
    (hπ : Admissible π) : E.V π = E.meanWelfare π := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability
  let i : Fin n := ⟨0, E.hn⟩
  obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units i
  have hb : Measurable (fun ω => bit (E.T π i ω)) :=
    (measurable_of_countable bit).comp hT
  have hi0 := RepairT6T7_mul_integrable hb (fun ω => RepairT6T7_bit_norm (E.T π i ω))
    (hS.integrable_units i).1
  have hi1 := RepairT6T7_mul_integrable hb (fun ω => RepairT6T7_bit_norm (E.T π i ω))
    (hS.integrable_units i).2
  obtain ⟨hm0, hm1⟩ := RepairT6T7_unit_outcome_moments E hS hπ i
  have hc : (E.law π)[(fun ω => bit (E.T π i ω) * E.Y1 i ω -
      bit (E.T π i ω) * E.Y0 i ω) | E.covariateSigma i] =ᵐ[E.law π]
      (fun ω => π (E.X i ω) * E.τ (E.X i ω)) := by
    refine (condExp_sub hi1 hi0 (E.covariateSigma i)).trans ?_
    filter_upwards [hm0, hm1] with ω h0 h1
    simp only [Pi.sub_apply, h0, h1, Experiment.τ]
    ring
  have heq : (fun ω => E.observed π ω i - E.Y0 i ω) =
      (fun ω => bit (E.T π i ω) * E.Y1 i ω - bit (E.T π i ω) * E.Y0 i ω) := by
    ext ω
    cases ht : E.T π i ω <;> simp [Experiment.observed, ht, bit]
  have hpop := RepairT6T7_law_transport E hS hπ i
    (hπ.1.mul (hS.means_measurable.2.sub hS.means_measurable.1))
    (RepairT6T7_mul_integrable hπ.1 (RepairT6T7_admissible_norm hπ)
      (hS.means_integrable.2.sub hS.means_integrable.1))
  have hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hTrimFinite : IsFiniteMeasure ((E.law π).trim hG) := isFiniteMeasure_trim hG
  have hTrimSigma : SigmaFinite ((E.law π).trim hG) := inferInstance
  change (∫ ω, E.observed π ω i - E.Y0 i ω ∂E.law π) = _
  rw [heq]
  calc
    _ = ∫ ω, (E.law π)[(fun η => bit (E.T π i η) * E.Y1 i η -
        bit (E.T π i η) * E.Y0 i η) | E.covariateSigma i] ω ∂E.law π :=
      (integral_condExp (μ := E.law π) (m := E.covariateSigma i)
        (hμm := hTrimSigma) hG).symm
    _ = ∫ ω, π (E.X i ω) * E.τ (E.X i ω) ∂E.law π := integral_congr_ae hc
    _ = E.meanWelfare π := hpop.2

/-- The actual reward summand is integrable and has the asserted conditional mean.
This retains the conditional identity needed when a later theorem introduces weights. -/
lemma RepairT6T7_actual_treated_summand (E : Experiment Ω C n) {π a : C → ℝ} (hS : RepairT6T7_Design E π)
    (hπ : Admissible π) (ha : Measurable a) (hai : Integrable a E.PX)
    (hR : ∀ i, Integrable (fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω))) (E.law π))
    (hU : ∀ i, (E.law π)[(fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω))) | E.covariateSigma i]
      =ᵐ[E.law π] (fun _ => (0 : ℝ))) (i : Fin n) :
    Integrable (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
      bit (E.T π i ω)) (E.law π) ∧
    (E.law π)[(fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
      bit (E.T π i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) * (E.μ1 (E.X i ω) - a (E.X i ω))) := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability
  obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units i
  have hb : Measurable (fun ω => bit (E.T π i ω)) :=
    (measurable_of_countable bit).comp hT
  have hbnd := fun ω => RepairT6T7_bit_norm (E.T π i ω)
  obtain ⟨hiY0, hiY1⟩ := hS.integrable_units i
  have hia := (RepairT6T7_law_transport E hS hπ i ha hai).1
  have hiba := RepairT6T7_mul_integrable hb hbnd hia
  have hibY := RepairT6T7_mul_integrable hb hbnd hiY1
  have hir := hR i
  have hib : Integrable (fun ω => bit (E.T π i ω)) (E.law π) :=
    (integrable_const (1 : ℝ)).mono' hb.aestronglyMeasurable (Eventually.of_forall hbnd)
  have haG : Measurable[E.covariateSigma i] (fun ω => a (E.X i ω)) :=
    ha.comp (comap_measurable (E.X i))
  have hca : (E.law π)[(fun ω => bit (E.T π i ω) * a (E.X i ω)) |
      E.covariateSigma i] =ᵐ[E.law π] (fun ω => π (E.X i ω) * a (E.X i ω)) :=
    (condExp_mul_of_stronglyMeasurable_right haG.stronglyMeasurable hiba hib).trans (by
      filter_upwards [hS.bernoulli i] with ω hω
      exact congrArg (· * a (E.X i ω)) hω)
  have hsutva : (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
      bit (E.T π i ω)) = (fun ω => bit (E.T π i ω) *
        (E.Y1 i ω - E.μhat π ω (E.X i ω))) := by
    ext ω
    cases ht : E.T π i ω <;> simp [Experiment.observed, ht, bit]
  rw [hsutva]
  have hsplit : (fun ω => bit (E.T π i ω) * (E.Y1 i ω - E.μhat π ω (E.X i ω))) =
      (fun ω => bit (E.T π i ω) * E.Y1 i ω - bit (E.T π i ω) * a (E.X i ω)) -
        (fun ω => bit (E.T π i ω) * (E.μhat π ω (E.X i ω) - a (E.X i ω))) := by
    ext ω
    simp only [Pi.sub_apply]
    ring
  rw [hsplit]
  refine ⟨(hibY.sub hiba).sub hir, ?_⟩
  refine (condExp_sub (hibY.sub hiba) hir (E.covariateSigma i)).trans ?_
  filter_upwards [condExp_sub hibY hiba (E.covariateSigma i),
    (RepairT6T7_unit_outcome_moments E hS hπ i).2, hca, hU i] with ω hsub hY ha' hr
  simp only [Pi.sub_apply, hsub, hY, ha', hr]
  ring

lemma RepairT6T7_actual_treated_score (E : Experiment Ω C n) {π a : C → ℝ} (hS : RepairT6T7_Design E π)
    (hπ : Admissible π) (ha : Measurable a) (hai : Integrable a E.PX)
    (hR : ∀ i, Integrable (fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω))) (E.law π))
    (hU : ∀ i, (E.law π)[(fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω))) | E.covariateSigma i]
      =ᵐ[E.law π] (fun _ => (0 : ℝ))) :
    E.expectedTT π = (n : ℝ) * ∫ c, π c * (E.μ1 c - a c) ∂E.PX := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability
  have hs := RepairT6T7_actual_treated_summand E hS hπ ha hai hR hU
  have hi (i : Fin n) :
      (∫ ω, (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) ∂E.law π) =
        ∫ c, π c * (E.μ1 c - a c) ∂E.PX := by
    have hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω› :=
      (hS.measurable_units i).1.comap_le
    have hTrimFinite : IsFiniteMeasure ((E.law π).trim hG) := isFiniteMeasure_trim hG
    have hTrimSigma : SigmaFinite ((E.law π).trim hG) := inferInstance
    calc
      _ = ∫ ω, (E.law π)[(fun η => (E.observed π η i - E.μhat π η (E.X i η)) *
          bit (E.T π i η)) | E.covariateSigma i] ω ∂E.law π :=
        (integral_condExp (μ := E.law π) (m := E.covariateSigma i)
          (hμm := hTrimSigma) hG).symm
      _ = ∫ ω, π (E.X i ω) * (E.μ1 (E.X i ω) - a (E.X i ω)) ∂E.law π :=
        integral_congr_ae (hs i).2
      _ = _ := (RepairT6T7_law_transport E hS hπ i (hπ.1.mul (hS.means_measurable.2.sub ha))
        (RepairT6T7_mul_integrable hπ.1 (RepairT6T7_admissible_norm hπ)
          (hS.means_integrable.2.sub hai))).2
  change (∫ ω, ∑ i : Fin n, (E.observed π ω i - E.μhat π ω (E.X i ω)) *
    bit (E.T π i ω) * 1 ∂E.law π) = _
  simp only [mul_one]
  rw [integral_finsetSum _ (fun i _ => (hs i).1)]
  simp_rw [hi]
  simp

lemma RepairT6T7_positive_rule_integral_maximum {P : Measure C} {t : C → ℝ}
    (ht : Measurable t) (hti : Integrable t P) :
    Admissible (positiveRule t) ∧ ∀ π : C → ℝ, Admissible π →
      (∫ c, π c * t c ∂P) ≤ ∫ c, positiveRule t c * t c ∂P := by
  have hp : Admissible (positiveRule t) := by
    refine ⟨Measurable.ite (measurableSet_lt measurable_const ht)
      measurable_const measurable_const, ?_⟩
    intro c
    by_cases h : 0 < t c <;> simp [positiveRule, h]
  refine ⟨hp, fun π hπ => integral_mono
    (RepairT6T7_mul_integrable hπ.1 (RepairT6T7_admissible_norm hπ) hti)
    (RepairT6T7_mul_integrable hp.1 (RepairT6T7_admissible_norm hp) hti) ?_⟩
  intro c
  by_cases h : 0 < t c
  · simp only [positiveRule, if_pos h, one_mul]
    exact mul_le_of_le_one_left h.le (hπ.2 c).2
  · simp only [positiveRule, if_neg h, zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hπ.2 c).1 (le_of_not_gt h)

end ExperimentMoments


/-- Corrected T6 on the feasible class, with only the treated estimator residual
integrable. The finite TT expectation follows from these assumptions. -/
theorem T6_corrected_TT_minimal_integrability {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (PiSet : Set (C → ℝ)) (hPiSet : ∀ π ∈ PiSet, Admissible π)
    (hS : ∀ π ∈ PiSet, RepairT6T7_Design E π)
    (hR : ∀ π ∈ PiSet, ∀ i, Integrable (fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : TreatedUnbiased E E.μ0 PiSet) :
    (∀ π ∈ PiSet, E.expectedTT π = (n : ℝ)*E.meanWelfare π ∧
      E.V π = E.meanWelfare π) ∧
    (∀ π, IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π) ∧
    (∀ π, IsBest PiSet E.expectedTT π → regret PiSet E.V π = 0) ∧
    (PiSet = {π | Admissible π} → IsBest PiSet E.expectedTT (positiveRule E.τ)) := by
  have hid (π : C → ℝ) (hπ : π ∈ PiSet) :
      E.expectedTT π = (n : ℝ) * E.meanWelfare π ∧ E.V π = E.meanWelfare π := by
    let S := hS π hπ
    refine ⟨?_, RepairT6T7_actual_welfare E S (hPiSet π hπ)⟩
    exact RepairT6T7_actual_treated_score E S (hPiSet π hπ)
      S.means_measurable.1 S.means_integrable.1 (hR π hπ) (hU π hπ)
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr E.hn
  have hscore (π : C → ℝ) (hπ : π ∈ PiSet) : E.expectedTT π = (n : ℝ) * E.V π := by
    rw [(hid π hπ).1, (hid π hπ).2]
  have hbest (π : C → ℝ) : IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π := by
    constructor
    · rintro ⟨hπ, hmax⟩
      refine ⟨hπ, fun q hq => ?_⟩
      have h := hmax q hq
      rw [hscore q hq, hscore π hπ] at h
      exact (mul_le_mul_iff_right₀ hn).mp h
    · rintro ⟨hπ, hmax⟩
      refine ⟨hπ, fun q hq => ?_⟩
      rw [hscore q hq, hscore π hπ]
      exact (mul_le_mul_iff_right₀ hn).mpr (hmax q hq)
  refine ⟨hid, hbest, ?_, ?_⟩
  · intro π hb
    rw [regret, bestValue_eq ((hbest π).mp hb), sub_self]
  · intro hAll
    have hz : (fun _ : C => (0 : ℝ)) ∈ PiSet := by
      rw [hAll]
      exact ⟨measurable_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩
    let S := hS _ hz
    obtain ⟨hp, hmax⟩ := RepairT6T7_positive_rule_integral_maximum (P := E.PX) (t := E.τ)
      (S.means_measurable.2.sub S.means_measurable.1)
      (S.means_integrable.2.sub S.means_integrable.1)
    have hmem : positiveRule E.τ ∈ PiSet := by rw [hAll]; exact hp
    apply (hbest _).mpr
    refine ⟨hmem, fun π hπ => ?_⟩
    rw [(hid π hπ).2, (hid _ hmem).2]
    exact hmax π (hPiSet π hπ)

/-- Conditional integration with respect to an independent auxiliary draw.
This is a direct set-integral uniqueness proof; the measurable spaces A and D
are arbitrary. In particular, no regular conditional distribution is used. -/
lemma RepairT6T7_auxiliary_condExp {Ω A D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace D]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → A) (V : Ω → D) (hZ : Measurable Z) (hV : Measurable V)
    (hI : IndepFun Z V μ) (F : A × D → ℝ) (g : D → ℝ)
    (hF : Measurable F) (hg : Measurable g)
    (hFi : Integrable (fun ω => F (Z ω, V ω)) μ)
    (hgi : Integrable (fun ω => g (V ω)) μ)
    (hmean : ∀ d, (∫ z, F (z,d) ∂μ.map Z) = g d) :
    μ[(fun ω => F (Z ω,V ω)) | MeasurableSpace.comap V inferInstance]
      =ᵐ[μ] (fun ω => g (V ω)) := by
  let ν : Measure A := μ.map Z
  let η : Measure D := μ.map V
  let P : Ω → A × D := fun ω => (Z ω,V ω)
  have hP : Measurable P := hZ.prodMk hV
  have hmap : μ.map P = ν.prod η :=
    hI.map_prod_eq_prod_map_map hZ.aemeasurable hV.aemeasurable
  letI : IsProbabilityMeasure ν := inferInstance
  letI : IsProbabilityMeasure η := inferInstance
  have hFP : Integrable F (ν.prod η) := by
    rw [← hmap]
    exact (integrable_map_measure hF.aestronglyMeasurable hP.aemeasurable).mpr hFi
  have hcomap : MeasurableSpace.comap V (inferInstance : MeasurableSpace D) ≤ (inferInstance : MeasurableSpace Ω) := hV.comap_le
  have hgm : Measurable[MeasurableSpace.comap V inferInstance] (fun ω => g (V ω)) :=
    hg.comp (comap_measurable V)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hcomap hFi
    (fun s _ _ => hgi.integrableOn) ?_ hgm.stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs hfinite
  rcases hs with ⟨t, ht, rfl⟩
  let J : A × D → ℝ := (Prod.snd ⁻¹' t).indicator F
  have hJ : Measurable J := hF.indicator (ht.preimage measurable_snd)
  have hJi : Integrable J (ν.prod η) := hFP.indicator (ht.preimage measurable_snd)
  have hslice (d : D) : (∫ z, J (z,d) ∂ν) = t.indicator g d := by
    by_cases hd : d ∈ t
    · simpa [J, hd, ν, Set.indicator_of_mem] using hmean d
    · simp [J, hd]
  have hJmap :
      (∫ z, J z ∂ν.prod η) =
        ∫ ω, (V ⁻¹' t).indicator (fun ω => F (Z ω,V ω)) ω ∂μ := by
    rw [← hmap]
    exact integral_map_of_stronglyMeasurable hP hJ.stronglyMeasurable
  have hgmap :
      (∫ d, t.indicator g d ∂η) =
        ∫ ω, (V ⁻¹' t).indicator (fun ω => g (V ω)) ω ∂μ := by
    exact integral_map_of_stronglyMeasurable hV (hg.indicator ht).stronglyMeasurable
  calc
    (∫ ω in V ⁻¹' t, g (V ω) ∂μ) = ∫ d, t.indicator g d ∂η := by
      rw [hgmap, integral_indicator (ht.preimage hV)]
    _ = ∫ z, J z ∂ν.prod η := by
      rw [integral_prod_symm J hJi]
      simp_rw [hslice]
    _ = ∫ ω in V ⁻¹' t, F (Z ω,V ω) ∂μ := by
      rw [hJmap, integral_indicator (ht.preimage hV)]

/-- Independence is applied directly to the treated residual; the unselected
estimator evaluation need not be integrable. -/
theorem T6_independent_estimation_minimal_integrability {Ω C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (PiSet : Set (C → ℝ))
    (hS : ∀ π ∈ PiSet, RepairT6T7_Design E π)
    (hR : ∀ π ∈ PiSet, ∀ i, Integrable (fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : PointwiseUnbiased E PiSet) (hI : IndependentEstimator E PiSet) :
    TreatedUnbiased E E.μ0 PiSet := by
  obtain ⟨A, mA, Z, f, hZ, hf⟩ := hI
  letI : MeasurableSpace A := mA
  intro π hπ i
  let S := hS π hπ
  letI : IsProbabilityMeasure (E.law π) := S.law_probability
  let D := (Fin n → C) × (Fin n → Bool)
  let V : Ω → D := fun ω => ((fun j => E.X j ω), (fun j => E.T π j ω))
  let F : A × D → ℝ := fun z => bit (z.2.2 i) *
    (f π z.1 (z.2.1 i) - E.μ0 (z.2.1 i))
  obtain ⟨hfm, hrep, hi⟩ := hf π hπ
  have hV : Measurable V :=
    (measurable_pi_iff.mpr (fun j => (S.measurable_units j).1)).prodMk
      (measurable_pi_iff.mpr (fun j => (S.measurable_units j).2.2.2))
  have hx : Measurable (fun z : A × D => z.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have ht : Measurable (fun z : A × D => z.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  have hF : Measurable F :=
    ((measurable_of_countable bit).comp ht).mul
      ((hfm.comp (measurable_fst.prodMk hx)).sub (S.means_measurable.1.comp hx))
  have heq : (fun ω => F (Z ω, V ω)) = (fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) := by
    funext ω
    dsimp [F, V]
    rw [← hrep]
  have hFi : Integrable (fun ω => F (Z ω, V ω)) (E.law π) := by
    rw [heq]
    exact hR π hπ i
  have hmean (d : D) : (∫ z, F (z, d) ∂(E.law π).map Z) = (0 : ℝ) := by
    have hslice : Measurable (fun z : A => F (z, d)) :=
      hF.comp (measurable_id.prodMk measurable_const)
    rw [integral_map_of_stronglyMeasurable hZ hslice.stronglyMeasurable]
    calc
      (∫ ω, F (Z ω, d) ∂E.law π) =
          ∫ ω, bit (d.2 i) * (E.μhat π ω (d.1 i) - E.μ0 (d.1 i)) ∂E.law π := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by dsimp [F]; rw [← hrep]
      _ = 0 := by
        rw [integral_const_mul, integral_sub (hU π hπ (d.1 i)).1 (integrable_const _),
          (hU π hπ (d.1 i)).2, integral_const]
        simp
  have hce := RepairT6T7_auxiliary_condExp (E.law π) Z V hZ hV hi F
    (fun _ => 0) hF measurable_const hFi (integrable_const _) hmean
  rw [heq] at hce
  have hXv : Measurable[E.vectorSigma π] (E.X i) :=
    ((measurable_pi_apply i).comp measurable_fst).comp (comap_measurable V)
  have hsmall : E.covariateSigma i ≤ E.vectorSigma π := hXv.comap_le
  have hvle : E.vectorSigma π ≤ (inferInstance : MeasurableSpace Ω) := hV.comap_le
  have htower := condExp_condExp_of_le (μ := E.law π)
    (f := fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) hsmall hvle
  exact htower.symm.trans ((condExp_congr_ae hce).trans (by simp))

end
end AronowAudit.P006.Wave1
