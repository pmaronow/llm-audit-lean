import AronowAudit.P006.P006_CounterfactualMetrics
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! P006-T6: the actual TT identity and its incentive-alignment consequences. -/

namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance instDecidableGLP006B2 (p : Prop) : Decidable p := Classical.propDecidable p

section ConditionalMoment

variable {Ω Z : Type*} {G : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace Z] {μ : Measure Ω}

lemma T6_mul_integrable {b f : Ω → ℝ} (hb : Measurable b)
    (hbnd : ∀ ω, ‖b ω‖ ≤ 1) (hf : Integrable f μ) :
    Integrable (fun ω => b ω * f ω) μ :=
  hf.bdd_mul hb.aestronglyMeasurable (Eventually.of_forall hbnd)

lemma T6_simple_moment [IsFiniteMeasure μ] {b p : Ω → ℝ} {z : Ω → Z}
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
      T6_mul_integrable ha ha' ((v.comp z hz).integrable_of_isFiniteMeasure)
    simp only [SimpleFunc.coe_add, Pi.add_apply, mul_add]
    exact (condExp_add (hi b hb hbnd s) (hi b hb hbnd t) G).trans
      ((hs.add ht).trans (condExp_add (hi p hp hpnd s) (hi p hp hpnd t) G).symm)

/-- The indicator conditional moment extends to every integrable measurable mark.
The two multiplied simple approximations share the integrable bound `2 * ‖f ∘ z‖`. -/
lemma T6_binary_conditional_moment_extension [IsFiniteMeasure μ]
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
    apply T6_simple_moment hb hp' hbnd hpnd hz
    intro A hA
    have hi : Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) (z ω)) μ := by
      have hm : Measurable (fun ω => A.indicator (fun _ => (1 : ℝ)) (z ω)) :=
        (measurable_const.indicator hA).comp hz
      refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
      exact Eventually.of_forall fun ω => by
        by_cases hω : z ω ∈ A <;> simp [hω]
    exact (hI A hA).trans
      (condExp_mul_of_stronglyMeasurable_left hp.stronglyMeasurable
        (T6_mul_integrable hp' hpnd hi) hi).symm
  let s : ℕ → SimpleFunc Z ℝ := SimpleFunc.approxOn f hf Set.univ 0 (Set.mem_univ 0)
  have hs_bound (n : ℕ) (ω : Ω) : ‖s n (z ω)‖ ≤ ‖f (z ω)‖ + ‖f (z ω)‖ :=
    SimpleFunc.norm_approxOn_zero_le hf (Set.mem_univ 0) (z ω) n
  have hs_tendsto (ω : Ω) : Tendsto (fun n => s n (z ω)) atTop (𝓝 (f (z ω))) :=
    SimpleFunc.tendsto_approxOn hf (Set.mem_univ 0) (by simp)
  have hi (a : Ω → ℝ) (ha : Measurable a) (ha' : ∀ ω, ‖a ω‖ ≤ 1) (n : ℕ) :
      Integrable (fun ω => a ω * s n (z ω)) μ :=
    T6_mul_integrable ha ha' (((s n).comp z hz).integrable_of_isFiniteMeasure)
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
    (T6_mul_integrable hp' hpnd hfi) hfi)

end ConditionalMoment

section ExperimentMoments

variable {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}

lemma T6_admissible_norm {π : C → ℝ} (hπ : Admissible π) (c : C) : ‖π c‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hπ.2 c).1] using (hπ.2 c).2

lemma T6_bit_norm (t : Bool) : ‖bit t‖ ≤ 1 := by
  cases t <;> norm_num [bit]

lemma T6_law_transport (E : Experiment Ω C n) (hS : Standing E)
    {π : C → ℝ} (hπ : Admissible π) (i : Fin n)
    {f : C → ℝ} (hf : Measurable f) (hfi : Integrable f E.PX) :
    Integrable (fun ω => f (E.X i ω)) (E.law π) ∧
      (∫ ω, f (E.X i ω) ∂E.law π) = ∫ c, f c ∂E.PX := by
  have h := (hS.covariate_law π hπ i).comp hf
  exact ⟨h.integrable_iff.mpr hfi, h.integral_eq⟩

/-- Both potential-outcome coordinates have the required treated conditional mean. -/
lemma T6_unit_outcome_moments (E : Experiment Ω C n) (hS : Standing E)
    {π : C → ℝ} (hπ : Admissible π) (i : Fin n) :
    (E.law π)[(fun ω => bit (E.T π i ω) * E.Y0 i ω) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) * E.μ0 (E.X i ω)) ∧
    (E.law π)[(fun ω => bit (E.T π i ω) * E.Y1 i ω) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) * E.μ1 (E.X i ω)) := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units π hπ i
  have hp : Measurable[E.covariateSigma i] (fun ω => π (E.X i ω)) :=
    hπ.1.comp (comap_measurable (E.X i))
  have hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hb : Measurable (fun ω => bit (E.T π i ω)) :=
    (measurable_of_countable bit).comp hT
  have h0 := T6_binary_conditional_moment_extension hG hb hp
    (fun ω => T6_bit_norm (E.T π i ω)) (fun ω => T6_admissible_norm hπ (E.X i ω))
    (hY0.prodMk hY1) (hS.ignorability π hπ i) measurable_fst
    (hS.integrable_units π hπ i).1
  have h1 := T6_binary_conditional_moment_extension hG hb hp
    (fun ω => T6_bit_norm (E.T π i ω)) (fun ω => T6_admissible_norm hπ (E.X i ω))
    (hY0.prodMk hY1) (hS.ignorability π hπ i) measurable_snd
    (hS.integrable_units π hπ i).2.1
  exact ⟨h0.trans (by
    filter_upwards [(hS.conditional_means π hπ i).1] with ω hω using congrArg (π (E.X i ω) * ·) hω),
    h1.trans (by
    filter_upwards [(hS.conditional_means π hπ i).2] with ω hω using congrArg (π (E.X i ω) * ·) hω)⟩

lemma T6_actual_welfare (E : Experiment Ω C n) (hS : Standing E)
    {π : C → ℝ} (hπ : Admissible π) : E.V π = E.meanWelfare π := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  let i : Fin n := ⟨0, E.hn⟩
  obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units π hπ i
  have hb : Measurable (fun ω => bit (E.T π i ω)) :=
    (measurable_of_countable bit).comp hT
  have hi0 := T6_mul_integrable hb (fun ω => T6_bit_norm (E.T π i ω))
    (hS.integrable_units π hπ i).1
  have hi1 := T6_mul_integrable hb (fun ω => T6_bit_norm (E.T π i ω))
    (hS.integrable_units π hπ i).2.1
  obtain ⟨hm0, hm1⟩ := T6_unit_outcome_moments E hS hπ i
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
  have hpop := T6_law_transport E hS hπ i
    (hπ.1.mul (hS.means_measurable.2.sub hS.means_measurable.1))
    (T6_mul_integrable hπ.1 (T6_admissible_norm hπ)
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
lemma T6_actual_treated_summand (E : Experiment Ω C n) (hS : Standing E)
    {π a : C → ℝ} (hπ : Admissible π) (ha : Measurable a) (hai : Integrable a E.PX)
    (hU : ∀ i, (E.law π)[(fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω))) | E.covariateSigma i]
      =ᵐ[E.law π] (fun _ => (0 : ℝ))) (i : Fin n) :
    Integrable (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
      bit (E.T π i ω)) (E.law π) ∧
    (E.law π)[(fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
      bit (E.T π i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] (fun ω => π (E.X i ω) * (E.μ1 (E.X i ω) - a (E.X i ω))) := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units π hπ i
  have hb : Measurable (fun ω => bit (E.T π i ω)) :=
    (measurable_of_countable bit).comp hT
  have hbnd := fun ω => T6_bit_norm (E.T π i ω)
  obtain ⟨hiY0, hiY1, hiH⟩ := hS.integrable_units π hπ i
  have hia := (T6_law_transport E hS hπ i ha hai).1
  have hiba := T6_mul_integrable hb hbnd hia
  have hibY := T6_mul_integrable hb hbnd hiY1
  have hir := T6_mul_integrable hb hbnd (hiH.sub hia)
  have hib : Integrable (fun ω => bit (E.T π i ω)) (E.law π) :=
    (integrable_const (1 : ℝ)).mono' hb.aestronglyMeasurable (Eventually.of_forall hbnd)
  have haG : Measurable[E.covariateSigma i] (fun ω => a (E.X i ω)) :=
    ha.comp (comap_measurable (E.X i))
  have hca : (E.law π)[(fun ω => bit (E.T π i ω) * a (E.X i ω)) |
      E.covariateSigma i] =ᵐ[E.law π] (fun ω => π (E.X i ω) * a (E.X i ω)) :=
    (condExp_mul_of_stronglyMeasurable_right haG.stronglyMeasurable hiba hib).trans (by
      filter_upwards [hS.bernoulli π hπ i] with ω hω
      exact congrArg (· * a (E.X i ω)) hω)
  have hsutva : (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
      bit (E.T π i ω)) = (fun ω => bit (E.T π i ω) *
        (E.Y1 i ω - E.μhat π ω (E.X i ω))) := by
    ext ω
    cases ht : E.T π i ω <;> simp [Experiment.observed, ht, bit]
  rw [hsutva]
  refine ⟨T6_mul_integrable hb hbnd (hiY1.sub hiH), ?_⟩
  have hsplit : (fun ω => bit (E.T π i ω) * (E.Y1 i ω - E.μhat π ω (E.X i ω))) =
      (fun ω => bit (E.T π i ω) * E.Y1 i ω - bit (E.T π i ω) * a (E.X i ω)) -
        (fun ω => bit (E.T π i ω) * (E.μhat π ω (E.X i ω) - a (E.X i ω))) := by
    ext ω
    simp only [Pi.sub_apply]
    ring
  rw [hsplit]
  refine (condExp_sub (hibY.sub hiba) hir (E.covariateSigma i)).trans ?_
  filter_upwards [condExp_sub hibY hiba (E.covariateSigma i),
    (T6_unit_outcome_moments E hS hπ i).2, hca, hU i] with ω hsub hY ha' hr
  simp only [Pi.sub_apply, hsub, hY, ha', hr]
  ring

lemma T6_actual_treated_score (E : Experiment Ω C n) (hS : Standing E)
    {π a : C → ℝ} (hπ : Admissible π) (ha : Measurable a) (hai : Integrable a E.PX)
    (hU : ∀ i, (E.law π)[(fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω))) | E.covariateSigma i]
      =ᵐ[E.law π] (fun _ => (0 : ℝ))) :
    E.expectedTT π = (n : ℝ) * ∫ c, π c * (E.μ1 c - a c) ∂E.PX := by
  have hLaw : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  have hs := T6_actual_treated_summand E hS hπ ha hai hU
  have hi (i : Fin n) :
      (∫ ω, (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) ∂E.law π) =
        ∫ c, π c * (E.μ1 c - a c) ∂E.PX := by
    have hG : E.covariateSigma i ≤ ‹MeasurableSpace Ω› :=
      (hS.measurable_units π hπ i).1.comap_le
    have hTrimFinite : IsFiniteMeasure ((E.law π).trim hG) := isFiniteMeasure_trim hG
    have hTrimSigma : SigmaFinite ((E.law π).trim hG) := inferInstance
    calc
      _ = ∫ ω, (E.law π)[(fun η => (E.observed π η i - E.μhat π η (E.X i η)) *
          bit (E.T π i η)) | E.covariateSigma i] ω ∂E.law π :=
        (integral_condExp (μ := E.law π) (m := E.covariateSigma i)
          (hμm := hTrimSigma) hG).symm
      _ = ∫ ω, π (E.X i ω) * (E.μ1 (E.X i ω) - a (E.X i ω)) ∂E.law π :=
        integral_congr_ae (hs i).2
      _ = _ := (T6_law_transport E hS hπ i (hπ.1.mul (hS.means_measurable.2.sub ha))
        (T6_mul_integrable hπ.1 (T6_admissible_norm hπ)
          (hS.means_integrable.2.sub hai))).2
  change (∫ ω, ∑ i : Fin n, (E.observed π ω i - E.μhat π ω (E.X i ω)) *
    bit (E.T π i ω) * 1 ∂E.law π) = _
  simp only [mul_one]
  rw [integral_finsetSum _ (fun i _ => (hs i).1)]
  simp_rw [hi]
  simp

lemma T6_positive_rule_integral_maximum {P : Measure C} {t : C → ℝ}
    (ht : Measurable t) (hti : Integrable t P) :
    Admissible (positiveRule t) ∧ ∀ π : C → ℝ, Admissible π →
      (∫ c, π c * t c ∂P) ≤ ∫ c, positiveRule t c * t c ∂P := by
  have hp : Admissible (positiveRule t) := by
    refine ⟨Measurable.ite (measurableSet_lt measurable_const ht)
      measurable_const measurable_const, ?_⟩
    intro c
    by_cases h : 0 < t c <;> simp [positiveRule, h]
  refine ⟨hp, fun π hπ => integral_mono
    (T6_mul_integrable hπ.1 (T6_admissible_norm hπ) hti)
    (T6_mul_integrable hp.1 (T6_admissible_norm hp) hti) ?_⟩
  intro c
  by_cases h : 0 < t c
  · simp only [positiveRule, if_pos h, one_mul]
    exact mul_le_of_le_one_left h.le (hπ.2 c).2
  · simp only [positiveRule, if_neg h, zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hπ.2 c).1 (le_of_not_gt h)

end ExperimentMoments

theorem T6_corrected_TT_proof {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (hS : Standing E) (PiSet : Set (C → ℝ)) (hPiSet : ∀ π ∈ PiSet, Admissible π)
    (hU : TreatedUnbiased E E.μ0 PiSet) :
    (∀ π ∈ PiSet, E.expectedTT π = (n : ℝ)*E.meanWelfare π ∧
      E.V π = E.meanWelfare π) ∧
    (∀ π, IsBest PiSet E.expectedTT π ↔ IsBest PiSet E.V π) ∧
    (∀ π, IsBest PiSet E.expectedTT π → regret PiSet E.V π = 0) ∧
    (PiSet = {π | Admissible π} → IsBest PiSet E.expectedTT (positiveRule E.τ)) := by
  have hid (π : C → ℝ) (hπ : π ∈ PiSet) :
      E.expectedTT π = (n : ℝ) * E.meanWelfare π ∧ E.V π = E.meanWelfare π := by
    refine ⟨?_, T6_actual_welfare E hS (hPiSet π hπ)⟩
    exact T6_actual_treated_score E hS (hPiSet π hπ)
      hS.means_measurable.1 hS.means_integrable.1 (hU π hπ)
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
    obtain ⟨hp, hmax⟩ := T6_positive_rule_integral_maximum (P := E.PX) (t := E.τ)
      (hS.means_measurable.2.sub hS.means_measurable.1)
      (hS.means_integrable.2.sub hS.means_integrable.1)
    have hmem : positiveRule E.τ ∈ PiSet := by rw [hAll]; exact hp
    apply (hbest _).mpr
    refine ⟨hmem, fun π hπ => ?_⟩
    rw [(hid π hπ).2, (hid _ hmem).2]
    exact hmax π (hPiSet π hπ)

example : type_of% @AronowAudit.P006.T6_corrected_TT := T6_corrected_TT_proof

end

end AronowAudit.P006.Wave1
