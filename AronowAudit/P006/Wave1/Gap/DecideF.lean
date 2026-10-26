import AronowAudit.P006.Wave1.Gap.GP006B3
import AronowAudit.P006.Wave1.Gap.RepairT6T7

/-!
P006-T7 with integrability of treated estimator residuals, rather than
integrability of the estimator at every evaluated covariate. Individual
weighted reward summands retain the stated integrability requirement.
-/

namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance instDecidableDecideF (p : Prop) : Decidable p := Classical.propDecidable p

/-- Project the estimator-free design fields from the zero-estimator experiment. -/
lemma DecideF_design {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n)
    (hDesign : Standing ({ E with μhat := fun _ _ _ => 0 } : Experiment Ω C n))
    (π : C → ℝ) (hπ : Admissible π) : RepairT6T7_Design E π where
  px_probability := hDesign.px_probability
  means_measurable := hDesign.means_measurable
  means_integrable := hDesign.means_integrable
  law_probability := hDesign.law_probability π hπ
  measurable_units := hDesign.measurable_units π hπ
  integrable_units := fun i =>
    ⟨(hDesign.integrable_units π hπ i).1, (hDesign.integrable_units π hπ i).2.1⟩
  covariate_law := hDesign.covariate_law π hπ
  conditional_means := hDesign.conditional_means π hπ
  bernoulli := hDesign.bernoulli π hπ
  ignorability := hDesign.ignorability π hπ

/-- Pull out the possibly unbounded weight only after obtaining an integrable
unweighted treated reward and an integrable weighted summand. -/
lemma DecideF_weighted_actual_score {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (hDesign : Standing ({ E with μhat := fun _ _ _ => 0 } : Experiment Ω C n))
    (g : C → ℝ) (hg : Measurable g)
    (hR : ∀ π, Admissible π → ∀ i, Integrable
      (fun ω => bit (E.T π i ω) *
        (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : TreatedUnbiased E E.μ0 {π | Admissible π})
    (hreward : ∀ π, Admissible π → ∀ i, Integrable
      (fun ω => (E.observed π ω i-E.μhat π ω (E.X i ω)) *
        bit (E.T π i ω) * g (E.X i ω)) (E.law π))
    (π : C → ℝ) (hπ : Admissible π) :
    E.expectedWeightedTT g π = (n : ℝ) * (∫ x, g x * E.τ x * π x ∂E.PX) := by
  have hS := DecideF_design E hDesign π hπ
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability
  have hs := RepairT6T7_actual_treated_summand E hS hπ
    hS.means_measurable.1 hS.means_integrable.1 (hR π hπ) (hU π hπ)
  let W : Fin n → Ω → ℝ := fun i ω =>
    (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω) * g (E.X i ω)
  have hmean (i : Fin n) : (∫ ω, W i ω ∂E.law π) =
      ∫ x, g x * E.τ x * π x ∂E.PX := by
    let U : Ω → ℝ := fun ω =>
      (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω)
    have hui : Integrable U (E.law π) := (hs i).1
    have heq : W i = fun ω => g (E.X i ω) * U ω := by
      funext ω
      exact mul_comm _ _
    have hgi : Integrable (fun ω => g (E.X i ω) * U ω) (E.law π) := by
      rw [← heq]
      exact hreward π hπ i
    have hgm : StronglyMeasurable[E.covariateSigma i] (fun ω => g (E.X i ω)) :=
      (hg.comp (comap_measurable (E.X i))).stronglyMeasurable
    have hpull := condExp_mul_of_stronglyMeasurable_left hgm hgi hui
    have hscore := (hs i).2
    have hce : (E.law π)[W i | E.covariateSigma i] =ᵐ[E.law π]
        fun ω => g (E.X i ω) * E.τ (E.X i ω) * π (E.X i ω) := by
      rw [heq]
      filter_upwards [hpull, hscore] with ω h₁ h₂
      simp only [Pi.mul_apply] at h₁
      change _ = π (E.X i ω) * E.τ (E.X i ω) at h₂
      rw [h₂] at h₁
      exact h₁.trans (by ring)
    have hm : E.covariateSigma i ≤ ‹MeasurableSpace Ω› :=
      (hS.measurable_units i).1.comap_le
    calc
      _ = ∫ ω, (E.law π)[W i | E.covariateSigma i] ω ∂E.law π :=
        (integral_condExp hm).symm
      _ = ∫ ω, g (E.X i ω) * E.τ (E.X i ω) * π (E.X i ω) ∂E.law π :=
        integral_congr_ae hce
      _ = _ := ((hS.covariate_law i).comp
        ((hg.mul (hS.means_measurable.2.sub hS.means_measurable.1)).mul hπ.1)).integral_eq
  change (∫ ω, ∑ i, W i ω ∂E.law π) = _
  rw [integral_finsetSum Finset.univ (fun i _ => hreward π hπ i)]
  simpa only [W, hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Corrected weighted alignment with only treated estimator residual
integrability and explicit per-unit weighted integrability assumptions. -/
theorem T7_corrected_weighted_alignment_treated_integrability
    {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {n : ℕ}
    (E : Experiment Ω C n)
    (hDesign : Standing ({ E with μhat := fun _ _ _ => 0 } : Experiment Ω C n))
    (g : C → ℝ) (hg : Measurable g) (hpos : ∀ x, 0 < g x)
    (hR : ∀ π, Admissible π → ∀ i, Integrable
      (fun ω => bit (E.T π i ω) *
        (E.μhat π ω (E.X i ω) - E.μ0 (E.X i ω))) (E.law π))
    (hU : TreatedUnbiased E E.μ0 {π | Admissible π})
    (hprod : Integrable (fun x => g x * E.τ x) E.PX)
    (hreward : ∀ π, Admissible π → ∀ i, Integrable
      (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) *
        bit (E.T π i ω) * g (E.X i ω)) (E.law π)) :
    (∀ π, Admissible π →
      E.expectedWeightedTT g π = (n : ℝ) * (∫ x, g x * E.τ x * π x ∂E.PX)) ∧
    IsBest {π | Admissible π} (E.expectedWeightedTT g) (positiveRule E.τ) ∧
    (∀ b, IsBest {π | Admissible π} (E.expectedWeightedTT g) b →
      (∀ᵐ x ∂E.PX, (0 < E.τ x → b x = 1) ∧ (E.τ x < 0 → b x = 0)) ∧
      E.V b = (∫ x, E.τ x * positiveRule E.τ x ∂E.PX) ∧
      IsBest {π | Admissible π} E.V b ∧
      regret {π | Admissible π} E.V b = 0) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr E.hn
  have ht : Measurable E.τ := hDesign.means_measurable.2.sub hDesign.means_measurable.1
  have hti : Integrable E.τ E.PX := hDesign.means_integrable.2.sub hDesign.means_integrable.1
  have hp : Admissible (positiveRule E.τ) := T7_positiveRule_admissible E.τ ht
  have hscore := DecideF_weighted_actual_score E hDesign g hg hR hU hreward
  have hbest : IsBest {π | Admissible π} (E.expectedWeightedTT g) (positiveRule E.τ) := by
    refine ⟨hp, ?_⟩
    intro π hπ
    rw [hscore π hπ, hscore _ hp]
    exact mul_le_mul_of_nonneg_left
      (T7_integral_maximum E.PX E.τ g ht hg (fun x => (hpos x).le) hprod π hπ) hn.le
  refine ⟨hscore, hbest, ?_⟩
  intro b hb
  have hba : Admissible b := hb.1
  have heq : (∫ x, g x * E.τ x * b x ∂E.PX) =
      ∫ x, g x * E.τ x * positiveRule E.τ x ∂E.PX := by
    have h₁ := hb.2 (positiveRule E.τ) hp
    have h₂ := hbest.2 b hba
    rw [hscore b hba, hscore _ hp] at h₁ h₂
    exact mul_left_cancel₀ hn.ne' (le_antisymm h₂ h₁)
  have hsign := T7_zero_deficit_characterization E.PX E.τ g ht hg hpos hprod b hba heq
  have hae : (fun x => b x * E.τ x) =ᵐ[E.PX]
      (fun x => E.τ x * positiveRule E.τ x) := by
    filter_upwards [hsign] with x hx
    rcases lt_trichotomy 0 (E.τ x) with h | h | h
    · rw [hx.1 h]
      simp [positiveRule, h]
    · simp [← h]
    · rw [hx.2 h]
      simp [positiveRule, not_lt.mpr h.le]
  have hvalue : E.V b = ∫ x, E.τ x * positiveRule E.τ x ∂E.PX := by
    rw [RepairT6T7_actual_welfare E (DecideF_design E hDesign b hba) hba, Experiment.meanWelfare]
    exact integral_congr_ae hae
  have hVbest : IsBest {π | Admissible π} E.V b := by
    refine ⟨hba, ?_⟩
    intro π hπ
    rw [RepairT6T7_actual_welfare E (DecideF_design E hDesign π hπ) hπ, Experiment.meanWelfare, hvalue]
    have h := T7_integral_maximum E.PX E.τ (fun _ => 1) ht measurable_const
      (fun _ => zero_le_one) (by simpa only [one_mul] using hti) π hπ
    simpa only [one_mul, mul_comm] using h
  refine ⟨hsign, hvalue, hVbest, ?_⟩
  rw [regret, bestValue_eq hVbest, sub_self]

end

end AronowAudit.P006.Wave1
