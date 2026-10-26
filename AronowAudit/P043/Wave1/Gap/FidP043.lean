import AronowAudit.P043.P043_Formalization
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace AronowAudit.P043.Wave1

/-- An arbitrary population law with an independent Bernoulli assignment.
The first coordinate is population type; the second is assignment. -/
def randomizedLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) : Measure (Ω × Bool) :=
  μ.prod (bernoulliMeasure true false p)

/-- Conditional mean of the consistent observed response f(T, type),
conditioned on a positive-probability assignment arm in the theorem. -/
def lawArmMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (t : Bool)
    (f : Bool → Ω → ℝ) : ℝ :=
  (∫ z in {z : Ω × Bool | z.2 = t}, f z.2 z.1 ∂(randomizedLaw μ p)) /
    ((randomizedLaw μ p) {z : Ω × Bool | z.2 = t}).toReal

def lawContrast {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (f : Bool → Ω → ℝ) : ℝ :=
  lawArmMean μ p true f - lawArmMean μ p false f

def lawReducedForm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (m : MediationModel Ω) : ℝ :=
  lawContrast μ p (observedSupport m)

def lawMediated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : MediationModel Ω) : ℝ :=
  ∫ i, m.support false (m.knowledge true i) i -
    m.support false (m.knowledge false i) i ∂μ

def lawDirect {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : MediationModel Ω) : ℝ :=
  ∫ i, m.support true (m.knowledge true i) i -
    m.support false (m.knowledge true i) i ∂μ

/-- Exactly the five finite expectations listed in the target.
In particular, S(1,K(0)) is not required to be integrable. -/
def IntegrableMediationPotentials {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : MediationModel Ω) : Prop :=
  Integrable (m.knowledge false) μ ∧
  Integrable (m.knowledge true) μ ∧
  Integrable (fun i => m.support false (m.knowledge false i) i) μ ∧
  Integrable (fun i => m.support false (m.knowledge true i) i) μ ∧
  Integrable (fun i => m.support true (m.knowledge true i) i) μ

def MediationLawClaims {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (m : MediationModel Ω) : Prop :=
  lawReducedForm μ p m =
    (∫ i, m.support true (m.knowledge true i) i ∂μ) -
      (∫ i, m.support false (m.knowledge false i) i ∂μ) ∧
  lawReducedForm μ p m = lawMediated μ m + lawDirect μ m ∧
  (lawReducedForm μ p m ≥ lawMediated μ m ↔ lawDirect μ m ≥ 0) ∧
  (lawReducedForm μ p m > lawMediated μ m ↔ lawDirect μ m > 0) ∧
  (lawDirect μ m ≥ 0 → lawReducedForm μ p m ≥ lawMediated μ m) ∧
  (lawDirect μ m ≥ 0 → lawReducedForm μ p m ≤ 0 → lawMediated μ m ≤ 0) ∧
  (lawDirect μ m ≥ 0 → lawReducedForm μ p m = 0 → lawMediated μ m ≤ 0)

def LinearMediationLawClaims {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : unitInterval) (α a σ b c : ℝ)
    (u₁ u₂ : Ω → ℝ) : Prop :=
  lawContrast μ p (linearModel α a σ b c u₁ u₂).knowledge = a ∧
  lawMediated μ (linearModel α a σ b c u₁ u₂) = a * b ∧
  lawDirect μ (linearModel α a σ b c u₁ u₂) = c ∧
  lawReducedForm μ p (linearModel α a σ b c u₁ u₂) = a * b + c ∧
  (lawReducedForm μ p (linearModel α a σ b c u₁ u₂) ≥
    lawMediated μ (linearModel α a σ b c u₁ u₂) ↔ c ≥ 0) ∧
  (∀ (n : ℕ) (d : Fin n → ℝ), c = ∑ j, d j →
    (lawReducedForm μ p (linearModel α a σ b c u₁ u₂) ≥
      lawMediated μ (linearModel α a σ b c u₁ u₂) ↔ 0 ≤ ∑ j, d j))

instance mediationRepair_randomizedLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : unitInterval) :
    IsProbabilityMeasure (randomizedLaw μ p) := by
  unfold randomizedLaw
  infer_instance

lemma mediationRepair_arm_set {Ω : Type*} (t : Bool) :
    {z : Ω × Bool | z.2 = t} = Set.univ ×ˢ {t} := by
  ext z
  simp

lemma mediationRepair_bernoulli_arm_probability (p : unitInterval) (t : Bool) :
    (bernoulliMeasure true false p).real {t} = armProb (p : ℝ) t := by
  cases t <;>
    simp [bernoulliMeasure_real_apply p (measurableSet_singleton _), armProb]

lemma mediationRepair_arm_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : unitInterval) (t : Bool) :
    ((randomizedLaw μ p) {z : Ω × Bool | z.2 = t}).toReal =
      armProb (p : ℝ) t := by
  change (μ.prod (bernoulliMeasure true false p)).real _ = _
  rw [mediationRepair_arm_set, measureReal_prod_prod]
  simp [mediationRepair_bernoulli_arm_probability]


/-- Restrict the observed response to its assignment arm, then integrate the
fixed potential branch against the restricted product law. -/
lemma mediationRepair_arm_numerator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : unitInterval) (t : Bool) (f : Bool → Ω → ℝ)
    (hf : Integrable (f t) μ) :
    (∫ z in {z : Ω × Bool | z.2 = t}, f z.2 z.1 ∂(randomizedLaw μ p)) =
      armProb (p : ℝ) t * ∫ i, f t i ∂μ := by
  have he : MeasurableSet {z : Ω × Bool | z.2 = t} :=
    measurable_snd (measurableSet_singleton t)
  calc
    _ = ∫ z in {z : Ω × Bool | z.2 = t}, f t z.1 ∂(randomizedLaw μ p) := by
      apply setIntegral_congr_fun he
      intro z hz
      change z.2 = t at hz
      change f z.2 z.1 = f t z.1
      rw [hz]
    _ = ∫ z : Ω × Bool, f t z.1
        ∂(μ.prod ((bernoulliMeasure true false p).restrict {t})) := by
      rw [mediationRepair_arm_set, randomizedLaw, ← Measure.prod_restrict,
        Measure.restrict_univ]
    _ = armProb (p : ℝ) t * ∫ i, f t i ∂μ := by
      rw [integral_prod _ (hf.comp_fst _)]
      simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
      rw [integral_const_mul, mediationRepair_bernoulli_arm_probability]

lemma mediationRepair_arm_mean_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : unitInterval) (hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1)
    (t : Bool) (f : Bool → Ω → ℝ) (hf : Integrable (f t) μ) :
    lawArmMean μ p t f = ∫ i, f t i ∂μ := by
  have hq : armProb (p : ℝ) t ≠ 0 := by
    cases t
    · exact ne_of_gt (sub_pos.mpr hp.2)
    · exact ne_of_gt hp.1
  rw [lawArmMean, mediationRepair_arm_numerator μ p t f hf,
    mediationRepair_arm_probability, mul_div_cancel_left₀ _ hq]

lemma mediationRepair_contrast_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : unitInterval) (hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1)
    (f : Bool → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) :
    lawContrast μ p f = (∫ i, f true i ∂μ) - ∫ i, f false i ∂μ := by
  rw [lawContrast, mediationRepair_arm_mean_eq μ p hp true f (hf true),
    mediationRepair_arm_mean_eq μ p hp false f (hf false)]

/-- Identification and the mediation comparison require exactly the five
finite expectations specified by the hypotheses. -/
lemma mediationRepair_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : unitInterval) (hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1)
    (m : MediationModel Ω) (hint : IntegrableMediationPotentials μ m) :
    MediationLawClaims μ p m := by
  rcases hint with ⟨_hk₀, _hk₁, hC, hB, hA⟩
  have hobs : ∀ t, Integrable (observedSupport m t) μ := by
    intro t
    cases t
    · exact hC
    · exact hA
  have hid : lawReducedForm μ p m =
      (∫ i, m.support true (m.knowledge true i) i ∂μ) -
        ∫ i, m.support false (m.knowledge false i) i ∂μ :=
    mediationRepair_contrast_eq μ p hp (observedSupport m) hobs
  have hdecomp : lawReducedForm μ p m = lawMediated μ m + lawDirect μ m := by
    rw [hid, lawMediated, lawDirect, integral_sub hB hC, integral_sub hA hB]
    ring
  unfold MediationLawClaims
  refine ⟨hid, hdecomp, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith
  · intro h
    linarith
  · intro h htotal
    linarith
  · intro h htotal
    linarith

lemma mediationRepair_linear_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (α a σ b c : ℝ) (u₁ u₂ : Ω → ℝ)
    (hu₁ : Integrable u₁ μ) (hu₂ : Integrable u₂ μ) :
    IntegrableMediationPotentials μ (linearModel α a σ b c u₁ u₂) := by
  have hk (t : Bool) :
      Integrable ((linearModel α a σ b c u₁ u₂).knowledge t) μ :=
    (integrable_const (α + a * assignment t)).add hu₁
  have hs (t s : Bool) : Integrable
      (fun i => (linearModel α a σ b c u₁ u₂).support t
        ((linearModel α a σ b c u₁ u₂).knowledge s i) i) μ :=
    (((integrable_const σ).add ((hk s).const_mul b)).add
      (integrable_const (c * assignment t))).add hu₂
  exact ⟨hk false, hk true, hs false false, hs false true, hs true true⟩

lemma mediationRepair_linear_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : unitInterval) (hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1)
    (α a σ b c : ℝ) (u₁ u₂ : Ω → ℝ)
    (hu₁ : Integrable u₁ μ) (hu₂ : Integrable u₂ μ) :
    LinearMediationLawClaims μ p α a σ b c u₁ u₂ := by
  have hint := mediationRepair_linear_integrable μ α a σ b c u₁ u₂ hu₁ hu₂
  have hk : lawContrast μ p (linearModel α a σ b c u₁ u₂).knowledge = a := by
    rw [mediationRepair_contrast_eq μ p hp _ (fun t => by
      cases t
      · exact hint.1
      · exact hint.2.1), ← integral_sub hint.2.1 hint.1]
    calc
      _ = ∫ _ : Ω, a ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with i
        simp [linearModel, assignment]
      _ = a := by simp
  have hm : lawMediated μ (linearModel α a σ b c u₁ u₂) = a * b := by
    unfold lawMediated
    calc
      _ = ∫ _ : Ω, a * b ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with i
        simp [linearModel, assignment]
        ring
      _ = a * b := by simp
  have hd : lawDirect μ (linearModel α a σ b c u₁ u₂) = c := by
    unfold lawDirect
    calc
      _ = ∫ _ : Ω, c ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with i
        simp [linearModel, assignment]
      _ = c := by simp
  have hgen := mediationRepair_comparison μ p hp
    (linearModel α a σ b c u₁ u₂) hint
  have ht : lawReducedForm μ p (linearModel α a σ b c u₁ u₂) = a * b + c := by
    rw [hgen.2.1, hm, hd]
  have hsign : (lawReducedForm μ p (linearModel α a σ b c u₁ u₂) ≥
      lawMediated μ (linearModel α a σ b c u₁ u₂) ↔ c ≥ 0) := by
    rw [ht, hm]
    constructor <;> intro h <;> linarith
  refine ⟨hk, hm, hd, ht, hsign, ?_⟩
  intro n d hc
  rw [hsign, ← hc]

/-- P043-T2: the complete mediation repair for an arbitrary integrable
population law under independent, nondegenerate Bernoulli assignment. -/
theorem mediation_repair_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : unitInterval) (hp : 0 < (p : ℝ) ∧ (p : ℝ) < 1)
    (m : MediationModel Ω) (hint : IntegrableMediationPotentials μ m) :
    MediationLawClaims μ p m ∧
    (∀ i, m.support true (m.knowledge true i) i -
      m.support false (m.knowledge false i) i =
        (m.support true (m.knowledge true i) i -
          m.support false (m.knowledge true i) i) +
        (m.support false (m.knowledge true i) i -
          m.support false (m.knowledge false i) i)) ∧
    (∀ (α a σ b c : ℝ) (u₁ u₂ : Ω → ℝ),
      Integrable u₁ μ → Integrable u₂ μ →
      LinearMediationLawClaims μ p α a σ b c u₁ u₂ ∧
      (0 < a →
        lawReducedForm μ p (linearModel α a σ b c u₁ u₂) / a = b + c / a ∧
        (lawReducedForm μ p (linearModel α a σ b c u₁ u₂) / a ≥ b ↔ c ≥ 0))) ∧
    (∀ (n : ℕ) (d : Fin n → ℝ), (∀ j, 0 ≤ d j) → 0 ≤ ∑ j, d j) ∧
    (∃ d : Fin 2 → ℝ, 0 ≤ ∑ j, d j ∧ ¬ (∀ j, 0 ≤ d j)) := by
  refine ⟨mediationRepair_comparison μ p hp m hint, mediation_unit_identity m,
    ?_, ?_, net_channels_not_necessary⟩
  · intro α a σ b c u₁ u₂ hu₁ hu₂
    have h := mediationRepair_linear_formula μ p hp α a σ b c u₁ u₂ hu₁ hu₂
    refine ⟨h, ?_⟩
    intro ha
    rw [h.2.2.2.1]
    exact linear_iv_direction a b c ha
  · intro n d
    exact net_channels d

end AronowAudit.P043.Wave1
end

