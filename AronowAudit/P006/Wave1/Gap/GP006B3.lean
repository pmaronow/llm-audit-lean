import AronowAudit.P006.P006_CounterfactualMetrics
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.IdentDistrib



namespace AronowAudit.P006.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance instDecidableGP006B3 (p : Prop) : Decidable p := Classical.propDecidable p

/-! P006-T7: bounded-factor and conditional-moment lemmas. -/

lemma T7_policy_norm {C : Type*} [MeasurableSpace C] {π : C → ℝ}
    (hπ : Admissible π) (x : C) : ‖π x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hπ.2 x).1]
  exact (hπ.2 x).2

lemma T7_policy_mul {C : Type*} [MeasurableSpace C] {P : Measure C}
    {f π : C → ℝ} (hf : Integrable f P) (hπ : Admissible π) :
    Integrable (fun x => π x * f x) P :=
  hf.bdd_mul hπ.1.aestronglyMeasurable (ae_of_all _ (T7_policy_norm hπ))

lemma T7_bit_norm (t : Bool) : ‖bit t‖ ≤ 1 := by
  cases t <;> norm_num [bit]

lemma T7_bit_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {T : Ω → Bool} {f : Ω → ℝ} (hT : Measurable T) (hf : Integrable f P) :
    Integrable (fun ω => bit (T ω) * f ω) P :=
  hf.bdd_mul ((measurable_of_finite bit).comp hT).aestronglyMeasurable
    (ae_of_all _ (fun ω => T7_bit_norm (T ω)))

/-- Extend the indicator-valued conditional independence premise to an
integrable Borel function of the outcome pair. Approximation takes place on
the outcome space, so no regularity assumption on Ω is needed. -/
lemma T7_binary_conditional_moment_extension
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (B p : Ω → ℝ) (hB : Measurable[mΩ] B) (hp : StronglyMeasurable[m] p)
    (hBn : ∀ ω, ‖B ω‖ ≤ 1) (hpn : ∀ ω, ‖p ω‖ ≤ 1)
    (Z : Ω → ℝ × ℝ) (hZ : Measurable[mΩ] Z)
    (hI : ∀ A : Set (ℝ × ℝ), MeasurableSet A →
      P[fun ω => B ω * A.indicator (fun _ => (1 : ℝ)) (Z ω) | m]
        =ᵐ[P] fun ω => p ω *
          P[fun η => A.indicator (fun _ => (1 : ℝ)) (Z η) | m] ω)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hfi : Integrable (fun ω => f (Z ω)) P) :
    P[fun ω => B ω * f (Z ω) | m]
      =ᵐ[P] fun ω => p ω * P[fun η => f (Z η) | m] ω := by
  letI : MeasurableSpace Ω := mΩ
  have hpm : AEStronglyMeasurable p P := (hp.mono hm).aestronglyMeasurable
  have intB {v : Ω → ℝ} (hv : Integrable v P) :
      Integrable (fun ω => B ω * v ω) P :=
    hv.bdd_mul hB.aestronglyMeasurable (ae_of_all _ hBn)
  have intp {v : Ω → ℝ} (hv : Integrable v P) :
      Integrable (fun ω => p ω * v ω) P :=
    hv.bdd_mul hpm (ae_of_all _ hpn)
  have hsimp (s : SimpleFunc (ℝ × ℝ) ℝ) :
      P[fun ω => B ω * s (Z ω) | m] =ᵐ[P]
        P[fun ω => p ω * s (Z ω) | m] := by
    induction s using SimpleFunc.induction with
    | @const c A hA =>
      let v : Ω → ℝ := fun ω => A.indicator (fun _ => (1 : ℝ)) (Z ω)
      have hv : Integrable v P :=
        (integrable_const (1 : ℝ)).mono
          (((measurable_const.indicator hA).comp hZ).aestronglyMeasurable)
          (ae_of_all _ (fun ω => by
            by_cases h : Z ω ∈ A <;> simp [v, h]))
      have hbase : P[fun ω => B ω * v ω | m] =ᵐ[P]
          P[fun ω => p ω * v ω | m] :=
        (hI A hA).trans
          (condExp_mul_of_stronglyMeasurable_left hp (intp hv) hv).symm
      have hleft := condExp_smul (μ := P) (c : ℝ) (fun ω => B ω * v ω) m
      have hright := condExp_smul (μ := P) (c : ℝ) (fun ω => p ω * v ω) m
      have heqB : (fun ω => B ω *
          (SimpleFunc.piecewise A hA (SimpleFunc.const _ c)
            (SimpleFunc.const _ 0)) (Z ω)) =
          c • (fun ω => B ω * v ω) := by
        funext ω
        by_cases h : Z ω ∈ A <;> simp [v, h, mul_comm, mul_left_comm]
      have heqp : (fun ω => p ω *
          (SimpleFunc.piecewise A hA (SimpleFunc.const _ c)
            (SimpleFunc.const _ 0)) (Z ω)) =
          c • (fun ω => p ω * v ω) := by
        funext ω
        by_cases h : Z ω ∈ A <;> simp [v, h, mul_comm, mul_left_comm]
      rw [heqB, heqp]
      filter_upwards [hleft, hright, hbase] with ω h₁ h₂ h₃
      simp only [Pi.smul_apply, smul_eq_mul] at h₁ h₂
      exact h₁.trans ((congrArg (fun r : ℝ => c * r) h₃).trans h₂.symm)
    | @add s t hdis hs ht =>
      have hsi : Integrable (fun ω => s (Z ω)) P :=
        (s.comp Z hZ).integrable_of_isFiniteMeasure
      have hti : Integrable (fun ω => t (Z ω)) P :=
        (t.comp Z hZ).integrable_of_isFiniteMeasure
      have h₁ := condExp_add (intB hsi) (intB hti) m
      have h₂ := condExp_add (intp hsi) (intp hti) m
      simp only [SimpleFunc.coe_add, Pi.add_apply, mul_add]
      filter_upwards [h₁, h₂, hs, ht] with ω h₁ h₂ h₃ h₄
      simp only [Pi.add_apply] at h₁ h₂
      exact h₁.trans ((congrArg₂ (fun r q : ℝ => r + q) h₃ h₄).trans h₂.symm)
  let s : ℕ → SimpleFunc (ℝ × ℝ) ℝ :=
    SimpleFunc.approxOn f hf Set.univ 0 (Set.mem_univ 0)
  have hsn (k : ℕ) (ω : Ω) : ‖s k (Z ω)‖ ≤ ‖f (Z ω)‖ + ‖f (Z ω)‖ :=
    SimpleFunc.norm_approxOn_zero_le hf (Set.mem_univ 0) (Z ω) k
  have hsl (ω : Ω) : Tendsto (fun k => s k (Z ω)) atTop (𝓝 (f (Z ω))) :=
    SimpleFunc.tendsto_approxOn hf (Set.mem_univ 0) (by simp)
  have hlimit : P[fun ω => B ω * f (Z ω) | m] =ᵐ[P]
      P[fun ω => p ω * f (Z ω) | m] := by
    apply tendsto_condExp_unique
      (fun k ω => B ω * s k (Z ω)) (fun k ω => p ω * s k (Z ω))
      (fun ω => B ω * f (Z ω)) (fun ω => p ω * f (Z ω))
      (fun k => intB ((s k).comp Z hZ).integrable_of_isFiniteMeasure)
      (fun k => intp ((s k).comp Z hZ).integrable_of_isFiniteMeasure)
      (ae_of_all _ (fun ω => tendsto_const_nhds.mul (hsl ω)))
      (ae_of_all _ (fun ω => tendsto_const_nhds.mul (hsl ω)))
      (fun ω => ‖f (Z ω)‖ + ‖f (Z ω)‖) (hfi.norm.add hfi.norm)
      (fun ω => ‖f (Z ω)‖ + ‖f (Z ω)‖) (hfi.norm.add hfi.norm)
      (fun k => ae_of_all _ (fun ω => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hBn ω)).trans (hsn k ω)))
      (fun k => ae_of_all _ (fun ω => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hpn ω)).trans (hsn k ω)))
      (fun k => hsimp (s k))
  exact hlimit.trans (condExp_mul_of_stronglyMeasurable_left hp (intp hfi) hfi)

lemma T7_outcome_condExp {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hS : Standing E)
    (π : C → ℝ) (hπ : Admissible π) (i : Fin n) :
    ((E.law π)[fun ω => bit (E.T π i ω) * E.Y0 i ω | E.covariateSigma i]
      =ᵐ[E.law π] fun ω => π (E.X i ω) * E.μ0 (E.X i ω)) ∧
    ((E.law π)[fun ω => bit (E.T π i ω) * E.Y1 i ω | E.covariateSigma i]
      =ᵐ[E.law π] fun ω => π (E.X i ω) * E.μ1 (E.X i ω)) := by
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  have hu := hS.measurable_units π hπ i
  have hi := hS.integrable_units π hπ i
  have hp : StronglyMeasurable[E.covariateSigma i] (fun ω => π (E.X i ω)) :=
    (hπ.1.comp (comap_measurable (E.X i))).stronglyMeasurable
  have hext := T7_binary_conditional_moment_extension (E.law π)
    (E.covariateSigma i) hu.1.comap_le (fun ω => bit (E.T π i ω))
    (fun ω => π (E.X i ω)) ((measurable_of_finite bit).comp hu.2.2.2)
    hp (fun ω => T7_bit_norm _) (fun ω => T7_policy_norm hπ _)
    (fun ω => (E.Y0 i ω, E.Y1 i ω)) (hu.2.1.prodMk hu.2.2.1)
    (hS.ignorability π hπ i)
  constructor
  · have he := hext Prod.fst measurable_fst hi.1
    filter_upwards [he, (hS.conditional_means π hπ i).1] with ω h₁ h₂
    exact h₁.trans (congrArg (fun z => π (E.X i ω) * z) h₂)
  · have he := hext Prod.snd measurable_snd hi.2.1
    filter_upwards [he, (hS.conditional_means π hπ i).2] with ω h₁ h₂
    exact h₁.trans (congrArg (fun z => π (E.X i ω) * z) h₂)

/-- The conditional score is retained, rather than merely its integral;
this refinement permits the unbounded weight in T7. -/
lemma T7_treated_score_condExp {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hS : Standing E)
    (a : C → ℝ) (ha : Measurable a) (hai : Integrable a E.PX)
    (π : C → ℝ) (hπ : Admissible π) (i : Fin n)
    (hU : (E.law π)[fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω)) | E.covariateSigma i]
        =ᵐ[E.law π] fun _ => (0 : ℝ)) :
    (E.law π)[fun ω => bit (E.T π i ω) *
      (E.Y1 i ω - E.μhat π ω (E.X i ω)) | E.covariateSigma i]
      =ᵐ[E.law π] fun ω => π (E.X i ω) * (E.μ1 (E.X i ω) - a (E.X i ω)) := by
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  have hmX := (hS.measurable_units π hπ i).1
  have hmT := (hS.measurable_units π hπ i).2.2.2
  have hi := hS.integrable_units π hπ i
  have haiX : Integrable (fun ω => a (E.X i ω)) (E.law π) :=
    ((hS.covariate_law π hπ i).comp ha).integrable_iff.mpr hai
  have hba := T7_bit_mul hmT haiX
  have hbh := T7_bit_mul hmT hi.2.2
  have hby := T7_bit_mul hmT hi.2.1
  have hpa : StronglyMeasurable[E.covariateSigma i] (fun ω => a (E.X i ω)) :=
    (ha.comp (comap_measurable (E.X i))).stronglyMeasurable
  have hpull : (E.law π)[fun ω => bit (E.T π i ω) * a (E.X i ω) |
      E.covariateSigma i] =ᵐ[E.law π]
      fun ω => a (E.X i ω) * π (E.X i ω) := by
    have hba' : Integrable (fun ω => a (E.X i ω) * bit (E.T π i ω))
        (E.law π) := by simpa only [mul_comm] using hba
    have hbit : Integrable (fun ω => bit (E.T π i ω)) (E.law π) := by
      simpa only [mul_one] using T7_bit_mul hmT (integrable_const (1 : ℝ))
    have hpull := condExp_mul_of_stronglyMeasurable_left hpa hba' hbit
    filter_upwards [hpull, hS.bernoulli π hπ i] with ω h₁ h₂
    simpa only [Pi.mul_def, Pi.mul_apply, h₂, mul_comm] using h₁
  have hsubH := condExp_sub hbh hba (E.covariateSigma i)
  have hsubY := condExp_sub hby hbh (E.covariateSigma i)
  have hdiffH : ((fun ω => bit (E.T π i ω) * E.μhat π ω (E.X i ω)) -
      (fun ω => bit (E.T π i ω) * a (E.X i ω))) =
      (fun ω => bit (E.T π i ω) * (E.μhat π ω (E.X i ω) - a (E.X i ω))) := by
    funext ω
    simp only [Pi.sub_apply, mul_sub]
  have hdiffY : ((fun ω => bit (E.T π i ω) * E.Y1 i ω) -
      (fun ω => bit (E.T π i ω) * E.μhat π ω (E.X i ω))) =
      (fun ω => bit (E.T π i ω) * (E.Y1 i ω - E.μhat π ω (E.X i ω))) := by
    funext ω
    simp only [Pi.sub_apply, mul_sub]
  rw [hdiffH] at hsubH
  rw [hdiffY] at hsubY
  have hUH : (E.law π)[fun ω => bit (E.T π i ω) * E.μhat π ω (E.X i ω) |
      E.covariateSigma i] =ᵐ[E.law π]
      fun ω => a (E.X i ω) * π (E.X i ω) := by
    filter_upwards [hsubH, hU, hpull] with ω h₁ h₂ h₃
    simp only [Pi.sub_apply] at h₁
    linarith
  filter_upwards [hsubY, hUH, (T7_outcome_condExp E hS π hπ i).2] with ω h₁ h₂ h₃
  simp only [Pi.sub_apply] at h₁
  rw [h₂, h₃] at h₁
  nlinarith [h₁]

lemma T7_actual_welfare {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hS : Standing E)
    (π : C → ℝ) (hπ : Admissible π) :
    E.V π = ∫ x, π x * E.τ x ∂E.PX := by
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  let i : Fin n := ⟨0, E.hn⟩
  have hu := hS.measurable_units π hπ i
  have hi := hS.integrable_units π hπ i
  have hm : E.covariateSigma i ≤ ‹MeasurableSpace Ω› := hu.1.comap_le
  have h₀ := T7_bit_mul hu.2.2.2 hi.1
  have h₁ := T7_bit_mul hu.2.2.2 hi.2.1
  have hc := condExp_sub h₁ h₀ (E.covariateSigma i)
  have hdiff : ((fun ω => bit (E.T π i ω) * E.Y1 i ω) -
      (fun ω => bit (E.T π i ω) * E.Y0 i ω)) =
      (fun ω => bit (E.T π i ω) * (E.Y1 i ω - E.Y0 i ω)) := by
    funext ω
    simp only [Pi.sub_apply, mul_sub]
  rw [hdiff] at hc
  have hout := T7_outcome_condExp E hS π hπ i
  have hce : (E.law π)[fun ω => bit (E.T π i ω) *
      (E.Y1 i ω - E.Y0 i ω) | E.covariateSigma i] =ᵐ[E.law π]
      fun ω => π (E.X i ω) * E.τ (E.X i ω) := by
    filter_upwards [hc, hout.1, hout.2] with ω h h₀ h₁
    simpa only [Pi.sub_apply, h₀, h₁, Experiment.τ, mul_sub] using h
  have hsutva : (fun ω => E.observed π ω i - E.Y0 i ω) =
      (fun ω => bit (E.T π i ω) * (E.Y1 i ω - E.Y0 i ω)) := by
    funext ω
    cases ht : E.T π i ω <;> simp [Experiment.observed, ht, bit]
  change (∫ ω, E.observed π ω i - E.Y0 i ω ∂E.law π) = _
  rw [hsutva, ← integral_condExp hm, integral_congr_ae hce]
  exact ((hS.covariate_law π hπ i).comp
    (hπ.1.mul (hS.means_measurable.2.sub hS.means_measurable.1))).integral_eq

lemma T7_actual_treated_score {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hS : Standing E)
    (a : C → ℝ) (ha : Measurable a) (hai : Integrable a E.PX)
    (π : C → ℝ) (hπ : Admissible π)
    (hU : ∀ i, (E.law π)[fun ω => bit (E.T π i ω) *
      (E.μhat π ω (E.X i ω) - a (E.X i ω)) | E.covariateSigma i]
        =ᵐ[E.law π] fun _ => (0 : ℝ)) :
    E.expectedTT π = (n : ℝ) * (∫ x, π x * (E.μ1 x - a x) ∂E.PX) := by
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  have hi (i : Fin n) : Integrable (fun ω => bit (E.T π i ω) *
      (E.Y1 i ω - E.μhat π ω (E.X i ω))) (E.law π) :=
    T7_bit_mul (hS.measurable_units π hπ i).2.2.2
      ((hS.integrable_units π hπ i).2.1.sub (hS.integrable_units π hπ i).2.2)
  have hmean (i : Fin n) : (∫ ω, bit (E.T π i ω) *
      (E.Y1 i ω - E.μhat π ω (E.X i ω)) ∂E.law π) =
      ∫ x, π x * (E.μ1 x - a x) ∂E.PX := by
    have hm : E.covariateSigma i ≤ ‹MeasurableSpace Ω› :=
      (hS.measurable_units π hπ i).1.comap_le
    have hce := T7_treated_score_condExp E hS a ha hai π hπ i (hU i)
    calc
      _ = ∫ ω, (E.law π)[fun ω => bit (E.T π i ω) *
          (E.Y1 i ω - E.μhat π ω (E.X i ω)) | E.covariateSigma i] ω ∂E.law π :=
        (integral_condExp hm).symm
      _ = ∫ ω, π (E.X i ω) * (E.μ1 (E.X i ω) - a (E.X i ω)) ∂E.law π :=
        integral_congr_ae hce
      _ = _ := ((hS.covariate_law π hπ i).comp
        (hπ.1.mul (hS.means_measurable.2.sub ha))).integral_eq
  have hsutva : (fun ω => wWeightedTT (E.μhat π ω) (fun _ => 1)
      (fun i => E.X i ω) (fun i => E.T π i ω) (E.observed π ω)) =
      fun ω => ∑ i, bit (E.T π i ω) * (E.Y1 i ω - E.μhat π ω (E.X i ω)) := by
    funext ω
    unfold wWeightedTT
    apply Finset.sum_congr rfl
    intro i _
    cases ht : E.T π i ω <;> simp [Experiment.observed, ht, bit]
  unfold Experiment.expectedTT Experiment.expectedWeightedTT
  rw [hsutva, integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]


lemma T7_positiveRule_admissible {C : Type*} [MeasurableSpace C]
    (t : C → ℝ) (ht : Measurable t) : Admissible (positiveRule t) := by
  constructor
  · exact Measurable.ite (measurableSet_lt measurable_const ht) measurable_const measurable_const
  · intro x
    by_cases h : 0 < t x <;> simp [positiveRule, h]

lemma T7_integral_maximum {C : Type*} [MeasurableSpace C] (P : Measure C)
    (t g : C → ℝ) (ht : Measurable t) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hgt : Integrable (fun x => g x * t x) P)
    (π : C → ℝ) (hπ : Admissible π) :
    (∫ x, g x * t x * π x ∂P) ≤
      ∫ x, g x * t x * positiveRule t x ∂P := by
  have hi : Integrable (fun x => g x * t x * π x) P := by
    simpa only [mul_comm] using T7_policy_mul hgt hπ
  have hi' : Integrable (fun x => g x * t x * positiveRule t x) P := by
    simpa only [mul_comm] using T7_policy_mul hgt (T7_positiveRule_admissible t ht)
  apply integral_mono hi hi'
  intro x
  have h := pointwise_policy_gain_le (t x) (π x) (hπ.2 x)
  have h' := mul_le_mul_of_nonneg_left h (hg0 x)
  simpa only [positivePart, positiveRule, mul_assoc] using h'

/-- The zero-deficit argument is packaged by Mathlib's integral equality
criterion, whose proof integrates the nonnegative difference. -/
lemma T7_zero_deficit_characterization {C : Type*} [MeasurableSpace C]
    (P : Measure C) (t g : C → ℝ) (ht : Measurable t) (hg : Measurable g)
    (hpos : ∀ x, 0 < g x) (hgt : Integrable (fun x => g x * t x) P)
    (b : C → ℝ) (hb : Admissible b)
    (heq : (∫ x, g x * t x * b x ∂P) =
      ∫ x, g x * t x * positiveRule t x ∂P) :
    ∀ᵐ x ∂P, (0 < t x → b x = 1) ∧ (t x < 0 → b x = 0) := by
  have hi : Integrable (fun x => g x * t x * b x) P := by
    simpa only [mul_comm] using T7_policy_mul hgt hb
  have hi' : Integrable (fun x => g x * t x * positiveRule t x) P := by
    simpa only [mul_comm] using T7_policy_mul hgt (T7_positiveRule_admissible t ht)
  have hle : (fun x => g x * t x * b x) ≤ᵐ[P]
      (fun x => g x * t x * positiveRule t x) := by
    apply ae_of_all
    intro x
    have h := mul_le_mul_of_nonneg_left
      (pointwise_policy_gain_le (t x) (b x) (hb.2 x)) (hpos x).le
    simpa only [positivePart, positiveRule, mul_assoc] using h
  have hzero := (integral_eq_iff_of_ae_le hi hi' hle).mp heq
  filter_upwards [hzero] with x hx
  constructor
  · intro htx
    have hc := mul_left_cancel₀ (mul_ne_zero (hpos x).ne' htx.ne') hx
    simpa only [positiveRule, if_pos htx] using hc
  · intro htx
    have hc := mul_left_cancel₀ (mul_ne_zero (hpos x).ne' htx.ne) hx
    simpa only [positiveRule, if_neg (not_lt.mpr htx.le)] using hc


/-! P006-T8: corrected information bound. -/

/-- The subtraction identity assumes integrability of all three functions y, m and a.
In the information bound, y is E.μ1, whose integrability is given by
Standing.means_integrable.2. -/
lemma T8_information_integral_bias_bound {C : Type*} [MeasurableSpace C]
    (P : Measure C) (y m a π : C → ℝ)
    (hy : Integrable y P) (hm : Integrable m P) (ha : Integrable a P)
    (hπ : Admissible π) :
    ((∫ x, π x * (y x - a x) ∂P) - (∫ x, π x * (y x - m x) ∂P) =
      ∫ x, π x * (m x - a x) ∂P) ∧
    |∫ x, π x * (m x - a x) ∂P| ≤ ∫ x, |m x - a x| ∂P := by
  have hya := T7_policy_mul (hy.sub ha) hπ
  have hym := T7_policy_mul (hy.sub hm) hπ
  have hma := T7_policy_mul (hm.sub ha) hπ
  constructor
  · simp only [Pi.sub_apply] at hya hym hma
    rw [← integral_sub hya hym]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    ring
  · apply (abs_integral_le_integral_abs).trans
    apply integral_mono hma.abs (hm.sub ha).abs
    intro x
    change |π x * (m x - a x)| ≤ |m x - a x|
    rw [abs_mul, abs_of_nonneg (hπ.2 x).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hπ.2 x).2

lemma T8_information_normalized_best {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n)
    (PiSet : Set (C → ℝ)) (b : C → ℝ) (hb : IsBest PiSet E.expectedTT b) :
    IsBest PiSet (normalizedTT E) b := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr E.hn
  refine ⟨hb.1, ?_⟩
  intro π hπ
  exact (div_le_div_iff_of_pos_right hn).mpr (hb.2 π hπ)

theorem T8_corrected_information_bound_proof {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (hS : Standing E) (b0 : X → ℝ)
    (hM : MarginalBaseline E b0) (hX : EstimatorUsesOnlyX E)
    (PiSet : Set ((X × U) → ℝ)) (hPiSet : ∀ π ∈ PiSet, Admissible π)
    (hU : TreatedUnbiased E (fun c => b0 c.1) PiSet)
    (γ : ℝ) (hγ : marginalHeterogeneity E b0 ≤ γ)
    (b s : (X × U) → ℝ) (hb : IsBest PiSet E.expectedTT b) (hs : IsBest PiSet E.V s) :
    (∀ π ∈ PiSet,
      normalizedTT E π = (∫ c, π c*(E.μ1 c-b0 c.1) ∂E.PX) ∧
      |normalizedTT E π-E.V π| =
        |∫ c, π c*(E.μ0 c-b0 c.1) ∂E.PX| ∧
      |normalizedTT E π-E.V π| ≤ marginalHeterogeneity E b0) ∧
    regret PiSet E.V b ≤ 2*γ := by
  have hn : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr E.hn).ne'
  have ha : Measurable (fun c : X × U => b0 c.1) := hM.1.comp measurable_fst
  have hid (π : (X × U) → ℝ) (hπ : π ∈ PiSet) :
      normalizedTT E π = ∫ c, π c * (E.μ1 c - b0 c.1) ∂E.PX := by
    unfold normalizedTT
    rw [T7_actual_treated_score E hS (fun c => b0 c.1) ha hM.2.1
      π (hPiSet π hπ) (hU π hπ)]
    exact mul_div_cancel_left₀ _ hn
  have hpolicy (π : (X × U) → ℝ) (hπ : π ∈ PiSet) :
      normalizedTT E π = (∫ c, π c * (E.μ1 c - b0 c.1) ∂E.PX) ∧
      |normalizedTT E π - E.V π| =
        |∫ c, π c * (E.μ0 c - b0 c.1) ∂E.PX| ∧
      |normalizedTT E π - E.V π| ≤ marginalHeterogeneity E b0 := by
    have hbias := T8_information_integral_bias_bound E.PX E.μ1 E.μ0
      (fun c => b0 c.1) π hS.means_integrable.2 hS.means_integrable.1
      hM.2.1 (hPiSet π hπ)
    have hdiff : normalizedTT E π - E.V π =
        ∫ c, π c * (E.μ0 c - b0 c.1) ∂E.PX := by
      rw [hid π hπ, T7_actual_welfare E hS π (hPiSet π hπ)]
      exact hbias.1
    refine ⟨hid π hπ, congrArg abs hdiff, ?_⟩
    rw [hdiff]
    simpa only [marginalHeterogeneity, abs_sub_comm] using hbias.2
  refine ⟨hpolicy, ?_⟩
  apply uniform_error_regret PiSet (normalizedTT E) E.V b s
    (T8_information_normalized_best E PiSet b hb) hs γ
  intro π hπ
  exact ((hpolicy π hπ).2.2).trans hγ

/-! Lemma 2 and Proposition 10. -/

/-- Integrate the coin-mean-independence premise without replacing the
random evaluated estimator by a population regression function. -/
lemma T8_lemma2_coin_mean_independent_score {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hS : Standing E)
    (π : C → ℝ) (hπ : Admissible π) (i : Fin n)
    (hI : (E.law π)[fun ω => bit (E.T π i ω) * E.μhat π ω (E.X i ω) |
      E.covariateSigma i] =ᵐ[E.law π] fun ω => π (E.X i ω) *
        (E.law π)[fun η => E.μhat π η (E.X i η) | E.covariateSigma i] ω) :
    (∫ ω, bit (E.T π i ω) * (E.Y1 i ω - E.μhat π ω (E.X i ω)) ∂E.law π) =
      (∫ x, π x * E.μ1 x ∂E.PX) -
      (∫ ω, π (E.X i ω) * E.μhat π ω (E.X i ω) ∂E.law π) := by
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability π hπ
  have hu := hS.measurable_units π hπ i
  have hi := hS.integrable_units π hπ i
  have hm : E.covariateSigma i ≤ ‹MeasurableSpace Ω› := hu.1.comap_le
  have hπX : Admissible (fun ω => π (E.X i ω)) :=
    ⟨hπ.1.comp hu.1, fun ω => hπ.2 _⟩
  have hπm : StronglyMeasurable[E.covariateSigma i] (fun ω => π (E.X i ω)) :=
    (hπ.1.comp (comap_measurable (E.X i))).stronglyMeasurable
  have hpH := T7_policy_mul hi.2.2 hπX
  have hpull := condExp_mul_of_stronglyMeasurable_left hπm hpH hi.2.2
  have hcoin : (∫ ω, bit (E.T π i ω) * E.μhat π ω (E.X i ω) ∂E.law π) =
      ∫ ω, π (E.X i ω) * E.μhat π ω (E.X i ω) ∂E.law π := by
    have hce := hI.trans hpull.symm
    have he := integral_congr_ae hce
    simpa only [integral_condExp hm, Pi.mul_def] using he
  have houtcome : (∫ ω, bit (E.T π i ω) * E.Y1 i ω ∂E.law π) =
      ∫ x, π x * E.μ1 x ∂E.PX := by
    rw [← integral_condExp hm,
      integral_congr_ae (T7_outcome_condExp E hS π hπ i).2]
    exact ((hS.covariate_law π hπ i).comp (hπ.1.mul hS.means_measurable.2)).integral_eq
  simp_rw [mul_sub]
  rw [integral_sub (T7_bit_mul hu.2.2.2 hi.2.1)
    (T7_bit_mul hu.2.2.2 hi.2.2), houtcome, hcoin]

lemma T8_lemma2_common_score {Ω C : Type*} [MeasurableSpace Ω]
    [MeasurableSpace C] {n : ℕ} (E : Experiment Ω C n) (hS : Standing E)
    (π : C → ℝ) (hπ : Admissible π)
    (hI : ∀ i, (E.law π)[fun ω => bit (E.T π i ω) * E.μhat π ω (E.X i ω) |
      E.covariateSigma i] =ᵐ[E.law π] fun ω => π (E.X i ω) *
        (E.law π)[fun η => E.μhat π η (E.X i η) | E.covariateSigma i] ω)
    (D : Measure (C × ℝ))
    (hcommon : ∀ i, IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω)))
      id (E.law π) D) :
    E.expectedTT π = (n : ℝ) *
      ((∫ x, π x * E.μ1 x ∂E.PX) - (∫ z, π z.1 * z.2 ∂D)) := by
  have hi (i : Fin n) : Integrable (fun ω => bit (E.T π i ω) *
      (E.Y1 i ω - E.μhat π ω (E.X i ω))) (E.law π) :=
    T7_bit_mul (hS.measurable_units π hπ i).2.2.2
      ((hS.integrable_units π hπ i).2.1.sub (hS.integrable_units π hπ i).2.2)
  have hmean (i : Fin n) : (∫ ω, bit (E.T π i ω) *
      (E.Y1 i ω - E.μhat π ω (E.X i ω)) ∂E.law π) =
      (∫ x, π x * E.μ1 x ∂E.PX) - (∫ z, π z.1 * z.2 ∂D) := by
    rw [T8_lemma2_coin_mean_independent_score E hS π hπ i (hI i)]
    have htransport := ((hcommon i).comp
      ((hπ.1.comp measurable_fst).mul measurable_snd)).integral_eq
    exact congrArg (fun r => (∫ x, π x * E.μ1 x ∂E.PX) - r) htransport
  have hsutva : (fun ω => wWeightedTT (E.μhat π ω) (fun _ => 1)
      (fun i => E.X i ω) (fun i => E.T π i ω) (E.observed π ω)) =
      fun ω => ∑ i, bit (E.T π i ω) * (E.Y1 i ω - E.μhat π ω (E.X i ω)) := by
    funext ω
    unfold wWeightedTT
    apply Finset.sum_congr rfl
    intro i _
    cases ht : E.T π i ω <;> simp [Experiment.observed, ht, bit]
  unfold Experiment.expectedTT Experiment.expectedWeightedTT
  rw [hsutva, integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- First recover integrability of the signed residual from its absolute
value, then add the population baseline. The absolute residual itself is
not the summand that reconstructs the second coordinate. -/
lemma T8_lemma2_signed_residual_integrable {C : Type*} [MeasurableSpace C]
    (D : Measure (C × ℝ)) (m : C → ℝ) (hm : Measurable m)
    (hmi : Integrable (fun z => m z.1) D)
    (herror : Integrable (fun z => |z.2 - m z.1|) D) :
    Integrable (fun z : C × ℝ => z.2) D := by
  have hresm : Measurable (fun z : C × ℝ => z.2 - m z.1) :=
    measurable_snd.sub (hm.comp measurable_fst)
  have hres : Integrable (fun z : C × ℝ => z.2 - m z.1) D :=
    (integrable_norm_iff hresm.aestronglyMeasurable).mp
      (by simpa only [Real.norm_eq_abs] using herror)
  have hsum := hres.add hmi
  convert hsum using 1
  funext z
  dsimp
  ring

theorem T8_lemma2_proposition10_proof {Ω X U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] {n : ℕ}
    (E : Experiment Ω (X × U) n) (hS : Standing E)
    (hX : EstimatorUsesOnlyX E) (PiSet : Set ((X × U) → ℝ))
    (hPiSet : ∀ π ∈ PiSet, Admissible π) (hI : EstimatorCoinMeanIndependent E PiSet)
    (D : Measure ((X × U) × ℝ)) (hD : IsProbabilityMeasure D)
    (hcommon : ∀ π ∈ PiSet, ∀ i, IdentDistrib
      (fun ω => (E.X i ω, E.μhat π ω (E.X i ω))) id (E.law π) D)
    (herror : Integrable (fun z => |z.2-E.μ0 z.1|) D)
    (b s : (X × U) → ℝ) (hb : IsBest PiSet E.expectedTT b) (hs : IsBest PiSet E.V s) :
    (∀ π ∈ PiSet, E.expectedTT π = (n : ℝ) *
      ((∫ ω, π (E.X ⟨0,E.hn⟩ ω)*E.μ1 (E.X ⟨0,E.hn⟩ ω) ∂E.law π) -
       (∫ ω, π (E.X ⟨0,E.hn⟩ ω)*E.μhat π ω (E.X ⟨0,E.hn⟩ ω) ∂E.law π))) ∧
    regret PiSet E.V b ≤ 2*(∫ z, |z.2-E.μ0 z.1| ∂D) := by
  letI : IsProbabilityMeasure D := hD
  let i0 : Fin n := ⟨0, E.hn⟩
  have hn : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr E.hn).ne'
  have hba : Admissible b := hPiSet b hb.1
  have hfst : IdentDistrib (fun z : (X × U) × ℝ => z.1) id D E.PX :=
    ((hcommon b hb.1 i0).comp measurable_fst).symm.trans
      (hS.covariate_law b hba i0)
  have hm0 : Integrable (fun z : (X × U) × ℝ => E.μ0 z.1) D :=
    (hfst.comp hS.means_measurable.1).integrable_iff.mpr hS.means_integrable.1
  have hm1 : Integrable (fun z : (X × U) × ℝ => E.μ1 z.1) D :=
    (hfst.comp hS.means_measurable.2).integrable_iff.mpr hS.means_integrable.2
  have hH : Integrable (fun z : (X × U) × ℝ => z.2) D :=
    T8_lemma2_signed_residual_integrable D E.μ0 hS.means_measurable.1 hm0 herror
  have hid (π : (X × U) → ℝ) (hπ : π ∈ PiSet) :
      E.expectedTT π = (n : ℝ) *
        ((∫ c, π c * E.μ1 c ∂E.PX) - (∫ z, π z.1 * z.2 ∂D)) :=
    T8_lemma2_common_score E hS π (hPiSet π hπ) (hI π hπ) D (hcommon π hπ)
  have hformula (π : (X × U) → ℝ) (hπ : π ∈ PiSet) :
      E.expectedTT π = (n : ℝ) *
        ((∫ ω, π (E.X ⟨0,E.hn⟩ ω) * E.μ1 (E.X ⟨0,E.hn⟩ ω) ∂E.law π) -
         (∫ ω, π (E.X ⟨0,E.hn⟩ ω) * E.μhat π ω (E.X ⟨0,E.hn⟩ ω) ∂E.law π)) := by
    have h₁ := ((hS.covariate_law π (hPiSet π hπ) i0).comp
      ((hPiSet π hπ).1.mul hS.means_measurable.2)).integral_eq
    have h₂ := ((hcommon π hπ i0).comp
      (((hPiSet π hπ).1.comp measurable_fst).mul measurable_snd)).integral_eq
    rw [hid π hπ]
    dsimp [i0] at h₁ h₂
    rw [h₁, h₂]
  have herror_policy (π : (X × U) → ℝ) (hπ : π ∈ PiSet) :
      |normalizedTT E π - E.V π| ≤ ∫ z, |z.2 - E.μ0 z.1| ∂D := by
    have hπa := hPiSet π hπ
    have hπD : Admissible (fun z : (X × U) × ℝ => π z.1) :=
      ⟨hπa.1.comp measurable_fst, fun z => hπa.2 z.1⟩
    have hnorm : normalizedTT E π =
        ∫ z, π z.1 * (E.μ1 z.1 - z.2) ∂D := by
      unfold normalizedTT
      rw [hid π hπ, mul_div_cancel_left₀ _ hn]
      have hy := (hfst.comp (hπa.1.mul hS.means_measurable.2)).integral_eq
      simp only [Function.comp_def, Pi.mul_apply, id_eq] at hy
      rw [← hy, ← integral_sub (T7_policy_mul hm1 hπD) (T7_policy_mul hH hπD)]
      apply integral_congr_ae
      apply ae_of_all
      intro z
      ring
    have hwelfare : E.V π = ∫ z, π z.1 * (E.μ1 z.1 - E.μ0 z.1) ∂D := by
      rw [T7_actual_welfare E hS π hπa]
      exact ((hfst.comp (hπa.1.mul
        (hS.means_measurable.2.sub hS.means_measurable.1))).integral_eq).symm
    have hbias := T8_information_integral_bias_bound D
      (fun z => E.μ1 z.1) (fun z => E.μ0 z.1) (fun z => z.2)
      (fun z => π z.1) hm1 hm0 hH hπD
    rw [hnorm, hwelfare, hbias.1]
    simpa only [abs_sub_comm] using hbias.2
  refine ⟨hformula, ?_⟩
  exact uniform_error_regret PiSet (normalizedTT E) E.V b s
    (T8_information_normalized_best E PiSet b hb) hs
    (∫ z, |z.2 - E.μ0 z.1| ∂D) herror_policy

end

end AronowAudit.P006.Wave1
