import AronowAudit.P009.Wave1.Gap.GLP0092B1
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Probability.Moments.Covariance

namespace AronowAudit.P009.Wave1
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000

/- The following measure-theoretic covariance lemmas are adapted from
StatLean/Stat-Lean, StatLean/TimeSeries/Mixing/Inequalities.lean and Defs.lean
(Apache-2.0; see AronowAudit/External/StatLean/LICENSE and NOTICE at the repository
root). Only the bounded covariance and Davydov proofs and their helpers are included. -/
namespace t45_donor
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
variable {Ω : Type*}
noncomputable def alphaMixCoeff {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (m₁ m₂ : MeasurableSpace Ω) : ℝ :=
  sSup {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
    r = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|}

private lemma le_alphaMixCoeff_of_measurableSet {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : MeasurableSet[m₁] A)
    (hB : MeasurableSet[m₂] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ alphaMixCoeff μ m₁ m₂ := by
  refine le_csSup ⟨1, ?_⟩ ⟨A, B, hA, hB, rfl⟩
  rintro r ⟨A', B', -, -, rfl⟩
  have h1 : (μ (A' ∩ B')).toReal ≤ 1 := measureReal_le_one
  have h2 : (μ A').toReal ≤ 1 := measureReal_le_one
  have h3 : (μ B').toReal ≤ 1 := measureReal_le_one
  have h4 : (0 : ℝ) ≤ (μ (A' ∩ B')).toReal := ENNReal.toReal_nonneg
  have h5 : (0 : ℝ) ≤ (μ A').toReal := ENNReal.toReal_nonneg
  have h6 : (0 : ℝ) ≤ (μ B').toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  refine ⟨by nlinarith, by nlinarith⟩

/-- The peeling step behind Billingsley's inequality: if the `m`-set discrepancies of `ψ`
are bounded by `K`, then `ψ` decorrelates from every `m`-measurable `φ` bounded by `C`,
with constant `2 C K`.

Proof: `∫ φ ψ = ∫ φ · E[ψ | m]` (pull-out property), so the left-hand side is
`∫ φ · W` with `W = E[ψ | m] − E ψ`; then `|∫ φ W| ≤ C ∫ |W|` and, splitting `Ω` at the
`m`-measurable sign event of `W`, `∫ |W| = ∫_A W − ∫_{Aᶜ} W ≤ 2 K` by hypothesis. -/
private lemma abs_integral_mul_sub_le_of_setIntegral_bound
    {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {φ ψ : Ω → ℝ} {C K : ℝ}
    (hφ : StronglyMeasurable[m] φ) (hφC : ∀ᵐ ω ∂μ, |φ ω| ≤ C)
    (hψ : Integrable ψ μ)
    (hK : ∀ A : Set Ω, MeasurableSet[m] A →
      |(∫ ω in A, ψ ω ∂μ) - (∫ ω, ψ ω ∂μ) * (μ A).toReal| ≤ K) :
    |(∫ ω, φ ω * ψ ω ∂μ) - (∫ ω, φ ω ∂μ) * ∫ ω, ψ ω ∂μ| ≤ 2 * C * K := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) hφC.exists.choose_spec
  have hφn : ∀ᵐ ω ∂μ, ‖φ ω‖ ≤ C := by simpa [Real.norm_eq_abs] using hφC
  have hφ' : StronglyMeasurable φ := hφ.mono hm
  have hφint : Integrable φ μ :=
    (memLp_top_of_bound hφ'.aestronglyMeasurable C hφn).integrable le_top
  set c : ℝ := ∫ ω, ψ ω ∂μ with hcdef
  set W : Ω → ℝ := fun ω => (μ[ψ|m]) ω - c with hWdef
  have hWm : StronglyMeasurable[m] W := stronglyMeasurable_condExp.sub stronglyMeasurable_const
  have hWint : Integrable W μ := integrable_condExp.sub (integrable_const c)
  have hpull : ∫ ω, φ ω * ψ ω ∂μ = ∫ ω, φ ω * (μ[ψ|m]) ω ∂μ := by
    have h1 : μ[φ * ψ|m] =ᵐ[μ] φ * μ[ψ|m] :=
      condExp_stronglyMeasurable_mul_of_bound hm hφ hψ C hφn
    calc ∫ ω, φ ω * ψ ω ∂μ = ∫ ω, (μ[φ * ψ|m]) ω ∂μ := (integral_condExp hm).symm
      _ = ∫ ω, (φ * μ[ψ|m]) ω ∂μ := integral_congr_ae h1
      _ = ∫ ω, φ ω * (μ[ψ|m]) ω ∂μ := rfl
  have hkey : (∫ ω, φ ω * ψ ω ∂μ) - (∫ ω, φ ω ∂μ) * c = ∫ ω, φ ω * W ω ∂μ := by
    rw [hpull]
    have h : ∀ ω, φ ω * W ω = φ ω * (μ[ψ|m]) ω - φ ω * c := by intro ω; ring
    simp_rw [h]
    rw [integral_sub (integrable_condExp.bdd_mul hφ'.aestronglyMeasurable hφn)
      (hφint.mul_const c), integral_mul_const]
  have hsetW : ∀ A : Set Ω, MeasurableSet[m] A →
      ∫ ω in A, W ω ∂μ = (∫ ω in A, ψ ω ∂μ) - c * (μ A).toReal := by
    intro A hA
    rw [hWdef]
    rw [integral_sub (integrable_condExp.restrict) (integrable_const c),
      setIntegral_condExp hm hψ hA, setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  set A : Set Ω := {ω | 0 ≤ W ω} with hAdef
  have hA : MeasurableSet[m] A := hWm.measurable measurableSet_Ici
  have hsplit : ∫ ω, |W ω| ∂μ = (∫ ω in A, W ω ∂μ) - ∫ ω in Aᶜ, W ω ∂μ := by
    have h1 : ∫ ω in A, |W ω| ∂μ = ∫ ω in A, W ω ∂μ :=
      setIntegral_congr_fun (hm A hA) fun x hx => abs_of_nonneg hx
    have h2 : ∫ ω in Aᶜ, |W ω| ∂μ = -∫ ω in Aᶜ, W ω ∂μ := by
      rw [← integral_neg]
      exact setIntegral_congr_fun (hm A hA).compl fun x hx => abs_of_neg (not_le.mp hx)
    rw [← integral_add_compl (hm A hA) hWint.abs, h1, h2]
    ring
  have hbd1 : |∫ ω in A, W ω ∂μ| ≤ K := by rw [hsetW A hA]; exact hK A hA
  have hbd2 : |∫ ω in Aᶜ, W ω ∂μ| ≤ K := by rw [hsetW _ hA.compl]; exact hK _ hA.compl
  have hW2K : ∫ ω, |W ω| ∂μ ≤ 2 * K := by
    rw [hsplit]
    linarith [(abs_le.mp hbd1).2, (abs_le.mp hbd2).1]
  rw [hkey]
  calc |∫ ω, φ ω * W ω ∂μ| ≤ ∫ ω, |φ ω * W ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, C * |W ω| ∂μ := by
        refine integral_mono_ae ((hWint.bdd_mul hφ'.aestronglyMeasurable hφn).abs)
          (hWint.abs.const_mul C) ?_
        filter_upwards [hφC] with ω hω
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
    _ = C * ∫ ω, |W ω| ∂μ := integral_const_mul _ _
    _ ≤ C * (2 * K) := mul_le_mul_of_nonneg_left hW2K hC
    _ = 2 * C * K := by ring

/-- Billingsley’s bounded covariance inequality: `m₁`/`m₂`-measurable bounded factors have
covariance at most `4 α C₁ C₂`. -/
theorem abs_covariance_le_of_bounded {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {C₁ C₂ : ℝ}
    -- Almost-sure bounds on the two factors.
    (hfC : ∀ᵐ ω ∂μ, |f ω| ≤ C₁) (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C₂) :
    |cov[f, g; μ]| ≤ 4 * alphaMixCoeff μ m₁ m₂ * C₁ * C₂ := by
  set α := alphaMixCoeff μ m₁ m₂ with hα
  have hC₁ : 0 ≤ C₁ := le_trans (abs_nonneg _) hfC.exists.choose_spec
  have hC₂ : 0 ≤ C₂ := le_trans (abs_nonneg _) hgC.exists.choose_spec
  have hfsm : StronglyMeasurable[m₁] f := hf.stronglyMeasurable
  have hgsm : StronglyMeasurable[m₂] g := hg.stronglyMeasurable
  have hfn : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C₁ := by simpa [Real.norm_eq_abs] using hfC
  have hgn : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C₂ := by simpa [Real.norm_eq_abs] using hgC
  have hfLp : MemLp f 2 μ :=
    (memLp_top_of_bound (hfsm.mono h₁).aestronglyMeasurable C₁ hfn).mono_exponent le_top
  have hgLp : MemLp g 2 μ :=
    (memLp_top_of_bound (hgsm.mono h₂).aestronglyMeasurable C₂ hgn).mono_exponent le_top
  have hfint : Integrable f μ := hfLp.integrable one_le_two
  -- Step A: peel `f` against an arbitrary `m₂`-event; the discrepancies are the α set.
  have hstepA : ∀ B : Set Ω, MeasurableSet[m₂] B →
      |(∫ ω in B, f ω ∂μ) - (∫ ω, f ω ∂μ) * (μ B).toReal| ≤ 2 * C₁ * α := by
    intro B hB
    have hBΩ : MeasurableSet B := h₂ B hB
    have hind : Integrable (B.indicator (1 : Ω → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator hBΩ
    have h := abs_integral_mul_sub_le_of_setIntegral_bound (m := m₁) (mΩ := mΩ) h₁
      hfsm hfC hind (K := α) ?_
    · have e1 : ∫ ω, f ω * B.indicator (1 : Ω → ℝ) ω ∂μ = ∫ ω in B, f ω ∂μ := by
        rw [← integral_indicator hBΩ]
        congr 1 with ω
        by_cases hω : ω ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      have e2 : ∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ = (μ B).toReal := by
        rw [integral_indicator hBΩ]
        simp [measureReal_def]
      rw [e1, e2] at h
      exact h
    · intro A hA
      have e3 : ∫ ω in A, B.indicator (1 : Ω → ℝ) ω ∂μ = (μ (A ∩ B)).toReal := by
        rw [setIntegral_indicator hBΩ]
        simp [measureReal_def]
      have e4 : ∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ = (μ B).toReal := by
        rw [integral_indicator hBΩ]
        simp [measureReal_def]
      rw [e3, e4, mul_comm ((μ B).toReal) ((μ A).toReal)]
      exact le_alphaMixCoeff_of_measurableSet (mΩ := mΩ) (μ := μ) hA hB
  -- Step B: peel `g` against `f`, feeding Step A as the discrepancy bound.
  have hstepB := abs_integral_mul_sub_le_of_setIntegral_bound (m := m₂) (mΩ := mΩ) h₂
    hgsm hgC hfint (K := 2 * C₁ * α) hstepA
  rw [covariance_eq_sub hfLp hgLp]
  have e5 : ∫ ω, g ω * f ω ∂μ = ∫ ω, f ω * g ω ∂μ := by simp_rw [mul_comm]
  rw [e5] at hstepB
  have e6 : (∫ ω, f ω * g ω ∂μ) - (∫ ω, g ω ∂μ) * ∫ ω, f ω ∂μ
      = μ[f * g] - μ[f] * μ[g] := by
    simp only [Pi.mul_apply]
    ring
  rw [e6] at hstepB
  calc |μ[f * g] - μ[f] * μ[g]| ≤ 2 * C₂ * (2 * C₁ * α) := hstepB
    _ = 4 * α * C₁ * C₂ := by ring

private lemma tail_holder {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ} {r t : ℝ} (hr : 0 < r) (hrt : r < t) (hu : MemLp u (ENNReal.ofReal t) μ)
    {S : Set Ω} (hS : MeasurableSet S) :
    ∫ ω, S.indicator (fun ω => |u ω| ^ r) ω ∂μ
      ≤ (∫ ω, |u ω| ^ t ∂μ) ^ (r / t) * (μ.real S) ^ (1 - r / t) := by
  have ht : 0 < t := lt_trans hr hrt
  have htr : 0 < t - r := by linarith
  set P : ℝ := t / r with hP
  set Q : ℝ := t / (t - r) with hQ
  have hconj : Real.HolderConjugate P Q := by
    refine ⟨?_, by positivity, by positivity⟩
    rw [hP, hQ]
    field_simp
    ring
  have hmem : MemLp (fun ω => |u ω| ^ r) (ENNReal.ofReal P) μ := by
    have h := hu.norm_rpow_div (ENNReal.ofReal r)
    rw [ENNReal.toReal_ofReal hr.le, ← ENNReal.ofReal_div_of_pos hr] at h
    simpa [Real.norm_eq_abs] using h
  have hind : MemLp (S.indicator (1 : Ω → ℝ)) (ENNReal.ofReal Q) μ := by
    refine (memLp_top_of_bound ((stronglyMeasurable_const.indicator hS)).aestronglyMeasurable 1
      ?_).mono_exponent le_top
    filter_upwards with ω
    exact (norm_indicator_le_norm_self (1 : Ω → ℝ) ω).trans (by simp)
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj
    (f := fun ω => |u ω| ^ r) (g := S.indicator (1 : Ω → ℝ))
    (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    hmem hind
  have e1 : ∀ ω, S.indicator (fun ω => |u ω| ^ r) ω
      = (|u ω| ^ r) * S.indicator (1 : Ω → ℝ) ω := by
    intro ω
    by_cases hω : ω ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  have e2 : ∫ ω, (S.indicator (1 : Ω → ℝ) ω) ^ Q ∂μ = μ.real S := by
    have h : ∀ ω, (S.indicator (1 : Ω → ℝ) ω) ^ Q = S.indicator (1 : Ω → ℝ) ω := by
      intro ω
      by_cases hω : ω ∈ S
      · simp [Set.indicator_of_mem, hω, Real.one_rpow]
      · simp [Set.indicator_of_notMem, hω, Real.zero_rpow hconj.symm.ne_zero]
    rw [funext h, integral_indicator_one hS]
  have e3 : ∀ ω, (|u ω| ^ r) ^ P = |u ω| ^ t := by
    intro ω
    rw [← Real.rpow_mul (abs_nonneg _), hP]
    congr 1
    field_simp
  simp_rw [e1]
  rw [e2] at key
  refine key.trans_eq ?_
  rw [show ∫ ω, (|u ω| ^ r) ^ P ∂μ = ∫ ω, |u ω| ^ t ∂μ from integral_congr_ae
    (Eventually.of_forall e3)]
  rw [show (1 : ℝ) / P = r / t by rw [hP]; field_simp,
    show (1 : ℝ) / Q = 1 - r / t by rw [hQ]; field_simp]


/-- Markov/Chebyshev in the form needed below. -/
private lemma markov_rpow {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ} {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (hum : Measurable u)
    (hint : Integrable (fun ω => |u ω| ^ r) μ) :
    μ.real {ω | c < |u ω|} * c ^ r ≤ ∫ ω, |u ω| ^ r ∂μ := by
  have hS : MeasurableSet {ω | c < |u ω|} := measurableSet_lt measurable_const (by fun_prop)
  have h1 : ∫ ω, ({ω | c < |u ω|}).indicator (fun _ => c ^ r) ω ∂μ ≤ ∫ ω, |u ω| ^ r ∂μ := by
    refine integral_mono ((integrable_const _).indicator hS) hint fun ω => ?_
    by_cases hω : ω ∈ {ω | c < |u ω|}
    · rw [Set.indicator_of_mem hω]
      exact Real.rpow_le_rpow hc.le (le_of_lt hω) hr.le
    · rw [Set.indicator_of_notMem hω]
      exact Real.rpow_nonneg (abs_nonneg _) _
  rwa [integral_indicator_const _ hS, smul_eq_mul] at h1

/-- Clamping to `[-c, c]` is bounded by `c`. -/
private lemma abs_clamp_le {c x : ℝ} (hc : 0 ≤ c) : |max (-c) (min c x)| ≤ c := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clamping is a contraction towards the origin. -/
private lemma abs_sub_clamp_le_of_lt {c x : ℝ} (hc : 0 ≤ c) (hx : c < |x|) :
    |x - max (-c) (min c x)| ≤ |x| := by
  rcases le_total c x with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - c),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
    linarith
  · have h2 : x ≤ -c := by
      rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hx <;> linarith
    rw [min_eq_right h, max_eq_left h2, abs_of_nonpos (by linarith : x - -c ≤ 0),
      abs_of_nonpos (by linarith : x ≤ 0)]
    linarith

/-- Below the level, clamping is the identity. -/
private lemma sub_clamp_eq_zero {c x : ℝ} (hx : |x| ≤ c) : x - max (-c) (min c x) = 0 := by
  rw [abs_le] at hx
  rw [min_eq_right hx.2, max_eq_right hx.1, sub_self]

private lemma covariance_eq_sub' {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : Integrable (fun ω => f ω * g ω) μ) :
    cov[f, g; μ] = (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
  have i1 : Integrable (fun ω => f ω * g ω - μ[g] * f ω) μ := hfg.sub (hf.const_mul _)
  have i2 : Integrable (fun ω => f ω * g ω - μ[g] * f ω - μ[f] * g ω) μ := i1.sub (hg.const_mul _)
  have e0 : ∫ ω, ((f ω * g ω - μ[g] * f ω - μ[f] * g ω) + μ[f] * μ[g]) ∂μ
      = (∫ ω, (f ω * g ω - μ[g] * f ω - μ[f] * g ω) ∂μ) + ∫ _ω : Ω, μ[f] * μ[g] ∂μ :=
    integral_add i2 (integrable_const _)
  have e1 : ∫ ω, (f ω * g ω - μ[g] * f ω - μ[f] * g ω) ∂μ
      = (∫ ω, (f ω * g ω - μ[g] * f ω) ∂μ) - ∫ ω, μ[f] * g ω ∂μ :=
    integral_sub i1 (hg.const_mul _)
  have e2 : ∫ ω, (f ω * g ω - μ[g] * f ω) ∂μ
      = (∫ ω, f ω * g ω ∂μ) - ∫ ω, μ[g] * f ω ∂μ :=
    integral_sub hfg (hf.const_mul _)
  have e3 : ∫ ω, μ[f] * g ω ∂μ = μ[f] * ∫ ω, g ω ∂μ := integral_const_mul _ _
  have e4 : ∫ ω, μ[g] * f ω ∂μ = μ[g] * ∫ ω, f ω ∂μ := integral_const_mul _ _
  have e5 : ∫ _ω : Ω, μ[f] * μ[g] ∂μ = μ[f] * μ[g] := by simp
  have h : ∀ ω, (f ω - μ[f]) * (g ω - μ[g])
      = (f ω * g ω - μ[g] * f ω - μ[f] * g ω) + μ[f] * μ[g] := by intro ω; ring
  rw [covariance, integral_congr_ae (Eventually.of_forall h), e0, e1, e2, e3, e4, e5]
  ring

set_option maxHeartbeats 1000000 in
-- Davydov's truncation argument uses four Hölder applications and a limit.

/-- Davydov’s covariance inequality: for `p, q > 1` with `1/p + 1/q < 1`,
`|Cov(f, g)| ≤ 8 α^{1 − 1/p − 1/q} ‖f‖_p ‖g‖_q`. The proof uses truncation against the
bounded case; see Doukhan §1.2.2. -/
theorem abs_covariance_le_davydov {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {p q : ℝ}
    -- Integrability exponents.
    (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q < 1)
    (hfLp : MemLp f (ENNReal.ofReal p) μ) (hgLq : MemLp g (ENNReal.ofReal q) μ) :
    |cov[f, g; μ]|
      ≤ 8 * alphaMixCoeff μ m₁ m₂ ^ (1 - 1 / p - 1 / q)
        * (eLpNorm f (ENNReal.ofReal p) μ).toReal
        * (eLpNorm g (ENNReal.ofReal q) μ).toReal := by
  -- exponent bookkeeping
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hq0 : (0 : ℝ) < q := lt_trans one_pos hq
  have hip : 0 < 1 / p := by positivity
  have hiq : 0 < 1 / q := by positivity
  set p' : ℝ := p / (p - 1) with hp'def
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hp'0 : 0 < p' := by positivity
  have hinvp' : 1 / p' = 1 - 1 / p := by rw [hp'def]; field_simp
  have hp'1 : 1 < p' := by
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have h : 1 ≤ 1 / p' := by rw [le_div_iff₀ hp'0]; linarith
    rw [hinvp'] at h; linarith
  have hp'q : p' < q := by
    have h1 : 1 / q < 1 / p' := by rw [hinvp']; linarith
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have := one_div_le_one_div_of_le hq0 hcon
    linarith
  set θ : ℝ := 1 - 1 / p - 1 / q with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hθp' : θ = 1 / p' - 1 / q := by rw [hθdef, hinvp']
  set α : ℝ := alphaMixCoeff μ m₁ m₂ with hαdef
  set A : ℝ := (eLpNorm f (ENNReal.ofReal p) μ).toReal with hAdef
  set B : ℝ := (eLpNorm g (ENNReal.ofReal q) μ).toReal with hBdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hα0 : 0 ≤ α := by
    have h := le_alphaMixCoeff_of_measurableSet (m₁ := m₁) (m₂ := m₂) (mΩ := mΩ) (μ := μ)
      (A := ∅) (B := ∅)
      (@MeasurableSet.empty Ω m₁) (@MeasurableSet.empty Ω m₂)
    simpa using h
  have hconjp : Real.HolderConjugate p p' := ⟨by rw [hp'def]; field_simp; ring, hp0, hp'0⟩
  -- measurability and integrability
  have hfm : Measurable f := hf.mono h₁ le_rfl
  have hgm : Measurable g := hg.mono h₂ le_rfl
  have hfint : Integrable f μ := hfLp.integrable (by simp [ENNReal.one_le_ofReal, hp.le])
  have hgint : Integrable g μ := hgLq.integrable (by simp [ENNReal.one_le_ofReal, hq.le])
  have hIf : Integrable (fun ω => |f ω| ^ p) μ := by
    have h := hfLp.integrable_norm_rpow (by simp [hp0]) (by simp)
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using h
  have hIg : Integrable (fun ω => |g ω| ^ q) μ := by
    have h := hgLq.integrable_norm_rpow (by simp [hq0]) (by simp)
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hq0.le] using h
  have hA : A = (∫ ω, |f ω| ^ p ∂μ) ^ (1 / p) := by
    rw [hAdef, toReal_eLpNorm,
      lpNorm_eq_integral_norm_rpow_toReal (by simp [hp0]) (by simp) hfLp.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le]
    simp [Real.norm_eq_abs, one_div]
  have hB : B = (∫ ω, |g ω| ^ q ∂μ) ^ (1 / q) := by
    rw [hBdef, toReal_eLpNorm,
      lpNorm_eq_integral_norm_rpow_toReal (by simp [hq0]) (by simp) hgLq.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq0.le]
    simp [Real.norm_eq_abs, one_div]
  have hAp : A ^ p = ∫ ω, |f ω| ^ p ∂μ := by
    rw [hA, ← Real.rpow_mul (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _), one_div,
      inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hBq : B ^ q = ∫ ω, |g ω| ^ q ∂μ := by
    rw [hB, ← Real.rpow_mul (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _), one_div,
      inv_mul_cancel₀ hq0.ne', Real.rpow_one]
  -- `g` lies in `L^{p'}` as well
  have hgLp' : MemLp g (ENNReal.ofReal p') μ :=
    hgLq.mono_exponent (ENNReal.ofReal_le_ofReal hp'q.le)
  have hfgint : Integrable (fun ω => f ω * g ω) μ := by
    have : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal p') 1 := by
      constructor
      simpa using hconjp.inv_add_inv_ennreal
    exact hfLp.integrable_mul hgLp'
  have hcov : cov[f, g; μ] = (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ :=
    covariance_eq_sub' hfint hgint hfgint
  -- degenerate cases
  rcases eq_or_lt_of_le hA0 with hA0' | hApos
  · have hfae : f =ᵐ[μ] 0 := by
      have hpne : ENNReal.ofReal p ≠ 0 := by simp [hp0]
      refine (eLpNorm_eq_zero_iff hpne).mp ?_
      have := hfLp.eLpNorm_ne_top
      rcases (ENNReal.toReal_eq_zero_iff _).mp hA0'.symm with h | h
      · exact h
      · exact absurd h this
    have hz : cov[f, g; μ] = 0 := by
      have h0 : μ[f] = 0 := by rw [integral_congr_ae hfae]; simp
      rw [covariance, h0]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hfae] with ω hω
      simp [hω]
    rw [hz, abs_zero, ← hA0']
    simp
  rcases eq_or_lt_of_le hB0 with hB0' | hBpos
  · have hgae : g =ᵐ[μ] 0 := by
      have hqne : ENNReal.ofReal q ≠ 0 := by simp [hq0]
      refine (eLpNorm_eq_zero_iff hqne).mp ?_
      have := hgLq.eLpNorm_ne_top
      rcases (ENNReal.toReal_eq_zero_iff _).mp hB0'.symm with h | h
      · exact h
      · exact absurd h this
    have hz : cov[f, g; μ] = 0 := by
      have h0 : μ[g] = 0 := by rw [integral_congr_ae hgae]; simp
      rw [covariance, h0]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hgae] with ω hω
      simp [hω]
    rw [hz, abs_zero, ← hB0']
    simp
  -- the main estimate, at every level `β = α + ε`
  have main : ∀ ε : ℝ, 0 < ε → |cov[f, g; μ]| ≤ 8 * (α + ε) ^ θ * A * B := by
    intro ε hε
    set β : ℝ := α + ε with hβdef
    have hβ0 : 0 < β := by rw [hβdef]; linarith
    set c₁ : ℝ := A * β ^ (-(1 / p)) with hc₁def
    set c₂ : ℝ := B * β ^ (-(1 / q)) with hc₂def
    have hc₁0 : 0 < c₁ := mul_pos hApos (Real.rpow_pos_of_pos hβ0 _)
    have hc₂0 : 0 < c₂ := mul_pos hBpos (Real.rpow_pos_of_pos hβ0 _)
    set f' : Ω → ℝ := fun ω => max (-c₁) (min c₁ (f ω)) with hf'def
    set g' : Ω → ℝ := fun ω => max (-c₂) (min c₂ (g ω)) with hg'def
    set S : Set Ω := {ω | c₁ < |f ω|} with hSdef
    set T : Set Ω := {ω | c₂ < |g ω|} with hTdef
    have hSm : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
    have hTm : MeasurableSet T := measurableSet_lt measurable_const (by fun_prop)
    have hf'meas : Measurable[m₁] f' := measurable_const.max (measurable_const.min hf)
    have hg'meas : Measurable[m₂] g' := measurable_const.max (measurable_const.min hg)
    have hf'm : Measurable f' := hf'meas.mono h₁ le_rfl
    have hg'm : Measurable g' := hg'meas.mono h₂ le_rfl
    have hf'bdd : ∀ ω, |f' ω| ≤ c₁ := fun ω => abs_clamp_le hc₁0.le
    have hg'bdd : ∀ ω, |g' ω| ≤ c₂ := fun ω => abs_clamp_le hc₂0.le
    have hf''le : ∀ ω, |f ω - f' ω| ≤ S.indicator (fun ω => |f ω|) ω := by
      intro ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω]
        exact abs_sub_clamp_le_of_lt hc₁0.le hω
      · rw [Set.indicator_of_notMem hω, sub_clamp_eq_zero (not_lt.mp hω), abs_zero]
    have hg''le : ∀ ω, |g ω - g' ω| ≤ T.indicator (fun ω => |g ω|) ω := by
      intro ω
      by_cases hω : ω ∈ T
      · rw [Set.indicator_of_mem hω]
        exact abs_sub_clamp_le_of_lt hc₂0.le hω
      · rw [Set.indicator_of_notMem hω, sub_clamp_eq_zero (not_lt.mp hω), abs_zero]
    -- pointwise domination of the tails
    have hgg'abs : ∀ ω, |g ω - g' ω| ≤ |g ω| := by
      intro ω
      refine (hg''le ω).trans ?_
      by_cases hω : ω ∈ T
      · rw [Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem hω]; exact abs_nonneg _
    -- Markov
    have hMS : μ.real S ≤ β := by
      have h := markov_rpow (u := f) (r := p) (c := c₁) hp0 hc₁0 hfm hIf
      have hc : c₁ ^ p * β = A ^ p := by
        rw [hc₁def, Real.mul_rpow hA0 (Real.rpow_nonneg hβ0.le _), ← Real.rpow_mul hβ0.le,
          show -(1 / p) * p = -1 by field_simp, Real.rpow_neg_one]
        field_simp
      have hcp : 0 < c₁ ^ p := Real.rpow_pos_of_pos hc₁0 p
      have h2 : μ.real S * c₁ ^ p ≤ β * c₁ ^ p := by
        rw [mul_comm β, hc, hAp]; exact h
      exact le_of_mul_le_mul_right h2 hcp
    have hMT : μ.real T ≤ β := by
      have h := markov_rpow (u := g) (r := q) (c := c₂) hq0 hc₂0 hgm hIg
      have hc : c₂ ^ q * β = B ^ q := by
        rw [hc₂def, Real.mul_rpow hB0 (Real.rpow_nonneg hβ0.le _), ← Real.rpow_mul hβ0.le,
          show -(1 / q) * q = -1 by field_simp, Real.rpow_neg_one]
        field_simp
      have hcq : 0 < c₂ ^ q := Real.rpow_pos_of_pos hc₂0 q
      have h2 : μ.real T * c₂ ^ q ≤ β * c₂ ^ q := by
        rw [mul_comm β, hc, hBq]; exact h
      exact le_of_mul_le_mul_right h2 hcq
    -- integrability of the pieces
    have hf'int : Integrable f' μ :=
      (memLp_top_of_bound hf'm.aestronglyMeasurable c₁
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hf'bdd ω)).integrable
        le_top
    have hg'int : Integrable g' μ :=
      (memLp_top_of_bound hg'm.aestronglyMeasurable c₂
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hg'bdd ω)).integrable
        le_top
    have hg'n : ∀ᵐ ω ∂μ, ‖g' ω‖ ≤ c₂ :=
      Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hg'bdd ω
    have hf''int : Integrable (fun ω => f ω - f' ω) μ := hfint.sub hf'int
    have hg''int : Integrable (fun ω => g ω - g' ω) μ := hgint.sub hg'int
    have hfg'int : Integrable (fun ω => f ω * g' ω) μ :=
      hfint.mul_bdd hg'm.aestronglyMeasurable hg'n
    have hf'g'int : Integrable (fun ω => f' ω * g' ω) μ :=
      hf'int.mul_bdd hg'm.aestronglyMeasurable hg'n
    have hf''g'int : Integrable (fun ω => (f ω - f' ω) * g' ω) μ :=
      hf''int.mul_bdd hg'm.aestronglyMeasurable hg'n
    have hfg''int : Integrable (fun ω => f ω * (g ω - g' ω)) μ := by
      have h : ∀ ω, f ω * (g ω - g' ω) = f ω * g ω - f ω * g' ω := by intro ω; ring
      simpa [h] using! hfgint.sub hfg'int
    -- the three-term decomposition
    have e1 : (∫ ω, f ω * g' ω ∂μ) + (∫ ω, f ω * (g ω - g' ω) ∂μ) = ∫ ω, f ω * g ω ∂μ := by
      rw [← integral_add hfg'int hfg''int]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have e2 : (∫ ω, f' ω * g' ω ∂μ) + (∫ ω, (f ω - f' ω) * g' ω ∂μ) = ∫ ω, f ω * g' ω ∂μ := by
      rw [← integral_add hf'g'int hf''g'int]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have e3 : (∫ ω, g' ω ∂μ) + (∫ ω, (g ω - g' ω) ∂μ) = ∫ ω, g ω ∂μ := by
      rw [← integral_add hg'int hg''int]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have e4 : (∫ ω, f' ω ∂μ) + (∫ ω, (f ω - f' ω) ∂μ) = ∫ ω, f ω ∂μ := by
      rw [← integral_add hf'int hf''int]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hsplit : (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)
        = ((∫ ω, f' ω * g' ω ∂μ) - (∫ ω, f' ω ∂μ) * ∫ ω, g' ω ∂μ)
          + ((∫ ω, (f ω - f' ω) * g' ω ∂μ) - (∫ ω, (f ω - f' ω) ∂μ) * ∫ ω, g' ω ∂μ)
          + ((∫ ω, f ω * (g ω - g' ω) ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, (g ω - g' ω) ∂μ) := by
      rw [← e1, ← e2, ← e3, ← e4]
      ring
    -- tail bounds
    have hTf : ∫ ω, |f ω - f' ω| ∂μ ≤ A * β ^ (1 - 1 / p) := by
      have h1 : ∫ ω, |f ω - f' ω| ∂μ ≤ ∫ ω, S.indicator (fun ω => |f ω|) ω ∂μ :=
        integral_mono hf''int.abs (hfint.abs.indicator hSm) fun ω => hf''le ω
      have h2 := tail_holder (u := f) (r := 1) (t := p) one_pos hp hfLp hSm
      simp only [Real.rpow_one] at h2
      refine h1.trans (h2.trans ?_)
      rw [← hA]
      refine mul_le_mul_of_nonneg_left ?_ hA0
      exact Real.rpow_le_rpow measureReal_nonneg hMS (by linarith)
    have hgg'Lp' : MemLp (fun ω => g ω - g' ω) (ENNReal.ofReal p') μ :=
      hgLp'.of_le (hgint.sub hg'int).aestronglyMeasurable
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgg'abs ω)
    have hIgg' : Integrable (fun ω => |g ω - g' ω| ^ p') μ := by
      have h := hgg'Lp'.integrable_norm_rpow (by simp [hp'0]) (by simp)
      simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp'0.le] using h
    have hN : (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p') ≤ B * β ^ θ := by
      have hIgp' : Integrable (fun ω => |g ω| ^ p') μ := by
        have h := hgLp'.integrable_norm_rpow (by simp [hp'0]) (by simp)
        simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp'0.le] using h
      have h1 : ∫ ω, |g ω - g' ω| ^ p' ∂μ ≤ ∫ ω, T.indicator (fun ω => |g ω| ^ p') ω ∂μ := by
        refine integral_mono hIgg' (hIgp'.indicator hTm) fun ω => ?_
        · by_cases hω : ω ∈ T
          · rw [Set.indicator_of_mem hω]
            exact Real.rpow_le_rpow (abs_nonneg _) (hgg'abs ω) hp'0.le
          · rw [Set.indicator_of_notMem hω, sub_clamp_eq_zero (not_lt.mp hω), abs_zero,
              Real.zero_rpow hp'0.ne']
      have h2 := tail_holder (u := g) (r := p') (t := q) hp'0 hp'q hgLq hTm
      have h3 : ∫ ω, |g ω - g' ω| ^ p' ∂μ ≤ B ^ p' * β ^ (1 - p' / q) := by
        refine (h1.trans (h2.trans ?_))
        have hBp' : (∫ ω, |g ω| ^ q ∂μ) ^ (p' / q) = B ^ p' := by
          rw [← hBq, ← Real.rpow_mul hB0]
          congr 1
          field_simp
        rw [hBp']
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hB0 _)
        refine Real.rpow_le_rpow measureReal_nonneg hMT ?_
        rw [sub_nonneg, div_le_one hq0]
        exact hp'q.le
      calc (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p')
          ≤ (B ^ p' * β ^ (1 - p' / q)) ^ (1 / p') := by
            refine Real.rpow_le_rpow ?_ h3 (by positivity)
            exact integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
        _ = B * β ^ θ := by
            rw [Real.mul_rpow (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hβ0.le _),
              ← Real.rpow_mul hB0, ← Real.rpow_mul hβ0.le,
              mul_one_div, div_self hp'0.ne', Real.rpow_one]
            congr 1
            rw [hθp']
            field_simp
    have hTg : ∫ ω, |g ω - g' ω| ∂μ ≤ (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p') := by
      have h := tail_holder (u := fun ω => g ω - g' ω) (r := 1) (t := p') one_pos hp'1 hgg'Lp'
        MeasurableSet.univ
      simpa using h
    have hIA : ∫ ω, |f ω| ∂μ ≤ A := by
      have h := tail_holder (u := f) (r := 1) (t := p) one_pos hp hfLp MeasurableSet.univ
      simp only [Real.rpow_one, Set.indicator_univ, probReal_univ, Real.one_rpow,
        mul_one] at h
      rw [hA]
      exact h
    -- the three covariance terms
    have hsub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
      have h := abs_add_le x (-y)
      rwa [abs_neg, ← sub_eq_add_neg] at h
    have hT1 : |(∫ ω, f' ω * g' ω ∂μ) - (∫ ω, f' ω ∂μ) * ∫ ω, g' ω ∂μ| ≤ 4 * α * c₁ * c₂ := by
      have h := abs_covariance_le_of_bounded (mΩ := mΩ) (μ := μ) h₁ h₂ hf'meas hg'meas
        (Eventually.of_forall hf'bdd) (Eventually.of_forall hg'bdd)
      rwa [covariance_eq_sub' hf'int hg'int hf'g'int] at h
    have hb1 : |∫ ω, (f ω - f' ω) * g' ω ∂μ| ≤ c₂ * ∫ ω, |f ω - f' ω| ∂μ := by
      calc |∫ ω, (f ω - f' ω) * g' ω ∂μ| ≤ ∫ ω, |(f ω - f' ω) * g' ω| ∂μ :=
            abs_integral_le_integral_abs
        _ ≤ ∫ ω, |f ω - f' ω| * c₂ ∂μ := by
            refine integral_mono hf''g'int.abs (hf''int.abs.mul_const c₂) fun ω => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hg'bdd ω) (abs_nonneg _)
        _ = (∫ ω, |f ω - f' ω| ∂μ) * c₂ := integral_mul_const _ _
        _ = c₂ * ∫ ω, |f ω - f' ω| ∂μ := mul_comm _ _
    have hb3 : |∫ ω, g' ω ∂μ| ≤ c₂ := by
      have h := norm_integral_le_of_norm_le_const (μ := μ) hg'n
      simpa using h
    have hT2 : |(∫ ω, (f ω - f' ω) * g' ω ∂μ) - (∫ ω, (f ω - f' ω) ∂μ) * ∫ ω, g' ω ∂μ|
        ≤ 2 * (c₂ * (A * β ^ (1 - 1 / p))) := by
      refine (hsub _ _).trans ?_
      rw [abs_mul]
      have h4 : |∫ ω, (f ω - f' ω) ∂μ| * |∫ ω, g' ω ∂μ| ≤ c₂ * ∫ ω, |f ω - f' ω| ∂μ := by
        rw [mul_comm c₂]
        exact mul_le_mul (abs_integral_le_integral_abs) hb3 (abs_nonneg _)
          (integral_nonneg fun ω => abs_nonneg _)
      have h5 : c₂ * (∫ ω, |f ω - f' ω| ∂μ) ≤ c₂ * (A * β ^ (1 - 1 / p)) :=
        mul_le_mul_of_nonneg_left hTf hc₂0.le
      linarith
    have hfabs : MemLp (fun ω => |f ω|) (ENNReal.ofReal p) μ := by
      simpa [Real.norm_eq_abs] using hfLp.norm
    have hgg'abs' : MemLp (fun ω => |g ω - g' ω|) (ENNReal.ofReal p') μ := by
      simpa [Real.norm_eq_abs] using hgg'Lp'.norm
    have hb4 : |∫ ω, f ω * (g ω - g' ω) ∂μ| ≤ A * (B * β ^ θ) := by
      calc |∫ ω, f ω * (g ω - g' ω) ∂μ| ≤ ∫ ω, |f ω * (g ω - g' ω)| ∂μ :=
            abs_integral_le_integral_abs
        _ = ∫ ω, |f ω| * |g ω - g' ω| ∂μ := by simp_rw [abs_mul]
        _ ≤ (∫ ω, |f ω| ^ p ∂μ) ^ (1 / p) * (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p') :=
            integral_mul_le_Lp_mul_Lq_of_nonneg hconjp
              (Eventually.of_forall fun ω => abs_nonneg _)
              (Eventually.of_forall fun ω => abs_nonneg _) hfabs hgg'abs'
        _ = A * (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p') := by rw [← hA]
        _ ≤ A * (B * β ^ θ) := mul_le_mul_of_nonneg_left hN hA0
    have hT3 : |(∫ ω, f ω * (g ω - g' ω) ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, (g ω - g' ω) ∂μ|
        ≤ 2 * (A * (B * β ^ θ)) := by
      refine (hsub _ _).trans ?_
      rw [abs_mul]
      have h5 : |∫ ω, f ω ∂μ| * |∫ ω, (g ω - g' ω) ∂μ| ≤ A * (B * β ^ θ) := by
        refine mul_le_mul (abs_integral_le_integral_abs.trans hIA)
          (abs_integral_le_integral_abs.trans (hTg.trans hN)) (abs_nonneg _) hA0
      linarith
    -- the exponent ledger
    have hβθ : β * (β ^ (-(1 / p)) * β ^ (-(1 / q))) = β ^ θ := by
      rw [← Real.rpow_add hβ0]
      calc β * β ^ (-(1 / p) + -(1 / q)) = β ^ (1 : ℝ) * β ^ (-(1 / p) + -(1 / q)) := by
            rw [Real.rpow_one]
        _ = β ^ (1 + (-(1 / p) + -(1 / q))) := (Real.rpow_add hβ0 _ _).symm
        _ = β ^ θ := by rw [hθdef]; congr 1; ring
    have hbc : β * (c₁ * c₂) = A * B * β ^ θ := by
      rw [hc₁def, hc₂def, ← hβθ]; ring
    have hbc2 : c₂ * (A * β ^ (1 - 1 / p)) = A * B * β ^ θ := by
      have h : β ^ (-(1 / q)) * β ^ (1 - 1 / p) = β ^ θ := by
        rw [← Real.rpow_add hβ0, hθdef]
        congr 1
        ring
      rw [hc₂def]
      calc B * β ^ (-(1 / q)) * (A * β ^ (1 - 1 / p))
          = A * B * (β ^ (-(1 / q)) * β ^ (1 - 1 / p)) := by ring
        _ = A * B * β ^ θ := by rw [h]
    -- assemble
    rw [hcov, hsplit]
    have habs3 : ∀ x y z : ℝ, |x + y + z| ≤ |x| + |y| + |z| := fun x y z => by
      have h1 := abs_add_le (x + y) z
      have h2 := abs_add_le x y
      linarith
    refine (habs3 _ _ _).trans ?_
    have hα' : α ≤ β := by rw [hβdef]; linarith
    have hcc : 0 ≤ c₁ * c₂ := by positivity
    have hkey1 : 4 * α * c₁ * c₂ ≤ 4 * (A * B * β ^ θ) := by
      have h : α * (c₁ * c₂) ≤ β * (c₁ * c₂) := mul_le_mul_of_nonneg_right hα' hcc
      rw [hbc] at h
      nlinarith [h]
    have h2 := hT2
    rw [hbc2] at h2
    have h3 : 2 * (A * (B * β ^ θ)) = 2 * (A * B * β ^ θ) := by ring
    rw [h3] at hT3
    have hfinal : 4 * (A * B * β ^ θ) + 2 * (A * B * β ^ θ) + 2 * (A * B * β ^ θ)
        = 8 * β ^ θ * A * B := by ring
    linarith [hT1, hkey1, h2, hT3]
  -- pass to the limit `ε → 0`
  have hcontα : ContinuousAt (fun y : ℝ => 8 * y ^ θ * A * B) α :=
    (((Real.continuousAt_rpow_const α θ (Or.inr hθ0.le)).const_mul 8).mul continuousAt_const).mul
      continuousAt_const
  have hlim : Tendsto (fun ε : ℝ => 8 * (α + ε) ^ θ * A * B) (𝓝[>] (0 : ℝ))
      (𝓝 (8 * α ^ θ * A * B)) := by
    have h1 : Tendsto (fun ε : ℝ => α + ε) (𝓝[>] (0 : ℝ)) (𝓝 α) := by
      have h2 : Continuous (fun ε : ℝ => α + ε) := continuous_const.add continuous_id
      simpa using (h2.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    exact hcontα.tendsto.comp h1
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using main ε hε

end t45_donor
open MeasureTheory

open MeasureTheory in
/-- The probability measure associated with a finite weighted law. -/
def t45_measure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (P : Law Ω) :
    Measure Ω := ∑ ω, ENNReal.ofReal (P.mass ω) • Measure.dirac ω

open MeasureTheory in
instance t45_measure_probability {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (P : Law Ω) : IsProbabilityMeasure (t45_measure P) := by
  constructor
  simp only [t45_measure, Measure.finset_sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => P.nonneg ω), P.total,
    ENNReal.ofReal_one]

open MeasureTheory in
theorem t45_integral {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Law Ω) (f : Ω → ℝ) :
    (∫ ω, f ω ∂t45_measure P) = mean P f := by
  rw [t45_measure, integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (P.nonneg _), mean]
  · intro ω _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

open MeasureTheory in
theorem t45_measure_real {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Law Ω) (A : Set Ω) :
    (t45_measure P A).toReal = prob P (fun ω => ω ∈ A) := by
  rw [← measureReal_def, ← integral_indicator_one (Set.toFinite A).measurableSet,
    t45_integral]
  congr 1

open MeasureTheory in
theorem t45_memLp {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Law Ω) (f : Ω → ℝ) (p : ENNReal) :
    MemLp f p (t45_measure P) := by
  apply MemLp.of_bound (C := ∑ ω, |f ω|)
    (measurable_of_finite f).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using
      (Finset.single_le_sum (fun x _ => abs_nonneg (f x)) (Finset.mem_univ ω))

open MeasureTheory in
theorem t45_covariance_bridge {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Law Ω) (f g : Ω → ℝ) :
    ProbabilityTheory.covariance f g (t45_measure P) = cov P f g := by
  simp only [ProbabilityTheory.covariance, t45_integral, cov]

open MeasureTheory in
theorem t45_alpha_bridge {Ω A B : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Law Ω) (X : Ω → A) (Y : Ω → B) :
    t45_donor.alphaMixCoeff (t45_measure P)
      (MeasurableSpace.comap X ⊤) (MeasurableSpace.comap Y ⊤) = alpha P X Y := by
  unfold t45_donor.alphaMixCoeff alpha
  congr 1
  ext r
  constructor
  · rintro ⟨U,V,⟨S,_,rfl⟩,⟨T,_,rfl⟩,hr⟩
    refine ⟨S,T,?_⟩
    simpa only [t45_measure_real, Set.mem_inter_iff, Set.mem_preimage] using hr
  · rintro ⟨S,T,hr⟩
    refine ⟨X ⁻¹' S,Y ⁻¹' T,⟨S,trivial,rfl⟩,⟨T,trivial,rfl⟩,?_⟩
    simpa only [t45_measure_real, Set.mem_inter_iff, Set.mem_preimage] using hr

/-- Davydov's finite-law equal-exponent specialization, with P009's exact alpha. -/
theorem t45_davydov {Ω A B : Type*} [Fintype Ω] (P : Law Ω)
    (X : Ω → A) (Y : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (q k : ℝ) (hq : 2 < q) (hk : 0 < k)
    (hf : mean P (fun ω => |f (X ω)| ^ q) ≤ k ^ q)
    (hg : mean P (fun ω => |g (Y ω)| ^ q) ≤ k ^ q) :
    |cov P (fun ω => f (X ω)) (fun ω => g (Y ω))| ≤
      8 * k^2 * (alpha P X Y) ^ ((q-2)/q) := by
  letI t45_instMeasurable : MeasurableSpace Ω := ⊤
  have hfm : Measurable[MeasurableSpace.comap X ⊤] (fun ω => f (X ω)) :=
    measurable_from_top.comp (comap_measurable X)
  have hgm : Measurable[MeasurableSpace.comap Y ⊤] (fun ω => g (Y ω)) :=
    measurable_from_top.comp (comap_measurable Y)
  have hq0 : 0 < q := by linarith
  have hn (u : Ω → ℝ) (hu : mean P (fun ω => |u ω| ^ q) ≤ k ^ q) :
      (eLpNorm u (ENNReal.ofReal q) (t45_measure P)).toReal ≤ k := by
    rw [toReal_eLpNorm,
      lpNorm_eq_integral_norm_rpow_toReal (by simp [hq0]) (by simp)
        (measurable_of_finite u).aestronglyMeasurable,
      ENNReal.toReal_ofReal hq0.le]
    simp only [Real.norm_eq_abs, t45_integral, ← one_div]
    calc
      _ ≤ (k ^ q) ^ (1/q) := Real.rpow_le_rpow
        (Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω)
          (Real.rpow_nonneg (abs_nonneg _) _)) hu (by positivity)
      _ = k := by rw [← Real.rpow_mul hk.le, mul_one_div_cancel hq0.ne', Real.rpow_one]
  have h := t45_donor.abs_covariance_le_davydov (μ := t45_measure P)
    (m₁ := MeasurableSpace.comap X ⊤) (m₂ := MeasurableSpace.comap Y ⊤)
    le_top le_top hfm hgm (by linarith : 1 < q) (by linarith : 1 < q)
    (by rw [show 1/q+1/q = 2/q by ring]; exact (div_lt_one hq0).mpr hq)
    (t45_memLp P _ _) (t45_memLp P _ _)
  rw [t45_covariance_bridge, t45_alpha_bridge] at h
  have he : 1-1/q-1/q = (q-2)/q := by field_simp; ring
  rw [he] at h
  calc
    _ ≤ _ := h
    _ ≤ 8 * (alpha P X Y)^((q-2)/q) * k * k := by
      have hα := MixingBasics.alpha_nonnegative P X Y
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hn _ hf) (by positivity))
        (hn _ hg) ENNReal.toReal_nonneg (by positivity)
    _ = _ := by ring


/-- Weighted sums ignore points with zero design mass. -/
theorem t45_mean_congr_support {Ω : Type*} [Fintype Ω] (P : Law Ω)
    (f g : Ω → ℝ) (h : ∀ ω, 0 < P.mass ω → f ω = g ω) : mean P f = mean P g := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hp : P.mass ω = 0
  · simp [hp]
  · rw [h ω (lt_of_le_of_ne (P.nonneg ω) (Ne.symm hp))]

/-- A bounded finite-law covariance estimate on the randomization support. -/
theorem t45_bounded_cov {Ω A B : Type*} [Fintype Ω] (P : Law Ω)
    (X : Ω → A) (Y : Ω → B) (f : A → ℝ) (g : B → ℝ) (C D : ℝ)
    (hf : ∀ ω, 0 < P.mass ω → |f (X ω)| ≤ C)
    (hg : ∀ ω, 0 < P.mass ω → |g (Y ω)| ≤ D) :
    |cov P (fun ω => f (X ω)) (fun ω => g (Y ω))| ≤ 4*alpha P X Y*C*D := by
  letI t45_instMeasurable : MeasurableSpace Ω := ⊤
  have hae (u : Ω → ℝ) (K : ℝ) (h : ∀ ω, 0 < P.mass ω → |u ω| ≤ K) :
      ∀ᵐ ω ∂t45_measure P, |u ω| ≤ K := by
    apply MeasureTheory.ae_iff_of_countable.mpr
    intro ω hω
    apply h
    have he : t45_measure P {ω} = ENNReal.ofReal (P.mass ω) := by
      simp [t45_measure, MeasureTheory.Measure.finset_sum_apply,
        MeasureTheory.Measure.smul_apply, smul_eq_mul, MeasureTheory.Measure.dirac_apply', Pi.single_apply]
    rw [he] at hω
    exact lt_of_not_ge (fun hle => hω (ENNReal.ofReal_eq_zero.mpr hle))
  have h := t45_donor.abs_covariance_le_of_bounded (μ := t45_measure P)
    (m₁ := MeasurableSpace.comap X ⊤) (m₂ := MeasurableSpace.comap Y ⊤)
    le_top le_top
    (measurable_from_top.comp (comap_measurable X))
    (measurable_from_top.comp (comap_measurable Y))
    (hae _ C hf) (hae _ D hg)
  simpa only [t45_covariance_bridge, t45_alpha_bridge, Function.comp_def] using h

/-- Zero event mixing makes covariance vanish, including the q=2 endpoint. -/
theorem t45_zero_cov {Ω A B : Type*} [Fintype Ω] (P : Law Ω)
    (X : Ω → A) (Y : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (ha : alpha P X Y = 0) : cov P (fun ω => f (X ω)) (fun ω => g (Y ω)) = 0 := by
  have h := t45_bounded_cov P X Y f g (∑ ω, |f (X ω)|) (∑ ω, |g (Y ω)|)
    (fun ω _ => Finset.single_le_sum (f := fun v => |f (X v)|)
      (fun v _ => abs_nonneg _) (Finset.mem_univ ω))
    (fun ω _ => Finset.single_le_sum (f := fun v => |g (Y v)|)
      (fun v _ => abs_nonneg _) (Finset.mem_univ ω))
  rw [ha] at h
  simpa using abs_eq_zero.mp (le_antisymm (by simpa using h) (abs_nonneg _))

/-- Extended moment bounds give the required integer moments at infinity too. -/
theorem t45_moment_nat {Ω : Type*} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ)
    (k : ℝ) (q : MomentIndex) (hk : 0 < k) (m : ℕ) (hm : 0 < m)
    (hq : (m:ℝ) ≤ q) (hM : MomentBound P X k q) :
    mean P (fun ω => |X ω|^m) ≤ k^m := by
  by_cases hqt : q = ⊤
  · have hs : ∀ ω, 0 < P.mass ω → |X ω| ≤ k := by simpa [MomentBound, hqt] using hM
    calc
      _ ≤ mean P (fun _ => k^m) := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hp : P.mass ω = 0
        · simp [hp]
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hs ω (lt_of_le_of_ne (P.nonneg ω) (Ne.symm hp))) m)
            (P.nonneg ω)
      _ = _ := mean_const P _
  · lift q to ℝ using hqt with q
    have hqR : (m:ℝ) ≤ q := by exact_mod_cast hq
    have hq0 : 0 < q := (by exact_mod_cast hm : (0:ℝ) < m).trans_le hqR
    have hM' : mean P (fun ω => |X ω| ^ q) ≤ k ^ q := by simpa [MomentBound] using hM
    calc
      _ ≤ (mean P (fun ω => |X ω| ^ q))^((m:ℝ)/q) :=
        finite_moment_interpolation P X m hm q hqR
      _ ≤ (k^q)^((m:ℝ)/q) := Real.rpow_le_rpow
        (Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω)
          (Real.rpow_nonneg (abs_nonneg _) _)) hM' (by positivity)
      _ = k^m := by
        rw [← Real.rpow_mul hk.le, mul_div_cancel₀ _ hq0.ne', Real.rpow_natCast]

/-- Use only second observed moments and first potential moments for overlap. -/
theorem t45_regular_two_one (S : Study) (k : ℝ) (q s : MomentIndex)
    (h : RegularMix S k q s) (t : ℕ) : Regular (S.experiment t) k 2 1 := by
  refine ⟨h.1,le_rfl,le_rfl,h.2.2.2.1 t,?_,?_⟩
  · intro i
    simpa only [Real.rpow_eq_pow, Real.rpow_two] using
      t45_moment_nat (S.experiment t).design _ k q h.1 2 (by decide) h.2.1 (h.2.2.2.2.1 t i)
  · intro i b
    simpa only [Real.rpow_eq_pow, Real.rpow_one, pow_one] using
      t45_moment_nat (S.experiment t).design _ k s h.1 1 (by decide) (by simpa using h.2.2.1)
        (h.2.2.2.2.2 t i b)

/-- The arbitrary-design conditional mean needs overlap, not independence. -/
theorem t45_muBreve_bound {n : ℕ} (hn : 0 < n) (E : Experiment n) (k : ℝ)
    (h : Regular E k 2 1) (b : Bool) : |muBreve E b| ≤ k^2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hm (i : Fin n) : |cmean E.design (fun z => z i = b) (E.outcome i)| ≤ k^2 := by
    have hp := BernoulliCompletion.regular_marginal_bounds E k 2 1 h i b
    have hY : mean E.design (fun z => |E.outcome i z|) ≤ k :=
      BernoulliCompletion.mean_abs_of_moment E.design _ k 2 h.1 (by norm_num) (h.2.2.2.2.1 i)
    have hc : |mean E.design (fun z => if z i = b then E.outcome i z else 0)| ≤ k := by
      apply (BernoulliCompletion.mean_abs_le _ _).trans
      apply le_trans _ hY
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (E.design.nonneg z)
      dsimp only
      split_ifs <;> simp
    rw [cmean, abs_div, show prob E.design (fun z => z i = b) = marginal E i b from rfl,
      abs_of_pos hp.2.2.1, div_eq_mul_inv]
    convert (mul_le_mul hc hp.2.2.2 (inv_nonneg.mpr hp.2.2.1.le) h.1.le).trans_eq
      (show k*k = k^2 by ring) using 1
    apply congrArg (fun u : ℝ => |u| * (marginal E i b)⁻¹)
    apply congrArg (mean E.design)
    funext z
    by_cases hz : z i = b <;> simp [hz]
  rw [muBreve, abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑ i, |cmean E.design (fun z => z i = b) (potential E i b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, k^2 := Finset.sum_le_sum fun i _ => by
      simpa only [BernoulliCompletion.conditional_potential_eq_observed] using hm i
    _ = _ := by simp; ring


/-- Second-moment covariance control, independent of the design. -/
theorem t45_cov_second {Ω : Type*} [Fintype Ω] (P : Law Ω) (f g : Ω → ℝ)
    (k : ℝ) (hf : mean P (fun ω => |f ω|^2) ≤ k^2)
    (hg : mean P (fun ω => |g ω|^2) ≤ k^2) : |cov P f g| ≤ k^2 := by
  have hv (u : Ω → ℝ) (hu : mean P (fun ω => |u ω|^2) ≤ k^2) : var P u ≤ k^2 := by
    rw [variance_second_moment]
    simpa only [sq_abs] using (sub_le_self _ (sq_nonneg (mean P u))).trans hu
  apply (covariance_cauchy_schwarz P f g).trans
  apply Real.sqrt_le_iff.mpr
  refine ⟨sq_nonneg _,?_⟩
  simpa only [pow_two] using mul_le_mul (hv f hf) (hv g hg)
    (variance_nonnegative P g) (sq_nonneg k)

/-- The mixing power is nonnegative with the explicit zero convention. -/
theorem t45_mixPower_nonneg (a θ : ℝ) (ha : 0 ≤ a) : 0 ≤ mixPower a θ := by
  unfold mixPower
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg ha _

/-- Unified covariance control at finite and infinite moment indices. -/
theorem t45_mixing_cov {Ω A B : Type*} [Fintype Ω] (P : Law Ω)
    (X : Ω → A) (Y : Ω → B) (f : A → ℝ) (g : B → ℝ)
    (k : ℝ) (q : MomentIndex) (hk : 0 < k) (hq : 2 ≤ q)
    (hf : MomentBound P (fun ω => f (X ω)) k q)
    (hg : MomentBound P (fun ω => g (Y ω)) k q) :
    |cov P (fun ω => f (X ω)) (fun ω => g (Y ω))| ≤
      8*k^2*mixPower (alpha P X Y) (extExponent q) := by
  have ha0 := MixingBasics.alpha_nonnegative P X Y
  by_cases ha : alpha P X Y = 0
  · simp [t45_zero_cov P X Y f g ha, mixPower, ha]
  · have hap : 0 < alpha P X Y := lt_of_le_of_ne ha0 (Ne.symm ha)
    by_cases hqt : q = ⊤
    · have h := t45_bounded_cov P X Y f g k k
        (by simpa [MomentBound, hqt] using hf) (by simpa [MomentBound, hqt] using hg)
      simp only [extExponent, hqt, ite_true, mixPower, if_neg ha, Real.rpow_eq_pow, Real.rpow_one]
      nlinarith [mul_nonneg (sq_nonneg k) ha0]
    · lift q to ℝ using hqt with q
      have hqR : 2 ≤ q := WithTop.coe_le_coe.mp (show ((2:ℝ):MomentIndex) ≤ (q:MomentIndex) from by simpa using hq)
      have he : extExponent (q:MomentIndex) = (q-2)/q := by simp [extExponent]
      rw [he, mixPower, if_neg ha]
      rcases eq_or_lt_of_le hqR with hqeq | hqgt
      · subst q
        norm_num
        have h := t45_cov_second P _ _ k
          (t45_moment_nat P _ k 2 hk 2 (by decide) le_rfl hf)
          (t45_moment_nat P _ k 2 hk 2 (by decide) le_rfl hg)
        nlinarith [sq_nonneg k]
      · exact t45_davydov P X Y f g q k hqgt hk
          (by simpa [MomentBound] using hf) (by simpa [MomentBound] using hg)

/-- Indicators can only reduce an absolute moment. -/
theorem t45_arm_moment {n : ℕ} (E : Experiment n) (i : Fin n) (b : Bool)
    (k : ℝ) (q : MomentIndex) (hq : 0 ≤ q)
    (h : MomentBound E.design (E.outcome i) k q) :
    MomentBound E.design (armVariable E b 1 i) k q := by
  by_cases hqt : q = ⊤
  · simp only [MomentBound, hqt, ite_true] at h ⊢
    intro z hz
    by_cases hb : z i = b
    · simpa [armVariable, hb] using h z hz
    · simp [armVariable, hb]
      exact (abs_nonneg _).trans (h z hz)
  · lift q to ℝ using hqt with q
    have hqR : 0 ≤ q := by exact_mod_cast hq
    simp only [MomentBound, WithTop.coe_ne_top, if_false, WithTop.untopD_coe] at h ⊢
    apply le_trans _ h
    apply Finset.sum_le_sum
    intro z _
    apply mul_le_mul_of_nonneg_left _ (E.design.nonneg z)
    apply Real.rpow_le_rpow (abs_nonneg _) _ hqR
    by_cases hb : z i = b <;> simp [armVariable, hb]

/-- The unweighted observed arm variable factors through the actual mask. -/
theorem t45_arm_mask {n : ℕ} (E : Experiment n) (b : Bool) (i : Fin n)
    (z : Assignment n) :
    armVariable E b 1 i z = armVariable E b 1 i (masked E i z) := by
  apply BernoulliCompletion.arm_dependsOn E i b 1
  intro j hj
  change Interferes E j i at hj
  simp [masked, hj]

/-- Nonnegative external coefficient, with all dependent pairs removed. -/
theorem t45_alphaExt_nonneg {n : ℕ} (E : Experiment n) (θ : ℝ) : 0 ≤ alphaExt E θ := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg
  · unfold d
    split_ifs <;> norm_num
  · exact t45_mixPower_nonneg _ _ (MixingBasics.alpha_nonnegative _ _ _)

theorem t45_alphaInt_nonneg {n : ℕ} (E : Experiment n) (θ : ℝ) : 0 ≤ alphaInt E θ :=
  Finset.sum_nonneg fun i _ => t45_mixPower_nonneg _ _ (MixingBasics.alpha_nonnegative _ _ _)

/-- Arm covariance: the universal second-moment bound on graph edges,
and the mixing bound elsewhere. -/
theorem t45_arm_cov {n : ℕ} (E : Experiment n) (k : ℝ) (q : MomentIndex)
    (hk : 0 < k) (hq : 2 ≤ q)
    (hM : ∀ i, MomentBound E.design (E.outcome i) k q) (b : Bool) (i j : Fin n) :
    |cov E.design (armVariable E b 1 i) (armVariable E b 1 j)| ≤
      d E i j*k^2 + (1-d E i j)*(8*k^2*mixPower
        (alpha E.design (masked E i) (masked E j)) (extExponent q)) := by
  have hm (i : Fin n) := t45_arm_moment E i b k q (le_trans (by norm_num) hq) (hM i)
  by_cases hd : Dependent E i j
  · simpa [d, hd] using t45_cov_second E.design _ _ k
      (t45_moment_nat E.design _ k q hk 2 (by decide) hq (hm i))
      (t45_moment_nat E.design _ k q hk 2 (by decide) hq (hm j))
  · have h := t45_mixing_cov E.design (masked E i) (masked E j)
        (armVariable E b 1 i) (armVariable E b 1 j) k q hk hq
        (by simpa only [← t45_arm_mask] using hm i)
        (by simpa only [← t45_arm_mask] using hm j)
    simpa only [← t45_arm_mask, d, hd, if_false, zero_mul, sub_zero, one_mul, zero_add] using h

/-- The general finite weighted variance bound after the graph/mixing split. -/
theorem t45_outcome_variance (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (t : ℕ) (b : Bool) :
    var (S.experiment t).design (muHat (S.experiment t) b) ≤
      k^4*dAvg (S.experiment t)/size S t +
        8*k^4*alphaExt (S.experiment t) (extExponent q)/size S t := by
  let E := S.experiment t
  have hn : (0:ℝ) < S.N t := by exact_mod_cast S.positive t
  have hR := t45_regular_two_one S k q s hReg t
  have he : muHat E b = fun z =>
      (∑ i, (marginal E i b)⁻¹*armVariable E b 1 i z)/(S.N t:ℝ) := by
    funext z
    simp only [muHat, armVariable, pow_one, div_eq_mul_inv]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, BernoulliCompletion.variance_div]
  have hw := weighted_variance_absolute E.design (armVariable E b 1)
    (fun i => (marginal E i b)⁻¹) k (fun i =>
      ⟨inv_pos.mpr (BernoulliCompletion.regular_marginal_bounds E k 2 1 hR i b).2.2.1,
        (BernoulliCompletion.regular_marginal_bounds E k 2 1 hR i b).2.2.2⟩)
  calc
    _ ≤ (k^2*(∑ i, ∑ j, |cov E.design (armVariable E b 1 i)
        (armVariable E b 1 j)|))/(S.N t:ℝ)^2 :=
      div_le_div_of_nonneg_right hw.2 (sq_nonneg _)
    _ ≤ (k^2*(∑ i, ∑ j, (d E i j*k^2 + (1-d E i j)*(8*k^2*mixPower
        (alpha E.design (masked E i) (masked E j)) (extExponent q)))))/(S.N t:ℝ)^2 := by
      gcongr with i j
      exact t45_arm_cov E k q hReg.1 hReg.2.1 (hReg.2.2.2.2.1 t) b i j
    _ = _ := by
      dsimp only [E]
      simp_rw [show ∀ i j : Fin (S.N t),
          d (S.experiment t) i j*k^2 + (1-d (S.experiment t) i j)*
            (8*k^2*mixPower (alpha (S.experiment t).design (masked (S.experiment t) i)
              (masked (S.experiment t) j)) (extExponent q)) =
          d (S.experiment t) i j*k^2 + (8*k^2)*((1-d (S.experiment t) i j)*
            mixPower (alpha (S.experiment t).design (masked (S.experiment t) i)
              (masked (S.experiment t) j)) (extExponent q)) from fun i j => by ring]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        alphaExt, dAvg, degree, size]
      field_simp
      <;> ring


/-- The external exponent lies in [0,1] at every admissible index. -/
theorem t45_extExponent_range (q : MomentIndex) (hq : 2 ≤ q) :
    0 ≤ extExponent q ∧ extExponent q ≤ 1 := by
  by_cases hqt : q = ⊤
  · simp [extExponent, hqt]
  · lift q to ℝ using hqt with q
    have hqR : 2 ≤ q := WithTop.coe_le_coe.mp (show ((2:ℝ):MomentIndex) ≤ (q:MomentIndex) from by simpa using hq)
    have hq0 : 0 < q := by linarith
    simp only [extExponent, WithTop.coe_ne_top, if_false, WithTop.untopD_coe]
    exact ⟨div_nonneg (by linarith) hq0.le, (div_le_one hq0).mpr (by linarith)⟩

/-- Every alpha coefficient is bounded by its admissible mixing power. -/
theorem t45_alpha_le_mixPower {Ω A B : Type*} [Fintype Ω]
    (P : Law Ω) (X : Ω → A) (Y : Ω → B) (q : MomentIndex) (hq : 2 ≤ q) :
    alpha P X Y ≤ mixPower (alpha P X Y) (extExponent q) := by
  by_cases ha : alpha P X Y = 0
  · simp [mixPower, ha]
  · have hp : 0 < alpha P X Y := lt_of_le_of_ne
      (MixingBasics.alpha_nonnegative P X Y) (Ne.symm ha)
    simpa only [mixPower, if_neg ha, Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hp (MixingBasics.alpha_le_one P X Y)
        (t45_extExponent_range q hq).2

/-- Indicator covariance is controlled by the same actual outcome masks. -/
theorem t45_indicator_cov {n : ℕ} (E : Experiment n) (b : Bool) (i j : Fin n) :
    |cov E.design (fun z => if z i = b then 1 else 0)
      (fun z => if z j = b then 1 else 0)| ≤
        alpha E.design (masked E i) (masked E j) := by
  rw [BernoulliCompletion.covariance_product_formula]
  have he : mean E.design (fun z => (if z i = b then 1 else 0)*
      (if z j = b then 1 else 0)) = prob E.design (fun z => z i = b ∧ z j = b) := by
    unfold prob
    congr 1
    funext z
    by_cases hi : z i = b <;> by_cases hj : z j = b <;> simp [hi,hj]
  rw [he]
  have hself (ℓ : Fin n) : Interferes E ℓ ℓ := Or.inl rfl
  have h := MixingBasics.event_abs_le_alpha E.design (masked E i) (masked E j)
      {w | w i = b} {w | w j = b}
  simp only [Set.mem_setOf_eq, masked, hself, if_true, prob] at h
  convert h using 1 <;> congr!
  unfold prob
  congr 1
  funext z
  by_cases hz : z i = b ∧ z j = b <;> simp [hz]

/-- The count variance retains graph diagonals and all nonedge mixing. -/
theorem t45_count_variance (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (t : ℕ) (b : Bool) :
    var (S.experiment t).design (fun z => nHat (S.experiment t) b z/size S t) ≤
      k^2*dAvg (S.experiment t)/size S t +
        k^2*alphaExt (S.experiment t) (extExponent q)/size S t := by
  let E := S.experiment t
  have hR := t45_regular_two_one S k q s hReg t
  let V := fun (i : Fin (S.N t)) (z : Assignment (S.N t)) => if z i = b then (1:ℝ) else 0
  have he : (fun z => nHat E b z/size S t) = fun z =>
      (∑ i, (marginal E i b)⁻¹*V i z)/(S.N t:ℝ) := by
    funext z
    simp only [nHat, V, div_eq_mul_inv, size]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, BernoulliCompletion.variance_div]
  have hw := weighted_variance_absolute E.design V
    (fun i => (marginal E i b)⁻¹) k (fun i =>
      ⟨inv_pos.mpr (BernoulliCompletion.regular_marginal_bounds E k 2 1 hR i b).2.2.1,
        (BernoulliCompletion.regular_marginal_bounds E k 2 1 hR i b).2.2.2⟩)
  have hc (i j : Fin (S.N t)) : |cov E.design (V i) (V j)| ≤
      d E i j + (1-d E i j)*mixPower
        (alpha E.design (masked E i) (masked E j)) (extExponent q) := by
    by_cases hd : Dependent E i j
    · simpa [d, hd] using (t45_indicator_cov E b i j).trans
        (MixingBasics.alpha_le_one E.design (masked E i) (masked E j))
    · simpa [d, hd] using (t45_indicator_cov E b i j).trans
        (t45_alpha_le_mixPower E.design (masked E i) (masked E j) q hReg.2.1)
  calc
    _ ≤ (k^2*(∑ i, ∑ j, |cov E.design (V i) (V j)|))/(S.N t:ℝ)^2 :=
      div_le_div_of_nonneg_right hw.2 (sq_nonneg _)
    _ ≤ (k^2*(∑ i, ∑ j, (d E i j + (1-d E i j)*mixPower
        (alpha E.design (masked E i) (masked E j)) (extExponent q))))/(S.N t:ℝ)^2 := by
      gcongr with i j
      exact hc i j
    _ = _ := by
      simp only [Finset.sum_add_distrib, alphaExt, dAvg, degree, size]
      field_simp
      <;> ring

/-- Support boundedness suffices for the internal-mixing discrepancy. -/
theorem t45_support_discrepancy {Ω A : Type*} [Fintype Ω] [Fintype A]
    (P : Law Ω) (B : Ω → Bool) (W : Ω → A) (b : Bool) (f : A → ℝ)
    (k : ℝ) (hk : 0 < k) (hp : 1/k ≤ prob P (fun ω => B ω = b))
    (hf : ∀ ω, 0 < P.mass ω → |f (W ω)| ≤ k) :
    |cmean P (fun ω => B ω = b) (fun ω => f (W ω)) -
      mean P (fun ω => f (W ω))| ≤ 2*k^2*alpha P B W := by
  let g := fun w => max (-k) (min k (f w))
  have hbound (w : A) : |g w| ≤ k := by
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have he (ω : Ω) (hω : 0 < P.mass ω) : f (W ω) = g (W ω) := by
    have hh := abs_le.mp (hf ω hω)
    simp only [g, min_eq_right hh.2, max_eq_right hh.1]
  have hm := t45_mean_congr_support P (fun ω => f (W ω)) (fun ω => g (W ω)) he
  have hc : cmean P (fun ω => B ω = b) (fun ω => f (W ω)) =
      cmean P (fun ω => B ω = b) (fun ω => g (W ω)) := by
    unfold cmean
    congr 1
    apply t45_mean_congr_support
    intro ω hω
    dsimp only
    rw [he ω hω]
  rw [hc, hm]
  simpa only [pow_two, mul_assoc] using
    t45_bounded_discrepancy P B W b g k k hk hk.le hp hbound

/-- Internal bias at every admissible extended moment index. -/
theorem t45_internal_bias (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (t : ℕ) :
    |adse (S.experiment t)-eate (S.experiment t)| ≤
      6*k^2*alphaInt (S.experiment t) (intExponent s)/size S t := by
  let E := S.experiment t
  have hn : (0:ℝ) < S.N t := by exact_mod_cast S.positive t
  have hR := t45_regular_two_one S k q s hReg t
  by_cases hst : s = ⊤
  · apply (t45_bias_estimand_expansion (S.positive t) E).trans
    apply div_le_div_of_nonneg_right _ hn.le
    rw [alphaInt, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb (b : Bool) :
        |cmean E.design (fun z => z i = b) (potential E i b) -
          mean E.design (potential E i b)| ≤
            2*k^2*alpha E.design (fun z => z i) (maskedOthers E i) := by
      obtain ⟨f,hf⟩ := t45_potential_mask_representation E i b
      have hfac : potential E i b = fun z => f (maskedOthers E i z) := funext hf
      have hM : ∀ z, 0 < E.design.mass z → |potential E i b z| ≤ k := by
        simpa only [MomentBound, hst, if_true] using hReg.2.2.2.2.2 t i b
      rw [hfac] at hM ⊢
      exact t45_support_discrepancy E.design (fun z => z i) (maskedOthers E i) b f k
        hReg.1 (by simpa only [one_div, marginal] using
          (BernoulliCompletion.regular_marginal_bounds E k 2 1 hR i b).1) hM
    have hα := MixingBasics.alpha_nonnegative E.design (fun z => z i) (maskedOthers E i)
    have hpow : mixPower (alpha E.design (fun z => z i) (maskedOthers E i)) (intExponent s) =
        alpha E.design (fun z => z i) (maskedOthers E i) := by
      by_cases ha : alpha E.design (fun z => z i) (maskedOthers E i) = 0 <;>
        simp [mixPower, intExponent, hst, ha]
    rw [hpow, Fintype.sum_bool]
    nlinarith [hb true, hb false, mul_nonneg (sq_nonneg k) hα]
  · lift s to ℝ using hst with s
    have hsR : 1 ≤ s := by exact_mod_cast hReg.2.2.1
    have hRf : Regular E k 2 s := by
      refine ⟨hR.1,hR.2.1,hsR,hR.2.2.2.1,hR.2.2.2.2.1,?_⟩
      intro i b
      simpa [MomentBound] using hReg.2.2.2.2.2 t i b
    simpa only [intExponent, WithTop.coe_ne_top, if_false, WithTop.untopD_coe, size]
      using arbitrary_bias_finite_proof (S.positive t) E k 2 s hRf

/-- The conditional observed arm means differ by ADSE under any design. -/
theorem t45_muBreve_difference {n : ℕ} (E : Experiment n) :
    muBreve E true - muBreve E false = adse E := by
  simp only [muBreve, BernoulliCompletion.conditional_potential_eq_observed,
    adse, Finset.sum_sub_distrib, sub_div]

/-- A general ratio wrapper; both counts are forced nonzero by the hypotheses. -/
theorem t45_hajek_error_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (B δ : ℝ) (z : Assignment n) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/2)
    (hm : ∀ b, |muBreve E b| ≤ B)
    (hX : ∀ b, |muHat E b z-muBreve E b| ≤ δ)
    (hY : ∀ b, |nHat E b z/(n:ℝ)-1| ≤ δ) :
    |hajek E z-adse E| ≤ 4*(1+B)*δ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hr (b : Bool) := BernoulliCompletion.ratio_error_bound (muHat E b z)
    (nHat E b z/(n:ℝ)) (muBreve E b) δ B hδ hδ1 (hX b) (hY b) (hm b)
  have hnonzero (b : Bool) : nHat E b z ≠ 0 := by
    intro hz
    have hh := (hr b).1
    rw [hz, zero_div] at hh
    exact (lt_irrefl 0 hh)
  have ha : ArmsNonempty E z := ⟨hnonzero true, hnonzero false⟩
  have he (b : Bool) : (n:ℝ)*muHat E b z/nHat E b z =
      muHat E b z/(nHat E b z/(n:ℝ)) := by
    field_simp [hnR.ne', hnonzero b]
    <;> ring
  rw [hajek, if_pos ha, he true, he false, ← t45_muBreve_difference E]
  calc
    _ = |(muHat E true z/(nHat E true z/(n:ℝ))-muBreve E true)-
      (muHat E false z/(nHat E false z/(n:ℝ))-muBreve E false)| := by congr 1; ring
    _ ≤ |muHat E true z/(nHat E true z/(n:ℝ))-muBreve E true|+
      |muHat E false z/(nHat E false z/(n:ℝ))-muBreve E false| := abs_sub _ _
    _ ≤ 2*(1+B)*δ+2*(1+B)*δ := add_le_add (hr true).2 (hr false).2
    _ = _ := by ring

/-- The arbitrary-design ADSE rate. -/
def t45_rate (S : Study) (q : MomentIndex) (t : ℕ) : ℝ :=
  bernoulliRate S t + Real.sqrt (alphaExt (S.experiment t) (extExponent q))/Real.sqrt (size S t)

theorem t45_rate_pos (S : Study) (q : MomentIndex) (t : ℕ) : 0 < t45_rate S q t :=
  add_pos_of_pos_of_nonneg (BernoulliCompletion.bernoulli_rate_pos S t)
    (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem t45_rate_zero (S : Study) (q : MomentIndex) (hR : Restricted S)
    (hExt : LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S)) :
    Tendsto (t45_rate S q) atTop (nhds 0) := by
  have he : Tendsto (fun t => Real.sqrt (alphaExt (S.experiment t) (extExponent q))/
      Real.sqrt (size S t)) atTop (nhds 0) := by
    simpa only [Real.sqrt_div (t45_alphaExt_nonneg _ _), Real.sqrt_zero] using hExt.sqrt
  change Tendsto (fun t => bernoulliRate S t +
    Real.sqrt (alphaExt (S.experiment t) (extExponent q))/Real.sqrt (size S t)) atTop (nhds 0)
  simpa only [add_zero] using (BernoulliCompletion.bernoulli_rate_zero S hR).add he

theorem t45_rate_square (S : Study) (q : MomentIndex) (t : ℕ) :
    dAvg (S.experiment t)/size S t + alphaExt (S.experiment t) (extExponent q)/size S t ≤
      (t45_rate S q t)^2 := by
  have hb := BernoulliCompletion.bernoulli_rate_square S t
  have hn : (0:ℝ) < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have he : (Real.sqrt (alphaExt (S.experiment t) (extExponent q))/Real.sqrt (size S t))^2 =
      alphaExt (S.experiment t) (extExponent q)/size S t := by
    rw [div_pow, Real.sq_sqrt (t45_alphaExt_nonneg _ _), Real.sq_sqrt hn.le]
  have hpos := mul_nonneg (BernoulliCompletion.bernoulli_rate_pos S t).le
    (div_nonneg (Real.sqrt_nonneg (alphaExt (S.experiment t) (extExponent q)))
      (Real.sqrt_nonneg (size S t)))
  dsimp only [t45_rate]
  nlinarith

/-- Common second-moment control of the four ratio components. -/
theorem t45_component_moments (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (t : ℕ) (b : Bool) :
    mean (S.experiment t).design (fun z =>
      (muHat (S.experiment t) b z-muBreve (S.experiment t) b)^2) ≤
      (8*k^4+k^2+1)*(t45_rate S q t)^2 ∧
    mean (S.experiment t).design (fun z =>
      (nHat (S.experiment t) b z/size S t-1)^2) ≤
      (8*k^4+k^2+1)*(t45_rate S q t)^2 := by
  have hR := t45_regular_two_one S k q s hReg t
  have hp := fun i => (BernoulliCompletion.regular_marginal_bounds _ k 2 1 hR i b).2.2.1
  have hm := BernoulliCompletion.mean_muHat_eq_muBreve (S.experiment t) b hp
  have hn : (0:ℝ) < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have hcount : mean (S.experiment t).design
      (fun z => nHat (S.experiment t) b z/size S t) = 1 := by
    rw [mean_div, expected_arm_count _ _ hp]
    exact div_self hn.ne'
  have hD : 0 ≤ dAvg (S.experiment t)/size S t := div_nonneg
    (le_trans (by norm_num) (average_degree_at_least_one _ (S.positive t))) hn.le
  have hA : 0 ≤ alphaExt (S.experiment t) (extExponent q)/size S t :=
    div_nonneg (t45_alphaExt_nonneg _ _) hn.le
  have hC : 0 ≤ 8*k^4+k^2+1 := by positivity
  have hscale := mul_le_mul_of_nonneg_left (t45_rate_square S q t) hC
  constructor
  · rw [← hm, BernoulliCompletion.centered_square_mean]
    apply (t45_outcome_variance S k q s hReg t b).trans
    calc
      _ = k^4*(dAvg (S.experiment t)/size S t)+
          8*k^4*(alphaExt (S.experiment t) (extExponent q)/size S t) := by ring
      _ ≤ (8*k^4+k^2+1)*(dAvg (S.experiment t)/size S t+
          alphaExt (S.experiment t) (extExponent q)/size S t) := by
        nlinarith [mul_nonneg (pow_nonneg hReg.1.le 4) hD,
          mul_nonneg (sq_nonneg k) hD, mul_nonneg (sq_nonneg k) hA]
      _ ≤ _ := hscale
  · conv_lhs => rw [← hcount, BernoulliCompletion.centered_square_mean]
    apply (t45_count_variance S k q s hReg t b).trans
    calc
      _ = k^2*(dAvg (S.experiment t)/size S t+
          alphaExt (S.experiment t) (extExponent q)/size S t) := by ring
      _ ≤ (8*k^4+k^2+1)*(dAvg (S.experiment t)/size S t+
          alphaExt (S.experiment t) (extExponent q)/size S t) := by
        apply mul_le_mul_of_nonneg_right _ (add_nonneg hD hA)
        nlinarith [pow_nonneg hReg.1.le 4]
      _ ≤ _ := hscale

/-- General-design HT error centered at its exact expectation, ADSE. -/
theorem t45_ht_op (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) :
    Op S (fun t z => ht (S.experiment t) z-adse (S.experiment t)) (t45_rate S q) := by
  apply BernoulliCompletion.op_of_second_moment S _ _ (4*(8*k^4+k^2+1))
    (by positivity) (t45_rate_pos S q)
  intro t
  have hR := t45_regular_two_one S k q s hReg t
  have hp (i : Fin (S.N t)) : 0 < marginal (S.experiment t) i true ∧
      0 < marginal (S.experiment t) i false :=
    ⟨(BernoulliCompletion.regular_marginal_bounds _ k 2 1 hR i true).2.2.1,
      (BernoulliCompletion.regular_marginal_bounds _ k 2 1 hR i false).2.2.1⟩
  have hm := ht_unbiased_ADSE (S.experiment t) hp
  rw [← hm, BernoulliCompletion.centered_square_mean]
  have hv := BernoulliCompletion.variance_sub_le (S.experiment t).design
    (muHat (S.experiment t) true) (muHat (S.experiment t) false)
  have hb (b : Bool) : var (S.experiment t).design (muHat (S.experiment t) b) ≤
      (8*k^4+k^2+1)*(t45_rate S q t)^2 := by
    have hm' := BernoulliCompletion.mean_muHat_eq_muBreve (S.experiment t) b
      (fun i => (BernoulliCompletion.regular_marginal_bounds _ k 2 1 hR i b).2.2.1)
    have hc := (t45_component_moments S k q s hReg t b).1
    rwa [← hm', BernoulliCompletion.centered_square_mean] at hc
  change var (S.experiment t).design (fun z => muHat (S.experiment t) true z-
    muHat (S.experiment t) false z) ≤ _
  nlinarith [hb true, hb false]

/-- General-design Hajek rate from the four centered components. -/
theorem t45_hajek_op (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (hRestricted : Restricted S)
    (hExt : LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S)) :
    Op S (fun t z => hajek (S.experiment t) z-adse (S.experiment t)) (t45_rate S q) := by
  intro ε hε
  let C := 8*k^4+k^2+1
  have hk := hReg.1
  have hC : 0 < C := by dsimp [C]; positivity
  let K := Real.sqrt (4*C/ε)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hs : C ≤ (ε/4)*K^2 := by
    have hr := Real.sq_sqrt (div_nonneg (by positivity : 0 ≤ 4*C) hε.le)
    have hsr := Real.sqrt_nonneg (4*C/ε)
    dsimp [K]
    nlinarith [div_mul_cancel₀ (4*C) hε.ne']
  have hlarge : 0 < 8*(1+k^2)*K := by positivity
  refine ⟨8*(1+k^2)*K, hlarge, ?_⟩
  have hlim : Tendsto (fun t => K*t45_rate S q t) atTop (nhds 0) := by
    simpa using (t45_rate_zero S q hRestricted hExt).const_mul K
  filter_upwards [hlim.eventually_le_const (by norm_num : (0:ℝ) < 1/2)] with t hδ1
  let δ := K*t45_rate S q t
  have hδ : 0 < δ := mul_pos hK (t45_rate_pos S q t)
  let A := fun b z => δ ≤ |muHat (S.experiment t) b z-muBreve (S.experiment t) b|
  let D := fun b z => δ ≤ |nHat (S.experiment t) b z/size S t-1|
  have hp (X : Assignment (S.N t) → ℝ)
      (hM : mean (S.experiment t).design (fun z => (X z)^2) ≤ C*(t45_rate S q t)^2) :
      prob (S.experiment t).design (fun z => δ ≤ |X z|) ≤ ε/4 := by
    calc
      _ ≤ mean (S.experiment t).design (fun z => (X z)^2)/δ^2 := BernoulliCompletion.second_moment_tail _ _ δ hδ
      _ ≤ (C*(t45_rate S q t)^2)/(K*t45_rate S q t)^2 :=
        div_le_div_of_nonneg_right hM (sq_nonneg _)
      _ = C/K^2 := by field_simp [(t45_rate_pos S q t).ne', hK.ne']
      _ ≤ ε/4 := (div_le_iff₀ (sq_pos_of_pos hK)).mpr hs
  have hA (b : Bool) : prob (S.experiment t).design (A b) ≤ ε/4 :=
    hp _ (t45_component_moments S k q s hReg t b).1
  have hD (b : Bool) : prob (S.experiment t).design (D b) ≤ ε/4 :=
    hp _ (t45_component_moments S k q s hReg t b).2
  have hi (z : Assignment (S.N t))
      (hz : (8*(1+k^2)*K)*t45_rate S q t ≤ |hajek (S.experiment t) z-adse (S.experiment t)|) :
      (A true z ∨ A false z) ∨ (D true z ∨ D false z) := by
    by_contra hn
    have hneg : (¬A true z ∧ ¬A false z) ∧ (¬D true z ∧ ¬D false z) := by tauto
    have hX (b : Bool) : |muHat (S.experiment t) b z-muBreve (S.experiment t) b| ≤ δ := by
      cases b
      · exact (lt_of_not_ge hneg.1.2).le
      · exact (lt_of_not_ge hneg.1.1).le
    have hY (b : Bool) : |nHat (S.experiment t) b z/size S t-1| ≤ δ := by
      cases b
      · exact (lt_of_not_ge hneg.2.2).le
      · exact (lt_of_not_ge hneg.2.1).le
    have hb := t45_hajek_error_bound (S.positive t) (S.experiment t) (k^2) δ z hδ.le hδ1
      (fun b => t45_muBreve_bound (S.positive t) _ k (t45_regular_two_one S k q s hReg t) b) hX hY
    have hh := hz.trans hb
    change (8*(1+k^2)*K)*t45_rate S q t ≤ 4*(1+k^2)*(K*t45_rate S q t) at hh
    have hprod : 0 < (1+k^2)*(K*t45_rate S q t) := mul_pos (by positivity) hδ
    nlinarith only [hh, hprod]
  calc
    _ ≤ prob (S.experiment t).design (fun z => A true z ∨ A false z)+
        prob (S.experiment t).design (fun z => D true z ∨ D false z) := probability_union_bound _ _ _ _ hi
    _ ≤ (prob (S.experiment t).design (A true)+prob (S.experiment t).design (A false))+
        (prob (S.experiment t).design (D true)+prob (S.experiment t).design (D false)) :=
      add_le_add (probability_union_bound _ _ _ _ (fun z hz => hz))
        (probability_union_bound _ _ _ _ (fun z hz => hz))
    _ ≤ ε := by linarith only [hA true, hA false, hD true, hD false]


/-- A deterministic centering error of order a preserves stochastic order a. -/
theorem t45_op_recenter (S : Study) (T : (t : ℕ) → Assignment (S.N t) → ℝ)
    (θ φ a : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hshift : ∀ t, |θ t-φ t| ≤ B*a t)
    (hT : Op S (fun t z => T t z-θ t) a) :
    Op S (fun t z => T t z-φ t) a := by
  intro ε hε
  obtain ⟨K,hK,hTail⟩ := hT ε hε
  refine ⟨K+B,by linarith,?_⟩
  filter_upwards [hTail] with t ht
  apply le_trans _ ht
  apply finite_probability_mono
  intro z hz
  have he : |T t z-φ t| ≤ |T t z-θ t|+|θ t-φ t| := by
    calc
      _ = |(T t z-θ t)+(θ t-φ t)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  nlinarith [hshift t]

/-- P009-T45: arbitrary-design consistency and stochastic rates for EATE. -/
theorem arbitrary_EATE_consistency_proof (S : Study) (k : ℝ) (q s : MomentIndex)
    (hReg : RegularMix S k q s) (hMax : MaximalMoments S q s)
    (hRestricted : Restricted S)
    (hExt : LittleO (fun t => alphaExt (S.experiment t) (extExponent q)) (size S))
    (hInt : LittleO (fun t => alphaInt (S.experiment t) (intExponent s)) (size S)) :
    EstimatorClaims S (fun t => eate (S.experiment t)) (fun t =>
      bernoulliRate S t + Real.sqrt (alphaExt (S.experiment t) (extExponent q))/Real.sqrt (size S t) +
        alphaInt (S.experiment t) (intExponent s)/size S t) := by
  let a := fun t => t45_rate S q t + alphaInt (S.experiment t) (intExponent s)/size S t
  have hn (t : ℕ) : 0 < size S t := by dsimp [size]; exact_mod_cast S.positive t
  have hJ (t : ℕ) : 0 ≤ alphaInt (S.experiment t) (intExponent s)/size S t :=
    div_nonneg (t45_alphaInt_nonneg _ _) (hn t).le
  have hRa (t : ℕ) : t45_rate S q t ≤ a t := le_add_of_nonneg_right (hJ t)
  have hlim : Tendsto a atTop (nhds 0) := by
    simpa only [a, add_zero] using (t45_rate_zero S q hRestricted hExt).add hInt
  have hb (t : ℕ) : |adse (S.experiment t)-eate (S.experiment t)| ≤ 6*k^2*a t := by
    calc
      _ ≤ 6*k^2*alphaInt (S.experiment t) (intExponent s)/size S t :=
        t45_internal_bias S k q s hReg t
      _ = 6*k^2*(alphaInt (S.experiment t) (intExponent s)/size S t) := by ring
      _ ≤ 6*k^2*a t := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (t45_rate_pos S q t).le) (by positivity)
  have hHTa : Op S (fun t z => ht (S.experiment t) z-adse (S.experiment t)) a :=
    BernoulliCompletion.op_change_rate S _ _ a 1 (by norm_num)
      (Eventually.of_forall fun t => by simpa only [one_mul] using hRa t)
      (t45_ht_op S k q s hReg)
  have hHJa : Op S (fun t z => hajek (S.experiment t) z-adse (S.experiment t)) a :=
    BernoulliCompletion.op_change_rate S _ _ a 1 (by norm_num)
      (Eventually.of_forall fun t => by simpa only [one_mul] using hRa t)
      (t45_hajek_op S k q s hReg hRestricted hExt)
  have hHT := t45_op_recenter S (fun t z => ht (S.experiment t) z)
    (fun t => adse (S.experiment t)) (fun t => eate (S.experiment t)) a
    (6*k^2) (by positivity) hb hHTa
  have hHJ := t45_op_recenter S (fun t z => hajek (S.experiment t) z)
    (fun t => adse (S.experiment t)) (fun t => eate (S.experiment t)) a
    (6*k^2) (by positivity) hb hHJa
  exact ⟨BernoulliCompletion.probability_of_op_zero S _ a hlim hHT,
    BernoulliCompletion.probability_of_op_zero S _ a hlim hHJ, hHT, hHJ⟩

end
end AronowAudit.P009.Wave1
