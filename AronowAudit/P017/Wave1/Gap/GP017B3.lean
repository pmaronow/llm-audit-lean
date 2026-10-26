import AronowAudit.P017.P017_Audit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
P017-T8: the two corrected mean-square limits.
The bounds follow from pointwise lemmas. The constant is twice the finite
fourth Gaussian moment; its exact value is irrelevant to these limits.
-/

namespace AronowAudit.P017.Wave1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

/-- Finiteness, without needing to evaluate the fourth Gaussian moment. -/
theorem t8limits_gaussian_fourth_integrable (v : ℝ≥0) :
    Integrable (fun z : ℝ => z ^ 4) (gaussianReal 0 v) := by
  exact integrable_pow_of_mem_interior_integrableExpSet
    (X := id) (μ := gaussianReal 0 v) (by simp) 4

/-- The printed remainder assumption already implies unscaled L² decay. -/
theorem t8limits_remainder_second_moment_zero {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) (ε : ℕ → Ξ → ℝ) (he : SmallRemainderMS P ε) :
    Tendsto (fun n => ∫ ω, ε n ω ^ 2 ∂P) atTop (𝓝 0) := by
  unfold SmallRemainderMS at he
  refine squeeze_zero'
    (Eventually.of_forall (fun n => integral_nonneg (fun ω => sq_nonneg (ε n ω))))
    ?_ he
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hs : 1 ≤ sqrtN n := by
    change 1 ≤ Real.sqrt (n : ℝ)
    apply Real.one_le_sqrt.mpr
    exact_mod_cast hn
  have hen : 0 ≤ ∫ ω, ε n ω ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg (ε n ω))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hen

/-- A deterministic squeeze shared by both squared-error sequences.
Only eventual bounds are required, so the value at zero is immaterial. -/
theorem t8limits_scaled_mse_limit (A e : ℕ → ℝ) (K c : ℝ) (hc : 0 < c)
    (hA : ∀ n, 0 ≤ A n) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      A n ≤ K / (c ^ 2 * (n : ℝ) ^ 2) + 2 * e n / (n : ℝ)) :
    Tendsto (fun n : ℕ => (n : ℝ) * A n) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun n : ℕ => (K / c ^ 2) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (K / c ^ 2)
  have hsecond : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul he
  have hupper : Tendsto (fun n : ℕ => (K / c ^ 2) / (n : ℝ) + 2 * e n)
      atTop (𝓝 0) := by
    simpa only [zero_add] using hfirst.add hsecond
  refine squeeze_zero'
    (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg n) (hA n)))
    ?_ hupper
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with n hb hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  calc
    (n : ℝ) * A n ≤
        (n : ℝ) * (K / (c ^ 2 * (n : ℝ) ^ 2) + 2 * e n / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
    _ = (K / c ^ 2) / (n : ℝ) + 2 * e n := by
      field_simp [hc.ne', hnne] <;> ring

/-- The two finite bounds needed below, using a fixed finite fourth moment.
Measurability and integrability are established before integral monotonicity.
The normal and remainder variables can be arbitrarily dependent. -/
theorem t8limits_finite_bounds {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (μ c : ℝ) (v : ℝ≥0) (hc : 0 < c)
    (hhm : ∀ n, Measurable (hat n)) (hr : NormalRemainder P hat Z ε μ v)
    (n : ℕ) (hn : 1 ≤ n) :
    ((∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤
      2 * (∫ z : ℝ, z ^ 4 ∂gaussianReal 0 v) / (c ^ 2 * (n : ℝ) ^ 2) +
        2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
    ((∫ ω, (μ + Z n ω / sqrtN n - clipReal μ c (hat n ω)) ^ 2 ∂P) ≤
      2 * (∫ z : ℝ, z ^ 4 ∂gaussianReal 0 v) / (c ^ 2 * (n : ℝ) ^ 2) +
        2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) := by
  have hZm : Measurable (Z n) := (hr.1 n hn).1
  have hZlaw : P.map (Z n) = gaussianReal 0 v := (hr.1 n hn).2
  have hε2 : Integrable (fun ω => ε n ω ^ 2) P := (hr.2.1 n hn).2
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : 0 < sqrtN n := Real.sqrt_pos.mpr hnpos
  have hsne : sqrtN n ≠ 0 := ne_of_gt hspos
  have hs2 : sqrtN n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs4 : sqrtN n ^ 4 = (n : ℝ) ^ 2 := by
    calc
      sqrtN n ^ 4 = (sqrtN n ^ 2) ^ 2 := by ring
      _ = (n : ℝ) ^ 2 := by rw [hs2]
  have hZ4map : Integrable (fun z : ℝ => z ^ 4) (P.map (Z n)) := by
    rw [hZlaw]
    exact t8limits_gaussian_fourth_integrable v
  have hZ4 : Integrable (fun ω => Z n ω ^ 4) P := by
    exact hZ4map.comp_measurable hZm
  have hZ4eq : (∫ ω, Z n ω ^ 4 ∂P) = ∫ z : ℝ, z ^ 4 ∂gaussianReal 0 v := by
    calc
      (∫ ω, Z n ω ^ 4 ∂P) = ∫ z : ℝ, z ^ 4 ∂P.map (Z n) :=
        (integral_map (μ := P) (φ := Z n) (f := fun z : ℝ => z ^ 4) hZm.aemeasurable
          (measurable_id.pow_const (4 : ℕ)).aestronglyMeasurable).symm
      _ = ∫ z : ℝ, z ^ 4 ∂gaussianReal 0 v := by rw [hZlaw]
  let T : Ξ → ℝ := fun ω => μ + Z n ω / sqrtN n
  let A : Ξ → ℝ := fun ω => residual μ c (hat n ω) ^ 2
  let B : Ξ → ℝ := fun ω => (T ω - clipReal μ c (hat n ω)) ^ 2
  let D : Ξ → ℝ := fun ω =>
    2 * Z n ω ^ 4 / (c ^ 2 * (n : ℝ) ^ 2) + 2 * ε n ω ^ 2 / (n : ℝ)
  have hTm : Measurable T := measurable_const.add (hZm.div_const (sqrtN n))
  have hclip : Measurable (fun ω => clipReal μ c (hat n ω)) := by
    unfold clipReal
    exact measurable_const.min (measurable_const.max (hhm n))
  have hAm : AEStronglyMeasurable A P := by
    change AEStronglyMeasurable (fun ω => (hat n ω - clipReal μ c (hat n ω)) ^ 2) P
    exact (((hhm n).sub hclip).pow_const (2 : ℕ)).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B P :=
    ((hTm.sub hclip).pow_const (2 : ℕ)).aestronglyMeasurable
  have hDi : Integrable D P :=
    ((hZ4.const_mul 2).div_const (c ^ 2 * (n : ℝ) ^ 2)).add
      ((hε2.const_mul 2).div_const (n : ℝ))
  have hpoint : ∀ᵐ ω ∂P, A ω ≤ D ω ∧ B ω ≤ D ω := by
    filter_upwards [hr.2.2 n hn] with ω hω
    have hrep : hat n ω = T ω + ε n ω / sqrtN n := by
      have hdiv : hat n ω - μ = (Z n ω + ε n ω) / sqrtN n := by
        apply (eq_div_iff hsne).mpr
        simpa only [mul_comm] using hω
      rw [add_div] at hdiv
      dsimp only [T]
      linarith only [hdiv]
    have hnormal : residual μ c (T ω) ^ 2 ≤
        Z n ω ^ 4 / (c ^ 2 * (n : ℝ) ^ 2) := by
      calc
        residual μ c (T ω) ^ 2 ≤ (T ω - μ) ^ 4 / c ^ 2 :=
          (residual_tail_fourth_bound μ c (T ω) hc).1.trans
            (residual_tail_fourth_bound μ c (T ω) hc).2
        _ = Z n ω ^ 4 / (c ^ 2 * (n : ℝ) ^ 2) := by
          dsimp only [T]
          rw [add_sub_cancel_left, div_pow, div_div, hs4,
            mul_comm ((n : ℝ) ^ 2) (c ^ 2)]
    have hpert := perturbation_square_bounds μ c (T ω) (ε n ω / sqrtN n) hc.le
    have hupper : 2 * residual μ c (T ω) ^ 2 + 2 * (ε n ω / sqrtN n) ^ 2 ≤ D ω := by
      calc
        _ ≤ 2 * (Z n ω ^ 4 / (c ^ 2 * (n : ℝ) ^ 2)) +
            2 * (ε n ω / sqrtN n) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hnormal (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
        _ = D ω := by
          dsimp only [D]
          rw [div_pow, hs2]
          ring
    constructor
    · change residual μ c (hat n ω) ^ 2 ≤ D ω
      rw [hrep]
      exact hpert.1.trans hupper
    · change (T ω - clipReal μ c (hat n ω)) ^ 2 ≤ D ω
      rw [hrep]
      exact hpert.2.trans hupper
  have hAi : Integrable A P :=
    hDi.mono_nonneg hAm (Eventually.of_forall (fun ω => sq_nonneg _))
      (hpoint.mono (fun _ h => h.1))
  have hBi : Integrable B P :=
    hDi.mono_nonneg hBm (Eventually.of_forall (fun ω => sq_nonneg _))
      (hpoint.mono (fun _ h => h.2))
  have hDint : (∫ ω, D ω ∂P) =
      2 * (∫ z : ℝ, z ^ 4 ∂gaussianReal 0 v) / (c ^ 2 * (n : ℝ) ^ 2) +
        2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ) := by
    dsimp only [D]
    rw [integral_add ((hZ4.const_mul 2).div_const (c ^ 2 * (n : ℝ) ^ 2))
      ((hε2.const_mul 2).div_const (n : ℝ))]
    simp only [integral_div, integral_const_mul, hZ4eq]
  constructor
  · exact (integral_mono_ae hAi hDi (hpoint.mono (fun _ h => h.1))).trans_eq hDint
  · exact (integral_mono_ae hBi hDi (hpoint.mono (fun _ h => h.2))).trans_eq hDint

/-- Both mean-square conclusions of corrected Proposition 4. -/
theorem corrected_proposition4_limits_proof {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (hat Z ε : ℕ → Ξ → ℝ)
    (μ c : ℝ) (v : ℝ≥0) (hc : 0 < c) (hv : 0 < v)
    (hhm : ∀ n, Measurable (hat n)) (hr : NormalRemainder P hat Z ε μ v)
    (he : SmallRemainderMS P ε) :
    SmallMSE P (fun n ω => residual μ c (hat n ω)) ∧
    SmallMSE P (fun n ω => μ + Z n ω / sqrtN n - clipReal μ c (hat n ω)) := by
  have he0 : Tendsto (fun n => ∫ ω, ε n ω ^ 2 ∂P) atTop (𝓝 0) :=
    t8limits_remainder_second_moment_zero P ε he
  let K : ℝ := 2 * (∫ z : ℝ, z ^ 4 ∂gaussianReal 0 v)
  have hfinite : ∀ᶠ n in atTop,
      ((∫ ω, residual μ c (hat n ω) ^ 2 ∂P) ≤
        K / (c ^ 2 * (n : ℝ) ^ 2) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) ∧
      ((∫ ω, (μ + Z n ω / sqrtN n - clipReal μ c (hat n ω)) ^ 2 ∂P) ≤
        K / (c ^ 2 * (n : ℝ) ^ 2) + 2 * (∫ ω, ε n ω ^ 2 ∂P) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact t8limits_finite_bounds P hat Z ε μ c v hc hhm hr n hn
  constructor
  · unfold SmallMSE
    exact t8limits_scaled_mse_limit
      (fun n => ∫ ω, residual μ c (hat n ω) ^ 2 ∂P)
      (fun n => ∫ ω, ε n ω ^ 2 ∂P) K c hc
      (fun n => integral_nonneg (fun ω => sq_nonneg _)) he0
      (hfinite.mono (fun _ h => h.1))
  · unfold SmallMSE
    exact t8limits_scaled_mse_limit
      (fun n => ∫ ω, (μ + Z n ω / sqrtN n - clipReal μ c (hat n ω)) ^ 2 ∂P)
      (fun n => ∫ ω, ε n ω ^ 2 ∂P) K c hc
      (fun n => integral_nonneg (fun ω => sq_nonneg _)) he0
      (hfinite.mono (fun _ h => h.2))

end

end AronowAudit.P017.Wave1
