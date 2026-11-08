import SAP.P061a.Defs.WholeW1
import SAP.P061a.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.WH.W1

open scoped BigOperators Topology Classical BoundedContinuousFunction ENNReal
open Filter MeasureTheory

/-- The power-set atomic measure is the project's design law with the top measurable space. -/
theorem atomic_measure_eqW1 {Ω : Type} (D : AtomicDesign Ω) :
    atomicMeasureW1 D = @AronowAudit.P061.designLaw Ω Ω ⊤ (Bridge.toProject D) id := rfl

theorem atomic_probabilityW1 {Ω : Type} (D : AtomicDesign Ω) :
    @IsProbabilityMeasure Ω ⊤ (atomicMeasureW1 D) := by
  rw [atomic_measure_eqW1]
  exact @AronowAudit.P061.designLaw_isProbability Ω Ω ⊤ (Bridge.toProject D) id

theorem atomic_eventW1 {Ω : Type} (D : AtomicDesign Ω) (A : Set Ω) :
    atomicMeasureW1 D A = ∑' z, if z ∈ A then ENNReal.ofReal (D.mass z) else 0 := by
  let : MeasurableSpace Ω := ⊤
  rw [atomicMeasureW1, Measure.sum_apply _ (MeasurableSet.of_discrete)]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ A <;>
    simp [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.of_discrete, hz]

theorem atomic_event_realW1 {Ω : Type} (D : AtomicDesign Ω) (A : Set Ω) :
    (atomicMeasureW1 D A).toReal = eventProbability D (fun z => z ∈ A) := by
  let : MeasurableSpace Ω := ⊤
  rw [atomic_measure_eqW1]
  exact @AronowAudit.P061.designLaw_apply Ω Ω ⊤ (Bridge.toProject D) id A
    MeasurableSet.of_discrete

/-- Expansion of nonnegative sign integrals never uses a totalized real integral. -/
theorem atomic_positive_integralW1 {Ω : Type} (D : AtomicDesign Ω) (f : Ω → ℝ) :
    positiveIntegralW1 (atomicMeasureW1 D) f = positiveExpectationW1 D f := by
  let : MeasurableSpace Ω := ⊤
  simp only [positiveIntegralW1, atomicMeasureW1, lintegral_sum_measure,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul, positiveExpectationW1]
  apply tsum_congr
  intro z
  exact (ENNReal.ofReal_mul (D.mass_nonnegative z)).symm

/-- Normalized restriction expresses the ordinary conditional law on a positive cell. -/
theorem conditional_positive_integralW1 {Ω : Type} (D : AtomicDesign Ω)
    (A : Ω → Prop) (f : Ω → ℝ) :
    positiveIntegralW1 (conditionalMeasureW1 D A) f =
      (ENNReal.ofReal (eventProbability D A))⁻¹ *
        positiveExpectationW1 D (fun z => if A z then f z else 0) := by
  let : MeasurableSpace Ω := ⊤
  unfold positiveIntegralW1 conditionalMeasureW1
  rw [lintegral_smul_measure]
  simp only [smul_eq_mul]
  congr 1
  rw [← atomic_positive_integralW1]
  unfold positiveIntegralW1
  rw [← lintegral_indicator MeasurableSet.of_discrete]
  apply lintegral_congr
  intro z
  by_cases hz : A z <;> simp [Set.indicator, hz]

theorem real_vector_bijectiveW1 : Function.Bijective realUnitVectorW1 := by
  constructor
  · intro x y h
    exact congrFun h 0
  · intro v
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i
    rfl

/-- A nonnegative sequence whose square diverges itself tends to positive infinity. -/
theorem positive_of_square_atTopW1 (f : ℕ → ℝ) (hp : ∀ n, 0 ≤ f n)
    (h : Tendsto (fun n => (f n)^2) atTop atTop) : Tendsto f atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(tendsto_atTop.mp h) ((max b 0)^2 + 1)] with n hn
  have hm : 0 ≤ max b 0 := le_max_right _ _
  have hf : max b 0 ≤ f n := by nlinarith [hp n]
  exact (le_max_left b 0).trans hf

/-- Exact population-size normalization for the gap along N=2m^8. -/
theorem gap_normalizationW1 (m : ℕ) (hm : 2 ≤ m) :
    (1/(m : ℝ)^2) * Real.rpow (m^8*2 : ℝ) (1/4 : ℝ) = Real.rpow 2 (1/4 : ℝ) := by
  simp only [Real.rpow_eq_pow]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hpow : Real.rpow ((m : ℝ)^8) (1/4 : ℝ) = (m : ℝ)^2 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast_mul hmpos.le]
    norm_num
  rw [Real.mul_rpow (by positivity) (by norm_num), (show ((m : ℝ)^8) ^ (1/4 : ℝ) = (m : ℝ)^2 from hpow)]
  field_simp

/-- The four-atom variance formula specializes to the displayed polynomial. -/
theorem variance_expressionW1 (m : ℕ) :
    variancePolynomial m = 8*(1+1/(m : ℝ))*(1+1/(m : ℝ)) +
      (6+2/(m : ℝ))*(1/(m : ℝ))^2 - 4*(1/(m : ℝ))^4 := by
  unfold variancePolynomial
  ring

/-- A relation consisting exactly of partners has degree and maximum degree one. -/
theorem matching_degreesW1 (K : ℕ) (hK : 0 < K) (R : Fin (K*2) → Fin (K*2) → Prop)
    (hR : ∀ i j, R i j ↔ j = partnerIndexW1 K i) :
    (∀ i, relationDegreeW1 R i = 1) ∧ relationMaxDegreeW1 R = 1 := by
  have hd (i : Fin (K*2)) : relationDegreeW1 R i = 1 := by
    unfold relationDegreeW1
    have hf : Finset.univ.filter (R i) = {partnerIndexW1 K i} := by
      ext j
      simp [hR]
    rw [hf, Finset.card_singleton]
  refine ⟨hd, ?_⟩
  have hn : (Finset.univ : Finset (Fin (K*2))).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  change Finset.univ.sup (fun i => relationDegreeW1 R i) = 1
  simp_rw [hd]
  exact Finset.sup_const hn 1

theorem boundary_scale_posW1 (n : ℕ) : 0 < boundaryScaleW1 n := by
  unfold boundaryScaleW1
  positivity

theorem boundary_gap_ratioW1 (n : ℕ) :
    |boundaryTargetW1 n| / boundaryScaleW1 n = boundaryScaleW1 n := by
  have hn : (n+2 : ℝ) ≠ 0 := by positivity
  rw [abs_of_nonneg (by unfold boundaryTargetW1; positivity)]
  unfold boundaryTargetW1 boundaryScaleW1
  field_simp

theorem boundary_scale_limitW1 : Tendsto boundaryScaleW1 atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1/(n+2 : ℝ)) atTop (𝓝 0)
  simpa only [boundaryScaleW1, Nat.cast_add, Nat.cast_ofNat, one_div, Function.comp_def] using
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)

theorem fair_law_probabilityW1 : IsProbabilityMeasure fairSignLawW1 := by
  constructor
  simpa [fairSignLawW1, Measure.add_apply, Measure.smul_apply] using ENNReal.inv_two_add_inv_two

theorem fair_law_integralW1 (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂fairSignLawW1) = (f (-1) + f 1)/2 := by
  let : IsFiniteMeasure ((1/2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) :=
    (Measure.dirac (-1 : ℝ)).smul_finite (by norm_num)
  let : IsFiniteMeasure ((1/2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
    (Measure.dirac (1 : ℝ)).smul_finite (by norm_num)
  have hneg : MeasureTheory.Integrable (fun x => f x) ((1/2 : ℝ≥0∞) • Measure.dirac (-1)) :=
    f.integrable _
  have hpos : MeasureTheory.Integrable (fun x => f x) ((1/2 : ℝ≥0∞) • Measure.dirac 1) :=
    f.integrable _
  rw [fairSignLawW1, integral_add_measure hneg hpos]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  norm_num
  ring

/-- The normalized padded-pair density; summing its first two coordinates leaves
n fair bits, including the empty remainder at n=0. -/
noncomputable def boundaryDesignW1 (n : ℕ) : AtomicDesign (BoundarySpaceW1 n) where
  mass := fun z => (if z 0 = z 1 then (3/8 : ℝ) else 1/8) * (1/2 : ℝ)^n
  mass_nonnegative := by intro z; split_ifs <;> positivity
  mass_summable := Summable.of_finite
  mass_total := by
    rw [tsum_fintype, AronowAudit.P061.sum_vector_succ (n+1)]
    simp only [AronowAudit.P061.sum_vector_succ n, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    have hn : (2 : ℝ)^n * (1/2 : ℝ)^n = 1 := by rw [← mul_pow]; norm_num
    norm_num [Fin.sum_univ_two]
    nlinarith

end SAP.P061a.WH.W1
