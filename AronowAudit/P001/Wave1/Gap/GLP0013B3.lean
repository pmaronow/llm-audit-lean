import AronowAudit.P001.P001_Foundations

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGLP0013B3r2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-- Uniform convergence controls evaluation at zero; the derivative is zero. -/
private theorem t56r2_quadratic_hadamard (F : ℝ → ℝ) (hF : F 0 = 1 / 2) :
    CDFHadamard quadraticCDFFunctional F := by
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro f g; simp
  · intro a f; simp
  · refine ⟨0, le_rfl, ?_⟩
    intro h hh; simp
  · intro h hh t hn ht hbn htlim hhlim hvalid
    have hdiff (n : ℕ) : BddAbove (Set.range (fun x => |hn n x - h x|)) := by
      rcases hbn n with ⟨a, ha⟩
      rcases hh with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      rintro _ ⟨x, rfl⟩
      calc
        |hn n x - h x| ≤ |hn n x| + |h x| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (hn n x) (-h x)
        _ ≤ a + b := add_le_add (ha (Set.mem_range_self x)) (hb (Set.mem_range_self x))
    have heval : Tendsto (fun n => hn n 0) atTop (nhds (h 0)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      simp only [Real.dist_eq]
      exact squeeze_zero (fun _ => abs_nonneg _) (fun n =>
        le_csSup (hdiff n) (Set.mem_range_self (0 : ℝ))) hhlim
    have hlim := htlim.mul (heval.pow 2)
    simp only [zero_mul] at hlim
    convert hlim using 1
    ext n
    dsimp [quadraticCDFFunctional]
    rw [hF]
    field_simp [(ht n).ne']
    <;> ring

private def t56r2_center (x : ℝ) : ℝ := (if x ≤ 0 then 1 else 0) - 1 / 2

private theorem t56r2_center_measurable : Measurable t56r2_center := by
  exact (measurable_const.piecewise measurableSet_Iic measurable_const).sub measurable_const

private theorem t56r2_center_sq (x : ℝ) : t56r2_center x ^ 2 = 1 / 4 := by
  by_cases hx : x ≤ 0 <;> norm_num [t56r2_center, hx]

private theorem t56r2_center_bound (x : ℝ) : ‖t56r2_center x‖ ≤ 1 := by
  by_cases hx : x ≤ 0 <;> norm_num [t56r2_center, hx]

private theorem t56r2_center_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X)
    (hlaw : μ.map (X 0) = (1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℝ) +
      (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) (i : ℕ) :
    (∫ ω, t56r2_center (X i ω) ∂μ) = 0 := by
  have hi := ((hiid.2.2 i).comp t56r2_center_measurable).integral_eq
  change (∫ ω, t56r2_center (X i ω) ∂μ) =
    (∫ ω, t56r2_center (X 0 ω) ∂μ) at hi
  rw [hi, ← integral_map (hiid.1 0).aemeasurable t56r2_center_measurable.aestronglyMeasurable,
    hlaw, integral_add_measure]
  · norm_num [integral_smul_measure, t56r2_center]
  all_goals exact (integrable_dirac (by simp)).smul_measure (by norm_num)

private def t56r2_partial {Ω : Type*} (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, Z i ω

private theorem t56r2_memLp_pow {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f ∞ μ) (k : ℕ) :
    MemLp (fun ω => f ω ^ k) ∞ μ := by
  induction k with
  | zero => simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) ∞ μ)
  | succ k ih => simpa only [pow_succ, Pi.mul_apply] using ih.fun_mul hf

private theorem t56r2_partial_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ) (hZ : ∀ i, MemLp (Z i) ∞ μ) (n : ℕ) :
    MemLp (t56r2_partial Z n) ∞ μ := by
  induction n with
  | zero =>
    have he : t56r2_partial Z 0 = fun _ => 0 := by funext ω; simp [t56r2_partial]
    rw [he]
    exact memLp_const 0
  | succ n ih =>
    have he : t56r2_partial Z (n + 1) = t56r2_partial Z n + Z n := by
      funext ω
      simp only [t56r2_partial, Finset.sum_range_succ, Pi.add_apply]
    rw [he]
    exact ih.add (hZ n)

private theorem t56r2_partial_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (Z i)) (n : ℕ) :
    Measurable (t56r2_partial Z n) := by
  unfold t56r2_partial
  fun_prop

/-- Induction on the sample size gives both exact moments. Independence makes
the mixed odd terms vanish, and the constant squared summands give the recurrence. -/
private theorem t56r2_partial_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (hm : ∀ i, Measurable (Z i)) (hi : iIndepFun Z μ)
    (hZ : ∀ i, MemLp (Z i) ∞ μ) (hsq : ∀ i ω, Z i ω ^ 2 = 1 / 4)
    (hmean : ∀ i, (∫ ω, Z i ω ∂μ) = 0) (n : ℕ) :
    (∫ ω, t56r2_partial Z n ω ^ 2 ∂μ) = (n : ℝ) / 4 ∧
    (∫ ω, t56r2_partial Z n ω ^ 4 ∂μ) = (3 * (n : ℝ) ^ 2 - 2 * n) / 16 := by
  induction n with
  | zero => simp [t56r2_partial]
  | succ n ih =>
    let S := t56r2_partial Z n
    have hS := t56r2_partial_memLp μ Z hZ n
    have hSm := t56r2_partial_measurable Z hm n
    have hind : IndepFun S (Z n) μ := by
      have hh := hi.indepFun_finsetSum_of_notMem hm (s := Finset.range n) (i := n) (by simp)
      have he : (∑ j ∈ Finset.range n, Z j) = S := by
        funext ω
        simp only [Finset.sum_apply, S, t56r2_partial]
      rw [he] at hh
      exact hh
    have hcross (k : ℕ) : (∫ ω, S ω ^ k * Z n ω ∂μ) = 0 := by
      have hi' : IndepFun (fun ω => S ω ^ k) (Z n) μ :=
        hind.comp (measurable_id.pow_const k) measurable_id
      rw [hi'.integral_fun_mul_eq_mul_integral
        (hSm.pow_const k).aestronglyMeasurable (hm n).aestronglyMeasurable, hmean n, mul_zero]
    have hiS (k : ℕ) : Integrable (fun ω => S ω ^ k) μ :=
      (t56r2_memLp_pow μ hS k).integrable (by simp)
    have hiSZ (k : ℕ) : Integrable (fun ω => S ω ^ k * Z n ω) μ := by
      have hp : MemLp (fun ω => S ω ^ k * Z n ω) ∞ μ :=
        (t56r2_memLp_pow μ hS k).fun_mul (hZ n)
      exact hp.integrable (by simp)
    have h2 (ω : Ω) : (S ω + Z n ω)^2 = S ω ^ 2 + 2 * (S ω * Z n ω) + 1 / 4 := by
      nlinarith [hsq n ω]
    have h4 (ω : Ω) : (S ω + Z n ω)^4 =
        S ω ^ 4 + 4 * (S ω ^ 3 * Z n ω) + (3 / 2) * S ω ^ 2 +
          S ω * Z n ω + 1 / 16 := by
      have hz := hsq n ω
      calc
        (S ω + Z n ω)^4 = S ω ^ 4 + 4 * (S ω ^ 3 * Z n ω) +
          6 * S ω ^ 2 * Z n ω ^ 2 + 4 * S ω * Z n ω * Z n ω ^ 2 + (Z n ω ^ 2)^2 := by ring
        _ = _ := by rw [hz]; ring
    have hc1 : (∫ ω, S ω * Z n ω ∂μ) = 0 := by simpa using hcross 1
    have hiSZ1 : Integrable (fun ω => S ω * Z n ω) μ := by simpa using hiSZ 1
    constructor
    · simp only [t56r2_partial, Finset.sum_range_succ]
      change (∫ ω, (S ω + Z n ω)^2 ∂μ) = _
      simp_rw [h2]
      rw [integral_add ((hiS 2).fun_add (hiSZ1.const_mul 2)) (integrable_const _),
        integral_add (hiS 2) (hiSZ1.const_mul 2), integral_const_mul, hc1]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      change (∫ ω, t56r2_partial Z n ω ^ 2 ∂μ) + 2 * 0 + 1 / 4 = _
      rw [ih.1]
      push_cast
      ring
    · simp only [t56r2_partial, Finset.sum_range_succ]
      change (∫ ω, (S ω + Z n ω)^4 ∂μ) = _
      simp_rw [h4]
      rw [integral_add ((((hiS 4).fun_add ((hiSZ 3).const_mul 4)).fun_add
          ((hiS 2).const_mul (3 / 2))).fun_add hiSZ1) (integrable_const _),
        integral_add (((hiS 4).fun_add ((hiSZ 3).const_mul 4)).fun_add
          ((hiS 2).const_mul (3 / 2))) hiSZ1,
        integral_add ((hiS 4).fun_add ((hiSZ 3).const_mul 4)) ((hiS 2).const_mul (3 / 2)),
        integral_add (hiS 4) ((hiSZ 3).const_mul 4), integral_const_mul,
        integral_const_mul, hcross 3, hc1]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      change (∫ ω, t56r2_partial Z n ω ^ 4 ∂μ) + 4 * 0 +
        (3 / 2) * (∫ ω, t56r2_partial Z n ω ^ 2 ∂μ) + 0 + 1 / 16 = _
      rw [ih.1, ih.2]
      push_cast
      ring


private theorem t56r2_population_cdf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (hlaw : μ.map X = (1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℝ) +
      (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :
    cdf μ X 0 = 1 / 2 := by
  change (μ (X ⁻¹' Set.Iic 0)).toReal = _
  rw [← Measure.map_apply hX measurableSet_Iic, hlaw]
  norm_num [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.indicator, Set.mem_Iic]

private theorem t56r2_empirical_zero {Ω : Type*} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    cdf (empirical X n ω) id 0 =
      (∑ i ∈ Finset.range n, if X i ω ≤ 0 then (1 : ℝ) else 0) / (n : ℝ) := by
  unfold cdf prob empirical
  simp only [id_eq, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top (Measure.dirac (X i ω)) _)]
  have hd (i : ℕ) :
      (Measure.dirac (X i ω) {x : ℝ | x ≤ 0}).toReal =
        if X i ω ≤ 0 then (1 : ℝ) else 0 := by
    by_cases hx : X i ω ≤ 0 <;> simp [Measure.dirac_apply, Set.indicator, hx]
  simp_rw [hd]
  ring

private theorem t56r2_empirical_center {Ω : Type*} (X : ℕ → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (ω : Ω) :
    cdf (empirical X n ω) id 0 - 1 / 2 =
      t56r2_partial (fun i z => t56r2_center (X i z)) n ω / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [t56r2_empirical_zero]
  simp only [t56r2_partial, t56r2_center, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

private theorem t56r2_statistic_square {Ω : Type*} (X : ℕ → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (ω : Ω) :
    (Real.sqrt n * quadraticCDFFunctional (cdf (empirical X n ω) id)) ^ 2 =
      (1 / (n : ℝ) ^ 3) *
        t56r2_partial (fun i z => t56r2_center (X i z)) n ω ^ 4 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold quadraticCDFFunctional
  rw [t56r2_empirical_center X n hn ω, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp
  <;> ring

/-- A second-moment bound gives the exact closed-threshold event in `CP`. -/
private theorem t56r2_cp_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Ω → ℝ)
    (hW : ∀ n, 0 < n → Integrable (fun ω => W n ω ^ 2) μ)
    (hmoment : Tendsto (fun n => ∫ ω, W n ω ^ 2 ∂μ) atTop (nhds 0)) :
    CP μ W 0 := by
  intro ε hε
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hbound : ∀ᶠ n in atTop,
      prob μ {ω | ε ≤ dist (W n ω) 0} ≤
        (∫ ω, W n ω ^ 2 ∂μ) / ε ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (W n ω))) (hW n hn) (ε ^ 2)
    have hsubset : {ω | ε ≤ dist (W n ω) 0} ⊆ {ω | ε ^ 2 ≤ W n ω ^ 2} := by
      intro ω hω
      have habs : ε ≤ |W n ω| := by simpa [Real.dist_eq] using hω
      change ε ^ 2 ≤ W n ω ^ 2
      exact (sq_le_sq (a := ε) (b := W n ω)).mpr
        (by simpa only [abs_of_pos hε] using habs)
    have hmono : prob μ {ω | ε ≤ dist (W n ω) 0} ≤
        μ.real {ω | ε ^ 2 ≤ W n ω ^ 2} := by
      exact measureReal_mono hsubset
    exact hmono.trans ((le_div_iff₀ hε2).2 (by nlinarith [hmarkov]))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => ENNReal.toReal_nonneg)) hbound
  simpa using hmoment.div_const (ε ^ 2)

/-- The quadratic CDF plug-in has zero derivative, its exact second moment,
and a degenerate probability limit under fair Bernoulli observations. -/
theorem quadratic_plugin_degenerate_counterexample_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (X : ℕ → Ω → ℝ) (hiid : IID μ X)
   (hlaw : μ.map (X 0)=(1/2 : ℝ≥0∞) • Measure.dirac (0 : ℝ)+
     (1/2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :
   CDFHadamard quadraticCDFFunctional (cdf μ (X 0)) ∧
   quadraticCDFFunctional (cdf μ (X 0))=0 ∧
   (∀ n : ℕ,0 < n → mean μ (fun ω =>
     (Real.sqrt n*quadraticCDFFunctional (cdf (empirical X n ω) id))^2)=
       (3*(n : ℝ)-2)/(16*(n : ℝ)^2)) ∧
   CP μ (fun n ω => Real.sqrt n*quadraticCDFFunctional (cdf (empirical X n ω) id)) 0 := by
  have hpop := t56r2_population_cdf μ (X 0) (hiid.1 0) hlaw
  let Z : ℕ → Ω → ℝ := fun i ω => t56r2_center (X i ω)
  have hZm (i : ℕ) : Measurable (Z i) := t56r2_center_measurable.comp (hiid.1 i)
  have hZi : iIndepFun Z μ :=
    hiid.2.1.comp (fun _ => t56r2_center) (fun _ => t56r2_center_measurable)
  have hZLp (i : ℕ) : MemLp (Z i) ∞ μ :=
    memLp_top_of_bound (hZm i).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => t56r2_center_bound (X i ω)))
  have hZmean (i : ℕ) : (∫ ω, Z i ω ∂μ) = 0 :=
    t56r2_center_mean μ X hiid hlaw i
  have hZsq (i : ℕ) (ω : Ω) : Z i ω ^ 2 = 1 / 4 := t56r2_center_sq (X i ω)
  have hpartial (n : ℕ) :=
    t56r2_partial_moments μ Z hZm hZi hZLp hZsq hZmean n
  let W : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt n * quadraticCDFFunctional (cdf (empirical X n ω) id)
  have hsquare (n : ℕ) (hn : 0 < n) (ω : Ω) :
      W n ω ^ 2 = (1 / (n : ℝ) ^ 3) * t56r2_partial Z n ω ^ 4 :=
    t56r2_statistic_square X n hn ω
  have hW (n : ℕ) (hn : 0 < n) : Integrable (fun ω => W n ω ^ 2) μ := by
    simp_rw [hsquare n hn]
    exact ((t56r2_memLp_pow μ (t56r2_partial_memLp μ Z hZLp n) 4).integrable
      (by simp)).const_mul _
  have hmoment (n : ℕ) (hn : 0 < n) :
      mean μ (fun ω => W n ω ^ 2) = (3 * (n : ℝ) - 2) / (16 * (n : ℝ) ^ 2) := by
    unfold mean
    simp_rw [hsquare n hn]
    rw [integral_const_mul, (hpartial n).2]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    <;> ring
  refine ⟨t56r2_quadratic_hadamard _ hpop, ?_, hmoment, ?_⟩
  · simp [quadraticCDFFunctional, hpop]
  · apply t56r2_cp_of_second_moment μ W hW
    have hlim : Tendsto (fun n : ℕ =>
        (3 / 16 : ℝ) * (n : ℝ)⁻¹ - (1 / 8 : ℝ) * ((n : ℝ)⁻¹) ^ 2)
        atTop (nhds 0) := by
      have h := ((tendsto_const_nhds (x := (3 / 16 : ℝ))).mul
        tendsto_inv_atTop_nhds_zero_nat).sub
        ((tendsto_const_nhds (x := (1 / 8 : ℝ))).mul
          (tendsto_inv_atTop_nhds_zero_nat.pow 2))
      simpa using h
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    change _ = mean μ (fun ω => W n ω ^ 2)
    rw [hmoment n hn]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    <;> ring

end
end AronowAudit.P001.Wave1
