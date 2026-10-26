import AronowAudit.P023.Wave1.Gap.GP023B1b
import AronowAudit.P023.Wave1.Gap.GP023B2b
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp

/-! The full-support clustered witness, using density normalization and
two-point integral formulas. -/
namespace AronowAudit.P023.Wave1
noncomputable section
open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Set Filter
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local instance GLP023B2_decidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxRecDepth 2048
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! Piecewise geometry, including the endpoint d = 1/2. -/

private theorem GLP023B2_cc_positive_bound (d x : ℝ) (hd : 0 < d) :
    |clusterPositive d x| ≤ d / 2 := by
  unfold clusterPositive
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

private theorem GLP023B2_cc_bound (d x : ℝ) (hd : 0 < d) :
    |clusterSmooth d x| ≤ d / 2 := by
  unfold clusterSmooth
  split_ifs
  · simpa only [abs_neg] using GLP023B2_cc_positive_bound d (-x) hd
  · exact GLP023B2_cc_positive_bound d x hd

private theorem GLP023B2_cc_positive_zero (d : ℝ) (hd : d ≤ 1/2) :
    clusterPositive d 0 = 0 := by
  unfold clusterPositive
  split_ifs <;> linarith

private theorem GLP023B2_cc_zero (d : ℝ) (hd : d ≤ 1/2) : clusterSmooth d 0 = 0 := by
  simpa [clusterSmooth] using GLP023B2_cc_positive_zero d hd

private theorem GLP023B2_cc_odd (d x : ℝ) (hd : d ≤ 1/2) :
    clusterSmooth d (-x) = -clusterSmooth d x := by
  by_cases hx : x = 0
  · simp [hx, GLP023B2_cc_zero d hd]
  · by_cases hn : x < 0
    · simp only [clusterSmooth, if_pos hn, if_neg (show ¬ -x < 0 by linarith), neg_neg]
    · have hp : -x < 0 := by rcases lt_or_gt_of_ne hx with h | h <;> linarith
      simp only [clusterSmooth, if_neg hn, if_pos hp, neg_neg]

private theorem GLP023B2_cc_vanish (d x : ℝ) (hd : 0 < d) (hx : |x| ≤ 1/2-d) :
    clusterSmooth d x = 0 := by
  unfold clusterSmooth clusterPositive
  split_ifs <;> rw [abs_le] at hx <;> linarith

private theorem GLP023B2_cc_positive_lipschitz (d : ℝ) (hd : 0 < d) (x y : ℝ) :
    |clusterPositive d x - clusterPositive d y| ≤ |x-y| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this y x (le_of_not_ge hxy)
  rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_le]
  unfold clusterPositive
  split_ifs <;> constructor <;> linarith

private theorem GLP023B2_cc_lipschitz (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) (x y : ℝ) :
    |clusterSmooth d x - clusterSmooth d y| ≤ |x-y| := by
  have hz := GLP023B2_cc_positive_zero d hd'
  have hb (x : ℝ) : |clusterPositive d x| ≤ |x| := by
    simpa [hz] using GLP023B2_cc_positive_lipschitz d hd x 0
  unfold clusterSmooth
  split_ifs with hx hy hy
  · simpa only [neg_sub_neg, abs_sub_comm, neg_sub_neg] using
      GLP023B2_cc_positive_lipschitz d hd (-x) (-y)
  · calc
      _ ≤ |clusterPositive d (-x)| + |clusterPositive d y| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (-clusterPositive d (-x)) 0 (clusterPositive d y)
      _ ≤ |(-x)| + |y| := add_le_add (hb _) (hb _)
      _ = |x-y| := by rw [abs_neg, abs_of_neg hx, abs_of_nonneg (le_of_not_gt hy),
          abs_of_nonpos (by linarith)]; ring
  · calc
      _ ≤ |clusterPositive d x| + |clusterPositive d (-y)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (clusterPositive d x) 0 (-clusterPositive d (-y))
      _ ≤ |x| + |(-y)| := add_le_add (hb _) (hb _)
      _ = |x-y| := by rw [abs_neg, abs_of_neg hy, abs_of_nonneg (le_of_not_gt hx),
          abs_of_nonneg (by linarith)]; ring
  · exact GLP023B2_cc_positive_lipschitz d hd x y

private theorem GLP023B2_cc_continuous (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    Continuous (clusterSmooth d) := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using GLP023B2_cc_lipschitz d hd hd' x y

private theorem GLP023B2_cc_positive_continuous (d : ℝ) (hd : 0 < d) :
    Continuous (clusterPositive d) := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro x y
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using GLP023B2_cc_positive_lipschitz d hd x y

private theorem GLP023B2_cc_sup (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    sSup ((fun x => |clusterSmooth d x|) '' Icc (-1 : ℝ) 1) = d/2 := by
  have hat : |clusterSmooth d (1/2+d/2)| = d/2 := by
    have h1 : ¬ (1/2+d/2 : ℝ) < 0 := by linarith
    have h2 : ¬ (1/2+d/2 : ℝ) < 1/2-d := by linarith
    have h3 : ¬ (1/2+d/2 : ℝ) ≤ 1/2-d/2 := by linarith
    simp only [clusterSmooth, if_neg h1, clusterPositive, if_neg h2, if_neg h3,
      if_pos le_rfl, add_sub_cancel_left, abs_of_pos (show 0 < d/2 by linarith)]
  have hmem : d/2 ∈ ((fun x => |clusterSmooth d x|) '' Icc (-1 : ℝ) 1) :=
    ⟨1/2+d/2, ⟨by linarith, by linarith⟩, hat⟩
  have hb : BddAbove ((fun x => |clusterSmooth d x|) '' Icc (-1 : ℝ) 1) := by
    refine ⟨d/2, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact GLP023B2_cc_bound d x hd
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro _ ⟨x, _, rfl⟩
    exact GLP023B2_cc_bound d x hd
  · exact le_csSup hb hmem

private theorem GLP023B2_cc_triangle_continuous (a w : ℝ) : Continuous (triangular a w) :=
  ((continuous_const.sub (continuous_id'.sub continuous_const).abs).max continuous_const).div_const _

private theorem GLP023B2_cc_density_continuous (d : ℝ) : Continuous (clusterDensity d) :=
  continuous_const.add (continuous_const.mul
    ((GLP023B2_cc_triangle_continuous _ _).add (GLP023B2_cc_triangle_continuous _ _)))

private theorem GLP023B2_cc_density_lower (d x : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    d^4/2 ≤ clusterDensity d x := by
  have hpow : d^4 ≤ 1 := pow_le_one₀ hd.le (by linarith)
  have ht (a : ℝ) : 0 ≤ triangular a (d/2) x := by unfold triangular; positivity
  dsimp [clusterDensity]
  nlinarith [mul_nonneg (show 0 ≤ (1-d^4)/2 by linarith) (add_nonneg (ht (1/2)) (ht (-1/2)))]

/-! Normalization of the clustered margin law. -/

private theorem GLP023B2_cc_probability (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    ProbabilityLaw (clusteredMargins d) := by
  have h := clustered_fit_bound_proof d ⟨hd, hd'⟩
  dsimp only at h
  rw [← h.2.1]
  unfold ProbabilityLaw marginLaw
  rw [Measure.map_apply measurable_fst MeasurableSet.univ]
  have hp := h.1
  unfold ProbabilityLaw at hp
  simpa only [preimage_univ] using hp

private theorem GLP023B2_cc_support (d : ℝ) : MarginSupport (clusteredMargins d) := by
  unfold MarginSupport clusteredMargins
  apply withDensity_absolutelyContinuous
  simp

private theorem GLP023B2_cc_noatom (d : ℝ) : clusteredMargins d {0} = 0 := by
  unfold clusteredMargins
  exact measure_singleton 0

private theorem GLP023B2_cc_open_mass (d a b : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2)
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < clusteredMargins d (Ioo a b) := by
  have hsub : Ioo a b ⊆ Icc (-1 : ℝ) 1 := fun x hx =>
    ⟨ha.trans hx.1.le, hx.2.le.trans hb⟩
  have hl : ENNReal.ofReal (d^4/2) * volume (Ioo a b) ≤ clusteredMargins d (Ioo a b) := by
    unfold clusteredMargins
    rw [withDensity_apply _ measurableSet_Ioo]
    calc
      _ = ∫⁻ x in Ioo a b, ENNReal.ofReal (d^4/2) ∂(volume : Measure ℝ).restrict (Icc (-1 : ℝ) 1) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hsub]
      _ ≤ _ := lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (GLP023B2_cc_density_lower d x hd hd'))
  apply lt_of_lt_of_le _ hl
  rw [Real.volume_Ioo]
  positivity

private theorem GLP023B2_cc_density_even (d x : ℝ) : clusterDensity d (-x) = clusterDensity d x := by
  have ht (a w x : ℝ) : triangular a w (-x) = triangular (-a) w x := by
    unfold triangular
    congr 2
    rw [show -x-a = -(x- -a) by ring, abs_neg]
  simp only [clusterDensity, ht, neg_div, neg_neg]
  ring

private theorem GLP023B2_cc_integral_density (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) (f : ℝ → ℝ) :
    expectation (clusteredMargins d) f = ∫ x in (-1 : ℝ)..1, clusterDensity d x * f x := by
  unfold expectation clusteredMargins
  rw [integral_withDensity_eq_integral_toReal_smul
    (GLP023B2_cc_density_continuous d).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (le_trans (by positivity : 0 ≤ d^4/2)
    (GLP023B2_cc_density_lower d _ hd hd')), smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]


/-! Reflection reduces all moments to the positive half-interval. -/

private theorem GLP023B2_cc_halves (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2)
    {f fm fp : ℝ → ℝ} (hm : Continuous fm) (hp : Continuous fp)
    (hem : ∀ x ∈ Ioo (-1 : ℝ) 0, f x = fm x)
    (hep : ∀ x ∈ Ioo (0 : ℝ) 1, f x = fp x) :
    expectation (clusteredMargins d) f =
      ∫ x in (0 : ℝ)..1, clusterDensity d x * (fm (-x) + fp x) := by
  have he1 : (uIoo (-1 : ℝ) 0).EqOn (fun x => clusterDensity d x * f x)
      (fun x => clusterDensity d x * fm x) := by
    rw [uIoo_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
    exact fun x hx => congrArg (fun z => clusterDensity d x * z) (hem x hx)
  have he2 : (uIoo (0 : ℝ) 1).EqOn (fun x => clusterDensity d x * f x)
      (fun x => clusterDensity d x * fp x) := by
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun x hx => congrArg (fun z => clusterDensity d x * z) (hep x hx)
  have hcm := (GLP023B2_cc_density_continuous d).mul hm
  have hcp := (GLP023B2_cc_density_continuous d).mul hp
  have hi1 := (hcm.intervalIntegrable (μ := volume) (-1) 0).congr_uIoo (fun x hx => (he1 hx).symm)
  have hi2 := (hcp.intervalIntegrable (μ := volume) 0 1).congr_uIoo (fun x hx => (he2 hx).symm)
  rw [GLP023B2_cc_integral_density d hd hd',
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    intervalIntegral.integral_congr_uIoo he1, intervalIntegral.integral_congr_uIoo he2]
  have hn := intervalIntegral.integral_comp_neg (fun x => clusterDensity d x * fm x)
    (a := (0 : ℝ)) (b := (1 : ℝ))
  norm_num only [neg_zero] at hn
  rw [← hn]
  simp_rw [GLP023B2_cc_density_even]
  have him : IntervalIntegrable (fun x => clusterDensity d x*fm (-x)) volume 0 1 :=
    ((GLP023B2_cc_density_continuous d).mul (hm.comp continuous_neg)).intervalIntegrable 0 1
  have hip : IntervalIntegrable (fun x => clusterDensity d x*fp x) volume 0 1 :=
    hcp.intervalIntegrable 0 1
  rw [← intervalIntegral.integral_add him hip]
  apply intervalIntegral.integral_congr
  intro x _
  ring

private theorem GLP023B2_cc_even_integral (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2)
    {f : ℝ → ℝ} (hf : Continuous f) (he : ∀ x, f (-x) = f x) :
    expectation (clusteredMargins d) f = 2 * ∫ x in (0 : ℝ)..1, clusterDensity d x * f x := by
  rw [GLP023B2_cc_halves d hd hd' hf hf (fun _ _ => rfl) (fun _ _ => rfl)]
  simp_rw [he]
  rw [show (fun x => clusterDensity d x * (f x + f x)) =
    (fun x => 2 * (clusterDensity d x * f x)) by funext x; ring,
    intervalIntegral.integral_const_mul]

private theorem GLP023B2_cc_odd_integral (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2)
    {f : ℝ → ℝ} (hf : Continuous f) (he : ∀ x, f (-x) = -f x) :
    expectation (clusteredMargins d) f = 0 := by
  rw [GLP023B2_cc_halves d hd hd' hf hf (fun _ _ => rfl) (fun _ _ => rfl)]
  simp_rw [he, neg_add_cancel, mul_zero, intervalIntegral.integral_zero]

private theorem GLP023B2_cc_cubic_integral (a b A B C D : ℝ) :
    (∫ x in a..b, A + B*x + C*x^2 + D*x^3) =
      A*(b-a) + B*(b^2-a^2)/2 + C*(b^3-a^3)/3 + D*(b^4-a^4)/4 := by
  have hi0 : IntervalIntegrable (fun _ : ℝ => A) volume a b := continuous_const.intervalIntegrable (μ := volume) _ _
  have hi1 : IntervalIntegrable (fun x : ℝ => B*x) volume a b :=
    (continuous_const.mul continuous_id').intervalIntegrable (μ := volume) _ _
  have hi2 : IntervalIntegrable (fun x : ℝ => C*x^2) volume a b :=
    (continuous_const.mul (continuous_id'.pow 2)).intervalIntegrable (μ := volume) _ _
  have hi3 : IntervalIntegrable (fun x : ℝ => D*x^3) volume a b :=
    (continuous_const.mul (continuous_id'.pow 3)).intervalIntegrable (μ := volume) _ _
  rw [intervalIntegral.integral_add ((hi0.add hi1).add hi2) hi3,
    intervalIntegral.integral_add (hi0.add hi1) hi2,
    intervalIntegral.integral_add hi0 hi1]
  rw [intervalIntegral.integral_const_mul B (fun x : ℝ => x)]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id, integral_pow, smul_eq_mul]
  norm_num
  ring

private theorem GLP023B2_cc_triangle_quadratic (c w A B C : ℝ) (hw : 0 < w)
    (hl : 0 ≤ c-w) (hr : c+w ≤ 1) :
    (∫ x in (0 : ℝ)..1, triangular c w x * (A+B*x+C*x^2)) =
      A+B*c+C*(c^2+w^2/6) := by
  have hsub : Icc (c-w) (c+w) ⊆ Icc (0 : ℝ) 1 :=
    fun x hx => ⟨hl.trans hx.1, hx.2.trans hr⟩
  have hout : ∀ x ∈ Icc (0 : ℝ) 1 \ Icc (c-w) (c+w),
      triangular c w x * (A+B*x+C*x^2) = 0 := by
    intro x hx
    have he : w ≤ |x-c| := by
      by_cases hh : x < c-w
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have hh' : c+w < x := by
          by_contra hn
          exact hx.2 ⟨le_of_not_gt hh, le_of_not_gt hn⟩
        rw [abs_of_nonneg (by linarith)]; linarith
    simp only [triangular, max_eq_right (sub_nonpos.mpr he), zero_div, zero_mul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub hout,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show c-w ≤ c+w by linarith)]
  have hc : Continuous (fun x => triangular c w x * (A+B*x+C*x^2)) :=
    (GLP023B2_cc_triangle_continuous c w).mul (by fun_prop)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) (c-w) c)
    (hc.intervalIntegrable (μ := volume) c (c+w))]
  have hleft : (∫ x in (c-w)..c, triangular c w x * (A+B*x+C*x^2)) =
      (∫ x in (c-w)..c,
        ((w-c)*A + (A+(w-c)*B)*x + (B+(w-c)*C)*x^2 + C*x^3) / w^2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (show c-w ≤ c by linarith)] at hx
    change triangular c w x * (A+B*x+C*x^2) = _
    rw [triangular, abs_of_nonpos (by linarith [hx.2]), max_eq_left (by linarith [hx.1])]
    ring
  have hright : (∫ x in c..(c+w), triangular c w x * (A+B*x+C*x^2)) =
      (∫ x in c..(c+w),
        ((w+c)*A + ((w+c)*B-A)*x + ((w+c)*C-B)*x^2 + (-C)*x^3) / w^2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (show c ≤ c+w by linarith)] at hx
    change triangular c w x * (A+B*x+C*x^2) = _
    rw [triangular, abs_of_nonneg (by linarith [hx.1]), max_eq_left (by linarith [hx.2])]
    ring
  rw [hleft, hright, intervalIntegral.integral_div, intervalIntegral.integral_div,
    GLP023B2_cc_cubic_integral, GLP023B2_cc_cubic_integral]
  field_simp [ne_of_gt hw]
  ring


private theorem GLP023B2_cc_affine_integral (a b U V A B : ℝ) :
    (∫ x in a..b, (U+V*x)*(A+B*x)) =
      U*A*(b-a) + (U*B+V*A)*(b^2-a^2)/2 + V*B*(b^3-a^3)/3 := by
  have he : (fun x : ℝ => (U+V*x)*(A+B*x)) =
      (fun x => U*A + (U*B+V*A)*x + (V*B)*x^2 + 0*x^3) := by funext x; ring
  rw [he, GLP023B2_cc_cubic_integral]
  ring

private theorem GLP023B2_cc_positive_linear_integral (d A B : ℝ)
    (hd : 0 < d) (hd' : d ≤ 1/2) :
    (∫ x in (0 : ℝ)..1, clusterPositive d x * (A+B*x)) = B*d^3/4 := by
  have hsub : Icc (1/2-d) (1/2+d) ⊆ Icc (0 : ℝ) 1 :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hout : ∀ x ∈ Icc (0 : ℝ) 1 \ Icc (1/2-d) (1/2+d),
      clusterPositive d x * (A+B*x) = 0 := by
    intro x hx
    suffices hz : clusterPositive d x = 0 by rw [hz, zero_mul]
    unfold clusterPositive
    split_ifs <;> try rfl
    all_goals exfalso; apply hx.2; constructor <;> linarith
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub hout,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show 1/2-d ≤ 1/2+d by linarith)]
  have hc : Continuous (fun x => clusterPositive d x * (A+B*x)) :=
    (GLP023B2_cc_positive_continuous d hd).mul (by fun_prop)
  have hi1 := hc.intervalIntegrable (μ := volume) (1/2-d) (1/2-d/2)
  have hi2 := hc.intervalIntegrable (μ := volume) (1/2-d/2) (1/2+d/2)
  have hi3 := hc.intervalIntegrable (μ := volume) (1/2+d/2) (1/2+d)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have he1 : (∫ x in (1/2-d)..(1/2-d/2), clusterPositive d x * (A+B*x)) =
      ∫ x in (1/2-d)..(1/2-d/2), ((1/2-d)+(-1)*x)*(A+B*x) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (show 1/2-d ≤ 1/2-d/2 by linarith)]
    intro x hx
    simp only [clusterPositive, if_neg (not_lt.mpr hx.1.le), if_pos hx.2.le]
    congr 1
    ring
  have he2 : (∫ x in (1/2-d/2)..(1/2+d/2), clusterPositive d x * (A+B*x)) =
      ∫ x in (1/2-d/2)..(1/2+d/2), ((-1/2)+1*x)*(A+B*x) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (show 1/2-d/2 ≤ 1/2+d/2 by linarith)]
    intro x hx
    simp only [clusterPositive, if_neg (show ¬ x < 1/2-d by linarith [hx.1]),
      if_neg (not_le.mpr hx.1), if_pos hx.2.le]
    congr 1
    ring
  have he3 : (∫ x in (1/2+d/2)..(1/2+d), clusterPositive d x * (A+B*x)) =
      ∫ x in (1/2+d/2)..(1/2+d), ((1/2+d)+(-1)*x)*(A+B*x) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (show 1/2+d/2 ≤ 1/2+d by linarith)]
    intro x hx
    simp only [clusterPositive, if_neg (show ¬ x < 1/2-d by linarith [hx.1]),
      if_neg (show ¬ x ≤ 1/2-d/2 by linarith [hx.1]),
      if_neg (not_le.mpr hx.1), if_pos hx.2.le]
    congr 1
    ring
  rw [he1, he2, he3, GLP023B2_cc_affine_integral, GLP023B2_cc_affine_integral,
    GLP023B2_cc_affine_integral]
  ring

private theorem GLP023B2_cc_triangle_positive_linear (d A B : ℝ)
    (hd : 0 < d) (hd' : d ≤ 1/2) :
    (∫ x in (0 : ℝ)..1, triangular (1/2) (d/2) x * (clusterPositive d x * (A+B*x))) =
      B*(d/2)^2/6 := by
  have he : (fun x : ℝ => triangular (1/2) (d/2) x * (clusterPositive d x * (A+B*x))) =
      (fun x => triangular (1/2) (d/2) x * (-A/2+(A-B/2)*x+B*x^2)) := by
    funext x
    by_cases ht : triangular (1/2) (d/2) x = 0
    · simp only [ht, zero_mul]
    · have hs : |x-1/2| < d/2 := by
        by_contra hn
        have hz : max (d/2-|x-1/2|) 0 = 0 := max_eq_right (by linarith)
        exact ht (by simp only [triangular, hz, zero_div])
      rw [abs_lt] at hs
      have h1 : ¬ x < 1/2-d := by linarith [hs.1]
      have h2 : ¬ x ≤ 1/2-d/2 := by linarith [hs.1]
      have h3 : x ≤ 1/2+d/2 := by linarith [hs.2]
      simp only [clusterPositive, if_neg h1, if_neg h2, if_pos h3]
      ring
  rw [he, GLP023B2_cc_triangle_quadratic _ _ _ _ _ (by linarith) (by linarith) (by linarith)]
  ring

private theorem GLP023B2_cc_positive_density_integral (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2)
    {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x in (0 : ℝ)..1, clusterDensity d x * f x) =
      (d^4/2)*(∫ x in (0 : ℝ)..1, f x) +
      ((1-d^4)/2)*(∫ x in (0 : ℝ)..1, triangular (1/2) (d/2) x * f x) := by
  have he : (uIoo (0 : ℝ) 1).EqOn (fun x => clusterDensity d x * f x)
      (fun x => d^4/2 * f x + (1-d^4)/2 * (triangular (1/2) (d/2) x * f x)) := by
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x hx
    have ht : triangular (-1/2) (d/2) x = 0 := by
      unfold triangular
      rw [abs_of_nonneg (by linarith [hx.1]), max_eq_right (by linarith [hx.1]), zero_div]
    simp only [clusterDensity, ht]
    ring
  rw [intervalIntegral.integral_congr_uIoo he]
  have hi1 : IntervalIntegrable (fun x => d^4/2*f x) volume 0 1 :=
    (hf.const_mul _).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x => (1-d^4)/2*(triangular (1/2) (d/2) x*f x)) volume 0 1 :=
    (((GLP023B2_cc_triangle_continuous _ _).mul hf).const_mul _).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

private theorem GLP023B2_cc_positive_moments (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    (∫ x in (0 : ℝ)..1, clusterDensity d x) = 1/2 ∧
    (∫ x in (0 : ℝ)..1, clusterDensity d x * x) = 1/4 ∧
    (∫ x in (0 : ℝ)..1, clusterDensity d x * x^2) =
      ((1-d^4)*((1/2)^2+(d/2)^2/6)+d^4/3)/2 ∧
    (∫ x in (0 : ℝ)..1, clusterDensity d x * clusterPositive d x) = 0 ∧
    (∫ x in (0 : ℝ)..1, clusterDensity d x * (x*clusterPositive d x)) =
      ((1-d^4)*(d/2)^2/6+2*d^4*(d/2)^3)/2 := by
  have ht0 : (∫ x in (0 : ℝ)..1, triangular (1/2) (d/2) x) = 1 := by
    simpa using GLP023B2_cc_triangle_quadratic (1/2) (d/2) 1 0 0
      (by linarith) (by linarith) (by linarith)
  have ht1 : (∫ x in (0 : ℝ)..1, triangular (1/2) (d/2) x * x) = 1/2 := by
    simpa using GLP023B2_cc_triangle_quadratic (1/2) (d/2) 0 1 0
      (by linarith) (by linarith) (by linarith)
  have ht2 : (∫ x in (0 : ℝ)..1, triangular (1/2) (d/2) x * x^2) = (1/2)^2+(d/2)^2/6 := by
    simpa using GLP023B2_cc_triangle_quadratic (1/2) (d/2) 0 0 1
      (by linarith) (by linarith) (by linarith)
  have hh0 : (∫ x in (0 : ℝ)..1, clusterPositive d x) = 0 := by
    simpa using GLP023B2_cc_positive_linear_integral d 1 0 hd hd'
  have hh1 : (∫ x in (0 : ℝ)..1, x*clusterPositive d x) = d^3/4 := by
    simpa [mul_comm] using GLP023B2_cc_positive_linear_integral d 0 1 hd hd'
  have hth0 : (∫ x in (0 : ℝ)..1, triangular (1/2) (d/2) x * clusterPositive d x) = 0 := by
    simpa using GLP023B2_cc_triangle_positive_linear d 1 0 hd hd'
  have hth1 : (∫ x in (0 : ℝ)..1, triangular (1/2) (d/2) x * (x*clusterPositive d x)) = (d/2)^2/6 := by
    simpa [mul_comm] using GLP023B2_cc_triangle_positive_linear d 0 1 hd hd'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := GLP023B2_cc_positive_density_integral d hd hd' (f := fun _ => 1) continuous_const
    simp only [mul_one, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    rw [h, ht0]
    ring
  · rw [GLP023B2_cc_positive_density_integral d hd hd' (f := fun x => x) continuous_id', integral_id, ht1]
    norm_num
    ring
  · rw [GLP023B2_cc_positive_density_integral d hd hd' (f := fun x => x^2) (continuous_id'.pow 2), integral_pow, ht2]
    norm_num
    ring
  · rw [GLP023B2_cc_positive_density_integral d hd hd' (GLP023B2_cc_positive_continuous d hd), hh0, hth0]
    ring
  · rw [GLP023B2_cc_positive_density_integral d hd hd' (f := fun x => x*clusterPositive d x)
      (continuous_id'.mul (GLP023B2_cc_positive_continuous d hd)), hh1, hth1]
    ring

private theorem GLP023B2_cc_party_integral (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2)
    {f : ℝ → ℝ} (hf : Continuous f) :
    expectation (clusteredMargins d) (fun x => party x * f x) =
      ∫ x in (0 : ℝ)..1, clusterDensity d x * f x := by
  rw [GLP023B2_cc_halves d hd hd' (fm := fun _ => 0) (fp := f)
    continuous_const hf (fun x hx => by simp [party, not_le.mpr hx.2])
      (fun x hx => by simp [party, hx.1.le])]
  simp only [zero_add]

private theorem GLP023B2_cc_replace_positive (d : ℝ) (g : ℝ → ℝ) :
    (∫ x in (0 : ℝ)..1, clusterDensity d x * (g x * clusterSmooth d x)) =
      ∫ x in (0 : ℝ)..1, clusterDensity d x * (g x * clusterPositive d x) := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  intro x hx
  simp only [clusterSmooth, if_neg (not_lt.mpr hx.1)]

private theorem GLP023B2_cc_moments (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    expectation (clusteredMargins d) (fun x => x) = 0 ∧
    expectation (clusteredMargins d) (clusterSmooth d) = 0 ∧
    expectation (clusteredMargins d) (fun x => (party x-1/2)*clusterSmooth d x) = 0 ∧
    expectation (clusteredMargins d) (fun x => x * party x) = 1/4 ∧
    expectation (clusteredMargins d) (fun x => x^2) = (1-d^4)*((1/2)^2+(d/2)^2/6)+d^4/3 ∧
    expectation (clusteredMargins d) (fun x => x * clusterSmooth d x) = (1-d^4)*(d/2)^2/6+2*d^4*(d/2)^3 ∧
    expectation (clusteredMargins d) party = 1/2 ∧
    expectation (clusteredMargins d) (fun x => party x * clusterSmooth d x) = 0 := by
  obtain ⟨h0, h1, h2, hh, hxh⟩ := GLP023B2_cc_positive_moments d hd hd'
  have hc := GLP023B2_cc_continuous d hd hd'
  refine ⟨GLP023B2_cc_odd_integral d hd hd' continuous_id' (fun _ => rfl),
    GLP023B2_cc_odd_integral d hd hd' hc (fun x => GLP023B2_cc_odd d x hd'),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GLP023B2_cc_halves d hd hd' (fm := fun x => (-1/2)*clusterSmooth d x)
      (fp := fun x => (1/2)*clusterSmooth d x) (hc.const_mul _) (hc.const_mul _)
      (fun x hx => by simp only [party, if_neg (not_le.mpr hx.2)]; ring)
      (fun x hx => by simp only [party, if_pos hx.1.le]; ring)]
    simp_rw [GLP023B2_cc_odd d _ hd']
    have he : (fun x => clusterDensity d x * ((-1/2)* -clusterSmooth d x+(1/2)*clusterSmooth d x)) =
        (fun x => clusterDensity d x * (1*clusterSmooth d x)) := by funext x; ring
    rw [he, GLP023B2_cc_replace_positive]
    simpa only [one_mul] using hh
  · simpa only [mul_comm] using (GLP023B2_cc_party_integral d hd hd' (f := fun x => x) continuous_id').trans h1
  · rw [GLP023B2_cc_even_integral d hd hd' (f := fun x => x^2) (continuous_id'.pow 2) (fun x => neg_sq x), h2]
    ring
  · rw [GLP023B2_cc_even_integral d hd hd' (f := fun x => x*clusterSmooth d x) (continuous_id'.mul hc)
      (fun x => by rw [GLP023B2_cc_odd d x hd']; ring),
      GLP023B2_cc_replace_positive, hxh]
    ring
  · have he := GLP023B2_cc_party_integral d hd hd' (f := fun _ => 1) continuous_const
    simpa only [mul_one] using he.trans (by simpa only [mul_one] using h0)
  · rw [GLP023B2_cc_party_integral d hd hd' hc]
    have he := GLP023B2_cc_replace_positive d (fun _ => 1)
    simp only [one_mul] at he
    rw [he, hh]

/-! Identify the actual epsilon-chosen coefficient by its three normal equations. -/

private def GLP023B2_cc_s (d : ℝ) : ℝ := (1-d^4)*((1/2)^2+(d/2)^2/6)+d^4/3
private def GLP023B2_cc_t (d : ℝ) : ℝ := (1-d^4)*(d/2)^2/6+2*d^4*(d/2)^3
private def GLP023B2_cc_gram (d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1,1/2,0], ![1/2,1/2,1/4], ![0,1/4,GLP023B2_cc_s d]]

private theorem GLP023B2_cc_column_integrable (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) (j : Fin 3) :
    Integrable (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j) (clusteredMargins d) := by
  exact GP023B1b_supported_integrable _ (GLP023B2_cc_probability d hd hd')
    (GLP023B2_cc_support d) (GP023B1b_column_measurable 1 j) 1 (GP023B1b_column_bound 1 j)

private theorem GLP023B2_cc_column_h_integrable (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) (j : Fin 3) :
    Integrable (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j * clusterSmooth d x)
      (clusteredMargins d) := by
  apply GP023B1b_supported_integrable _ (GLP023B2_cc_probability d hd hd')
    (GLP023B2_cc_support d)
    ((GP023B1b_column_measurable 1 j).mul (GLP023B2_cc_continuous d hd hd').measurable) (d/2)
  intro x hx
  change |polynomialDesign 1 (fun x : ℝ => x) party x j * clusterSmooth d x| ≤ d/2
  rw [abs_mul]
  calc
    _ ≤ 1 * |clusterSmooth d x| := mul_le_mul_of_nonneg_right (GP023B1b_column_bound 1 j x hx) (abs_nonneg _)
    _ ≤ d/2 := by simpa only [one_mul] using GLP023B2_cc_bound d x hd

private theorem GLP023B2_cc_gram_integrable (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) (i j : Fin 3) :
    Integrable (fun x => polynomialDesign 1 (fun x : ℝ => x) party x i *
      polynomialDesign 1 (fun x : ℝ => x) party x j) (clusteredMargins d) := by
  apply GP023B1b_supported_integrable _ (GLP023B2_cc_probability d hd hd')
    (GLP023B2_cc_support d)
    ((GP023B1b_column_measurable 1 i).mul (GP023B1b_column_measurable 1 j)) 1
  intro x hx
  change |polynomialDesign 1 (fun x : ℝ => x) party x i * polynomialDesign 1 (fun x : ℝ => x) party x j| ≤ 1
  rw [abs_mul]
  exact (mul_le_mul (GP023B1b_column_bound 1 i x hx) (GP023B1b_column_bound 1 j x hx)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)

private theorem GLP023B2_cc_gram_value (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) (i j : Fin 3) :
    expectation (clusteredMargins d) (fun x => polynomialDesign 1 (fun x : ℝ => x) party x i *
      polynomialDesign 1 (fun x : ℝ => x) party x j) = GLP023B2_cc_gram d i j := by
  obtain ⟨hx, _, _, hxd, hs, _, hD, _⟩ := GLP023B2_cc_moments d hd hd'
  have hpx : expectation (clusteredMargins d) (fun x => party x*x) = 1/4 := by
    simpa only [mul_comm] using hxd
  have hx2 : expectation (clusteredMargins d) (fun x => x*x) = GLP023B2_cc_s d := by
    simpa only [← pow_two, GLP023B2_cc_s] using hs
  have hD2 : expectation (clusteredMargins d) (fun x => party x*party x) = 1/2 := by
    simpa only [GP023B1b_party_square] using hD
  have hconst : expectation (clusteredMargins d) (fun _ => 1) = 1 := by
    letI : IsProbabilityMeasure (clusteredMargins d) := ⟨GLP023B2_cc_probability d hd hd'⟩
    simp [expectation]
  fin_cases i <;> fin_cases j <;>
    simp [polynomialDesign, GLP023B2_cc_gram, hconst, hx, hD, hxd, hpx, hx2, hD2]

private theorem GLP023B2_cc_response_value (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) (j : Fin 3) :
    expectation (clusteredMargins d) (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j *
      (1/2+clusterSmooth d x)) = ![1/2,1/4,GLP023B2_cc_t d] j := by
  obtain ⟨hx, hh, _, _, _, hxh, hD, hDh⟩ := GLP023B2_cc_moments d hd hd'
  have hconst : expectation (clusteredMargins d) (fun _ => 1) = 1 := by
    letI : IsProbabilityMeasure (clusteredMargins d) := ⟨GLP023B2_cc_probability d hd hd'⟩
    simp [expectation]
  have he : expectation (clusteredMargins d) (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j *
      (1/2+clusterSmooth d x)) =
      expectation (clusteredMargins d) (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j) * (1/2) +
      expectation (clusteredMargins d) (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j * clusterSmooth d x) := by
    unfold expectation
    simp_rw [mul_add]
    rw [integral_add ((GLP023B2_cc_column_integrable d hd hd' j).mul_const _)
      (GLP023B2_cc_column_h_integrable d hd hd' j), integral_mul_const]
  rw [he]
  fin_cases j <;> simp [polynomialDesign, hconst, hx, hh, hD, hDh, hxh, GLP023B2_cc_t] <;> norm_num

private theorem GLP023B2_cc_normal_iff (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) (c : Fin 3 → ℝ) :
    PopNormal (clusteredMargins d) 1 (fun x => 1/2+clusterSmooth d x) c ↔
      (GLP023B2_cc_gram d).mulVec c = ![1/2,1/4,GLP023B2_cc_t d] := by
  have hp (j : Fin 3) : expectation (clusteredMargins d) (fun x =>
      polynomialDesign 1 (fun x : ℝ => x) party x j * predict (polynomialDesign 1 (fun x : ℝ => x) party) c x) =
      (GLP023B2_cc_gram d).mulVec c j := by
    unfold expectation predict Matrix.mulVec dotProduct
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum _ (fun i _ => (GLP023B2_cc_gram_integrable d hd hd' j i).mul_const (c i))]
    simp_rw [integral_mul_const]
    change (∑ i, expectation (clusteredMargins d) (fun x =>
      polynomialDesign 1 (fun x : ℝ => x) party x j *
      polynomialDesign 1 (fun x : ℝ => x) party x i) * c i) = _
    simp_rw [GLP023B2_cc_gram_value d hd hd']
  have hi (j : Fin 3) : Integrable (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j *
      predict (polynomialDesign 1 (fun x : ℝ => x) party) c x) (clusteredMargins d) := by
    simp only [predict, Finset.mul_sum, ← mul_assoc]
    exact integrable_finsetSum _ (fun i _ => (GLP023B2_cc_gram_integrable d hd hd' j i).mul_const (c i))
  have hr (j : Fin 3) : Integrable (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j *
      (1/2+clusterSmooth d x)) (clusteredMargins d) := by
    have hsum := ((GLP023B2_cc_column_integrable d hd hd' j).mul_const (1/2)).add
      (GLP023B2_cc_column_h_integrable d hd hd' j)
    exact hsum.congr (Filter.Eventually.of_forall (fun x => by dsimp; ring))
  unfold PopNormal
  simp_rw [mul_sub, expectation, integral_sub (hr _) (hi _)]
  change (∀ j, expectation (clusteredMargins d) (fun x =>
      polynomialDesign 1 (fun x : ℝ => x) party x j * (1/2+clusterSmooth d x)) -
      expectation (clusteredMargins d) (fun x => polynomialDesign 1 (fun x : ℝ => x) party x j *
      predict (polynomialDesign 1 (fun x : ℝ => x) party) c x) = 0) ↔ _
  simp_rw [hp, GLP023B2_cc_response_value d hd hd', sub_eq_zero]
  exact ⟨fun h => funext (fun j => (h j).symm), fun h j => (congrFun h j).symm⟩

private theorem GLP023B2_cc_den_positive (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    0 < 4*GLP023B2_cc_s d-1 := by
  have hpow : d^4 < 1 := pow_lt_one₀ hd.le (by linarith) (by norm_num : 4 ≠ 0)
  have he : 4*GLP023B2_cc_s d-1 = (d^2/6)*(1-d^4+2*d^2) := by dsimp [GLP023B2_cc_s]; ring
  rw [he]
  positivity

private theorem GLP023B2_cc_coefficient (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    populationCoefficient (clusteredMargins d) 1 (fun x => 1/2+clusterSmooth d x) =
      -(1-d^4+6*d^5)/(1-d^4+2*d^2) := by
  have hden := ne_of_gt (GLP023B2_cc_den_positive d hd hd')
  let s := GLP023B2_cc_s d
  let t := GLP023B2_cc_t d
  let c : Fin 3 → ℝ := ![1/2+2*t/(4*s-1), -4*t/(4*s-1), 4*t/(4*s-1)]
  have hc : PopNormal (clusteredMargins d) 1 (fun x => 1/2+clusterSmooth d x) c := by
    apply (GLP023B2_cc_normal_iff d hd hd' c).mpr
    ext j
    fin_cases j <;> simp [GLP023B2_cc_gram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, c, s, t] <;>
      field_simp [hden] <;> ring
  have hs := (GLP023B2_cc_normal_iff d hd hd' _).mp (Classical.epsilon_spec ⟨c, hc⟩)
  let z := Classical.epsilon (PopNormal (clusteredMargins d) 1 (fun x => 1/2+clusterSmooth d x))
  have he0 := congrFun hs 0
  have he1 := congrFun hs 1
  have he2 := congrFun hs 2
  change (GLP023B2_cc_gram d).mulVec z 0 = _ at he0
  change (GLP023B2_cc_gram d).mulVec z 1 = _ at he1
  change (GLP023B2_cc_gram d).mulVec z 2 = _ at he2
  simp [GLP023B2_cc_gram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at he0 he1 he2
  have hz : z 1 = -4*GLP023B2_cc_t d/(4*GLP023B2_cc_s d-1) := by
    apply (eq_div_iff hden).mpr
    linear_combination -8*GLP023B2_cc_s d*he0 + 16*GLP023B2_cc_s d*he1 - 4*he2
  change z 1 = _
  rw [hz]
  have hpow : d^4 < 1 := pow_lt_one₀ hd.le (by linarith) (by norm_num : 4 ≠ 0)
  have hden' : 1-d^4+2*d^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1-d^4+2*d^2)
  apply (div_eq_div_iff hden hden').mpr
  dsimp [GLP023B2_cc_s, GLP023B2_cc_t]
  ring


private theorem GLP023B2_cc_bounded_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : Measurable f) (B : ℝ) (hb : ∀ x, |f x| ≤ B) : Integrable f μ := by
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

private theorem GLP023B2_cc_conditional_mean (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    ConditionalMean (witnessLaw (clusteredMargins d) (clusterSmooth d))
      (fun x => 1/2+clusterSmooth d x) := by
  let μ := clusteredMargins d
  let h := clusterSmooth d
  letI : IsProbabilityMeasure μ := ⟨GLP023B2_cc_probability d hd hd'⟩
  have hm : Measurable h := (GLP023B2_cc_continuous d hd hd').measurable
  have hmi : Integrable (fun x => 1/2+h x) μ := (integrable_const (1/2)).add
    (GLP023B2_cc_bounded_integrable μ hm (d/2) (fun x => GLP023B2_cc_bound d x hd))
  have hmm : Measurable (fun x => 1/2+h x) := measurable_const.add hm
  have hiY : Integrable (fun z : ℝ × ℝ => z.2) (witnessLaw μ h) :=
    (GP023B1b_integrable_witness_iff μ hm measurable_snd).mpr
      ⟨hmi.add (integrable_const _), hmi.add (integrable_const _)⟩
  have hiM : Integrable (fun z : ℝ × ℝ => 1/2+h z.1) (witnessLaw μ h) :=
    (GP023B1b_integrable_witness_iff μ hm (hmm.comp measurable_fst)).mpr ⟨hmi, hmi⟩
  refine ⟨hiY, hiM, ?_⟩
  intro t ht hb
  obtain ⟨B, hB⟩ := hb
  have hti := GLP023B2_cc_bounded_integrable μ ht B hB
  have htae : ∀ᵐ x ∂μ, ‖t x‖ ≤ B := Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using hB x)
  have hitm := hmi.bdd_mul ht.aestronglyMeasurable htae
  have hitY : Integrable (fun z : ℝ × ℝ => t z.1*z.2) (witnessLaw μ h) :=
    (GP023B1b_integrable_witness_iff μ hm ((ht.comp measurable_fst).mul measurable_snd)).mpr
      ⟨(hmi.add (integrable_const _)).bdd_mul ht.aestronglyMeasurable htae,
       (hmi.add (integrable_const _)).bdd_mul ht.aestronglyMeasurable htae⟩
  have hitM : Integrable (fun z : ℝ × ℝ => t z.1*(1/2+h z.1)) (witnessLaw μ h) :=
    (GP023B1b_integrable_witness_iff μ hm ((ht.comp measurable_fst).mul (hmm.comp measurable_fst))).mpr
      ⟨hitm, hitm⟩
  change (∫ z : ℝ × ℝ, t z.1*z.2 ∂witnessLaw μ h) =
    ∫ z : ℝ × ℝ, t z.1*(1/2+h z.1) ∂witnessLaw μ h
  rw [GP023B1b_integral_witness μ hm (g := fun z : ℝ × ℝ => t z.1*z.2)
      ((ht.comp measurable_fst).mul measurable_snd) hitY,
    GP023B1b_integral_witness μ hm (g := fun z : ℝ × ℝ => t z.1*(1/2+h z.1))
      ((ht.comp measurable_fst).mul (hmm.comp measurable_fst)) hitM]
  dsimp only
  have he (u : ℝ) : (fun x => t x*(1/2+h x+u)) =
      (fun x => t x*(1/2+h x)+t x*u) := by funext x; ring
  rw [he, he, integral_add hitm (hti.mul_const _), integral_add hitm (hti.mul_const _),
    integral_mul_const, integral_mul_const]
  ring

private theorem GLP023B2_cc_rd (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2)
    (k : ℝ) (hk : 0 < k) (hk' : k < 1/2-d) :
    populationRD (clusteredMargins d) (fun x => 1/2+clusterSmooth d x) k = 0 := by
  let μ := clusteredMargins d
  letI : IsProbabilityMeasure μ := ⟨GLP023B2_cc_probability d hd hd'⟩
  have hp : 0 < μ (Ioc 0 k) := lt_of_lt_of_le
    (GLP023B2_cc_open_mass d 0 k hd hd' (by norm_num) hk (by linarith))
    (measure_mono Ioo_subset_Ioc_self)
  have hn : 0 < μ (Ioo (-k) 0) := GLP023B2_cc_open_mass d (-k) 0 hd hd'
    (by linarith) (by linarith) (by norm_num)
  have hpr : (μ (Ioc 0 k)).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hp.ne' (measure_ne_top _ _))
  have hnr : (μ (Ioo (-k) 0)).toReal ≠ 0 := ne_of_gt (ENNReal.toReal_pos hn.ne' (measure_ne_top _ _))
  have hep : (∫ x in Ioc 0 k, (1/2+clusterSmooth d x) ∂μ) = ∫ _ in Ioc 0 k, (1/2 : ℝ) ∂μ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    change (1/2 : ℝ)+clusterSmooth d x = 1/2
    rw [GLP023B2_cc_vanish d x hd (by rw [abs_of_pos hx.1]; linarith [hx.2]), add_zero]
  have hen : (∫ x in Ioo (-k) 0, (1/2+clusterSmooth d x) ∂μ) = ∫ _ in Ioo (-k) 0, (1/2 : ℝ) ∂μ := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    change (1/2 : ℝ)+clusterSmooth d x = 1/2
    rw [GLP023B2_cc_vanish d x hd (by rw [abs_of_neg hx.2]; linarith [hx.1]), add_zero]
  change (∫ x in Ioc 0 k, (1/2+clusterSmooth d x) ∂μ)/(μ (Ioc 0 k)).toReal -
    (∫ x in Ioo (-k) 0, (1/2+clusterSmooth d x) ∂μ)/(μ (Ioo (-k) 0)).toReal = 0
  rw [hep, hen, integral_const, integral_const]
  simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  field_simp [hpr, hnr]
  ring

private theorem GLP023B2_cc_square_bound (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    expectation (clusteredMargins d) (fun x => clusterSmooth d x^2) ≤ (d/2)^2 := by
  let μ := clusteredMargins d
  letI : IsProbabilityMeasure μ := ⟨GLP023B2_cc_probability d hd hd'⟩
  have hb (x : ℝ) : clusterSmooth d x^2 ≤ (d/2)^2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (clusterSmooth d x)) (show 0 ≤ d/2 by linarith)).mpr
      (GLP023B2_cc_bound d x hd)
    simpa only [sq_abs] using hs
  have hi : Integrable (fun x => clusterSmooth d x^2) μ := by
    apply GLP023B2_cc_bounded_integrable μ (f := fun x => clusterSmooth d x^2)
      ((GLP023B2_cc_continuous d hd hd').measurable.pow_const 2) ((d/2)^2)
    intro x
    simpa only [abs_of_nonneg (sq_nonneg (clusterSmooth d x))] using hb x
  change (∫ x, clusterSmooth d x^2 ∂μ) ≤ _
  calc
    _ ≤ ∫ _ : ℝ, (d/2)^2 ∂μ := integral_mono_ae hi (integrable_const _) (Filter.Eventually.of_forall hb)
    _ = _ := by simp

private theorem GLP023B2_cc_outcomes (d : ℝ) (hd : 0 < d) (hd' : d ≤ 1/2) :
    ∀ᵐ z ∂witnessLaw (clusteredMargins d) (clusterSmooth d),
      1/2-d/2-1/10 ≤ z.2 ∧ z.2 ≤ 1/2+d/2+1/10 := by
  let μ := clusteredMargins d
  let h := clusterSmooth d
  letI : IsProbabilityMeasure μ := ⟨GLP023B2_cc_probability d hd hd'⟩
  have hm : Measurable h := (GLP023B2_cc_continuous d hd hd').measurable
  have hs : MeasurableSet {z : ℝ × ℝ | 1/2-d/2-1/10 ≤ z.2 ∧ z.2 ≤ 1/2+d/2+1/10} :=
    (measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const)
  have hmap (u : ℝ) (hu : |u| ≤ 1/10) :
      ∀ᵐ z ∂Measure.map (fun x => (x, 1/2+h x+u)) μ,
        1/2-d/2-1/10 ≤ z.2 ∧ z.2 ≤ 1/2+d/2+1/10 := by
    apply (ae_map_iff (measurable_id.prodMk ((measurable_const.add hm).add measurable_const)).aemeasurable hs).mpr
    apply Filter.Eventually.of_forall
    intro x
    have hx := abs_le.mp (GLP023B2_cc_bound d x hd)
    have hu' := abs_le.mp hu
    change 1/2-d/2-1/10 ≤ 1/2+clusterSmooth d x+u ∧
      1/2+clusterSmooth d x+u ≤ 1/2+d/2+1/10
    constructor <;> linarith
  change ∀ᵐ z ∂witnessLaw μ h, _
  rw [GP023B1b_witness_split μ hm, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (hmap (-1/10) (by norm_num)) _,
    Measure.ae_smul_measure (hmap (1/10) (by norm_num)) _⟩

private theorem GLP023B2_cc_near :
    ∀ᶠ d : ℝ in nhdsWithin 0 (Ioi 0), 0 < d ∧ d ≤ 1/2 := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with d hd hd'
  exact ⟨hd, hd'.le⟩

private theorem GLP023B2_cc_limit :
    Tendsto (fun d => populationCoefficient (clusteredMargins d) 1 (fun x => 1/2+clusterSmooth d x))
      (nhdsWithin 0 (Ioi 0)) (nhds (-1)) := by
  have hc : ContinuousAt (fun d : ℝ => -(1-d^4+6*d^5)/(1-d^4+2*d^2)) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have ht : Tendsto (fun d : ℝ => -(1-d^4+6*d^5)/(1-d^4+2*d^2))
      (nhdsWithin 0 (Ioi 0)) (nhds (-1)) := by
    simpa only [zero_pow (by norm_num : 4 ≠ 0), zero_pow (by norm_num : 5 ≠ 0),
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero, add_zero, neg_div, one_div, inv_one]
      using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [GLP023B2_cc_near] with d hd
  exact (GLP023B2_cc_coefficient d hd.1 hd.2).symm

private theorem GLP023B2_cc_no_uniform_bound :
    ¬ (∃ C : ℝ, ∀ d, 0 < d → d ≤ 1/2 →
      |populationCoefficient (clusteredMargins d) 1 (fun x => 1/2+clusterSmooth d x)| ≤ C*(d/2)) := by
  rintro ⟨C, hC⟩
  have hd : Tendsto (fun d : ℝ => d) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun d : ℝ => C*(d/2)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hd.div_const 2)
  have hl := GLP023B2_cc_limit.abs
  have hb := le_of_tendsto_of_tendsto hl hr (GLP023B2_cc_near.mono (fun d hd => hC d hd.1 hd.2))
  norm_num at hb

/-- The full clustered-law family. -/
theorem clustered_counterexample_proof :
    (∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
      ProbabilityLaw (clusteredMargins d) ∧ MarginSupport (clusteredMargins d) ∧
      clusteredMargins d {0}=0 ∧
      (∀ a b : ℝ, -1 ≤ a → a<b → b ≤ 1 → 0 < clusteredMargins d (Set.Ioo a b)) ∧
      Continuous (clusterDensity d) ∧ (∀ x ∈ Set.Icc (-1) 1, d^4/2 ≤ clusterDensity d x) ∧
      Continuous (clusterSmooth d) ∧ clusterSmooth d 0 = 0 ∧
      (∀ x, |x| ≤ 1/2-d → clusterSmooth d x=0) ∧
      (∀ x, clusterSmooth d (-x) = -clusterSmooth d x) ∧
      (∀ x x', |clusterSmooth d x - clusterSmooth d x'| ≤ |x-x'|) ∧
      (∀ x, |clusterSmooth d x| ≤ d/2) ∧
      sSup ((fun x => |clusterSmooth d x|) '' Set.Icc (-1) 1) = d/2 ∧
      ConditionalMean (witnessLaw (clusteredMargins d) (clusterSmooth d)) (fun x => 1/2 + clusterSmooth d x) ∧
      expectation (clusteredMargins d) (fun x => x) = 0 ∧
      expectation (clusteredMargins d) (clusterSmooth d) = 0 ∧
      expectation (clusteredMargins d) (fun x => (party x-1/2)*clusterSmooth d x) = 0 ∧
      expectation (clusteredMargins d) (fun x => x * party x) = 1/4 ∧
      expectation (clusteredMargins d) (fun x => x^2) = (1-d^4)*((1/2)^2+(d/2)^2/6)+d^4/3 ∧
      expectation (clusteredMargins d) (fun x => x * clusterSmooth d x) = (1-d^4)*(d/2)^2/6+2*d^4*(d/2)^3 ∧
      populationCoefficient (clusteredMargins d) 1 (fun x => 1/2 + clusterSmooth d x) =
        -(1-d^4+6*d^5)/(1-d^4+2*d^2) ∧
      (∀ k, 0 < k → k < 1/2-d → populationRD (clusteredMargins d) (fun x => 1/2 + clusterSmooth d x) k = 0) ∧
      expectation (clusteredMargins d) (fun x => clusterSmooth d x^2) ≤ (d/2)^2) ∧
    populationCoefficient (clusteredMargins (1/1000)) 1 (fun x => 1/2 + clusterSmooth (1/1000) x) =
      -499999999999503/500000999999500 ∧
    (∀ᵐ z ∂witnessLaw (clusteredMargins (1/1000)) (clusterSmooth (1/1000)),
      799/2000 ≤ z.2 ∧ z.2 ≤ 1201/2000) ∧
    Tendsto (fun d => populationCoefficient (clusteredMargins d) 1 (fun x => 1/2 + clusterSmooth d x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) ∧
    ¬ (∃ C : ℝ, ∀ d, 0 < d → d ≤ 1/2 →
      |populationCoefficient (clusteredMargins d) 1 (fun x => 1/2 + clusterSmooth d x)| ≤ C*(d/2)) := by
  refine ⟨?_, ?_, ?_, GLP023B2_cc_limit, GLP023B2_cc_no_uniform_bound⟩
  · intro d hd hd'
    obtain ⟨hx, hh, hDh, hxd, hxx, hxh, _, _⟩ := GLP023B2_cc_moments d hd hd'
    exact ⟨GLP023B2_cc_probability d hd hd', GLP023B2_cc_support d, GLP023B2_cc_noatom d,
      fun a b ha hab hb => GLP023B2_cc_open_mass d a b hd hd' ha hab hb,
      GLP023B2_cc_density_continuous d, fun x _ => GLP023B2_cc_density_lower d x hd hd',
      GLP023B2_cc_continuous d hd hd', GLP023B2_cc_zero d hd',
      fun x hx => GLP023B2_cc_vanish d x hd hx, fun x => GLP023B2_cc_odd d x hd',
      GLP023B2_cc_lipschitz d hd hd', fun x => GLP023B2_cc_bound d x hd,
      GLP023B2_cc_sup d hd hd', GLP023B2_cc_conditional_mean d hd hd',
      hx, hh, hDh, hxd, hxx, hxh, GLP023B2_cc_coefficient d hd hd',
      fun k hk hk' => GLP023B2_cc_rd d hd hd' k hk hk', GLP023B2_cc_square_bound d hd hd'⟩
  · have h := GLP023B2_cc_coefficient (1/1000) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  · have h := GLP023B2_cc_outcomes (1/1000) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h

end
end AronowAudit.P023.Wave1
