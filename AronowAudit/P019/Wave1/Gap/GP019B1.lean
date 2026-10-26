import AronowAudit.P019.P019_Audit
import AronowAudit.P053.P053_NormalQuantiles
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.ChiSquared
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi


namespace AronowAudit.P019.Wave1

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

variable {Ω : Type*} [Fintype Ω]

local instance npu_normal_atomless : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

/-! ## Uniformity of normal p-values -/

lemma npu_cdf_eq (x : ℝ) : normalCDF x = cdf (gaussianReal 0 1) x := by
  rw [cdf_eq_real]
  rfl

lemma npu_strictMono : StrictMono normalCDF := by
  intro x y hxy
  rw [npu_cdf_eq, npu_cdf_eq]
  exact AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hxy

lemma npu_cdf_neg (x : ℝ) : normalCDF (-x) = 1 - normalCDF x := by
  simp only [npu_cdf_eq]
  exact AronowAudit.P053.NormalCompletion.normal_cdf_neg x

lemma npu_cdf_pos (x : ℝ) : 0 < normalCDF x := by
  have hlt : normalCDF (x-1) < normalCDF x :=
    npu_strictMono (by linarith)
  have hnonneg : 0 ≤ normalCDF (x-1) := by
    rw [npu_cdf_eq]
    exact cdf_nonneg _ _
  linarith

lemma npu_cdf_lt_one (x : ℝ) : normalCDF x < 1 := by
  have hlt : normalCDF x < normalCDF (x+1) :=
    npu_strictMono (by linarith)
  have hle : normalCDF (x+1) ≤ 1 := by
    rw [npu_cdf_eq]
    exact cdf_le_one _ _
  linarith

lemma npu_quantile_bridge (α : ℝ) :
    normalQuantile (1-α/2) = AronowAudit.P053.normalCritical α := by
  rfl

lemma npu_quantile_cdf (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    normalCDF (normalQuantile (1-α/2)) = 1-α/2 := by
  rw [npu_quantile_bridge]
  exact AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα0 hα1

lemma npu_quantile_pos (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    0 < normalQuantile (1-α/2) := by
  rw [npu_quantile_bridge]
  exact AronowAudit.P053.NormalCompletion.normalCritical_pos α hα0 hα1

lemma npu_mass_Iio (x : ℝ) :
    ((gaussianReal 0 1) (Set.Iio x)).toReal = normalCDF x := by
  rw [measure_congr (Iio_ae_eq_Iic' (measure_singleton x))]
  rfl

lemma npu_mass_Ioi (x : ℝ) :
    ((gaussianReal 0 1) (Set.Ioi x)).toReal = 1-normalCDF x := by
  have h := measureReal_add_measureReal_compl (μ := gaussianReal 0 1)
    (s := Set.Iic x) measurableSet_Iic
  simp only [Set.compl_Iic, measureReal_def, measure_univ, ENNReal.toReal_one] at h
  change (gaussianReal 0 1 (Set.Ioi x)).toReal =
    1-(gaussianReal 0 1 (Set.Iic x)).toReal
  linarith

lemma npu_mass_Ici (x : ℝ) :
    ((gaussianReal 0 1) (Set.Ici x)).toReal = 1-normalCDF x := by
  rw [← measure_congr (Ioi_ae_eq_Ici' (measure_singleton x))]
  exact npu_mass_Ioi x

lemma npu_tail_event (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    {g : ℝ | 2*normalCDF (-|g|) ≤ u} =
      Set.Iic (-normalQuantile (1-u/2)) ∪ Set.Ici (normalQuantile (1-u/2)) := by
  let c := normalQuantile (1-u/2)
  have hcdf : normalCDF (-c) = u/2 := by
    rw [npu_cdf_neg]
    dsimp only [c]
    rw [npu_quantile_cdf u hu0 hu1]
    ring
  ext g
  change (2*normalCDF (-|g|) ≤ u) ↔ (g ≤ -c ∨ c ≤ g)
  have hfirst : (2*normalCDF (-|g|) ≤ u) ↔
      normalCDF (-|g|) ≤ normalCDF (-c) := by
    rw [hcdf]; constructor <;> intro h <;> linarith
  rw [hfirst, npu_strictMono.le_iff_le]
  have hneg : (-|g| ≤ -c) ↔ c ≤ |g| := by constructor <;> intro h <;> linarith
  rw [hneg]
  constructor
  · intro h
    by_cases hg : 0 ≤ g
    · right
      simpa only [abs_of_nonneg hg] using h
    · left
      rw [abs_of_neg (lt_of_not_ge hg)] at h
      linarith
  · rintro (h | h)
    · exact le_trans (by linarith) (neg_le_abs g)
    · exact le_trans h (le_abs_self g)

theorem normal_pvalue_uniform_proof (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    ((gaussianReal 0 1) {g : ℝ | 2*normalCDF (-|g|) ≤ u}).toReal = u := by
  let c := normalQuantile (1-u/2)
  have hc : 0 < c := npu_quantile_pos u hu0 hu1
  have hdisj : Disjoint (Set.Iic (-c)) (Set.Ici c) := by
    refine Set.disjoint_left.mpr ?_
    intro g hg1 hg2
    change g ≤ -c at hg1
    change c ≤ g at hg2
    linarith
  rw [npu_tail_event u hu0 hu1]
  change (gaussianReal 0 1).real (Set.Iic (-c) ∪ Set.Ici c) = u
  rw [measureReal_union hdisj measurableSet_Ici]
  change normalCDF (-c) + (gaussianReal 0 1 (Set.Ici c)).toReal = u
  rw [npu_mass_Ici, npu_cdf_neg]
  have hq : normalCDF c = 1-u/2 := npu_quantile_cdf u hu0 hu1
  rw [hq]
  ring

/-! ## Fisher identity for independent uniforms -/

-- Restricting ordinary Lebesgue measure to [0,1] already has mass one.
local instance ufi_uniform_probability :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

lemma ufi_log_measurable : Measurable (fun u : ℝ => -2 * Real.log u) := by
  fun_prop

lemma ufi_uniform_ae : ∀ᵐ u : ℝ ∂volume.restrict (Set.Icc (0 : ℝ) 1),
    0 < u ∧ u ≤ 1 := by
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := (volume : Measure ℝ).ae_ne 0
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with u hu hne
  exact ⟨lt_of_le_of_ne hu.1 (Ne.symm hne), hu.2⟩

/-- The logarithm at zero is harmless because zero has restricted volume zero.
The proof computes the CDF for all real thresholds, including zero. -/
lemma ufi_uniform_log_law :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun u : ℝ => -2*Real.log u) =
      expMeasure (1/2) := by
  let U : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure (expMeasure (1/2)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  apply Measure.eq_of_cdf
  refine StieltjesFunction.ext fun t => ?_
  rw [cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1/2)]
  rw [cdf_eq_real]
  change ((U.map (fun u : ℝ => -2*Real.log u)) (Set.Iic t)).toReal = _
  rw [Measure.map_apply ufi_log_measurable measurableSet_Iic]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    let a : ℝ := Real.exp (-t/2)
    have ha0 : 0 < a := Real.exp_pos _
    have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hevent : (fun u : ℝ => -2*Real.log u) ⁻¹' Set.Iic t =ᵐ[U] Set.Ici a := by
      filter_upwards [ufi_uniform_ae] with u hu
      apply propext
      change (-2*Real.log u ≤ t) ↔ a ≤ u
      have hlog : (-t/2 ≤ Real.log u) ↔ a ≤ u :=
        Real.le_log_iff_exp_le hu.1
      constructor
      · intro h
        exact hlog.mp (by linarith)
      · intro h
        have := hlog.mpr h
        linarith
    rw [measure_congr hevent]
    change ((volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Ici a)).toReal = _
    rw [Measure.restrict_apply measurableSet_Ici]
    have hinter : Set.Ici a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc a 1 := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨hau, _, hu1⟩
        exact ⟨hau, hu1⟩
      · rintro ⟨hau, hu1⟩
        exact ⟨hau, le_trans ha0.le hau, hu1⟩
    rw [hinter, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr ha1)]
    dsimp only [a]
    have hexp : -t/2 = -((1/2 : ℝ)*t) := by ring
    rw [hexp]
  · rw [if_neg ht]
    have hevent : (fun u : ℝ => -2*Real.log u) ⁻¹' Set.Iic t =ᵐ[U] ∅ := by
      filter_upwards [ufi_uniform_ae] with u hu
      have hlog : Real.log u ≤ 0 := Real.log_nonpos hu.1.le hu.2
      apply propext
      change (-2*Real.log u ≤ t) ↔ False
      constructor
      · intro h
        linarith
      · exact False.elim
    rw [measure_congr hevent, measure_empty, ENNReal.toReal_zero]

/-- One independent pair of standard normals has the same radius-squared
law as one transformed uniform. -/
lemma ufi_normal_pair_law :
    (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map
      (fun x : Fin 2 → ℝ => ∑ b, (x b)^2) = expMeasure (1/2) := by
  have h := StatLean.MultipleTesting.map_sum_sq_eq_chiSquared
    (n := 2) (by norm_num) (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))
    (fun b (x : Fin 2 → ℝ) => x b)
    (fun b => measurable_pi_apply b)
    (fun b => (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) b).map_eq)
    (by simpa only [id_eq] using
      (iIndepFun_pi (μ := fun _ : Fin 2 => gaussianReal 0 1)
        (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)))
  simpa only [StatLean.MultipleTesting.chiSquared, expMeasure,
    Nat.cast_ofNat, show (2 : ℝ)/2 = 1 by norm_num] using h

/-- Flatten five two-coordinate blocks into ten coordinates. -/
def ufi_flat (x : Fin 5 → Fin 2 → ℝ) (k : Fin 10) : ℝ :=
  x ((finProdFinEquiv : Fin 5 × Fin 2 ≃ Fin 10).symm k).1
    ((finProdFinEquiv : Fin 5 × Fin 2 ≃ Fin 10).symm k).2

lemma ufi_flat_measurable : Measurable ufi_flat := by
  apply Measurable.of_eval
  intro k
  let e : Fin 5 × Fin 2 ≃ Fin 10 := finProdFinEquiv
  exact (measurable_pi_apply (e.symm k).2).comp
    (measurable_pi_apply (e.symm k).1)

/-- The rectangular-set proof makes the independence of disjoint pairs
explicit, without requiring an extra independence hypothesis. -/
lemma ufi_flat_law :
    (Measure.pi (fun _ : Fin 5 => Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))).map
      ufi_flat = Measure.pi (fun _ : Fin 10 => gaussianReal 0 1) := by
  let e : Fin 5 × Fin 2 ≃ Fin 10 := finProdFinEquiv
  refine (Measure.pi_eq (μ := fun _ : Fin 10 => gaussianReal 0 1) ?_).symm
  intro s hs
  rw [Measure.map_apply ufi_flat_measurable (MeasurableSet.univ_pi hs)]
  have hpre : ufi_flat ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun j : Fin 5 => Set.univ.pi (fun b : Fin 2 => s (e (j,b)))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h j b
      have hh := h (e (j,b))
      change x (e.symm (e (j,b))).1 (e.symm (e (j,b))).2 ∈ s (e (j,b)) at hh
      simpa only [Equiv.symm_apply_apply] using hh
    · intro h k
      have hh := h (e.symm k).1 (e.symm k).2
      change x (e.symm k).1 (e.symm k).2 ∈ s k
      rwa [Prod.mk.eta, Equiv.apply_symm_apply] at hh
  rw [hpre, Measure.pi_pi]
  simp only [Measure.pi_pi]
  calc
    (∏ j : Fin 5, ∏ b : Fin 2, gaussianReal 0 1 (s (e (j,b)))) =
        ∏ p : Fin 5 × Fin 2, gaussianReal 0 1 (s (e p)) :=
      (Fintype.prod_prod_type (fun p : Fin 5 × Fin 2 => gaussianReal 0 1 (s (e p)))).symm
    _ = ∏ k : Fin 10, gaussianReal 0 1 (s k) :=
      e.prod_comp (fun k => gaussianReal 0 1 (s k))

lemma ufi_flat_sum (x : Fin 5 → Fin 2 → ℝ) :
    (∑ j : Fin 5, ∑ b : Fin 2, (x j b)^2) = ∑ k : Fin 10, (ufi_flat x k)^2 := by
  let e : Fin 5 × Fin 2 ≃ Fin 10 := finProdFinEquiv
  calc
    _ = ∑ p : Fin 5 × Fin 2, (x p.1 p.2)^2 := (Fintype.sum_prod_type _).symm
    _ = ∑ p : Fin 5 × Fin 2, (ufi_flat x (e p))^2 := by
      apply Finset.sum_congr rfl
      intro p _
      change (x p.1 p.2)^2 = (x (e.symm (e p)).1 (e.symm (e p)).2)^2
      rw [Equiv.symm_apply_apply]
    _ = _ := e.sum_comp (fun k => (ufi_flat x k)^2)

theorem uniform_fisher_identity_proof :
    (Measure.pi (fun _ : Fin 5 => volume.restrict (Set.Icc (0 : ℝ) 1))).map
      fisherStatistic = chiSquareTen := by
  let U : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let N₂ : Measure (Fin 2 → ℝ) := Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)
  let E : Measure ℝ := expMeasure (1/2)
  let L : (Fin 5 → ℝ) → Fin 5 → ℝ := fun u j => -2*Real.log (u j)
  let R : (Fin 5 → Fin 2 → ℝ) → Fin 5 → ℝ := fun x j => ∑ b, (x j b)^2
  let sum₅ : (Fin 5 → ℝ) → ℝ := fun y => ∑ j, y j
  have hL : Measurable L := by
    apply Measurable.of_eval
    intro j
    exact ufi_log_measurable.comp (measurable_pi_apply j)
  have hR : Measurable R := by
    apply Measurable.of_eval
    intro j
    exact Finset.measurable_sum _ (fun b _ =>
      ((measurable_pi_apply b).comp (measurable_pi_apply j)).pow_const 2)
  have hsum : Measurable sum₅ := by
    exact Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)
  have hUL : (Measure.pi (fun _ : Fin 5 => U)).map L = Measure.pi (fun _ : Fin 5 => E) := by
    dsimp only [L, E, U]
    rw [Measure.pi_map_pi (fun _ => ufi_log_measurable.aemeasurable)]
    simp only [ufi_uniform_log_law]
  have hNR : (Measure.pi (fun _ : Fin 5 => N₂)).map R = Measure.pi (fun _ : Fin 5 => E) := by
    dsimp only [R, E, N₂]
    rw [Measure.pi_map_pi (fun _ =>
      (Finset.measurable_sum _ (fun b _ => (measurable_pi_apply b).pow_const 2)).aemeasurable)]
    simp only [ufi_normal_pair_law]
  have hF : fisherStatistic = sum₅ ∘ L := by
    funext u
    change -2 * ∑ j, Real.log (u j) = ∑ j, -2 * Real.log (u j)
    exact Finset.mul_sum _ _ _
  have hSquares : sum₅ ∘ R = (fun x : Fin 10 → ℝ => ∑ k, (x k)^2) ∘ ufi_flat := by
    funext x
    exact ufi_flat_sum x
  calc
    _ = ((Measure.pi (fun _ : Fin 5 => U)).map L).map sum₅ := by
      rw [Measure.map_map hsum hL, ← hF]
    _ = (Measure.pi (fun _ : Fin 5 => E)).map sum₅ := by rw [hUL]
    _ = ((Measure.pi (fun _ : Fin 5 => N₂)).map R).map sum₅ := by rw [hNR]
    _ = (Measure.pi (fun _ : Fin 5 => N₂)).map
        ((fun x : Fin 10 → ℝ => ∑ k, (x k)^2) ∘ ufi_flat) := by
      rw [Measure.map_map hsum hR, hSquares]
    _ = ((Measure.pi (fun _ : Fin 5 => N₂)).map ufi_flat).map
        (fun x : Fin 10 → ℝ => ∑ k, (x k)^2) := by
      rw [Measure.map_map (by fun_prop) ufi_flat_measurable]
    _ = chiSquareTen := by
      change ((Measure.pi (fun _ : Fin 5 => Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))).map
        ufi_flat).map (fun x : Fin 10 → ℝ => ∑ k, (x k)^2) = chiSquareTen
      rw [ufi_flat_law]
      rfl

/-! ## Corrected two-sided planning power -/

/-- With d=|p1-p2|, s=√(S/n), and t=c√(V/n), this is exactly the stated
planning rejection event. The disjointness is part of the conclusion, not an
implicit convention. -/
lemma tpc_rejection_tail_split (d s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    {g : ℝ | t < |d+s*g|} =
      Set.Ioi ((t-d)/s) ∪ Set.Iio ((-t-d)/s) ∧
    Disjoint (Set.Ioi ((t-d)/s)) (Set.Iio ((-t-d)/s)) := by
  constructor
  · ext g
    change (t < |d+s*g|) ↔ ((t-d)/s < g ∨ g < (-t-d)/s)
    constructor
    · intro h
      by_cases hx : 0 ≤ d+s*g
      · left
        rw [div_lt_iff₀ hs]
        rw [abs_of_nonneg hx] at h
        nlinarith
      · right
        rw [lt_div_iff₀ hs]
        rw [abs_of_neg (lt_of_not_ge hx)] at h
        nlinarith
    · rintro (h | h)
      · rw [div_lt_iff₀ hs] at h
        exact lt_of_lt_of_le (by nlinarith : t < d+s*g) (le_abs_self _)
      · rw [lt_div_iff₀ hs] at h
        exact lt_of_lt_of_le (by nlinarith : t < -(d+s*g)) (neg_le_abs _)
  · refine Set.disjoint_left.mpr ?_
    intro g hg1 hg2
    change (t-d)/s < g at hg1
    change g < (-t-d)/s at hg2
    rw [div_lt_iff₀ hs] at hg1
    rw [lt_div_iff₀ hs] at hg2
    nlinarith

lemma tpc_affine_normal_probability (d s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ((gaussianReal 0 1) {g : ℝ | t < |d+s*g|}).toReal =
      normalCDF ((d-t)/s) + normalCDF ((-t-d)/s) := by
  obtain ⟨hsplit, hdisj⟩ := tpc_rejection_tail_split d s t hs ht
  rw [hsplit]
  change (gaussianReal 0 1).real (Set.Ioi ((t-d)/s) ∪ Set.Iio ((-t-d)/s)) = _
  rw [measureReal_union hdisj measurableSet_Iio]
  change (gaussianReal 0 1 (Set.Ioi ((t-d)/s))).toReal +
    (gaussianReal 0 1 (Set.Iio ((-t-d)/s))).toReal = _
  rw [npu_mass_Ioi, npu_mass_Iio]
  have hneg : (d-t)/s = -((t-d)/s) := by ring
  rw [hneg, npu_cdf_neg]

lemma tpc_two_tails (n p1 p2 c : ℝ) (hn : 0 < n)
    (hs : 0 < planningS p1 p2) (hc : 0 < c) :
    twoSidedPlanningPower n p1 p2 c =
      favoredTail n p1 p2 c + oppositeTail n p1 p2 c := by
  have hv : 0 < planningV p1 p2 :=
    lt_of_lt_of_le hs (pooled_variance_difference p1 p2).2
  have hscale : 0 < Real.sqrt (planningS p1 p2/n) :=
    Real.sqrt_pos.mpr (div_pos hs hn)
  have hthreshold : 0 < c*Real.sqrt (planningV p1 p2/n) :=
    mul_pos hc (Real.sqrt_pos.mpr (div_pos hv hn))
  have hN : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  have hS : Real.sqrt (planningS p1 p2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  have hA : (|p1-p2| - c*Real.sqrt (planningV p1 p2/n)) /
        Real.sqrt (planningS p1 p2/n) =
      (Real.sqrt n * |p1-p2| - c*Real.sqrt (planningV p1 p2)) /
        Real.sqrt (planningS p1 p2) := by
    rw [Real.sqrt_div hv.le, Real.sqrt_div hs.le]
    field_simp [hN, hS] <;> ring
  have hB : (-c*Real.sqrt (planningV p1 p2/n) - |p1-p2|) /
        Real.sqrt (planningS p1 p2/n) =
      (-Real.sqrt n * |p1-p2| - c*Real.sqrt (planningV p1 p2)) /
        Real.sqrt (planningS p1 p2) := by
    rw [Real.sqrt_div hv.le, Real.sqrt_div hs.le]
    field_simp [hN, hS] <;> ring
  unfold twoSidedPlanningPower favoredTail oppositeTail
  rw [tpc_affine_normal_probability |p1-p2| (Real.sqrt (planningS p1 p2/n))
    (c*Real.sqrt (planningV p1 p2/n)) hscale hthreshold]
  rw [hA]
  have hB' : (-(c*Real.sqrt (planningV p1 p2/n)) - |p1-p2|) /
        Real.sqrt (planningS p1 p2/n) =
      (-Real.sqrt n * |p1-p2| - c*Real.sqrt (planningV p1 p2)) /
        Real.sqrt (planningS p1 p2) := by
    simpa only [neg_mul] using hB
  rw [hB']

lemma tpc_opposite_reflection (n p1 p2 c : ℝ) :
    oppositeTail n p1 p2 c = 1 -
      normalCDF ((Real.sqrt n * |p1-p2| + c*Real.sqrt (planningV p1 p2)) /
        Real.sqrt (planningS p1 p2)) := by
  unfold oppositeTail
  have he : (-Real.sqrt n * |p1-p2| - c*Real.sqrt (planningV p1 p2)) /
      Real.sqrt (planningS p1 p2) =
      -((Real.sqrt n * |p1-p2| + c*Real.sqrt (planningV p1 p2)) /
        Real.sqrt (planningS p1 p2)) := by ring
  rw [he, npu_cdf_neg]

theorem two_sided_power_corrected_proof (n p1 p2 α : ℝ) (hn : 0 < n)
    (hp10 : 0 ≤ p1) (hp11 : p1 ≤ 1) (hp20 : 0 ≤ p2) (hp21 : p2 ≤ 1)
    (hs : 0 < planningS p1 p2) (ha0 : 0 < α) (ha1 : α < 1) :
    let c := normalQuantile (1-α/2)
    0 < c ∧
    twoSidedPlanningPower n p1 p2 c = favoredTail n p1 p2 c + oppositeTail n p1 p2 c ∧
    oppositeTail n p1 p2 c = 1 -
      normalCDF ((Real.sqrt n * |p1-p2| + c*Real.sqrt (planningV p1 p2)) /
        Real.sqrt (planningS p1 p2)) ∧
    0 < oppositeTail n p1 p2 c ∧ oppositeTail n p1 p2 c ≤ α/2 ∧
    (oppositeTail n p1 p2 c = α/2 ↔ p1=p2) ∧
    twoSidedPlanningPower n p1 p2 c - favoredTail n p1 p2 c = oppositeTail n p1 p2 c := by
  dsimp only
  let c := normalQuantile (1-α/2)
  let T := (Real.sqrt n * |p1-p2| + c*Real.sqrt (planningV p1 p2)) /
    Real.sqrt (planningS p1 p2)
  have hc : 0 < c := npu_quantile_pos α ha0 ha1
  have hcdf : normalCDF c = 1-α/2 := npu_quantile_cdf α ha0 ha1
  have hsum : twoSidedPlanningPower n p1 p2 c =
      favoredTail n p1 p2 c + oppositeTail n p1 p2 c :=
    tpc_two_tails n p1 p2 c hn hs hc
  have hreflect : oppositeTail n p1 p2 c = 1-normalCDF T :=
    tpc_opposite_reflection n p1 p2 c
  have harg : c ≤ T ∧ (T = c ↔ p1=p2) :=
    planning_tail_argument n p1 p2 c hn hs hc
  have hpos : 0 < oppositeTail n p1 p2 c := by
    rw [hreflect]
    linarith [npu_cdf_lt_one T]
  have hbound : oppositeTail n p1 p2 c ≤ α/2 := by
    have hmono : normalCDF c ≤ normalCDF T := npu_strictMono.monotone harg.1
    rw [hreflect]
    linarith
  have heq : oppositeTail n p1 p2 c = α/2 ↔ p1=p2 := by
    constructor
    · intro h
      have hCDF : normalCDF T = normalCDF c := by rw [hreflect] at h; linarith
      exact harg.2.mp (npu_strictMono.injective hCDF)
    · intro h
      have hT : T = c := harg.2.mpr h
      rw [hreflect, hT, hcdf]
      ring
  exact ⟨hc, hsum, hreflect, hpos, hbound, heq, by linarith [hsum]⟩

end
end AronowAudit.P019.Wave1
