import AronowAudit.P023.Wave1.Lib.PopulationProjectionTailC
import AronowAudit.P023.Wave1.Lib.AmplificationDivergenceTailC
import AronowAudit.P023.Wave1.Gap.GP023B1b
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Continuous bias functionals on the closed space of functions vanishing at zero. -/
namespace AronowAudit.P023.Wave1
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal
set_option maxHeartbeats 600000
set_option maxRecDepth 2048

local instance tc10_decidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance tc10_uniform_probability : IsProbabilityMeasure uniformMargins :=
  ⟨uniform_law_normalized.1⟩

abbrev tc10_interval := Set.Icc (-1 : ℝ) 1

local instance tc10_interval_normedAddCommGroup : NormedAddCommGroup C(tc10_interval, ℝ) := inferInstance
local instance tc10_interval_normedSpace : NormedSpace ℝ C(tc10_interval, ℝ) := inferInstance

def tc10_origin : tc10_interval := ⟨0, by norm_num⟩

abbrev tc10_C0 : Submodule ℝ C(tc10_interval, ℝ) :=
  (ContinuousMap.evalCLM ℝ tc10_origin).ker

local instance tc10_C0_normedAddCommGroup : NormedAddCommGroup tc10_C0 := inferInstance
local instance tc10_C0_normedSpace : NormedSpace ℝ tc10_C0 := inferInstance

instance tc10_C0_complete : CompleteSpace tc10_C0 :=
  (ContinuousLinearMap.isClosed_ker (ContinuousMap.evalCLM ℝ tc10_origin)).completeSpace_coe

def tc10_clamp : C(ℝ, tc10_interval) :=
  ⟨fun x => ⟨max (-1) (min 1 x), le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩,
    (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _⟩

def tc10_extend (f : tc10_C0) : C(ℝ, ℝ) := f.1.comp tc10_clamp

theorem tc10_extend_eq (f : tc10_C0) (x : tc10_interval) : tc10_extend f x = f.1 x := by
  change f.1 ⟨max (-1) (min 1 x.val), _⟩ = f.1 x
  congr 1
  exact Subtype.ext (by simp [min_eq_right x.2.2, max_eq_right x.2.1])

theorem tc10_extend_zero (f : tc10_C0) : tc10_extend f 0 = 0 := by
  have h := f.2
  change f.1 tc10_origin = 0 at h
  exact (tc10_extend_eq f tc10_origin).trans h

theorem tc10_extend_bound (f : tc10_C0) (x : ℝ) : |tc10_extend f x| ≤ ‖f‖ :=
  f.1.norm_coe_le_norm (tc10_clamp x)

theorem tc10_residual_integrable (J : ℕ) : Integrable (popResidual uniformMargins J) uniformMargins := by
  change Integrable (fun x => party x - (projection uniformMargins J).eval x) uniformMargins
  simpa using tc04_residual_mul_integrable (projection uniformMargins J) 1

theorem tc10_residual_measurable (J : ℕ) : Measurable (popResidual uniformMargins J) :=
  GP023B1b_measurable_party.sub (projection uniformMargins J).continuous.measurable

theorem tc10_residual_mul (J : ℕ) (f : tc10_C0) :
    Integrable (fun x => popResidual uniformMargins J x * tc10_extend f x) uniformMargins :=
  (tc10_residual_integrable J).mul_bdd (tc10_extend f).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (tc10_extend_bound f))

theorem tc10_variance_pos (J : ℕ) : 0 < residualVariance uniformMargins J :=
  tc04_residual_variance_pos uniformMargins uniform_law_normalized.2 J (uniform_full_rank J)

theorem tc10_amplification_nonneg (J : ℕ) : 0 ≤ amplification uniformMargins J :=
  div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) (tc10_variance_pos J).le

theorem tc10_bias_bound (J : ℕ) (f : tc10_C0) :
    |biasFunctional uniformMargins J (tc10_extend f)| ≤ amplification uniformMargins J * ‖f‖ := by
  unfold biasFunctional amplification expectation
  rw [abs_div, abs_of_pos (tc10_variance_pos J)]
  apply (div_le_div_of_nonneg_right abs_integral_le_integral_abs (tc10_variance_pos J).le).trans
  have hi := (tc10_residual_integrable J).abs.mul_const ‖f‖
  have hb : (∫ x, |popResidual uniformMargins J x * tc10_extend f x| ∂uniformMargins) ≤
      (∫ x, |popResidual uniformMargins J x| * ‖f‖ ∂uniformMargins) := by
    apply integral_mono (tc10_residual_mul J f).abs hi
    intro x
    dsimp only
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (tc10_extend_bound f x) (abs_nonneg _)
  rw [integral_mul_const] at hb
  exact (div_le_div_of_nonneg_right hb (tc10_variance_pos J).le).trans_eq (by ring)

def tc10_biasLinear (J : ℕ) : tc10_C0 →ₗ[ℝ] ℝ where
  toFun f := biasFunctional uniformMargins J (tc10_extend f)
  map_add' f g := by
    change (∫ x, popResidual uniformMargins J x * (tc10_extend f x + tc10_extend g x)
      ∂uniformMargins) / _ = _
    simp_rw [mul_add]
    rw [integral_add (tc10_residual_mul J f) (tc10_residual_mul J g), add_div]
    rfl
  map_smul' c f := by
    change (∫ x, popResidual uniformMargins J x * (c * tc10_extend f x) ∂uniformMargins) / _ = _
    simp_rw [mul_left_comm _ c]
    rw [integral_const_mul]
    change _ = c * _
    unfold biasFunctional expectation
    ring

def tc10_biasCLM (J : ℕ) : tc10_C0 →L[ℝ] ℝ :=
  (tc10_biasLinear J).mkContinuous (amplification uniformMargins J) (tc10_bias_bound J)


theorem tc10_projection_zero (J : ℕ) : (projection uniformMargins J).eval 0 = 1/2 := by
  rw [tc04_uniform_projection_expansion]
  simp [tc04_uniform_candidate, Polynomial.eval_finsetSum, tc08_legendre_odd_zero]

def tc10_delta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def tc10_ramp (J n : ℕ) (x : ℝ) : ℝ :=
  sigmoid 1 (tc10_delta n)
    (1/2 + sigmoid (1/2) (tc10_delta n) x - (projection uniformMargins J).eval x)

theorem tc10_ramp_continuous (J n : ℕ) : Continuous (tc10_ramp J n) :=
  (GP023B1b_continuous 1 _).comp
    ((continuous_const.add (GP023B1b_continuous (1/2) _)).sub (projection uniformMargins J).continuous)

theorem tc10_ramp_zero (J n : ℕ) : tc10_ramp J n 0 = 0 := by
  simp [tc10_ramp, sigmoid, tc10_projection_zero]

theorem tc10_ramp_bound (J n : ℕ) (x : ℝ) : |tc10_ramp J n x| ≤ 1 :=
  GP023B1b_abs_le 1 _ _ (by norm_num)

def tc10_rampC0 (J n : ℕ) : tc10_C0 :=
  ⟨⟨fun x => tc10_ramp J n x, (tc10_ramp_continuous J n).comp continuous_subtype_val⟩,
    tc10_ramp_zero J n⟩

theorem tc10_rampC0_norm (J n : ℕ) : ‖tc10_rampC0 J n‖ ≤ 1 :=
  (ContinuousMap.norm_le _ (by norm_num)).mpr (fun x => tc10_ramp_bound J n x)

theorem tc10_delta_zero : Tendsto tc10_delta atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n:ℝ)+1)) atTop (nhds 0)
  simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

theorem tc10_sigmoid_saturated (a δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ |x|) :
    sigmoid a δ x = if 0 ≤ x then a else -a := by
  by_cases hp : 0 ≤ x
  · have h : 1 ≤ x / δ := (le_div_iff₀ hδ).mpr (by simpa [abs_of_nonneg hp] using hx)
    simp [sigmoid, hp, min_eq_left h]
  · have h : x / δ ≤ -1 := (div_le_iff₀ hδ).mpr (by rw [abs_of_neg (lt_of_not_ge hp)] at hx; linarith)
    simp [sigmoid, hp, min_eq_right (by linarith : x / δ ≤ 1), max_eq_left h]

theorem tc10_ramp_eventually (J : ℕ) (x : ℝ) (hx : x ≠ 0) :
    ∀ᶠ n in atTop, popResidual uniformMargins J x * tc10_ramp J n x = |popResidual uniformMargins J x| := by
  by_cases hr : popResidual uniformMargins J x = 0
  · simp [hr]
  have hxp : 0 < |x| := abs_pos.mpr hx
  have hrp : 0 < |popResidual uniformMargins J x| := abs_pos.mpr hr
  filter_upwards [tc10_delta_zero.eventually (gt_mem_nhds hxp),
    tc10_delta_zero.eventually (gt_mem_nhds hrp)] with n hn hn'
  have hd : 0 < tc10_delta n := by dsimp [tc10_delta]; positivity
  have he : 1/2 + sigmoid (1/2) (tc10_delta n) x - (projection uniformMargins J).eval x =
      popResidual uniformMargins J x := by
    rw [tc10_sigmoid_saturated _ _ _ hd hn.le]
    dsimp [popResidual, party]
    split_ifs <;> ring
  rw [tc10_ramp, he, tc10_sigmoid_saturated _ _ _ hd hn'.le]
  split_ifs with hp
  · simp [abs_of_nonneg hp]
  · simp [abs_of_neg (lt_of_not_ge hp)]

theorem tc10_ramp_integral_limit (J : ℕ) :
    Tendsto (fun n => biasFunctional uniformMargins J (tc10_extend (tc10_rampC0 J n)))
      atTop (nhds (amplification uniformMargins J)) := by
  have he (n : ℕ) : (fun x => popResidual uniformMargins J x * tc10_extend (tc10_rampC0 J n) x)
      =ᵐ[uniformMargins] (fun x => popResidual uniformMargins J x * tc10_ramp J n x) := by
    filter_upwards [show ∀ᵐ x ∂uniformMargins, x ∈ Icc (-1:ℝ) 1 from ae_iff.mpr uniform_law_normalized.2]
      with x hx
    rw [tc10_extend_eq _ ⟨x,hx⟩]
    rfl
  have hlim : Tendsto (fun n => ∫ x, popResidual uniformMargins J x * tc10_ramp J n x ∂uniformMargins)
      atTop (nhds (∫ x, |popResidual uniformMargins J x| ∂uniformMargins)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |popResidual uniformMargins J x|)
    · intro n
      exact ((tc10_residual_measurable J).mul (tc10_ramp_continuous J n).measurable).aestronglyMeasurable
    · exact (tc10_residual_integrable J).abs
    · intro n
      apply ae_of_all
      intro x
      simp only [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (tc10_ramp_bound J n x) (abs_nonneg _)).trans_eq (mul_one _)
    · have hz : ∀ᵐ x ∂uniformMargins, x ≠ 0 := by
        rw [ae_iff]
        simp [uniformMargins, Measure.smul_apply]
      filter_upwards [hz] with x hx
      exact tendsto_const_nhds.congr' ((tc10_ramp_eventually J x hx).mono (fun _ hn => hn.symm))
  change Tendsto _ atTop (nhds ((∫ x, |popResidual uniformMargins J x| ∂uniformMargins) / residualVariance uniformMargins J))
  apply (hlim.div_const (residualVariance uniformMargins J)).congr
  intro n
  exact congrArg (fun t => t / residualVariance uniformMargins J) (integral_congr_ae (he n)).symm


/-- Exact operator norm on the Banach space of continuous functions vanishing at zero. -/
theorem tc10_biasCLM_norm (J : ℕ) : ‖tc10_biasCLM J‖ = amplification uniformMargins J := by
  apply le_antisymm
  · exact (tc10_biasCLM J).opNorm_le_bound (tc10_amplification_nonneg J) (fun f => tc10_bias_bound J f)
  · apply le_of_tendsto (tc10_ramp_integral_limit J)
    apply Eventually.of_forall
    intro n
    exact (le_abs_self _).trans ((tc10_biasCLM J).unit_le_opNorm (x := tc10_rampC0 J n) (tc10_rampC0_norm J n))

/-- The precise supremum over the real-function domain. -/
theorem continuous_bias_norm (J : ℕ) (hJ : 1 ≤ J) :
    sSup {t | ∃ h : ℝ → ℝ, ContinuousOn h (Set.Icc (-1) 1) ∧ h 0 = 0 ∧
      (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1) ∧ t = biasFunctional uniformMargins J h} =
      amplification uniformMargins J := by
  let S : Set ℝ := {t | ∃ h : ℝ → ℝ, ContinuousOn h (Set.Icc (-1) 1) ∧ h 0 = 0 ∧
      (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1) ∧ t = biasFunctional uniformMargins J h}
  have hzero : 0 ∈ S := by
    refine ⟨fun _ => 0, continuousOn_const, rfl, fun _ _ => by norm_num, ?_⟩
    simp [biasFunctional, expectation]
  have hu : ∀ t ∈ S, t ≤ amplification uniformMargins J := by
    rintro t ⟨h, hh, h0, hb, rfl⟩
    let f : tc10_C0 := ⟨⟨fun x => h x, continuousOn_iff_continuous_restrict.mp hh⟩, h0⟩
    have hfn : ‖f‖ ≤ 1 := (ContinuousMap.norm_le _ (by norm_num)).mpr (fun x => hb x x.2)
    have he : biasFunctional uniformMargins J h = tc10_biasCLM J f := by
      unfold biasFunctional expectation
      congr 1
      apply integral_congr_ae
      filter_upwards [show ∀ᵐ x ∂uniformMargins, x ∈ Icc (-1:ℝ) 1 from ae_iff.mpr uniform_law_normalized.2]
        with x hx
      rw [tc10_extend_eq _ ⟨x,hx⟩]
      rfl
    rw [he, ← tc10_biasCLM_norm]
    exact (le_abs_self _).trans ((tc10_biasCLM J).unit_le_opNorm (x := f) hfn)
  have hbd : BddAbove S := ⟨amplification uniformMargins J, hu⟩
  apply le_antisymm (csSup_le ⟨0,hzero⟩ hu)
  apply le_of_tendsto (tc10_ramp_integral_limit J)
  apply Eventually.of_forall
  intro n
  apply le_csSup hbd
  refine ⟨tc10_extend (tc10_rampC0 J n), (tc10_extend _).continuous.continuousOn,
    tc10_extend_zero _, ?_, rfl⟩
  intro x _
  exact (tc10_extend_bound _ x).trans (tc10_rampC0_norm J n)

/-- Uniform boundedness yields one function with unbounded absolute bias. -/
theorem tc10_exists_unbounded_abs
    (h_amp : Tendsto (amplification uniformMargins) atTop atTop) :
    ∃ f : tc10_C0, ∀ C : ℝ, ∃ J, C < |tc10_biasCLM J f| := by
  by_contra! hn
  have hpoint : ∀ f : tc10_C0, ∃ C, ∀ J, ‖tc10_biasCLM J f‖ ≤ C := hn
  obtain ⟨C,hC⟩ := banach_steinhaus hpoint
  obtain ⟨J,hJ⟩ := (h_amp.eventually_gt_atTop C).exists
  exact (not_lt_of_ge (hC J)) (by simpa [tc10_biasCLM_norm] using hJ)

/-- One sign has unbounded positive bias. -/
theorem tc10_exists_unbounded_positive
    (h_amp : Tendsto (amplification uniformMargins) atTop atTop) :
    ∃ f : tc10_C0, ∀ C : ℝ, ∃ J, C < tc10_biasCLM J f := by
  obtain ⟨f,hf⟩ := tc10_exists_unbounded_abs h_amp
  by_cases hp : ∀ C : ℝ, ∃ J, C < tc10_biasCLM J f
  · exact ⟨f,hp⟩
  push Not at hp
  obtain ⟨C,hC⟩ := hp
  refine ⟨-f, fun D => ?_⟩
  obtain ⟨J,hJ⟩ := hf (max C D)
  refine ⟨J, ?_⟩
  rw [map_neg]
  have hu := hC J
  rcases abs_cases (tc10_biasCLM J f) with ⟨he,hp⟩ | ⟨he,hp⟩
  · rw [he] at hJ
    exact False.elim (not_lt_of_ge hu ((le_max_left C D).trans_lt hJ))
  · rw [he] at hJ
    exact (le_max_right C D).trans_lt hJ

/-- An unbounded sequence has arbitrarily large values beyond each finite prefix. -/
theorem tc10_unbounded_tail (v : ℕ → ℝ) (hv : ∀ C : ℝ, ∃ J, C < v J)
    (N : ℕ) (C : ℝ) : ∃ J, N < J ∧ C < v J := by
  let B : ℝ := ∑ j ∈ Finset.range (N+1), |v j|
  obtain ⟨J,hJ⟩ := hv (max B C)
  have hN : N < J := by
    by_contra hn
    have hmem : J ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    have hb : v J ≤ B := (le_abs_self _).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (v j)) hmem)
    exact (not_lt_of_ge hb) ((le_max_left B C).trans_lt hJ)
  exact ⟨J,hN,(le_max_right B C).trans_lt hJ⟩

/-- Strictly increasing degrees with a prescribed linear positive lower bound. -/
theorem tc10_select_degrees (v : ℕ → ℝ) (hv : ∀ C : ℝ, ∃ J, C < v J) :
    ∃ degrees : ℕ → ℕ, StrictMono degrees ∧
      ∀ m : ℕ, 1 ≤ m → (m : ℝ)/4 ≤ v (degrees m) := by
  choose next hnext using tc10_unbounded_tail v hv
  let degrees : ℕ → ℕ := fun m => Nat.rec 0 (fun n j => next j ((n+1:ℕ):ℝ)) m
  have hd (m : ℕ) : degrees (m+1) = next (degrees m) ((m+1:ℕ):ℝ) := rfl
  refine ⟨degrees, strictMono_nat_of_lt_succ (fun m => by rw [hd]; exact (hnext _ _).1), ?_⟩
  intro m hm
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [hd]
  have h := (hnext (degrees n) ((n+1:ℕ):ℝ)).2
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  push_cast at h ⊢
  linarith

/-- A single globally continuous bounded mean with growing population bias. -/
theorem tc10_fixed_bad_mean_global (h_amp : Filter.Tendsto (amplification uniformMargins)
    Filter.atTop Filter.atTop) :
    ∃ h : ℝ → ℝ, ∃ degrees : ℕ → ℕ,
      Continuous h ∧ h 0 = 0 ∧ (∀ x, |h x| ≤ 1/12) ∧
      StrictMono degrees ∧ (∀ m : ℕ, 1 ≤ m → (m : ℝ)/4 ≤ biasFunctional uniformMargins (degrees m) h) ∧
      (∀ J, 1 ≤ J → populationCoefficient uniformMargins J (fun x => 1/2+h x) =
        biasFunctional uniformMargins J h) := by
  obtain ⟨f,hf⟩ := tc10_exists_unbounded_positive h_amp
  let c : ℝ := (12*(‖f‖+1))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  let g : tc10_C0 := c • f
  have hg : ∀ C : ℝ, ∃ J, C < tc10_biasCLM J g := by
    intro C
    obtain ⟨J,hJ⟩ := hf (C/c)
    refine ⟨J, ?_⟩
    change C < tc10_biasCLM J (c • f)
    rw [map_smul, smul_eq_mul]
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hJ
  obtain ⟨degrees,hmono,hdegrees⟩ := tc10_select_degrees (fun J => tc10_biasCLM J g) hg
  refine ⟨tc10_extend g, degrees, (tc10_extend g).continuous, tc10_extend_zero g,
    ?_, hmono, hdegrees, ?_⟩
  · intro x
    apply (tc10_extend_bound g x).trans
    change ‖c • f‖ ≤ 1/12
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    dsimp only [c]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (by positivity : 0 < 12*(‖f‖+1))).mpr
    nlinarith [norm_nonneg f]
  · intro J hJ
    exact population_fwl uniformMargins uniform_law_normalized.2 J hJ (uniform_full_rank J)
      _ (tc10_extend g).continuous.continuousOn

/-- A fixed continuous bounded mean with growing bias, assuming amplification diverges. -/
theorem fixed_bad_mean (h_amp : Filter.Tendsto (amplification uniformMargins)
    Filter.atTop Filter.atTop) :
    ∃ h : ℝ → ℝ, ∃ degrees : ℕ → ℕ,
      Continuous h ∧ h 0 = 0 ∧ (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1/12) ∧
      StrictMono degrees ∧ (∀ m : ℕ, 1 ≤ m → (m : ℝ)/4 ≤ biasFunctional uniformMargins (degrees m) h) ∧
      (∀ J, 1 ≤ J → populationCoefficient uniformMargins J (fun x => 1/2+h x) =
        biasFunctional uniformMargins J h) := by
  obtain ⟨h,degrees,hc,h0,hb,hm,hgrow,hfwl⟩ := tc10_fixed_bad_mean_global h_amp
  exact ⟨h,degrees,hc,h0,fun x _ => hb x,hm,hgrow,hfwl⟩


/-- The amplification premise is discharged by the proved analytic divergence theorem. -/
theorem fixed_bad_mean_unconditional :
    ∃ h : ℝ → ℝ, ∃ degrees : ℕ → ℕ,
      Continuous h ∧ h 0 = 0 ∧ (∀ x ∈ Set.Icc (-1) 1, |h x| ≤ 1/12) ∧
      StrictMono degrees ∧ (∀ m : ℕ, 1 ≤ m → (m : ℝ)/4 ≤ biasFunctional uniformMargins (degrees m) h) ∧
      (∀ J, 1 ≤ J → populationCoefficient uniformMargins J (fun x => 1/2+h x) =
        biasFunctional uniformMargins J h) := fixed_bad_mean uniform_amplification_diverges

end
end AronowAudit.P023.Wave1
