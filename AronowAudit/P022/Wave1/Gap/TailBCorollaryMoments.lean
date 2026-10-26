import AronowAudit.P022.Wave1.Gap.TailBBoundConsistency
import AronowAudit.P022.Wave1.SharpBounds

/-! Moment limits and strict nondegeneracy for the literal P022 corollary. -/
namespace AronowAudit.P022.Wave1
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
noncomputable section

/-- The printed third-moment condition implies the exact printed square-tail condition. -/
theorem tb13_square_integrability (S : ExperimentSequence) (h3 : BoundedThirdMoments S) :
    UniformSquareIntegrability S := by
  classical
  obtain ⟨M, hM⟩ := h3
  have hM0 : 0 ≤ M := le_trans (Finset.expect_nonneg (fun i _ => by positivity)) (hM 0 true)
  have hb (t : Bool) (β : ℝ) : BddAbove (range (fun q =>
      finiteMean (fun i : Fin (S.design q).N =>
        if β ≤ rowOutcomes S t q i ^ 2 then rowOutcomes S t q i ^ 2 else 0))) := by
    refine ⟨1 + M, ?_⟩
    rintro _ ⟨q, rfl⟩
    calc
      _ ≤ finiteMean (fun i => 1 + |rowOutcomes S t q i| ^ 3) := by
        apply Finset.expect_le_expect
        intro i _
        have ha := abs_nonneg (rowOutcomes S t q i)
        have hs := sq_abs (rowOutcomes S t q i)
        have ht : rowOutcomes S t q i ^ 2 ≤ 1 + |rowOutcomes S t q i| ^ 3 := by
          by_cases h : |rowOutcomes S t q i| ≤ 1
          · nlinarith [sq_nonneg (|rowOutcomes S t q i| - 1)]
          · nlinarith [mul_nonneg (sq_nonneg (|rowOutcomes S t q i|))
              (sub_nonneg.mpr (le_of_not_ge h))]
        split_ifs <;> first | exact ht | positivity
      _ ≤ 1 + M := by
        unfold finiteMean
        rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
        exact add_le_add le_rfl (hM q t)
  intro t
  refine ⟨?_, hb t⟩
  have hm : Tendsto (fun β : ℝ => M / Real.sqrt β) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  refine squeeze_zero' ?_ ?_ hm
  · filter_upwards [] with β
    apply le_csSup_of_le (hb t β) (mem_range_self 0)
    exact Finset.expect_nonneg (fun _ _ => by split_ifs <;> positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    apply csSup_le (range_nonempty _)
    rintro _ ⟨q, rfl⟩
    exact (third_moment_tail_bound _ β hβ).trans
      (div_le_div_of_nonneg_right (hM q t) (Real.sqrt_nonneg β))

/-- Marginal first and second moments converge under the original assumptions. -/
theorem tb13_marginal_moments (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) (t : Bool) :
    Tendsto (fun q => finiteMean (rowOutcomes S t q)) atTop (𝓝 (lawMean H t)) ∧
    Tendsto (fun q => finiteMean (fun i => rowOutcomes S t q i ^ 2)) atTop
      (𝓝 (∫ p, (if t then p.1 else p.2) ^ 2 ∂(H : Measure (ℝ × ℝ)))) := by
  obtain ⟨hq, hlim⟩ := TailB_population_quantile_L2 S H θ ρ h hUI t
  have hm := TailB_population_coordinate_memLp S H θ ρ h hUI t
  have ht := TailB_L2_moments_tendsto _ _
    (fun q => TailB_empirical_quantile_memLp (rowOutcomes S t q)) hq hlim
  have hmeas : Measurable (fun p : ℝ × ℝ => if t then p.1 else p.2) := by
    cases t <;> simp <;> fun_prop
  have hi (f : ℝ → ℝ) (hf : Measurable f) :
      (∫ u, f (Causalean.Stat.quantile (TailB_marginalLaw H t : Measure ℝ) u)
        ∂Causalean.Stat.unifOI) =
      ∫ p, f (if t then p.1 else p.2) ∂(H : Measure (ℝ × ℝ)) := by
    rw [TailB_integral_quantile _ f hf]
    exact integral_map hmeas.aemeasurable hf.aestronglyMeasurable
  have he (q : ℕ) : (∫ u, Causalean.Stat.quantile
      (TailB_empiricalLaw (rowOutcomes S t q) : Measure ℝ) u ∂Causalean.Stat.unifOI) =
      finiteMean (rowOutcomes S t q) :=
    TailB_integral_empirical_quantile _ (fun x => x) measurable_id
  have he2 (q : ℕ) : (∫ u, Causalean.Stat.quantile
      (TailB_empiricalLaw (rowOutcomes S t q) : Measure ℝ) u ^ 2 ∂Causalean.Stat.unifOI) =
      finiteMean (fun i => rowOutcomes S t q i ^ 2) :=
    TailB_integral_empirical_quantile _ (fun x => x^2) (measurable_id.pow_const 2)
  have hl : (∫ u, Causalean.Stat.quantile (TailB_marginalLaw H t : Measure ℝ) u
      ∂Causalean.Stat.unifOI) = lawMean H t := hi (fun x => x) measurable_id
  have hl2 : (∫ u, Causalean.Stat.quantile (TailB_marginalLaw H t : Measure ℝ) u ^ 2
      ∂Causalean.Stat.unifOI) = ∫ p, (if t then p.1 else p.2)^2 ∂(H : Measure (ℝ × ℝ)) :=
    hi (fun x => x^2) (measurable_id.pow_const 2)
  simpa only [he, he2, hl, hl2] using ht


/-- Weak convergence supplies an eventual lower bound for every nonnegative
continuous integrable moment, using bounded continuous truncations. -/
theorem tb13_moment_lower (S : ExperimentSequence) (H : JointLaw)
    (hw : weakPopulationConvergence S H) (f : ℝ × ℝ → ℝ)
    (hc : Continuous f) (hn : ∀ p, 0 ≤ f p)
    (hi : Integrable f (H : Measure (ℝ × ℝ))) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q in atTop, (∫ p, f p ∂(H : Measure (ℝ × ℝ))) - ε <
      finiteMean (fun i : Fin (S.design q).N => f (S.y1 i.val, S.y0 i.val)) := by
  let F (n : ℕ) : BoundedContinuousFunction (ℝ × ℝ) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun p => min (n : ℝ) (f p))
      (continuous_const.min hc) n (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg n) (hn p))]
        exact min_le_left _ _)
  have hlim : Tendsto (fun n => ∫ p, F n p ∂(H : Measure (ℝ × ℝ))) atTop
      (𝓝 (∫ p, f p ∂(H : Measure (ℝ × ℝ)))) := by
    apply tendsto_integral_of_dominated_convergence f
    · intro n; exact (F n).continuous.aestronglyMeasurable
    · exact hi
    · intro n
      exact ae_of_all _ (fun p => by
        change ‖min (n : ℝ) (f p)‖ ≤ f p
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg n) (hn p))]
        exact min_le_right _ _)
    · apply ae_of_all
      intro p
      apply tendsto_const_nhds.congr'
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (f p))] with n hn'
      exact (min_eq_right hn').symm
  obtain ⟨n, hn'⟩ := (hlim.eventually_const_lt
    (show (∫ p, f p ∂(H : Measure (ℝ × ℝ))) - ε / 2 <
      ∫ p, f p ∂(H : Measure (ℝ × ℝ)) by linarith)).exists
  filter_upwards [(hw (F n)).eventually_const_lt
    (show (∫ p, f p ∂(H : Measure (ℝ × ℝ))) - ε <
      ∫ p, F n p ∂(H : Measure (ℝ × ℝ)) by linarith)] with q hq
  exact hq.trans_le (Finset.expect_le_expect (fun i _ => min_le_right _ _))

/-- The joint product moment follows from the two marginal second moments:
truncate the nonnegative squares of the sum and the difference. -/
theorem tb13_product_moment (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) :
    Tendsto (fun q => finiteMean (fun i : Fin (S.design q).N =>
      S.y1 i.val * S.y0 i.val)) atTop
      (𝓝 (∫ p, p.1 * p.2 ∂(H : Measure (ℝ × ℝ)))) := by
  have h1 := TailB_population_coordinate_memLp S H θ ρ h hUI true
  have h0 := TailB_population_coordinate_memLp S H θ ρ h hUI false
  simp only [Bool.false_eq_true, if_true, if_false] at h1 h0
  let K := (∫ p, p.1 ^ 2 ∂(H : Measure (ℝ × ℝ))) +
    ∫ p, p.2 ^ 2 ∂(H : Measure (ℝ × ℝ))
  let C := ∫ p, p.1 * p.2 ∂(H : Measure (ℝ × ℝ))
  have hK := ((tb13_marginal_moments S H θ ρ h hUI true).2).add
    ((tb13_marginal_moments S H θ ρ h hUI false).2)
  have hi (a : ℝ) : (∫ p, (p.1 + a * p.2)^2 ∂(H : Measure (ℝ × ℝ))) =
      (∫ p, p.1^2 ∂(H : Measure (ℝ × ℝ))) +
        a^2 * (∫ p, p.2^2 ∂(H : Measure (ℝ × ℝ))) + 2*a*C := by
    have hp : (fun p : ℝ × ℝ => (p.1 + a*p.2)^2) =
        fun p => p.1^2 + a^2*p.2^2 + (2*a)*(p.1*p.2) := by funext p; ring
    have ia : Integrable (fun p => p.1^2+a^2*p.2^2) (H : Measure (ℝ × ℝ)) :=
      h1.integrable_sq.add (h0.integrable_sq.const_mul (a^2))
    have ic : Integrable (fun p => (2*a)*(p.1*p.2)) (H : Measure (ℝ × ℝ)) :=
      (h1.integrable_mul h0).const_mul (2*a)
    rw [hp, integral_add ia ic, integral_add h1.integrable_sq
      (h0.integrable_sq.const_mul (a^2)), integral_const_mul, integral_const_mul]
  have hf (q : ℕ) (a : ℝ) :
      finiteMean (fun i : Fin (S.design q).N => (S.y1 i.val + a*S.y0 i.val)^2) =
        finiteMean (fun i : Fin (S.design q).N => (S.y1 i.val)^2) +
          a^2*finiteMean (fun i : Fin (S.design q).N => (S.y0 i.val)^2) +
          2*a*finiteMean (fun i : Fin (S.design q).N => S.y1 i.val*S.y0 i.val) := by
    have hp : (fun i : Fin (S.design q).N => (S.y1 i.val + a*S.y0 i.val)^2) =
        fun i => (S.y1 i.val)^2 + a^2*(S.y0 i.val)^2 + (2*a)*(S.y1 i.val*S.y0 i.val) := by
      funext i; ring
    rw [hp]
    simp only [finiteMean, Finset.expect_add_distrib, ← Finset.mul_expect]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hp := tb13_moment_lower S H h.2.2.2.2.2.2.1 (fun p => (p.1+p.2)^2)
    (by fun_prop) (fun p => sq_nonneg _) ((h1.add h0).integrable_sq) ε hε
  have hm := tb13_moment_lower S H h.2.2.2.2.2.2.1 (fun p => (p.1-p.2)^2)
    (by fun_prop) (fun p => sq_nonneg _) ((h1.sub h0).integrable_sq) ε hε
  have hplus : (∫ p, (p.1+p.2)^2 ∂(H : Measure (ℝ × ℝ))) = K+2*C := by
    simpa [K] using hi 1
  have hminus : (∫ p, (p.1-p.2)^2 ∂(H : Measure (ℝ × ℝ))) = K-2*C := by
    simpa [K, sub_eq_add_neg] using hi (-1)
  obtain ⟨q0, hq0⟩ := eventually_atTop.mp
    (hp.and (hm.and ((Metric.tendsto_nhds.mp hK) ε hε)))
  refine ⟨q0, fun q hq => ?_⟩
  obtain ⟨hp, hm, hk⟩ := hq0 q hq
  rw [hplus] at hp
  rw [hminus] at hm
  have hp' := hf q 1
  have hm' := hf q (-1)
  simp only [one_mul, one_pow, mul_one] at hp'
  simp only [neg_one_sq, one_mul, mul_neg_one] at hm'
  have heq : (fun i : Fin (S.design q).N => (S.y1 i.val - S.y0 i.val)^2) =
      fun i => (S.y1 i.val + -1*S.y0 i.val)^2 := by funext i; ring
  rw [heq, hm'] at hm
  rw [hp'] at hp
  simp only [rowOutcomes, Bool.false_eq_true, if_true, if_false, Real.dist_eq, abs_lt] at hk ⊢
  dsimp [K, C] at hp hm ⊢
  constructor <;> linarith [hk.1, hk.2]


/-- The actual paired covariance converges, rather than an extremal coupling. -/
theorem tb13_covariance_limit (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) :
    Tendsto (fun q => finiteCovariance (rowOutcomes S true q) (rowOutcomes S false q))
      atTop (𝓝 (lawCovariance H)) := by
  have hm1 := (tb13_marginal_moments S H θ ρ h hUI true).1
  have hm0 := (tb13_marginal_moments S H θ ρ h hUI false).1
  have h1 := TailB_population_coordinate_memLp S H θ ρ h hUI true
  have h0 := TailB_population_coordinate_memLp S H θ ρ h hUI false
  have hh := (tb13_product_moment S H θ ρ h hUI).sub (hm1.mul hm0)
  have he (q : ℕ) : finiteCovariance (rowOutcomes S true q) (rowOutcomes S false q) =
      finiteMean (fun i : Fin (S.design q).N => S.y1 i.val*S.y0 i.val) -
        finiteMean (rowOutcomes S true q)*finiteMean (rowOutcomes S false q) :=
    SharpBounds.n12_proof _ _
  simpa only [he, TailB_lawCovariance_eq_sub H h1 h0] using hh

/-- N times the actual randomization variance converges to its limiting expression. -/
theorem tb13_true_variance_limit (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) :
    Tendsto (fun q => ((S.design q).N : ℝ) * trueVariance (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q)) atTop
      (𝓝 (limitingTrueVariance H θ ρ)) := by
  have hv (t : Bool) : Tendsto (fun q => finiteVariance (rowOutcomes S t q)) atTop
      (𝓝 (lawVariance H t)) := by
    have hh := (tb13_marginal_moments S H θ ρ h hUI t).2.sub
      ((tb13_marginal_moments S H θ ρ h hUI t).1.pow 2)
    simpa only [← finite_variance_second_moment (NeZero.pos (S.design _).N),
      ← TailB_lawVariance_eq_second H t
        (TailB_population_coordinate_memLp S H θ ρ h hUI t)] using hh
  obtain ⟨hc, ha, hb⟩ := TailB_allocation_limits S H θ ρ h
  have hh := hc.mul (((ha.mul (hv true)).add (hb.mul (hv false))).add
    ((tb13_covariance_limit S H θ ρ h hUI).const_mul 2))
  convert hh using 1
  · funext q
    rw [(sharp_bounds_variance_and_all_couplings (S.design q)
      (rowOutcomes S true q) (rowOutcomes S false q)).2.1]
    dsimp [varianceExpression]
    ring
  · simp only [one_mul]
    rfl

/-- A nonzero linear combination has strictly positive centered square moment
when the joint law is not concentrated on an affine line. -/
theorem tb13_affine_variance_pos (H : JointLaw) (hns : NonsingularLaw H)
    (h1 : MemLp (fun p : ℝ × ℝ => p.1) 2 (H : Measure (ℝ × ℝ)))
    (h0 : MemLp (fun p : ℝ × ℝ => p.2) 2 (H : Measure (ℝ × ℝ)))
    (a b : ℝ) (ha : a ≠ 0 ∨ b ≠ 0) :
    0 < a^2 * lawVariance H true + b^2 * lawVariance H false +
      2*a*b*lawCovariance H := by
  let u : ℝ × ℝ → ℝ := fun p => p.1-lawMean H true
  let v : ℝ × ℝ → ℝ := fun p => p.2-lawMean H false
  have hu : MemLp u 2 (H : Measure (ℝ × ℝ)) := h1.sub (memLp_const _)
  have hv : MemLp v 2 (H : Measure (ℝ × ℝ)) := h0.sub (memLp_const _)
  have hi := ((hu.const_mul a).add (hv.const_mul b)).integrable_sq
  have he : (∫ p, (a*u p+b*v p)^2 ∂(H : Measure (ℝ × ℝ))) =
      a^2 * lawVariance H true + b^2 * lawVariance H false + 2*a*b*lawCovariance H := by
    have hp : (fun p => (a*u p+b*v p)^2) =
        fun p => a^2*(u p)^2+b^2*(v p)^2+(2*a*b)*(u p*v p) := by funext p; ring
    have ia : Integrable (fun p => a^2*(u p)^2+b^2*(v p)^2) (H : Measure (ℝ × ℝ)) :=
      (hu.integrable_sq.const_mul (a^2)).add (hv.integrable_sq.const_mul (b^2))
    have ic : Integrable (fun p => (2*a*b)*(u p*v p)) (H : Measure (ℝ × ℝ)) :=
      (hu.integrable_mul hv).const_mul (2*a*b)
    rw [hp, integral_add ia ic, integral_add (hu.integrable_sq.const_mul (a^2))
      (hv.integrable_sq.const_mul (b^2)), integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  rw [← he]
  have hn : 0 ≤ ∫ p, (a*u p+b*v p)^2 ∂(H : Measure (ℝ × ℝ)) :=
    integral_nonneg (fun p => sq_nonneg _)
  apply lt_of_le_of_ne hn
  intro hz
  have hzero := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg _) hi).mp hz.symm
  apply hns a b (a*lawMean H true+b*lawMean H false) ha
  filter_upwards [hzero] with p hp
  have hp' := sq_eq_zero_iff.mp hp
  dsimp [u,v] at hp'
  linarith

/-- Positive allocation coefficients and nonsingularity give a strictly
positive limiting variance, including the census case θ = 1. -/
theorem tb13_limiting_variance_pos (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S)
    (hns : NonsingularLaw H) : 0 < limitingTrueVariance H θ ρ := by
  let A := (1-θ*ρ)/(θ*ρ)
  let B := (1-θ*(1-ρ))/(θ*(1-ρ))
  have hA : 0 < A := by
    apply div_pos _ (mul_pos h.1 h.2.2.1)
    have hh : θ*ρ < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right h.2.1 h.2.2.1.le)
      (by simpa using h.2.2.2.1)
    linarith
  have hAB : 1 ≤ A*B := (allocation_coefficient_product θ ρ h.1 h.2.1
    h.2.2.1 h.2.2.2.1).2
  have ha := Real.sqrt_pos.mpr hA
  have hs := Real.sq_sqrt hA.le
  have h1 := TailB_population_coordinate_memLp S H θ ρ h hUI true
  have h0 := TailB_population_coordinate_memLp S H θ ρ h hUI false
  have hp := tb13_affine_variance_pos H hns h1 h0 (Real.sqrt A) (1/Real.sqrt A)
    (Or.inl ha.ne')
  have hB : 1/A ≤ B := (div_le_iff₀ hA).mpr (by nlinarith [hAB])
  have hv : 0 ≤ lawVariance H false := integral_nonneg (fun _ => sq_nonneg _)
  have hh : (1/Real.sqrt A)^2 = 1/A := by rw [div_pow, hs]; norm_num
  have hh' : 2*Real.sqrt A*(1/Real.sqrt A) = 2 := by field_simp
  rw [hs, hh, hh'] at hp
  dsimp [limitingTrueVariance]
  change 0 < A*lawVariance H true+B*lawVariance H false+2*lawCovariance H
  nlinarith [mul_nonneg (sub_nonneg.mpr hB) hv]

/-- The finite sharp upper bound remains an upper bound at the limit. -/
theorem tb13_true_le_bound (S : ExperimentSequence) (H : JointLaw) (θ ρ : ℝ)
    (h : Conditions123 S H θ ρ) (hUI : UniformSquareIntegrability S) :
    limitingTrueVariance H θ ρ ≤ limitingBound H θ ρ .H := by
  apply le_of_tendsto_of_tendsto' (tb13_true_variance_limit S H θ ρ h hUI)
    (TailB_population_bound_limits S H θ ρ h hUI .H)
  intro q
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact ((sharp_bounds_variance_and_all_couplings (S.design q)
    (rowOutcomes S true q) (rowOutcomes S false q)).2.2.1 _ _
      (List.Perm.refl _) (List.Perm.refl _)).2.2.2

end
end AronowAudit.P022.Wave1
