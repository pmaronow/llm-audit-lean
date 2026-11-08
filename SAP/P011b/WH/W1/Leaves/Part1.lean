import SAP.P011b.Defs.WholeW1
import SAP.P011b.Bridge
import AronowAudit.P011.Wave1.Gap.GP011B1
import AronowAudit.P011.Wave1.Gap.GLP011B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

/-- The finite design calculations use the existing block-sum donor and a diagonal inverse. -/
theorem star_design_facts : W1StarDesignFacts := by
  intro u K hK
  let s : ℝ := if u then 2*(K : ℝ) else 12*(K : ℝ)
  have hsum (f : Fin 4 → ℝ) :
      (∑ i : Fin (4*K), f (localIndex (by decide) i)) = (K : ℝ) * ∑ r, f r :=
    AronowAudit.P011.BlockOLSCompletion.local_sum (by decide : 0 < 4) f
  have hz : (∑ i : Fin (4*K), w1StarX u (localIndex (by decide) i)) = 0 := by
    rw [hsum]
    cases u <;> norm_num [w1StarX, Fin.sum_univ_succ]
  have hzz : (∑ i : Fin (4*K), (w1StarX u (localIndex (by decide) i))^2) = s := by
    rw [hsum (fun r => (w1StarX u r)^2)]
    cases u <;> norm_num [w1StarX, s, Fin.sum_univ_succ] <;> ring
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hn : (4*(K : ℝ)) ≠ 0 := by positivity
  have hs : s ≠ 0 := by dsimp [s]; cases u <;> positivity
  have hG : (w1StarD u K)ᵀ * w1StarD u K = Matrix.diagonal (![4*(K : ℝ), s]) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, w1StarD, Matrix.diagonal_apply, ←pow_two, hz, hzz]
  have hdet : ((w1StarD u K)ᵀ * w1StarD u K).det ≠ 0 := by
    rw [hG, Matrix.det_diagonal]
    simpa [Fin.prod_univ_succ] using mul_ne_zero hn hs
  have hinv : ((w1StarD u K)ᵀ * w1StarD u K)⁻¹ =
      Matrix.diagonal (![(4*(K : ℝ))⁻¹, s⁻¹]) := by
    apply Matrix.inv_eq_left_inv
    rw [hG]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.one_apply, hn, hs, hK0] <;> field_simp
  refine ⟨hz, hG, hdet, ?_, ?_⟩
  · intro i
    unfold olsTheta
    rw [hinv]
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ, w1StarD,
      starModel, hn, hK0, mul_comm] <;> field_simp
  · intro y
    have hOLS := (AronowAudit.P011.block_ols_representations.2 u K hK).2 y
    change ols (w1StarD u K) y 0 = average y at hOLS
    change average (fun i => 1*y i) = _
    simpa only [one_mul] using hOLS.symm

/-- The old counterexample package uses only proved donor theorems. -/
theorem star_existing : T15Statement := by
  refine ⟨Bridge.starCore_correspondence.mpr AronowAudit.P011.Wave1.star_counterexample_proof,
    Bridge.starRegression_correspondence.mpr AronowAudit.P011.block_ols_representations.2,
    Bridge.starRelaxation_correspondence.mpr AronowAudit.P011.star_relaxation_singleton,
    Bridge.starExtraFacts_correspondence.mpr
      ⟨fun u k => AronowAudit.P011.Wave1.star_binary u (k+1),
       fun u k A => AronowAudit.P011.Wave1.star_compatible u (k+1) A⟩,
    AronowAudit.P011.star_mean_terms.1, AronowAudit.P011.star_mean_terms.2, ?_⟩
  norm_num

/-- Subtracting the known target intercept from the block means gives both offset vectors. -/
theorem star_offsets (u : Bool) (K : ℕ) (hK : 0 < K) :
    (∀ i, expectation (starModel u K) (fun y => y i) =
      w1StarMu u (localIndex (by decide) i)) ∧
    (∀ i, delta (starModel u K) i = w1StarOffset u (localIndex (by decide) i)) := by
  have hm (i : Fin (4*K)) : expectation (starModel u K) (fun y => y i) =
      w1StarMu u (localIndex (by decide) i) := AronowAudit.P011.Wave1.star_mean u K i
  have hb : beta (starModel u K) = if u then 1/2 else 3/8 :=
    AronowAudit.P011.Wave1.star_beta u K hK
  refine ⟨hm, ?_⟩
  intro i
  change expectation (starModel u K) (fun y => 1*y i) - beta (starModel u K) = _
  simp_rw [one_mul]
  rw [hm, hb]
  generalize localIndex (by decide : 0 < 4) i = r
  cases u <;> fin_cases r <;>
    norm_num [w1StarMu, w1StarOffset]

/-- Removing recruitment constraints leaves every Scaling component unchanged. -/
theorem unforced_scaling : Scaling w1UnforcedFamily 1 3 (27/128) 2 :=
  AronowAudit.P011.Wave1.star_scaling false

theorem unforced_valid : Valid w1UnforcedFamily := by
  intro k
  refine ⟨?_, ?_⟩
  · intro i j hij
    simp [w1UnforcedFamily, w1UnforcedModel, emptyGraph] at hij
  · exact (AronowAudit.P011.Wave1.star_valid false k).2

/-- Exact marginal variance and mean spread for the intercept counterexample. -/
theorem unforced_moments (K : ℕ) (hK : 0 < K) :
    meanVariance (w1UnforcedModel K) = 3/16 ∧ meanSpread (w1UnforcedModel K) = 3/64 := by
  have hn : (4*K : ℕ) ≠ 0 := by omega
  have hnR : (4*(K : ℝ)) ≠ 0 := by positivity
  have hdiag (i : Fin (4*K)) : covariance (w1UnforcedModel K) i i = 3/16 := by
    have hh : covariance (w1UnforcedModel K) i i =
        ((3/16 : ℝ) • (1 : Matrix (Fin (4*K)) (Fin (4*K)) ℝ) +
          (1/64 : ℝ) • adjacency (starModel false K).G) i i :=
      AronowAudit.P011.Wave1.star_covariance_primary K i i
    simpa [Matrix.one_apply, adjacency, (starModel false K).G.property.2] using hh
  constructor
  · unfold meanVariance
    simp_rw [hdiag]
    simp [hnR]
  · have hd (i : Fin (4*K)) : delta (w1UnforcedModel K) i =
        w1StarOffset false (localIndex (by decide) i) := (star_offsets false K hK).2 i
    unfold meanSpread
    simp_rw [hd]
    have hsum : (∑ i : Fin (4*K), (w1StarOffset false (localIndex (by decide) i))^2) =
        (K : ℝ)*(∑ r, (w1StarOffset false r)^2) :=
      AronowAudit.P011.BlockOLSCompletion.local_sum (K := K) (by decide : 0 < 4)
        (fun r => (w1StarOffset false r)^2)
    rw [hsum]
    norm_num [w1StarOffset, Fin.sum_univ_succ]
    field_simp
    <;> ring

/-- A feasible empty graph has scaled raw estimate equal to the sample variance. -/
theorem unforced_empty (k : ℕ) :
    Compatible (w1UnforcedFamily.model k).R (w1UnforcedFamily.model k).d
      (emptyGraph (w1UnforcedFamily.size k)) ∧
    (∀ y, (w1UnforcedFamily.size k : ℝ)*
      V1 (emptyGraph (w1UnforcedFamily.size k)) (weighted (w1UnforcedFamily.model k) y) =
        sampleVariance (weighted (w1UnforcedFamily.model k) y)) := by
  constructor
  · constructor
    · intro i j hij
      simp [w1UnforcedFamily, w1UnforcedModel, emptyGraph] at hij
    · intro i
      simp [degree, emptyGraph]
  · intro y
    have hn : (w1UnforcedFamily.size k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (w1UnforcedFamily.positive k)
    simp only [V1, quadratic, adjacency, emptyGraph, Bool.false_eq_true, ↓reduceIte,
      zero_mul, Finset.sum_const_zero, add_zero, sampleVariance]
    field_simp

/-- The existing sample-variance theorem gives a limit strictly above the true variance. -/
theorem unforced_sample_limit : InProbability w1UnforcedFamily
    (fun k y => sampleVariance (weighted (w1UnforcedFamily.model k) y)) (fun _ => 15/64) := by
  have hh := AronowAudit.P011.revised_sample_variance
    (Bridge.toFamily w1UnforcedFamily) 1 3 (27/128) 2 unforced_scaling
  change InProbability w1UnforcedFamily
    (fun k y => sampleVariance (weighted (w1UnforcedFamily.model k) y))
    (fun k => meanVariance (w1UnforcedFamily.model k) + meanSpread (w1UnforcedFamily.model k)) at hh
  have he (k : ℕ) : meanVariance (w1UnforcedFamily.model k) +
      meanSpread (w1UnforcedFamily.model k) = 15/64 := by
    change meanVariance (w1UnforcedModel (k+1)) + meanSpread (w1UnforcedModel (k+1)) = _
    rw [(unforced_moments (k+1) (by omega)).1, (unforced_moments (k+1) (by omega)).2]
    norm_num
  simpa only [he] using hh

/-- Maximization dominates the feasible empty graph. The fixed positive gap makes
an underestimation event a subset of a sample-variance deviation event. -/
theorem unforced_max_conservative
    (A : ∀ k, (Fin (w1UnforcedFamily.size k) → ℝ) → Graph (w1UnforcedFamily.size k))
    (hA : ∀ k y, Maximizes (w1UnforcedFamily.model k).R (w1UnforcedFamily.model k).d
      (fun B => V1 B (weighted (w1UnforcedFamily.model k) y)) (A k y)) :
    Conservative w1UnforcedFamily
      (fun k y => V1 (A k y) (weighted (w1UnforcedFamily.model k) y)) := by
  intro ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_)
    (unforced_sample_limit ε hε)
  letI : IsProbabilityMeasure (w1UnforcedFamily.model k).law :=
    (w1UnforcedFamily.model k).probability
  apply measureReal_mono (μ := (w1UnforcedFamily.model k).law) ?_ (measure_ne_top _ _)
  intro y hy
  have hdom := (hA k y).2 _ (unforced_empty k).1
  have hscaled := mul_le_mul_of_nonneg_left hdom
    (Nat.cast_nonneg (w1UnforcedFamily.size k) : (0 : ℝ) ≤ _)
  rw [(unforced_empty k).2 y] at hscaled
  have ht : scaledTrue w1UnforcedFamily k = 27/128 :=
    AronowAudit.P011.Wave1.star_scaledTrue false k
  change ε < (w1UnforcedFamily.size k : ℝ)*
    (var (w1UnforcedFamily.model k) (betaHat (w1UnforcedFamily.model k)) -
      V1 (A k y) (weighted (w1UnforcedFamily.model k) y)) at hy
  rw [mul_sub, ←scaledTrue, ht] at hy
  change ε < |sampleVariance (weighted (w1UnforcedFamily.model k) y) - 15/64|
  have ha := neg_le_abs (sampleVariance (weighted (w1UnforcedFamily.model k) y) - 15/64)
  linarith

/-- Correlation algebra and the existing degree bound give the factor ratio and bounds. -/
theorem auxiliary_factor_facts (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hs : ∀ k, Homoskedastic (F.model k))
    (hp : ∀ k, 0 < meanVariance (F.model k)) (k : ℕ) :
    w1CorrelationFactor (F.model k) = scaledTrue F k / meanVariance (F.model k) ∧
    0 ≤ w1CorrelationFactor (F.model k) ∧ w1CorrelationFactor (F.model k) ≤ 1+c2 := by
  have hScaling := h
  rcases h with ⟨_, _, _, _, _, hdep, hbound, _, _, _⟩
  have hL2 := AronowAudit.P011.ProbabilityCompletion.weighted_memLp
    (Bridge.toModel (F.model k)) c1 (hbound k)
  have hc := AronowAudit.P011.pairwise_correlation_repair (F.positive k)
    (Bridge.toModel (F.model k)) (hdep k) (hs k) hL2
  have hid : scaledTrue F k = meanVariance (F.model k)*w1CorrelationFactor (F.model k) := hc.1
  have hrho (i j : Fin (F.size k)) : rho (F.model k) i j ≤ 1 := hc.2.1 i j
  have hn : (0 : ℝ) < F.size k := by exact_mod_cast F.positive k
  have hv : 0 ≤ scaledTrue F k :=
    mul_nonneg hn.le (integral_nonneg (fun y => sq_nonneg _))
  have hlo : 0 ≤ w1CorrelationFactor (F.model k) := by
    rw [hid] at hv
    exact (mul_nonneg_iff_of_pos_left (hp k)).mp hv
  have ha (i j : Fin (F.size k)) : 0 ≤ adjacency (F.model k).G i j := by
    unfold adjacency
    split_ifs <;> norm_num
  have hsum : (∑ i, ∑ j, adjacency (F.model k).G i j*rho (F.model k) i j) ≤
      ∑ i, ∑ j, adjacency (F.model k).G i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hrho i j) (ha i j)
  have hgb : 1+(∑ i, ∑ j, adjacency (F.model k).G i j)/(F.size k : ℝ) ≤ 1+c2 :=
    (AronowAudit.P011.printed_auxiliary_degree_bound (Bridge.toFamily F)
      c1 c2 c3 c4 hScaling k).2
  refine ⟨?_, hlo, ?_⟩
  · apply (eq_div_iff (ne_of_gt (hp k))).mpr
    linarith [hid]
  · unfold w1CorrelationFactor
    linarith [div_le_div_of_nonneg_right hsum hn.le]

/-- A deterministic squeeze using n/(n+1) ≤ t_n ≤ 1. -/
theorem alternating_weight_limit :
    Tendsto (fun k => w1AlternatingWeight (k+1)) atTop (𝓝 1) := by
  have hN : Tendsto (fun k : ℕ => (k+1 : ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (show Tendsto (fun k : ℕ => k+1+1) atTop atTop from
          tendsto_atTop_mono (fun k => by change k ≤ k+1+1; omega) tendsto_id))
  have hlow : Tendsto (fun k : ℕ => (k+1 : ℝ)/((k+1 : ℝ)+1)) atTop (𝓝 1) := by
    have he : (fun k : ℕ => (k+1 : ℝ)/((k+1 : ℝ)+1)) =
        (fun k : ℕ => 1-1/((k+1 : ℝ)+1)) := by
      funext k
      have hden : (k+1 : ℝ)+1 ≠ 0 := by positivity
      field_simp
      <;> ring
    rw [he]
    simpa using tendsto_const_nhds.sub (hN.const_div_atTop 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun k => by simpa only [Nat.cast_add, Nat.cast_one, w1AlternatingWeight,
      AronowAudit.P011.alternatingWeight] using
      (AronowAudit.P011.Wave1.afm_weight_bounds (k+1) (by omega)).2.2)
    (fun k => (AronowAudit.P011.Wave1.afm_weight_bounds (k+1) (by omega)).2.1)

/-- The alternating-mean witness has positive common variance and mean spread tending to one. -/
theorem alternating_details :
    (∀ k, Homoskedastic (w1AlternatingFamily.model k) ∧
      0 < meanVariance (w1AlternatingFamily.model k) ∧
      meanVariance (w1AlternatingFamily.model k) = w1AlternatingWeight (k+1)^2 ∧
      beta (w1AlternatingFamily.model k) = 1) ∧
    Tendsto (fun k => meanSpread (w1AlternatingFamily.model k)) atTop (𝓝 1) := by
  constructor
  · intro k
    have hm : meanVariance (w1AlternatingFamily.model k) = w1AlternatingWeight (k+1)^2 :=
      AronowAudit.P011.Wave1.afm_meanVariance (k+1) (by omega)
    have hb : (1/2 : ℝ) ≤ w1AlternatingWeight (k+1) :=
      (AronowAudit.P011.Wave1.afm_weight_bounds (k+1) (by omega)).1
    refine ⟨(AronowAudit.P011.Wave1.alternating_counterexample_proof.2.2.1 k).1,
      ?_, hm, AronowAudit.P011.Wave1.afm_beta (k+1) (by omega)⟩
    rw [hm]
    have ht : 0 < w1AlternatingWeight (k+1) := by linarith
    positivity
  · have he (k : ℕ) : meanSpread (w1AlternatingFamily.model k) =
        2*w1AlternatingWeight (k+1)-1 := AronowAudit.P011.Wave1.afm_spread (k+1) (by omega)
    simp_rw [he]
    convert (tendsto_const_nhds.mul alternating_weight_limit).sub tendsto_const_nhds using 1
    <;> norm_num

end
end SAP.P011b.WH.W1
