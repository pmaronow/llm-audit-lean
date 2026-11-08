import SAP.P011b.WH.W2.Finite
import AronowAudit.P011.Wave1.Gap.GLP011B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.WH.W2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

/-- The donor's binary-star regression is full rank, with intercept weights one. -/
theorem star_designW2 (K : ℕ) (hK : 0 < K) :
    (starDesignW2 K)ᵀ * starDesignW2 K =
      Matrix.diagonal (![4*(K : ℝ), 12*(K : ℝ)] : Fin 2 → ℝ) ∧
    ((starDesignW2 K)ᵀ * starDesignW2 K).det ≠ 0 ∧
    (∀ i, olsTheta (starDesignW2 K) 0 i = 1) := by
  let x : Fin (4*K) → ℝ := fun i =>
    (![3, -1, -1, -1] : Fin 4 → ℝ) (localIndex (by decide) i)
  have hsum (f : Fin 4 → ℝ) :
      (∑ i : Fin (4*K), f (localIndex (by decide) i)) = (K : ℝ) * ∑ r, f r :=
    AronowAudit.P011.BlockOLSCompletion.local_sum (by decide : 0 < 4) f
  have hz : (∑ i, x i) = 0 := by
    dsimp [x]
    rw [hsum]
    norm_num [Fin.sum_univ_succ]
  have hzz : (∑ i, (x i)^2) = 12*(K : ℝ) := by
    dsimp [x]
    rw [hsum (fun r => ((![3, -1, -1, -1] : Fin 4 → ℝ) r)^2)]
    norm_num [Fin.sum_univ_succ]
    <;> ring
  dsimp [x] at hz hzz
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hG : (starDesignW2 K)ᵀ * starDesignW2 K =
      Matrix.diagonal (![4*(K : ℝ), 12*(K : ℝ)] : Fin 2 → ℝ) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, starDesignW2, Matrix.diagonal_apply, ← pow_two, hz, hzz]
  have hdet : ((starDesignW2 K)ᵀ * starDesignW2 K).det ≠ 0 := by
    rw [hG, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ, ne_of_gt hK]
  have hinv : ((starDesignW2 K)ᵀ * starDesignW2 K)⁻¹ =
      Matrix.diagonal (![(4*(K : ℝ))⁻¹, (12*(K : ℝ))⁻¹] : Fin 2 → ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [hG]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply,
        Matrix.one_apply, hK0] <;> field_simp <;> ring
  refine ⟨hG, hdet, ?_⟩
  intro i
  unfold olsTheta
  rw [hinv]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ,
    starDesignW2, hK0] <;> field_simp <;> ring

theorem unforced_scalingW2 : Scaling unforcedFamilyW2 1 3 (27/128) 2 :=
  AronowAudit.P011.Wave1.star_scaling false

theorem unforced_validW2 : Valid unforcedFamilyW2 := by
  intro k
  refine ⟨?_, (AronowAudit.P011.Wave1.star_valid false k).2⟩
  intro i j hij
  simp [unforcedFamilyW2, unforcedModelW2, emptyGraph] at hij

theorem unforced_momentsW2 (K : ℕ) (hK : 0 < K) :
    meanVariance (unforcedModelW2 K) = 3/16 ∧
    meanSpread (unforcedModelW2 K) = 3/64 := by
  have hnR : (4*(K : ℝ)) ≠ 0 := by positivity
  have hdiag (i : Fin (4*K)) : covariance (unforcedModelW2 K) i i = 3/16 := by
    have hh : covariance (unforcedModelW2 K) i i =
        ((3/16 : ℝ) • (1 : Matrix (Fin (4*K)) (Fin (4*K)) ℝ) +
          (1/64 : ℝ) • adjacency (starModel false K).G) i i :=
      AronowAudit.P011.Wave1.star_covariance_primary K i i
    simpa [Matrix.one_apply, adjacency, (starModel false K).G.property.2] using hh
  constructor
  · unfold meanVariance
    simp_rw [hdiag]
    simp [hnR]
  · let offset : Fin 4 → ℝ := ![3/8, -1/8, -1/8, -1/8]
    have hd (i : Fin (4*K)) : delta (unforcedModelW2 K) i =
        offset (localIndex (by decide) i) := by
      have hm : expectation (unforcedModelW2 K) (fun y => y i) =
          (![3/4, 1/4, 1/4, 1/4] : Fin 4 → ℝ) (localIndex (by decide) i) :=
        AronowAudit.P011.Wave1.star_mean false K i
      have hb : beta (unforcedModelW2 K) = 3/8 :=
        AronowAudit.P011.Wave1.star_beta false K hK
      change expectation (unforcedModelW2 K) (fun y => 1 * y i) - beta (unforcedModelW2 K) = _
      simp_rw [one_mul]
      rw [hm, hb]
      generalize localIndex (by decide : 0 < 4) i = r
      fin_cases r <;> norm_num [offset]
    unfold meanSpread
    simp_rw [hd]
    have hsum : (∑ i : Fin (4*K), (offset (localIndex (by decide) i))^2) =
        (K : ℝ) * (∑ r, (offset r)^2) :=
      AronowAudit.P011.BlockOLSCompletion.local_sum (K := K) (by decide : 0 < 4)
        (fun r => (offset r)^2)
    rw [hsum]
    norm_num [offset, Fin.sum_univ_succ]
    field_simp
    <;> ring

theorem unforced_emptyW2 (k : ℕ) :
    Compatible (unforcedFamilyW2.model k).R (unforcedFamilyW2.model k).d
      (emptyGraph (unforcedFamilyW2.size k)) ∧
    (∀ y, (unforcedFamilyW2.size k : ℝ) *
      V1 (emptyGraph (unforcedFamilyW2.size k)) (weighted (unforcedFamilyW2.model k) y) =
        sampleVariance (weighted (unforcedFamilyW2.model k) y)) := by
  constructor
  · constructor
    · intro i j hij
      simp [unforcedFamilyW2, unforcedModelW2, emptyGraph] at hij
    · intro i
      simp [degree, emptyGraph]
  · intro y
    have hn : (unforcedFamilyW2.size k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (unforcedFamilyW2.positive k)
    simp only [V1, quadratic, adjacency, emptyGraph, Bool.false_eq_true, ↓reduceIte,
      zero_mul, Finset.sum_const_zero, add_zero, sampleVariance]
    field_simp

theorem unforced_sample_limitW2 : InProbability unforcedFamilyW2
    (fun k y => sampleVariance (weighted (unforcedFamilyW2.model k) y)) (fun _ => 15/64) := by
  have hh := AronowAudit.P011.revised_sample_variance
    (Bridge.toFamily unforcedFamilyW2) 1 3 (27/128) 2 unforced_scalingW2
  change InProbability unforcedFamilyW2
    (fun k y => sampleVariance (weighted (unforcedFamilyW2.model k) y))
    (fun k => meanVariance (unforcedFamilyW2.model k) + meanSpread (unforcedFamilyW2.model k)) at hh
  have he (k : ℕ) : meanVariance (unforcedFamilyW2.model k) +
      meanSpread (unforcedFamilyW2.model k) = 15/64 := by
    change meanVariance (unforcedModelW2 (k+1)) + meanSpread (unforcedModelW2 (k+1)) = _
    rw [(unforced_momentsW2 (k+1) (by omega)).1, (unforced_momentsW2 (k+1) (by omega)).2]
    norm_num
  simpa only [he] using hh

/-- A feasible estimate strictly above the true limit makes every maximum conservative. -/
theorem unforced_max_conservativeW2 : AllRawMaxConservativeW2 unforcedFamilyW2 := by
  intro A hA ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_)
    (unforced_sample_limitW2 ε hε)
  letI : IsProbabilityMeasure (unforcedFamilyW2.model k).law :=
    (unforcedFamilyW2.model k).probability
  apply measureReal_mono (μ := (unforcedFamilyW2.model k).law) ?_ (measure_ne_top _ _)
  intro y hy
  have hdom := (hA k y).2 _ (unforced_emptyW2 k).1
  have hscaled := mul_le_mul_of_nonneg_left hdom
    (Nat.cast_nonneg (unforcedFamilyW2.size k) : (0 : ℝ) ≤ _)
  rw [(unforced_emptyW2 k).2 y] at hscaled
  have ht : scaledTrue unforcedFamilyW2 k = 27/128 :=
    AronowAudit.P011.Wave1.star_scaledTrue false k
  change ε < (unforcedFamilyW2.size k : ℝ) *
    (var (unforcedFamilyW2.model k) (betaHat (unforcedFamilyW2.model k)) -
      V1 (A k y) (weighted (unforcedFamilyW2.model k) y)) at hy
  rw [mul_sub, ← scaledTrue, ht] at hy
  change ε < |sampleVariance (weighted (unforcedFamilyW2.model k) y) - 15/64|
  have ha := neg_le_abs (sampleVariance (weighted (unforcedFamilyW2.model k) y) - 15/64)
  linarith

/-- This witnesses the corrected nonnecessity assertion; it does not refute T16. -/
theorem raw_maximum_witnessW2 : RawMaximumWitnessW2 := by
  have hb (k : ℕ) : meanBias (unforcedFamilyW2.model k) = -3/128 :=
    AronowAudit.P011.Wave1.star_meanBias false (k+1) (by omega)
  refine ⟨unforced_scalingW2, unforced_validW2, ?_, unforced_sample_limitW2,
    selection_existsW2 unforcedFamilyW2 unforced_validW2
      (fun k y B => V1 B (weighted (unforcedFamilyW2.model k) y)),
    unforced_max_conservativeW2, ?_⟩
  · intro k
    have hd := star_designW2 (k+1) (by omega)
    refine ⟨hd.2.1, ?_, ?_, AronowAudit.P011.Wave1.star_scaledTrue false k,
      hb k, (unforced_emptyW2 k).1, (unforced_emptyW2 k).2⟩
    · exact (AronowAudit.P011.block_ols_representations.2 false (k+1) (by omega)).1
    · intro i
      exact (hd.2.2 i).symm
  · simp_rw [hb]
    rw [(tendsto_const_nhds : Tendsto (fun _ : ℕ => (-3/128 : ℝ))
      atTop (𝓝 (-3/128))).liminf_eq]
    norm_num

end
end SAP.P011b.WH.W2
