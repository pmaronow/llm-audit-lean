import SAP.P011a.WH.W2.Helpers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W2

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

theorem residual_failure_finite : ResidualFailureFiniteWhole := by
  have hexp (m : ℕ) (hm : 0 < m) :
      expectation (unstableModel m) (unstableResidualStatistic m) =
        (4*m : ℝ)+2-7/(4*m : ℝ) :=
    AronowAudit.P011.Wave1.rmr_T_expectation m hm
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    refine ⟨(fun _ => rfl), ?_, ?_⟩
    · intro y
      have ho : ols (unstableDesign m) y =
          ![(∑ i, y i)/(4*m : ℝ), (∑ i, unstableW m i*y i)/(2*m : ℝ)] :=
        AronowAudit.P011.Wave1.rmr_ols m hm y
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have hi : ols (unstableDesign m) y 0 = average y := by
        rw [ho]
        simp only [Matrix.cons_val_zero, average, Nat.cast_mul, Nat.cast_ofNat]
      have hs : ols (unstableDesign m) y 1 = (2/(4*m : ℝ))*∑ i, unstableW m i*y i := by
        rw [ho]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        field_simp
        ring
      refine ⟨hi, hs, ?_, ?_⟩
      · rw [hs]
        unfold betaHat average weighted
        change (∑ i, 2*unstableW m i*y i)/((4*m : ℕ) : ℝ) = _
        simp only [mul_assoc, ←Finset.mul_sum, Nat.cast_mul, Nat.cast_ofNat]
        ring
      · have hq (x : Fin (4*m) → ℝ) :
            quadratic (oracleMatrix (emptyGraph (4*m))) x = ∑ i, x i^2 := by
          simp [quadratic, oracleMatrix, adjacency, emptyGraph, Matrix.one_apply, pow_two]
        have hr (i : Fin (4*m)) : fittedResidual (unstableModel m) (unstableDesign m)
            (ols (unstableDesign m)) y i = 2*unstableW m i*
            (y i-average y-unstableW m i*ols (unstableDesign m) y 1) := by
          unfold fittedResidual
          simp only [unstableDesign, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          simp only [Fin.isValue, ite_true, Fin.reduceEq, ite_false, one_mul, hi]
          change 2*unstableW m i*(y i-(average y+unstableW m i*ols (unstableDesign m) y 1)) = _
          ring
        have he (i : Fin (4*m)) (x : ℝ) : (2*unstableW m i*x)^2 =
            if unstableW m i ≠ 0 then 4*x^2 else 0 := by
          unfold unstableW
          generalize localIndex (q := 4) (by decide) i = r
          fin_cases r <;> norm_num <;> ring
        unfold unstableResidualStatistic VResidual
        change (4*m : ℝ)*(quadratic (oracleMatrix (emptyGraph (4*m))) _/_) = _
        rw [hq]
        simp_rw [hr, he]
        rw [Finset.sum_filter]
        have hsum (f : Fin (4*m) → ℝ) :
            (∑ i, if unstableW m i ≠ 0 then 4*f i else 0) =
              4*∑ i, if unstableW m i ≠ 0 then f i else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> ring
        rw [hsum]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        generalize (∑ i, if unstableW m i ≠ 0 then
          (y i-average y-unstableW m i*ols (unstableDesign m) y 1)^2 else 0) = q
        field_simp [hm0]
    · refine ⟨AronowAudit.P011.Wave1.rmr_scaled_variance m hm,
        AronowAudit.P011.Wave1.rmr_beta m, ?_, ?_⟩
      · intro i
        have hm : MeanModel (unstableModel m) (unstableDesign m) 0 :=
          AronowAudit.P011.Wave1.rmr_mean_model m
        simpa only [Matrix.mulVec_zero, Pi.zero_apply] using hm.2 i
      · apply AronowAudit.P011.Wave1.rmr_ae_source m
        intro u i
        change |AronowAudit.P011.weighted (AronowAudit.P011.unstableModel m)
          (AronowAudit.P011.Wave1.rmr_Y m u) i| ≤ 2
        rw [AronowAudit.P011.Wave1.rmr_weighted_source, abs_mul, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2),
          AronowAudit.P011.Wave1.rmr_sign_abs, mul_one]
        nlinarith [(AronowAudit.P011.Wave1.rmr_point m i).2.2.2.2.2.2.2]
  · exact (hexp 1 (by decide)).trans (by norm_num)
  · exact (hexp 2 (by decide)).trans (by norm_num)

theorem path_sharp_bound (t : ℝ) (ht : t=1 ∨ t=2) (K : ℕ) :
    ∀ᵐ y ∂(pathModel t K).law, ∀ i, |y i| ≤ 27/5 := by
  let f : (Fin K → Fin 2 → Bool) → (Fin (3*K) → ℝ) := fun u i =>
    pathBlock t (sign (u (blockIndex (by decide) i) 0))
      (sign (u (blockIndex (by decide) i) 1)) (localIndex (by decide) i)
  have hl : (pathModel t K).law = uniformLaw f := rfl
  rw [hl]
  rw [uniformLaw, ←PMF.toMeasure_map _ _
    (measurable_of_finite f)]
  have hset : MeasurableSet {y : Fin (3*K) → ℝ | ∀ i, |y i| ≤ 27/5} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  apply (ae_map_iff
    (measurable_of_finite f).aemeasurable hset).mpr
  filter_upwards [] with u
  intro i
  have hb (u v : Bool) (r : Fin 3) : |pathBlock t (sign u) (sign v) r| ≤ 27/5 := by
    rcases ht with rfl | rfl <;> cases u <;> cases v <;> fin_cases r <;>
      norm_num [pathBlock,sign]
  exact hb _ _ _

theorem path_finite_whole : PathFiniteWhole := by
  refine ⟨?_, ?_⟩
  · intro t ht K hK
    refine ⟨path_sharp_bound t ht K, ?_, ?_, ?_⟩
    · intro i
      have hm : expectation (pathModel t K) (fun y => weighted (pathModel t K) y i) =
          (![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) i) :=
        AronowAudit.P011.Wave1.path_ce_mean t K i
      simpa only [weighted, pathModel, one_mul] using hm
    · intro i j
      have hc := congrFun (congrFun (AronowAudit.P011.Wave1.path_ce_covariance t K) i) j
      exact hc
    · intro y
      have h := AronowAudit.P011.Wave1.PropositionOne.n8_proof
        AronowAudit.P011.Wave1.PropositionOne.n2_proof K hK y
      have h2 := (AronowAudit.P011.Wave1.PropositionOne.n2_proof K).1 y
      change (∑ i, y i) = (∑ b, pathS (pathBlockVector K y b)) ∧
        quadratic (oracleMatrix (pathModel t K).G) y =
          (∑ b, pathQ (pathBlockVector K y b)) ∧
        (∑ i, ∑ j, oracleMatrix (pathModel t K).G i j*y j) =
          ∑ b, pathL (pathBlockVector K y b) at h2
      change ((3*K : ℕ) : ℝ)*V1 (pathModel t K).G y =
        (quadratic (oracleMatrix (pathModel t K).G) y/(K : ℝ) -
          2*average y*((∑ i, ∑ j, oracleMatrix (pathModel t K).G i j*y j)/(K : ℝ)) +
          7*(average y)^2)/3 at h
      simp only [Nat.cast_mul, Nat.cast_ofNat] at h
      rw [h, h2.2.1, h2.2.2]
      have hK0 : (K : ℝ) ≠ 0 := by positivity
      generalize (∑ b, pathQ (pathBlockVector K y b)) = q
      generalize (∑ b, pathL (pathBlockVector K y b)) = l
      field_simp [hK0]
  · intro t u v
    cases u <;> cases v <;>
      norm_num [pathS, pathL, pathQ, quadratic, oracleMatrix, adjacency, pathGraph,
        pathBlock, sign, Fin.sum_univ_succ, Matrix.one_apply] <;>
      (repeat' constructor) <;> ring

end
end SAP.P011a.WH.W2
