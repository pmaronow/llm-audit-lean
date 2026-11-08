import SAP.P027b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem SAP.P027b.WH.W1.T14_L1_proof : SAP.P027b.WH.W1.T14_L1 := by
  intro Ξ _ μ _ M hM α ε hε
  let D := strataDesign M (by omega)
  let y := stratumOutcomes α ε
  let N : ℝ := 2 * (M:ℝ)
  change Integrable (fun ξ => variance D (htMean D (y ξ))) μ ∧
    Integrable (fun ξ => expect D (fun ω =>
      htVarianceEstimator D (y ξ) ω / N^2)) μ ∧
    Integrable (fun ξ => expect D (fun ω =>
      c2Estimator D (y ξ) ω / N^2)) μ ∧
    Integrable (fun ξ => expect D (collapsedEstimator (y ξ))) μ ∧
    Integrable (fun ξ => expect D (fun ω => c2Estimator D (y ξ) ω / N^2) -
      variance D (htMean D (y ξ))) μ ∧
    Integrable (fun ξ => expect D (collapsedEstimator (y ξ)) -
      variance D (htMean D (y ξ))) μ
  have hmR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hunit (k : Fin M × Fin 2) : Integrable (fun ξ => y ξ k ^ 2) μ := by
    have h := AronowAudit.P027.shifted_noise_second_moment μ ε 1 hε k
      (stratumMeans α k.2)
    have hs : (stratumMeans α k.2)^2 = α^2 := by
      unfold stratumMeans
      split_ifs <;> ring
    rw [hs] at h
    exact h.1
  have havg (s : Fin 2) :
      Integrable (fun ξ => ((∑ i : Fin M, y ξ (i,s))/(M:ℝ))^2) μ := by
    let es := fun i : Fin M => ε (i,s)
    have heps : NoiseMoments μ es 1 := by
      constructor
      · intro i
        exact hε.1 (i,s)
      · intro i j
        have h := hε.2 (i,s) (j,s)
        by_cases hij : i = j
        · subst j
          simpa [es] using h
        · simpa [es, hij] using h
    let c := fun _ : Fin M => 1/(M:ℝ)
    have hf : (fun ξ => ((∑ i : Fin M, y ξ (i,s))/(M:ℝ))^2) =
        (fun ξ => (stratumMeans α s + ∑ i, c i * es i ξ)^2) := by
      funext ξ
      congr 1
      dsimp [y, stratumOutcomes, c, es]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum]
      field_simp [hmR.ne']
    have h := AronowAudit.P027.noise_linear_moments μ es 1 heps c
      (stratumMeans α s)
    dsimp only at h
    rw [hf]
    exact h.2.2.2.2.1
  have hstr (s : Fin 2) : Integrable (fun ξ => stratumVariance (y ξ) s) μ := by
    have hssq : Integrable (fun ξ => ∑ i : Fin M, y ξ (i,s)^2) μ :=
      integrable_finsetSum _ (fun i _ => hunit (i,s))
    have hmean : Integrable
        (fun ξ => ((∑ i : Fin M, y ξ (i,s))/(M:ℝ))^2) μ := havg s
    have hfirst := hssq.div_const (M:ℝ)
    have hf : (fun ξ => stratumVariance (y ξ) s) =
        (fun ξ => (∑ i : Fin M, y ξ (i,s)^2)/(M:ℝ) -
          ((∑ i : Fin M, y ξ (i,s))/(M:ℝ))^2) := by
      funext ξ
      unfold stratumVariance
      rfl
    rw [hf]
    exact hfirst.sub hmean
  have hVfun : (fun ξ => variance D (htMean D (y ξ))) =
      (fun ξ => (stratumVariance (y ξ) 0 + stratumVariance (y ξ) 1)/4) := by
    funext ξ
    exact (AronowAudit.P027.strata_finite_formulas M hM (y ξ)).2
  have hV : Integrable (fun ξ => variance D (htMean D (y ξ))) μ := by
    rw [hVfun]
    exact ((hstr 0).add (hstr 1)).div_const 4
  have hweighted (ω : Fin M × Fin M) (c : ℝ) :
      Integrable (fun ξ => c * (y ξ (ω.1,0)^2 + y ξ (ω.2,1)^2)) μ :=
    ((hunit (ω.1,0)).add (hunit (ω.2,1))).const_mul c
  have hHpoint (ω : Fin M × Fin M) :
      Integrable (fun ξ => htVarianceEstimator D (y ξ) ω / N^2) μ := by
    have hf : (fun ξ => htVarianceEstimator D (y ξ) ω / N^2) =
        (fun ξ => ((M:ℝ)-1)/(4*M) *
          (y ξ (ω.1,0)^2 + y ξ (ω.2,1)^2)) := by
      funext ξ
      dsimp [N]
      exact ((AronowAudit.P027.strata_finite_formulas M hM (y ξ)).1 ω).2.1
    rw [hf]
    exact hweighted ω _
  have hCpoint (ω : Fin M × Fin M) :
      Integrable (fun ξ => c2Estimator D (y ξ) ω / N^2) μ := by
    have hf : (fun ξ => c2Estimator D (y ξ) ω / N^2) =
        (fun ξ => ((M:ℝ)-1)/(2*M) *
          (y ξ (ω.1,0)^2 + y ξ (ω.2,1)^2)) := by
      funext ξ
      dsimp [N]
      exact ((AronowAudit.P027.strata_finite_formulas M hM (y ξ)).1 ω).2.2
    rw [hf]
    exact hweighted ω _
  have hCSpoint (ω : Fin M × Fin M) :
      Integrable (fun ξ => collapsedEstimator (y ξ) ω) μ := by
    let k₀ : Fin M × Fin 2 := (ω.1,0)
    let k₁ : Fin M × Fin 2 := (ω.2,1)
    let c : (Fin M × Fin 2) → ℝ := fun k =>
      (if k = k₀ then 1 else 0) - (if k = k₁ then 1 else 0)
    have hne : k₀ ≠ k₁ := by
      intro he
      have hs := congrArg Prod.snd he
      exact (by decide : (0:Fin 2) ≠ 1) hs
    have hZ (ξ : Ξ) : (∑ k, c k * ε k ξ) = ε k₀ ξ - ε k₁ ξ := by
      calc
        (∑ k, c k * ε k ξ) =
            (∑ k, (if k = k₀ then 1 else 0) * ε k ξ) -
              (∑ k, (if k = k₁ then 1 else 0) * ε k ξ) := by
          simp only [c, sub_mul, Finset.sum_sub_distrib]
        _ = ε k₀ ξ - ε k₁ ξ := by simp
    have hf : (fun ξ => y ξ k₀ - y ξ k₁) =
        (fun ξ => 2*α + ∑ k, c k * ε k ξ) := by
      funext ξ
      rw [hZ ξ]
      simp [y, stratumOutcomes, stratumMeans, k₀, k₁]
      ring
    have hlin := AronowAudit.P027.noise_linear_moments μ ε 1 hε c (2*α)
    dsimp only at hlin
    have hsquare : Integrable (fun ξ => (y ξ k₀ - y ξ k₁)^2) μ := by
      have hf2 := congrArg (fun f : Ξ → ℝ => fun ξ => f ξ ^ 2) hf
      rw [hf2]
      exact hlin.2.2.2.2.1
    have hc : (fun ξ => collapsedEstimator (y ξ) ω) =
        (fun ξ => (y ξ k₀ - y ξ k₁)^2 / 4) := by
      funext ξ
      simp [collapsedEstimator, k₀, k₁]
    rw [hc]
    exact hsquare.div_const 4
  have hHsample : Integrable (fun ξ => expect D
      (fun ω => htVarianceEstimator D (y ξ) ω / N^2)) μ := by
    unfold expect
    exact integrable_finsetSum _ (fun ω _ => (hHpoint ω).const_mul _)
  have hCsample : Integrable (fun ξ => expect D
      (fun ω => c2Estimator D (y ξ) ω / N^2)) μ := by
    unfold expect
    exact integrable_finsetSum _ (fun ω _ => (hCpoint ω).const_mul _)
  have hCSsample : Integrable (fun ξ => expect D (collapsedEstimator (y ξ))) μ := by
    unfold expect
    exact integrable_finsetSum _ (fun ω _ => (hCSpoint ω).const_mul _)
  refine ⟨hV, hHsample, hCsample, hCSsample, ?_, ?_⟩
  · exact hCsample.sub hV
  · exact hCSsample.sub hV

end
