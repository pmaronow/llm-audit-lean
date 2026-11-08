import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018a.WH.W2.P.T3_L6

open MeasureTheory ProbabilityTheory

private abbrev expNeg : ℝ → ℝ := fun t => Real.exp (-t)

private abbrev expNegPair : ℝ × ℝ → ℝ := fun uv => expNeg uv.1 + expNeg uv.2

private lemma paretoUnitLaw_probability : IsProbabilityMeasure SAP.P018a.paretoUnitLaw := by
  change IsProbabilityMeasure AronowAudit.P018.paretoUnitLaw
  rw [AronowAudit.P018.Wave1.inverse_gram_pareto_eq]
  exact ProbabilityTheory.isProbabilityMeasure_paretoMeasure (by norm_num) (by norm_num)

private lemma expNeg_memLp :
    MemLp expNeg 2 SAP.P018a.paretoUnitLaw := by
  letI := paretoUnitLaw_probability
  apply MemLp.of_bound (by fun_prop) 2
  filter_upwards [AronowAudit.P018.Wave1.inverse_gram_exp_bound] with t ht
  calc
    ‖expNeg t‖ = Real.exp (-t) := by
      simp [expNeg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 := ht
    _ ≤ 2 := by norm_num

private lemma expNegPair_memLp :
    MemLp expNegPair 2
      (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) := by
  simpa [SAP.P018a.paretoUnitLaw, AronowAudit.P018.paretoUnitLaw,
    expNegPair, expNeg] using AronowAudit.P018.Wave1.inverse_gram_W_lp

private lemma expNegPair_variance_eq :
    variance expNegPair
      (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) =
      2 * variance expNeg SAP.P018a.paretoUnitLaw := by
  letI := paretoUnitLaw_probability
  have hbase := expNeg_memLp
  have hfst : MemLp (fun uv : ℝ × ℝ => expNeg uv.1) 2
      (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) :=
    hbase.comp_fst _
  have hsnd : MemLp (fun uv : ℝ × ℝ => expNeg uv.2) 2
      (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) :=
    hbase.comp_snd _
  have hind : (fun uv : ℝ × ℝ => expNeg uv.1) ⟂ᵢ[
      SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw]
      (fun uv : ℝ × ℝ => expNeg uv.2) := by
    exact indepFun_prod (by fun_prop) (by fun_prop)
  have hfstVar : variance (fun uv : ℝ × ℝ => expNeg uv.1)
      (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) =
      variance expNeg SAP.P018a.paretoUnitLaw := by
    exact (measurePreserving_fst (μ := SAP.P018a.paretoUnitLaw)
      (ν := SAP.P018a.paretoUnitLaw)).variance_fun_comp (by fun_prop)
  have hsndVar : variance (fun uv : ℝ × ℝ => expNeg uv.2)
      (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) =
      variance expNeg SAP.P018a.paretoUnitLaw := by
    exact (measurePreserving_snd (μ := SAP.P018a.paretoUnitLaw)
      (ν := SAP.P018a.paretoUnitLaw)).variance_fun_comp (by fun_prop)
  calc
    variance expNegPair
        (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) =
        variance (fun uv : ℝ × ℝ => expNeg uv.1 + expNeg uv.2)
          (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) := rfl
    _ = variance (fun uv : ℝ × ℝ => expNeg uv.1)
          (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) +
        2 * covariance (fun uv : ℝ × ℝ => expNeg uv.1)
          (fun uv : ℝ × ℝ => expNeg uv.2)
          (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) +
        variance (fun uv : ℝ × ℝ => expNeg uv.2)
          (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) :=
      variance_fun_add hfst hsnd
    _ = 2 * variance expNeg SAP.P018a.paretoUnitLaw := by
      rw [hind.covariance_eq_zero hfst hsnd, hfstVar, hsndVar]
      ring

theorem proof_body : SAP.P018a.WH.W2.T3_L6 := by
  letI := paretoUnitLaw_probability
  have hmat : SAP.P018a.populationGram SAP.P018a.inverseKernel =
      !![1, ∫ uv, expNegPair uv ∂(SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw);
        ∫ uv, expNegPair uv ∂(SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw),
        ∫ uv, (expNegPair uv)^2 ∂(SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SAP.P018a.populationGram, SAP.P018a.meanMat, SAP.P018a.outer,
        SAP.P018a.inverseKernel, expNegPair, expNeg, pow_two]
  have hdet : (SAP.P018a.populationGram SAP.P018a.inverseKernel).det =
      variance expNegPair (SAP.P018a.paretoUnitLaw.prod SAP.P018a.paretoUnitLaw) := by
    rw [hmat, Matrix.det_fin_two]
    rw [variance_eq_sub expNegPair_memLp]
    simpa [pow_two]
  have hsum := expNegPair_variance_eq
  have hidentity : (SAP.P018a.populationGram SAP.P018a.inverseKernel).det =
      2 * variance expNeg SAP.P018a.paretoUnitLaw := hdet.trans hsum
  have hpos : 0 < (SAP.P018a.populationGram SAP.P018a.inverseKernel).det := by
    exact AronowAudit.P018.Wave1.inverse_gram_population_det_pos
  have hvarpos : 0 < variance expNeg SAP.P018a.paretoUnitLaw := by
    rw [hidentity] at hpos
    linarith
  exact ⟨by simpa [expNeg] using hidentity, by simpa [expNeg] using hvarpos⟩

end SAP.P018a.WH.W2.P.T3_L6

theorem SAP.P018a.WH.W2.T3_L6_proof : SAP.P018a.WH.W2.T3_L6 := by
  exact SAP.P018a.WH.W2.P.T3_L6.proof_body
