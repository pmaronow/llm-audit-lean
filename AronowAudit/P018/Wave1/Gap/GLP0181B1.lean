import AronowAudit.P018.Wave1.Gap.GP0182B2b
import Mathlib.Probability.CramerWold

/-!
P018-T1: the nonlinear uniform counterexample, with the actual uniform law.
-/
noncomputable section
namespace AronowAudit.P018.Wave1
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

private instance nonlinear_witness_unit_probability : IsProbabilityMeasure nonlinearKernel.μ :=
  nonlinear_model_assumptions.1

private instance nonlinear_witness_sample_probability (N : ℕ) :
    IsProbabilityMeasure (unitSampleLaw nonlinearKernel N) := by
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => uniformUnitLaw))
  infer_instance

private lemma nonlinear_witness_mu : nonlinearKernel.μ = uniformUnitLaw := rfl

private lemma nonlinear_witness_residual (z t : ℝ) :
    populationResidual nonlinearKernel z t = (z+t)^2 - 2/3 := by
  rw [populationResidual, nonlinear_population_projection.2.2.2]
  simp [nonlinearKernel, dot, Fin.sum_univ_succ]

private lemma nonlinear_witness_score (z t : ℝ) :
    populationScore nonlinearKernel z t =
      ![(z+t)^2-2/3, (2+z+t)*((z+t)^2-2/3)] := by
  rw [populationScore, nonlinear_witness_residual]
  ext a
  fin_cases a <;> simp [nonlinearKernel, score] <;> ring

private lemma nonlinear_witness_unit_polynomial {m : ℕ} (c : Fin m → ℝ) (a : Fin m → ℕ) :
    (∫ z, ∑ i, c i * z^(a i) ∂uniformUnitLaw) =
      ∑ i, c i * ((1-(-1 : ℝ)^(a i+1))/(2*(a i+1 : ℝ))) := by
  rw [integral_finsetSum univ (fun i _ =>
    ((uniform_unit_power_L2 (a i)).integrable one_le_two).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, uniform_unit_moment]

private lemma nonlinear_witness_H0 :
    (∫ uv : ℝ × ℝ, (2+uv.1+uv.2)^0 * ((uv.1+uv.2)^2-2/3)^2 ∂uniformUnitLaw.prod uniformUnitLaw) = 28/45 := by
  have h := uniform_polynomial_integral (![4/9,-4/3,1,-8/3,4,-4/3,6,4,1] : Fin 9 → ℝ)
    (![0,0,0,1,1,2,2,3,4] : Fin 9 → ℕ) (![0,2,4,1,3,0,2,1,0] : Fin 9 → ℕ)
  have he : (fun uv : ℝ × ℝ => ∑ i : Fin 9,
      (![4/9,-4/3,1,-8/3,4,-4/3,6,4,1] : Fin 9 → ℝ) i *
        (uv.1^((![0,0,0,1,1,2,2,3,4] : Fin 9 → ℕ) i) * uv.2^((![0,2,4,1,3,0,2,1,0] : Fin 9 → ℕ) i))) =
      fun uv => (2+uv.1+uv.2)^0 * ((uv.1+uv.2)^2-2/3)^2 := by
    funext uv
    simp [Fin.sum_univ_succ]
    <;> ring
  rw [he] at h
  norm_num [Fin.sum_univ_succ] at h
  simpa using h

private lemma nonlinear_witness_H1 :
    (∫ uv : ℝ × ℝ, (2+uv.1+uv.2)^1 * ((uv.1+uv.2)^2-2/3)^2 ∂uniformUnitLaw.prod uniformUnitLaw) = 56/45 := by
  have h := uniform_polynomial_integral (![8/9,4/9,-8/3,-4/3,2,1,4/9,-16/3,-4,8,5,-8/3,-4,12,10,-4/3,8,10,2,5,1] : Fin 21 → ℝ)
    (![0,0,0,0,0,0,1,1,1,1,1,2,2,2,2,3,3,3,4,4,5] : Fin 21 → ℕ) (![0,1,2,3,4,5,0,1,2,3,4,0,1,2,3,0,1,2,0,1,0] : Fin 21 → ℕ)
  have he : (fun uv : ℝ × ℝ => ∑ i : Fin 21,
      (![8/9,4/9,-8/3,-4/3,2,1,4/9,-16/3,-4,8,5,-8/3,-4,12,10,-4/3,8,10,2,5,1] : Fin 21 → ℝ) i *
        (uv.1^((![0,0,0,0,0,0,1,1,1,1,1,2,2,2,2,3,3,3,4,4,5] : Fin 21 → ℕ) i) * uv.2^((![0,1,2,3,4,5,0,1,2,3,4,0,1,2,3,0,1,2,0,1,0] : Fin 21 → ℕ) i))) =
      fun uv => (2+uv.1+uv.2)^1 * ((uv.1+uv.2)^2-2/3)^2 := by
    funext uv
    simp [Fin.sum_univ_succ]
    <;> ring
  rw [he] at h
  norm_num [Fin.sum_univ_succ] at h
  simpa using h

private lemma nonlinear_witness_H2 :
    (∫ uv : ℝ × ℝ, (2+uv.1+uv.2)^2 * ((uv.1+uv.2)^2-2/3)^2 ∂uniformUnitLaw.prod uniformUnitLaw) = 3448/945 := by
  have h := uniform_polynomial_integral (![16/9,16/9,-44/9,-16/3,8/3,4,1,16/9,-88/9,-16,32/3,20,6,-44/9,-16,16,40,15,-16/3,32/3,40,20,8/3,20,15,4,6,1] : Fin 28 → ℝ)
    (![0,0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,3,3,3,3,4,4,4,5,5,6] : Fin 28 → ℕ) (![0,1,2,3,4,5,6,0,1,2,3,4,5,0,1,2,3,4,0,1,2,3,0,1,2,0,1,0] : Fin 28 → ℕ)
  have he : (fun uv : ℝ × ℝ => ∑ i : Fin 28,
      (![16/9,16/9,-44/9,-16/3,8/3,4,1,16/9,-88/9,-16,32/3,20,6,-44/9,-16,16,40,15,-16/3,32/3,40,20,8/3,20,15,4,6,1] : Fin 28 → ℝ) i *
        (uv.1^((![0,0,0,0,0,0,0,1,1,1,1,1,1,2,2,2,2,2,3,3,3,3,4,4,4,5,5,6] : Fin 28 → ℕ) i) * uv.2^((![0,1,2,3,4,5,6,0,1,2,3,4,5,0,1,2,3,4,0,1,2,3,0,1,2,0,1,0] : Fin 28 → ℕ) i))) =
      fun uv => (2+uv.1+uv.2)^2 * ((uv.1+uv.2)^2-2/3)^2 := by
    funext uv
    simp [Fin.sum_univ_succ]
    <;> ring
  rw [he] at h
  norm_num [Fin.sum_univ_succ] at h
  simpa using h

private lemma nonlinear_witness_scoreH : scoreH nonlinearKernel = nonlinearH := by
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [scoreH, meanMat, nonlinear_witness_mu, nonlinear_witness_score, outer, nonlinearH, pow_two]
      using nonlinear_witness_H0
  · simpa [scoreH, meanMat, nonlinear_witness_mu, nonlinear_witness_score, outer, nonlinearH,
      pow_two, mul_left_comm, mul_assoc, mul_comm] using nonlinear_witness_H1
  · simpa [scoreH, meanMat, nonlinear_witness_mu, nonlinear_witness_score, outer, nonlinearH,
      pow_two, mul_left_comm, mul_assoc, mul_comm] using nonlinear_witness_H1
  · simpa [scoreH, meanMat, nonlinear_witness_mu, nonlinear_witness_score, outer, nonlinearH,
      pow_two, mul_left_comm, mul_assoc, mul_comm] using nonlinear_witness_H2

private lemma nonlinear_witness_projection (z : ℝ) :
    projection nonlinearKernel z = ![z^2-1/3, 2*(z^2-1/3)+z^3+z/3] := by
  have h0 := nonlinear_witness_unit_polynomial
    (![z^2-2/3,2*z,1] : Fin 3 → ℝ) (![0,1,2] : Fin 3 → ℕ)
  have he0 : (fun t : ℝ => ∑ i : Fin 3,
      (![z^2-2/3,2*z,1] : Fin 3 → ℝ) i * t^((![0,1,2] : Fin 3 → ℕ) i)) =
      fun t => (z+t)^2-2/3 := by
    funext t
    simp [Fin.sum_univ_succ]
    <;> ring
  rw [he0] at h0
  norm_num [Fin.sum_univ_succ] at h0
  have h1 := nonlinear_witness_unit_polynomial
    (![(2+z)*(z^2-2/3), (2+z)*2*z+z^2-2/3, 2+3*z, 1] : Fin 4 → ℝ)
    (![0,1,2,3] : Fin 4 → ℕ)
  have he1 : (fun t : ℝ => ∑ i : Fin 4,
      (![(2+z)*(z^2-2/3), (2+z)*2*z+z^2-2/3, 2+3*z, 1] : Fin 4 → ℝ) i *
        t^((![0,1,2,3] : Fin 4 → ℕ) i)) =
      fun t => (2+z+t)*((z+t)^2-2/3) := by
    funext t
    simp [Fin.sum_univ_succ]
    <;> ring
  rw [he1] at h1
  norm_num [Fin.sum_univ_succ] at h1
  ext a
  fin_cases a
  · change (∫ t, populationScore nonlinearKernel z t 0 ∂uniformUnitLaw) = _
    simp only [nonlinear_witness_score, Matrix.cons_val_zero]
    rw [h0]
    norm_num
    <;> ring
  · change (∫ t, populationScore nonlinearKernel z t 1 ∂uniformUnitLaw) = _
    simp only [nonlinear_witness_score, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [h1]
    norm_num
    <;> ring

private lemma nonlinear_witness_G0 :
    (∫ z, (z^2-1/3) * (z^2-1/3) ∂uniformUnitLaw) = 4/45 := by
  have h := nonlinear_witness_unit_polynomial (![1/9,-2/3,1] : Fin 3 → ℝ)
    (![0,2,4] : Fin 3 → ℕ)
  have he : (fun z : ℝ => ∑ i : Fin 3, (![1/9,-2/3,1] : Fin 3 → ℝ) i *
      z^((![0,2,4] : Fin 3 → ℕ) i)) = fun z => (z^2-1/3) * (z^2-1/3) := by
    funext z
    simp [Fin.sum_univ_succ]
    <;> ring
  rw [he] at h
  norm_num [Fin.sum_univ_succ] at h
  simpa using h

private lemma nonlinear_witness_G1 :
    (∫ z, (z^2-1/3) * (2*(z^2-1/3)+z^3+z/3) ∂uniformUnitLaw) = 8/45 := by
  have h := nonlinear_witness_unit_polynomial (![2/9,-1/9,-4/3,2,1] : Fin 5 → ℝ)
    (![0,1,2,4,5] : Fin 5 → ℕ)
  have he : (fun z : ℝ => ∑ i : Fin 5, (![2/9,-1/9,-4/3,2,1] : Fin 5 → ℝ) i *
      z^((![0,1,2,4,5] : Fin 5 → ℕ) i)) = fun z => (z^2-1/3) * (2*(z^2-1/3)+z^3+z/3) := by
    funext z
    simp [Fin.sum_univ_succ]
    <;> ring
  rw [he] at h
  norm_num [Fin.sum_univ_succ] at h
  simpa using h

private lemma nonlinear_witness_G2 :
    (∫ z, (2*(z^2-1/3)+z^3+z/3) * (2*(z^2-1/3)+z^3+z/3) ∂uniformUnitLaw) = 632/945 := by
  have h := nonlinear_witness_unit_polynomial (![4/9,-4/9,-23/9,14/3,4,1] : Fin 6 → ℝ)
    (![0,1,2,4,5,6] : Fin 6 → ℕ)
  have he : (fun z : ℝ => ∑ i : Fin 6, (![4/9,-4/9,-23/9,14/3,4,1] : Fin 6 → ℝ) i *
      z^((![0,1,2,4,5,6] : Fin 6 → ℕ) i)) = fun z => (2*(z^2-1/3)+z^3+z/3) * (2*(z^2-1/3)+z^3+z/3) := by
    funext z
    simp [Fin.sum_univ_succ]
    <;> ring
  rw [he] at h
  norm_num [Fin.sum_univ_succ] at h
  simpa using h

private lemma nonlinear_witness_projectionGamma :
    projectionGamma nonlinearKernel = nonlinearGamma := by
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [projectionGamma, meanMat, nonlinear_witness_mu, nonlinear_witness_projection,
      outer, nonlinearGamma] using nonlinear_witness_G0
  · simpa [projectionGamma, meanMat, nonlinear_witness_mu, nonlinear_witness_projection,
      outer, nonlinearGamma] using nonlinear_witness_G1
  · simpa [projectionGamma, meanMat, nonlinear_witness_mu, nonlinear_witness_projection,
      outer, nonlinearGamma, mul_comm] using nonlinear_witness_G1
  · simpa [projectionGamma, meanMat, nonlinear_witness_mu, nonlinear_witness_projection,
      outer, nonlinearGamma] using nonlinear_witness_G2

private instance nonlinear_witness_null_singleton : NullSingletonClass uniformUnitLaw := by
  refine ⟨fun x => ?_⟩
  simp [uniformUnitLaw, ProbabilityTheory.cond, Measure.smul_apply]

private lemma nonlinear_witness_distinct {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ ω ∂unitSampleLaw nonlinearKernel N, ω i ≠ ω j := by
  have hp : MeasurePreserving (fun ω : Fin N → ℝ => (ω i, ω j))
      (unitSampleLaw nonlinearKernel N) (uniformUnitLaw.prod uniformUnitLaw) := by
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    have hind := (iIndepFun_pi (μ := fun _ : Fin N => uniformUnitLaw)
      (fun _ => aemeasurable_id)).indepFun hij
    change (Measure.pi (fun _ : Fin N => uniformUnitLaw)).map (fun ω => (ω i, ω j)) = _
    rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable]
    simp only [(measurePreserving_eval (fun _ : Fin N => uniformUnitLaw) i).map_eq,
      (measurePreserving_eval (fun _ : Fin N => uniformUnitLaw) j).map_eq]
  have ha : ∀ᵐ uv : ℝ × ℝ ∂uniformUnitLaw.prod uniformUnitLaw, uv.1 ≠ uv.2 := by
    apply (Measure.ae_prod_iff_ae_ae (p := fun uv : ℝ × ℝ => uv.1 ≠ uv.2)
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Eventually.of_forall (fun x => by
      simpa only [ne_comm] using Measure.ae_ne uniformUnitLaw x)
  exact hp.quasiMeasurePreserving.tendsto_ae ha

private lemma nonlinear_witness_gram_quad {N : ℕ} (X : Dyad N → Vec 2) (c : Vec 2) :
    dot c ((sampleGram X).mulVec c) = ∑ d, (dot c (X d))^2 := by
  simp only [sampleGram, Matrix.sum_mulVec, dot, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp [outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring


private lemma nonlinear_witness_rank_pointwise (N : ℕ) (hN : 3 ≤ N)
    (ω : Fin N → ℝ) (hω : ω ⟨1, by omega⟩ ≠ ω ⟨2, by omega⟩) :
    (sampleGram (design nonlinearKernel ω)).det ≠ 0 := by
  classical
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  let l : Fin N := ⟨2, by omega⟩
  let d := printed_mkDyad i j (by simp [i,j])
  let f := printed_mkDyad i l (by simp [i,l])
  have hed := printed_mkDyad_endpoints i j (by simp [i,j])
  have hef := printed_mkDyad_endpoints i l (by simp [i,l])
  have hpd : (sampleGram (design nonlinearKernel ω)).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext a b
      simp only [sampleGram, Matrix.conjTranspose_apply, star_trivial, Matrix.sum_apply, outer]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    · intro c hc
      change 0 < dot c ((sampleGram (design nonlinearKernel ω)).mulVec c)
      rw [nonlinear_witness_gram_quad]
      have hn : ∃ q : Dyad N, dot c (design nonlinearKernel ω q) ≠ 0 := by
        by_contra! hh
        have hd := hh d
        have hf := hh f
        simp [design, d, f, hed.1, hed.2, hef.1, hef.2, nonlinearKernel,
          dot, Fin.sum_univ_succ] at hd hf
        have he : c 1 * (ω j - ω l) = 0 := by nlinarith [hd,hf]
        have hc1 : c 1 = 0 := (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hω)
        have hc0 : c 0 = 0 := by simpa only [hc1, zero_mul, add_zero] using hd
        apply hc
        ext a
        fin_cases a <;> assumption
      obtain ⟨q,hq⟩ := hn
      exact Finset.sum_pos' (fun q _ => sq_nonneg _) ⟨q, mem_univ q, sq_pos_of_ne_zero hq⟩
  exact hpd.det_pos.ne'

private lemma nonlinear_witness_sample_rank (N : ℕ) (hN : 3 ≤ N) :
    ∀ᵐ ω ∂unitSampleLaw nonlinearKernel N,
      (sampleGram (design nonlinearKernel ω)).det ≠ 0 := by
  have ha := nonlinear_witness_distinct (⟨1, by omega⟩ : Fin N)
    (⟨2, by omega⟩ : Fin N) (by simp)
  filter_upwards [ha] with ω hω
  exact nonlinear_witness_rank_pointwise N hN ω hω

private lemma nonlinear_witness_conditional_mean {N : ℕ} (d : Dyad N) :
    conditionalResidualMean nonlinearKernel d = fun ω => epsilon nonlinearKernel ω d := by
  have hm : designSigma (N := N) nonlinearKernel ≤
      (inferInstance : MeasurableSpace (Fin N → ℝ)) := by
    have hdesign : Measurable (@design ℝ _ 2 N nonlinearKernel) := by
      apply measurable_pi_lambda
      intro q
      have hp : Measurable (fun ω : Fin N → ℝ =>
          (ω (firstUnit q), ω (secondUnit q))) :=
        (measurable_pi_apply _).prodMk (measurable_pi_apply _)
      simpa only [design, Function.comp_def] using nonlinear_model_assumptions.2.1.comp hp
    exact hdesign.comap_le
  have hd : Measurable[designSigma (N := N) nonlinearKernel]
      (@design ℝ _ 2 N nonlinearKernel) := comap_measurable _
  have hx := (measurable_pi_apply 1).comp ((measurable_pi_apply d).comp hd)
  have he : (fun ω : Fin N → ℝ => epsilon nonlinearKernel ω d) =
      fun ω => (design nonlinearKernel ω d 1 - 2)^2 - 2/3 := by
    funext ω
    rw [epsilon, nonlinear_witness_residual]
    change (ω (firstUnit d) + ω (secondUnit d))^2 - 2/3 =
      (2 + ω (firstUnit d) + ω (secondUnit d) - 2)^2 - 2/3
    ring
  have hs : StronglyMeasurable[designSigma nonlinearKernel]
      (fun ω : Fin N → ℝ => epsilon nonlinearKernel ω d) := by
    rw [he]
    exact ((hx.sub_const 2).pow_const 2 |>.sub_const (2/3)).stronglyMeasurable
  have hi : Integrable (fun ω : Fin N → ℝ => epsilon nonlinearKernel ω d)
      (unitSampleLaw nonlinearKernel N) := by
    have hp := (GP0182B2b_score_memLp nonlinearKernel nonlinear_model_assumptions 0 2).comp_measurePreserving
      (corrected_pair_preserving nonlinearKernel d)
    convert hp.integrable one_le_two using 1
    funext ω
    simp [epsilon, populationScore, score, nonlinearKernel, Function.comp_def]
  exact condExp_of_stronglyMeasurable hm hs hi

private lemma nonlinear_witness_conditional_zero {N : ℕ} (d f : Dyad N) :
    conditionalResidualCov nonlinearKernel d f = 0 := by
  unfold conditionalResidualCov
  simp only [nonlinear_witness_conditional_mean, sub_self, zero_mul]
  exact condExp_zero

private lemma nonlinear_witness_printed_zero (N : ℕ) : printedSigma nonlinearKernel N = 0 := by
  have hz (d f : Dyad N) : conditionalTerm nonlinearKernel d f = 0 := by
    ext a b
    simp [conditionalTerm, meanMat, nonlinear_witness_conditional_zero]
  simp [printedSigma, hz]

private lemma nonlinear_witness_matrix_ext (A B : Mat 2)
    (hA : A 0 1 = A 1 0) (hB : B 0 1 = B 1 0)
    (hq : ∀ c : Vec 2, dot c (A.mulVec c) = dot c (B.mulVec c)) : A = B := by
  have h0 := hq ![1,0]
  have h1 := hq ![0,1]
  have h2 := hq ![1,1]
  simp [dot, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
  ext a b
  fin_cases a <;> fin_cases b <;> dsimp <;> linarith

private lemma nonlinear_witness_quad_lin (r s : ℝ) (A B : Mat 2) (c : Vec 2) :
    dot c ((r • A + s • B).mulVec c) =
      r * dot c (A.mulVec c) + s * dot c (B.mulVec c) := by
  simp [dot, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring

private lemma nonlinear_witness_variance (N : ℕ) (hN : 2 ≤ N) :
    varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) =
      (Dreal N) • nonlinearH + ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • nonlinearGamma := by
  let K := nonlinearKernel
  have hK : Standing K := nonlinear_model_assumptions
  apply nonlinear_witness_matrix_ext
  · exact covariance_comm _ _
  · simp [nonlinearH, nonlinearGamma]
  intro c
  rw [GP0182B2b_varMat_centered _ _ (GP0182B2b_scoreSum_memLp K hK N)
      (GP0182B2b_scoreSum_mean K hK N),
    GP0182B2b_mean_outer_quad _ _ (fun i j =>
      (GP0182B2b_scoreSum_memLp K hK N i).integrable_mul
        (GP0182B2b_scoreSum_memLp K hK N j))]
  simp_rw [GP0182B2b_dot_scoreSum]
  have hs := GP0182B2b_contrast_score K hK c
  rw [show unitSampleLaw K N = Measure.pi (fun _ : Fin N => K.μ) from rfl,
    GP0182B2b_dyad_second K.μ hN _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2]
  have hH : (∫ uv : ℝ × ℝ, (dot c (populationScore K uv.1 uv.2))^2 ∂K.μ.prod K.μ) =
      dot c ((scoreH K).mulVec c) :=
    (GP0182B2b_mean_outer_quad _ _ (fun i j =>
      (GP0182B2b_score_memLp K hK i 2).integrable_mul (GP0182B2b_score_memLp K hK j 2)) c).symm
  have hG : (∫ u, (GP0182B2b_rowIntegral (μ := K.μ)
        (fun uv : ℝ × ℝ => dot c (populationScore K uv.1 uv.2)) u)^2 ∂K.μ) =
      dot c ((projectionGamma K).mulVec c) := by
    rw [integral_congr_ae ((GP0182B2b_contrast_projection K hK c).mono
      (fun u hu => congrArg (fun x : ℝ => x^2) hu))]
    exact (GP0182B2b_mean_outer_quad _ _ (fun i j =>
      (GP0182B2b_projection_memLp K hK i).2.integrable_mul
        (GP0182B2b_projection_memLp K hK j).2) c).symm
  rw [hH, hG]
  change _ = dot c (((Dreal N) • nonlinearH +
    ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • nonlinearGamma).mulVec c)
  rw [nonlinear_witness_quad_lin]
  dsimp only [K]
  rw [nonlinear_witness_scoreH, nonlinear_witness_projectionGamma]

private lemma nonlinear_witness_variance_ne_zero (N : ℕ) (hN : 3 ≤ N) :
    varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) ≠ 0 := by
  rw [nonlinear_witness_variance N (by omega)]
  intro he
  have h00 := congrArg (fun M : Mat 2 => M 0 0) he
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : 0 < Dreal N := printed_Dpos (by omega : 2 ≤ N)
  have hC : 0 < (N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  norm_num [nonlinearH, nonlinearGamma] at h00
  nlinarith

private lemma nonlinear_witness_target_matrix : limitingTarget nonlinearKernel = nonlinearVstar := by
  have hi : nonlinearQ⁻¹ = (!![7,-3;-3,3/2] : Mat 2) := by
    apply Matrix.inv_eq_left_inv
    norm_num [nonlinearQ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
      funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]
  rw [limitingTarget, nonlinear_population_projection.1, nonlinear_witness_projectionGamma, hi]
  norm_num [sandwich, nonlinearGamma, nonlinearVstar, Matrix.mul_apply,
    Fin.sum_univ_succ, funext_iff, ← Matrix.ext_iff, Fin.forall_fin_succ]

private lemma nonlinear_witness_target_limit :
    Tendsto (trueTarget nonlinearKernel) atTop (𝓝 nonlinearVstar) := by
  have hV : Tendsto (fun N : ℕ => ((N : ℝ)/(Dreal N)^2) •
      ((Dreal N) • nonlinearH + ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • nonlinearGamma))
      atTop (𝓝 ((4 : ℝ) • nonlinearGamma)) := by
    have h := (GP0182B2b_NdivD_limit.smul_const nonlinearH).add
      (GP0182B2b_overlap_factor_limit.smul_const nonlinearGamma)
    simp only [zero_smul, zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [smul_add, smul_smul]
    congr 1
    · congr 1
      field_simp [(printed_Dpos hN).ne']
    · congr 1
      ring
  have h := (tendsto_const_nhds (x := (populationGram nonlinearKernel)⁻¹)).mul hV
  have hh := h.mul_const ((populationGram nonlinearKernel)⁻¹)
  have hl : (populationGram nonlinearKernel)⁻¹ * ((4 : ℝ) • nonlinearGamma) *
      (populationGram nonlinearKernel)⁻¹ = nonlinearVstar := by
    simpa only [limitingTarget, nonlinear_witness_projectionGamma, sandwich,
      Matrix.mul_smul, Matrix.smul_mul] using nonlinear_witness_target_matrix
  rw [hl] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  simp only [trueTarget, sandwich, nonlinear_witness_variance N hN,
    Matrix.mul_smul, Matrix.smul_mul]

private lemma nonlinear_witness_estimator_limit :
    inProbability (unitSampleLaw nonlinearKernel) (fun N ω =>
      (N : ℝ) • sampleVariance members (design nonlinearKernel ω) (response nonlinearKernel ω) -
        nonlinearVstar) := by
  have h0 := GP0182B2b_variance_consistency nonlinearKernel nonlinear_model_assumptions
  have hd := WeightedConsistency.inProbability_deterministic (unitSampleLaw nonlinearKernel)
    (fun N => trueTarget nonlinearKernel N - nonlinearVstar)
    (by convert nonlinear_witness_target_limit.sub_const nonlinearVstar using 1 <;>
      simp only [sub_self] <;> rfl)
  simpa only [sub_add_sub_cancel] using
    WeightedConsistency.inProbability_add (unitSampleLaw nonlinearKernel) h0 hd

private lemma nonlinear_witness_gaussian_contrasts (c : Vec 2) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) nonlinearVstar).map
      (fun x => dot c (WithLp.ofLp x)) =
        gaussianReal 0 (dot c (nonlinearVstar.mulVec c)).toNNReal := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin 2)) :=
    innerSL ℝ (WithLp.toLp 2 c)
  have he : (fun x : EuclideanSpace ℝ (Fin 2) => dot c (WithLp.ofLp x)) = L := by
    funext x
    simp [L, innerSL_apply_apply, PiLp.inner_apply, dot, mul_comm]
  rw [he, IsGaussian.map_eq_gaussianReal]
  have hm : (∫ x, L x ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) nonlinearVstar) = 0 := by
    rw [L.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian, map_zero]
  have hv : ProbabilityTheory.variance L
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) nonlinearVstar) =
      dot c (nonlinearVstar.mulVec c) := by
    have hh := covarianceBilin_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 2)))
      nonlinear_matrices_positive.2.posSemidef (WithLp.toLp 2 c) (WithLp.toLp 2 c)
    rw [covarianceBilin_self IsGaussian.memLp_two_id] at hh
    exact hh
  rw [hm,hv]

private lemma nonlinear_witness_coordinate_dot (i : Fin 2) (x : Vec 2) :
    dot (Pi.single i 1) x = x i := by
  classical
  simp [dot, Pi.single_apply]

private lemma nonlinear_witness_coefficient_measurable (N : ℕ) :
    Measurable (fun ω : Fin N → ℝ => Real.sqrt N • coefficientError nonlinearKernel ω) := by
  apply measurable_pi_lambda
  intro i
  have h := (GP0182B2b_measurable_statistics nonlinearKernel nonlinear_model_assumptions
    (Pi.single i 1) N).1
  simpa only [nonlinear_witness_coordinate_dot, Pi.smul_apply, smul_eq_mul] using
    h.const_mul (Real.sqrt N)

private lemma nonlinear_witness_inner (x c : Vec 2) :
    inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 c) = dot c x := by
  simp [PiLp.inner_apply, dot, mul_comm]

private lemma nonlinear_witness_vector_clt :
    ∃ ν : Measure (Vec 2), centeredNormalLaw ν nonlinearVstar ∧
      weakLimit (unitSampleLaw nonlinearKernel)
        (fun N ω => Real.sqrt N • coefficientError nonlinearKernel ω) ν := by
  let νE := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) nonlinearVstar
  let ν : Measure (Vec 2) := νE.map WithLp.ofLp
  have hνE : IsProbabilityMeasure νE := by dsimp [νE]; infer_instance
  letI nonlinear_witness_gaussian_probability : IsProbabilityMeasure νE := hνE
  have hν : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  let X := fun (N : ℕ) (ω : ℕ → ℝ) => WithLp.toLp 2
    (Real.sqrt N • coefficientError nonlinearKernel (GP0182B2b_prefix N ω))
  have hXm (N : ℕ) : Measurable (X N) :=
    (WithLp.measurable_toLp 2 (Vec 2)).comp ((nonlinear_witness_coefficient_measurable N).comp
      (GP0182B2b_prefix_measurable N))
  have hdist : TendstoInDistribution X atTop id
      (fun _ => GP0182B2b_product nonlinearKernel.μ) νE := by
    apply TendstoInDistribution.of_inner measurable_id.aemeasurable (fun N => (hXm N).aemeasurable)
    intro t
    have hs := GP0182B2b_numerator_clt nonlinearKernel nonlinear_model_assumptions (WithLp.ofLp t)
    rw [nonlinear_witness_target_matrix] at hs
    have he (N : ℕ) : (fun ω : ℕ → ℝ => inner ℝ (X N ω) t) =
        fun ω => Real.sqrt N * dot (WithLp.ofLp t)
          (coefficientError nonlinearKernel (GP0182B2b_prefix N ω)) := by
      funext ω
      change inner ℝ (WithLp.toLp 2 _) (WithLp.toLp 2 (WithLp.ofLp t)) = _
      rw [nonlinear_witness_inner, GP0182B2b_dot_smul]
    have hl : νE.map (fun x => inner ℝ (id x) t) =
        gaussianReal 0 (dot (WithLp.ofLp t) (nonlinearVstar.mulVec (WithLp.ofLp t))).toNNReal := by
      convert nonlinear_witness_gaussian_contrasts (WithLp.ofLp t) using 1
      congr 1
    refine ⟨fun N => (by rw [he]; exact hs.forall_aemeasurable N), (by fun_prop), ?_⟩
    simpa only [he, hl, Measure.map_id] using hs.tendsto
  have hpi := hdist.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ))
  have hnormal : centeredNormalLaw ν nonlinearVstar := by
    refine ⟨nonlinear_matrices_positive.2.posSemidef, hν, ?_⟩
    intro c
    change (νE.map WithLp.ofLp).map (fun x => dot c x) = _
    rw [Measure.map_map (by unfold dot; fun_prop) (WithLp.measurable_ofLp 2 (Vec 2))]
    exact nonlinear_witness_gaussian_contrasts c
  refine ⟨ν, hnormal, fun N => (nonlinear_witness_coefficient_measurable N).aemeasurable, hν, ?_⟩
  intro g
  have hh := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hpi.forall_aemeasurable hpi.aemeasurable_limit).mp hpi g
  have he (N : ℕ) :
      (∫ ω, g (Real.sqrt N • coefficientError nonlinearKernel (GP0182B2b_prefix N ω))
        ∂GP0182B2b_product nonlinearKernel.μ) =
      ∫ ω, g (Real.sqrt N • coefficientError nonlinearKernel ω) ∂unitSampleLaw nonlinearKernel N :=
    GP0182B2b_prefix_integral nonlinearKernel.μ N _
      (g.continuous.measurable.comp (nonlinear_witness_coefficient_measurable N))
  have hl : (∫ x, g (WithLp.ofLp x) ∂νE) = ∫ x, g x ∂ν := by
    dsimp only [ν]
    rw [integral_map (WithLp.measurable_ofLp 2 (Vec 2)).aemeasurable (by fun_prop)]
  change Tendsto (fun N : ℕ => ∫ ω, g (Real.sqrt N • coefficientError nonlinearKernel
    (GP0182B2b_prefix N ω)) ∂GP0182B2b_product nonlinearKernel.μ)
      atTop (𝓝 (∫ x, g (WithLp.ofLp x) ∂νE)) at hh
  simpa only [he,hl] using hh

theorem nonlinear_counterexample_proof :
    Standing nonlinearKernel ∧
    (∀ N : ℕ, 3 ≤ N → ∀ᵐ ω ∂ unitSampleLaw nonlinearKernel N, (sampleGram (design nonlinearKernel ω)).det ≠ 0) ∧
    populationGram nonlinearKernel = nonlinearQ ∧ nonlinearQ.det = 2/3 ∧
    populationBeta nonlinearKernel = ![2/3,0] ∧
    scoreH nonlinearKernel = nonlinearH ∧ projectionGamma nonlinearKernel = nonlinearGamma ∧
    nonlinearGamma.PosDef ∧
    (∀ N : ℕ, 3 ≤ N →
      (∀ d f : Dyad N, conditionalResidualCov nonlinearKernel d f =ᵐ[unitSampleLaw nonlinearKernel N] 0) ∧
      printedSigma nonlinearKernel N = 0 ∧
      varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) =
        (Dreal N) • nonlinearH + ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)) • nonlinearGamma ∧
      varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) ≠ 0) ∧
    varMat (unitSampleLaw nonlinearKernel 3) (scoreSum nonlinearKernel) = !![12/5,24/5;24/5,4712/315] ∧
    Tendsto (trueTarget nonlinearKernel) atTop (𝓝 nonlinearVstar) ∧
    nonlinearVstar.PosDef ∧
    (∃ ν : Measure (Vec 2), centeredNormalLaw ν nonlinearVstar ∧
      weakLimit (unitSampleLaw nonlinearKernel) (fun N ω => Real.sqrt N • coefficientError nonlinearKernel ω) ν) ∧
    inProbability (unitSampleLaw nonlinearKernel) (fun N ω =>
      (N : ℝ) • sampleVariance members (design nonlinearKernel ω) (response nonlinearKernel ω) - nonlinearVstar) := by
  refine ⟨nonlinear_model_assumptions, nonlinear_witness_sample_rank,
    nonlinear_population_projection.1, nonlinear_population_projection.2.2.1,
    nonlinear_population_projection.2.2.2, nonlinear_witness_scoreH,
    nonlinear_witness_projectionGamma, nonlinear_matrices_positive.1, ?_, ?_,
    nonlinear_witness_target_limit, nonlinear_matrices_positive.2,
    nonlinear_witness_vector_clt, nonlinear_witness_estimator_limit⟩
  · intro N hN
    refine ⟨fun d f => ?_, nonlinear_witness_printed_zero N,
      nonlinear_witness_variance N (by omega), nonlinear_witness_variance_ne_zero N hN⟩
    rw [nonlinear_witness_conditional_zero]
  · rw [nonlinear_witness_variance 3 (by decide)]
    convert nonlinear_matrix_certificate.2.2.2.2.2 using 1 <;> norm_num [Dreal]

end AronowAudit.P018.Wave1
