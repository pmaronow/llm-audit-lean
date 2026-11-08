import SAP.P039.WH.W1.Leaves
import AronowAudit.P039.P039_GaussianCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P039.WH.W1.P.T4_L3

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix NNReal ENNReal

noncomputable section

theorem matrix_frame_standard_law {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℝ) (hB : B * Bᵀ = 1) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (fun z => B *ᵥ z) =
      Measure.pi (fun _ : Fin m => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let L := AronowAudit.P039.GaussianCompletion.matrixCLM B
  have hL : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L =
      stdGaussian (EuclideanSpace ℝ (Fin m)) :=
    AronowAudit.P039.GaussianCompletion.gaussian_coisometry L
      (AronowAudit.P039.GaussianCompletion.matrixCLM_coisometry B hB)
  have hn : μ.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    map_pi_eq_stdGaussian
  have hm : ν.map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin m)) :=
    map_pi_eq_stdGaussian
  have hof : (stdGaussian (EuclideanSpace ℝ (Fin m))).map WithLp.ofLp = ν := by
    rw [← hm, Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, WithLp.ofLp_toLp, Measure.map_id']
  have he : (fun z : Fin n → ℝ => B *ᵥ z) =
      WithLp.ofLp ∘ L ∘ WithLp.toLp 2 := by
    funext z
    rfl
  rw [he]
  change μ.map (WithLp.ofLp ∘ L ∘ WithLp.toLp 2) = ν
  rw [← Measure.map_map (by fun_prop : Measurable WithLp.ofLp)
      (by fun_prop : Measurable (L ∘ WithLp.toLp 2)),
    ← Measure.map_map (by fun_prop : Measurable L)
      (by fun_prop : Measurable (WithLp.toLp 2)), hn, hL, hof]

theorem normalized_frame_law {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (hB : B * Bᵀ = 1) (σ : ℝ≥0) (hσ : 0 < σ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 (σ ^ 2))).map
      (fun e => B *ᵥ (fun i => e i / (σ : ℝ))) =
        Measure.pi (fun _ : Fin m => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 (σ ^ 2))
  have hn : μ.map (fun e i => e i / (σ : ℝ)) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
    have hmap := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 (σ ^ 2))
      (f := fun (_ : Fin n) (x : ℝ) => x / (σ : ℝ))
      (fun _ => (measurable_id.div_const (σ : ℝ)).aemeasurable)
    simpa only [AronowAudit.P039.GaussianCompletion.normalize_gaussian σ hσ] using hmap
  calc
    _ = (μ.map (fun e i => e i / (σ : ℝ))).map (fun z => B *ᵥ z) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by rw [hn, matrix_frame_standard_law B hB]

def frameEnergy {ν : ℕ} (z : Fin (ν + 1) → ℝ) : ℝ :=
  ∑ i : Fin ν, (z i.succ) ^ 2

def frameRatio {ν : ℕ} (z : Fin (ν + 1) → ℝ) : ℝ :=
  z 0 / Real.sqrt (frameEnergy z / (ν : ℝ))

@[fun_prop] theorem frameRatio_measurable {ν : ℕ} :
    Measurable (frameRatio (ν := ν)) := by
  fun_prop [frameRatio, frameEnergy]

theorem frame_ratio_student_law (ν : ℕ) :
    (Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1)).map
      (frameRatio (ν := ν)) = studentLaw ν := by
  unfold studentLaw
  apply Measure.map_congr
  filter_upwards [] with z
  dsimp only [Function.comp_apply, frameRatio, frameEnergy]
  rw [AronowAudit.P039.GaussianCompletion.erase_zero_sum]

theorem frame_energy_positive_ae (ν : ℕ) (hν : 0 < ν) :
    ∀ᵐ z ∂(Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1)),
      0 < frameEnergy z := by
  let j : Fin ν := ⟨0, by omega⟩
  let j' : Fin (ν + 1) := j.succ
  have hcoord : (Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1)).map
      (fun z => z j') = gaussianReal 0 1 :=
    by simpa using
      (Measure.pi_map_eval (fun _ : Fin (ν + 1) => gaussianReal 0 1) j')
  have hg : ∀ᵐ x ∂gaussianReal 0 1, x ≠ 0 := by
    letI : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal (by norm_num)
    exact Measure.ae_ne _ 0
  have hz : ∀ᵐ z ∂(Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1)),
      z j' ≠ 0 := by
    apply ae_of_ae_map (μ := Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1))
      (p := fun x : ℝ => x ≠ 0)
      (measurable_pi_apply j').aemeasurable
    rw [hcoord]
    exact hg
  filter_upwards [hz] with z hz
  have hterm : (z j') ^ 2 ≤ frameEnergy z := by
    change (z j.succ) ^ 2 ≤ ∑ i : Fin ν, (z i.succ) ^ 2
    exact Finset.single_le_sum (fun i hi => sq_nonneg (z i.succ)) (Finset.mem_univ j)
  have hpositive : 0 < (z j') ^ 2 := sq_pos_of_ne_zero hz
  exact lt_of_lt_of_le hpositive hterm

theorem scaled_ratio_identity (c S σ sm : ℝ) (ν : ℕ)
    (hS : 0 ≤ S) (hσ : 0 < σ) (hsm : 0 < sm) (hν : 0 < ν) :
    (c / Real.sqrt sm) / Real.sqrt ((σ ^ 2 * S) / ((ν : ℝ) * sm)) =
      (c / σ) / Real.sqrt (S / (ν : ℝ)) := by
  by_cases hzero : S = 0
  · subst S
    simp
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
  have hνpos : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hdiv : 0 ≤ S / (ν : ℝ) := div_nonneg hS hνpos.le
  have hdivpos : 0 < S / (ν : ℝ) := div_pos hSpos hνpos
  have hsmroot : 0 < Real.sqrt sm := Real.sqrt_pos.mpr hsm
  have hinside : (σ ^ 2 * S) / ((ν : ℝ) * sm) =
      (S / (ν : ℝ)) * (σ ^ 2 / sm) := by
    field_simp [ne_of_gt hνpos, ne_of_gt hsm]
    <;> ring
  have hroot : Real.sqrt ((σ ^ 2 * S) / ((ν : ℝ) * sm)) =
      Real.sqrt (S / (ν : ℝ)) * (σ / Real.sqrt sm) := by
    rw [hinside, Real.sqrt_mul hdiv, Real.sqrt_div (sq_nonneg σ), Real.sqrt_sq hσ.le]
  rw [hroot]
  field_simp [ne_of_gt hσ, ne_of_gt hsmroot,
    ne_of_gt (Real.sqrt_pos.mpr hdivpos)]
  <;> ring

theorem proof : SAP.P039.WH.W1.T4_L3 := by
  intro n k Z x γ σ hσ hn hgeom hframe
  let ν : ℕ := n - k - 1
  let μ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 (σ ^ 2))
  have hν : 0 < ν := by dsimp [ν]; omega
  have hνcast : (ν : ℝ) = (n : ℝ) - k - 1 := by
    dsimp [ν]
    rw [Nat.cast_sub (by omega : 1 ≤ n - k), Nat.cast_sub (by omega : k ≤ n)]
    norm_num
  obtain ⟨B, hBframe⟩ := hframe
  rcases hBframe with ⟨hBB, hB0, hBenergy⟩
  rcases hgeom with ⟨hsm, he, hQsym, hQidem, hQe, hQrank, hcoef, hres, hse⟩
  have hnorm : μ.map (fun ε => B *ᵥ (fun i => ε i / (σ : ℝ))) =
      Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1) := by
    exact normalized_frame_law B hBB σ hσ
  have hcoord (ε : Fin n → ℝ) (j : Fin (ν + 1)) :
      (B *ᵥ (fun i => ε i / (σ : ℝ))) j = (B *ᵥ ε) j / (σ : ℝ) := by
    have hv : (fun i => ε i / (σ : ℝ)) = ((σ : ℝ)⁻¹) • ε := by
      ext i
      simp [div_eq_mul_inv, smul_eq_mul]
      ring
    rw [hv, Matrix.mulVec_smul]
    simp [smul_eq_mul, div_eq_mul_inv]
    <;> ring
  have hfirst (ε : Fin n → ℝ) : (B *ᵥ ε) 0 = dotProduct (wholeRegressorContrast Z x) ε := by
    simp [Matrix.mulVec, dotProduct, hB0]
  have hsse (ε : Fin n → ℝ) :
      olsSSE (fullDesign Z x) (Z *ᵥ γ + ε) =
        ∑ i : Fin ν, ((B *ᵥ ε) i.succ) ^ 2 := by
    unfold olsSSE
    rw [hres γ ε, hBenergy ε]
  have henergy_norm (ε : Fin n → ℝ) :
      frameEnergy (B *ᵥ (fun i => ε i / (σ : ℝ))) =
        olsSSE (fullDesign Z x) (Z *ᵥ γ + ε) / (σ : ℝ) ^ 2 := by
    rw [hsse]
    simp only [frameEnergy]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord ε i.succ]
    simp [div_pow]
  have hSSEscale (ε : Fin n → ℝ) :
      olsSSE (fullDesign Z x) (Z *ᵥ γ + ε) =
        (σ : ℝ) ^ 2 * frameEnergy (B *ᵥ (fun i => ε i / (σ : ℝ))) := by
    have h := henergy_norm ε
    have hσne : (σ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hσ.ne')
    calc
      _ = (_ / (σ : ℝ) ^ 2) * (σ : ℝ) ^ 2 := by field_simp [hσne]
      _ = _ := by rw [← h]; ring
  have hstatpoint (ε : Fin n → ℝ) :
      olsT (fullDesign Z x) (Z *ᵥ γ + ε) (Fin.last k) =
        frameRatio (B *ᵥ (fun i => ε i / (σ : ℝ))) := by
    let c := dotProduct (wholeRegressorContrast Z x) ε
    let S := frameEnergy (B *ᵥ (fun i => ε i / (σ : ℝ)))
    have hc : ols (fullDesign Z x) (Z *ᵥ γ + ε) (Fin.last k) = c / Real.sqrt
        (dotProduct x (residualMaker Z *ᵥ x)) := by
      have h := hcoef γ ε
      dsimp [c] at h ⊢
      have hsqrt : 0 < Real.sqrt (dotProduct x (residualMaker Z *ᵥ x)) :=
        Real.sqrt_pos.mpr hsm
      calc
        _ = (_ * Real.sqrt (dotProduct x (residualMaker Z *ᵥ x))) /
            Real.sqrt (dotProduct x (residualMaker Z *ᵥ x)) := by
              field_simp [ne_of_gt hsqrt]
        _ = _ := by rw [h]
    have hcoefB : (B *ᵥ ε) 0 = c := by simpa [c] using hfirst ε
    have hzn : (B *ᵥ (fun i => ε i / (σ : ℝ))) 0 = c / (σ : ℝ) := by
      rw [hcoord ε 0, hcoefB]
    have hS : 0 ≤ S := by
      dsimp [S, frameEnergy]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hSSEscale' : olsSSE (fullDesign Z x) (Z *ᵥ γ + ε) = (σ : ℝ) ^ 2 * S := by
      simpa [S] using hSSEscale ε
    have hse' : olsSESquared (fullDesign Z x) (Z *ᵥ γ + ε) (Fin.last k) =
        ((σ : ℝ) ^ 2 * S) / ((ν : ℝ) * dotProduct x (residualMaker Z *ᵥ x)) := by
      rw [hse (Z *ᵥ γ + ε), hSSEscale', hνcast]
    change ols (fullDesign Z x) (Z *ᵥ γ + ε) (Fin.last k) /
      Real.sqrt (olsSESquared (fullDesign Z x) (Z *ᵥ γ + ε) (Fin.last k)) = _
    rw [hc, hse']
    change (c / Real.sqrt (dotProduct x (residualMaker Z *ᵥ x))) /
      Real.sqrt (((σ : ℝ) ^ 2 * S) /
        ((ν : ℝ) * dotProduct x (residualMaker Z *ᵥ x))) =
      (B *ᵥ (fun i => ε i / (σ : ℝ))) 0 /
        Real.sqrt (S / (ν : ℝ))
    rw [hzn]
    exact scaled_ratio_identity c S (σ : ℝ)
      (dotProduct x (residualMaker Z *ᵥ x)) ν hS (by exact_mod_cast hσ) hsm hν
  have hstatlaw : μ.map (fun ε =>
      olsT (fullDesign Z x) (Z *ᵥ γ + ε) (Fin.last k)) = studentLaw ν := by
    have hfun : (fun ε : Fin n → ℝ =>
        olsT (fullDesign Z x) (Z *ᵥ γ + ε) (Fin.last k)) =
        frameRatio (ν := ν) ∘ (fun ε => B *ᵥ (fun i => ε i / (σ : ℝ))) := by
      funext ε
      exact hstatpoint ε
    rw [hfun, ← Measure.map_map frameRatio_measurable (by fun_prop), hnorm]
    exact frame_ratio_student_law ν
  have hposcoords : ∀ᵐ z ∂(Measure.pi (fun _ : Fin (ν + 1) => gaussianReal 0 1)),
      0 < frameEnergy z := frame_energy_positive_ae ν hν
  have hpospre : ∀ᵐ ε ∂μ,
      0 < frameEnergy (B *ᵥ (fun i => ε i / (σ : ℝ))) := by
    have hmeas : Measurable (fun ε : Fin n → ℝ =>
        B *ᵥ (fun i => ε i / (σ : ℝ))) := by
      apply measurable_pi_iff.mpr
      intro j
      change Measurable (fun ε : Fin n → ℝ =>
        ∑ i, B j i * (ε i / (σ : ℝ)))
      fun_prop
    apply ae_of_ae_map (μ := μ)
      (p := fun z : Fin (ν + 1) → ℝ => 0 < frameEnergy z)
      hmeas.aemeasurable
    rw [hnorm]
    exact hposcoords
  have hsspos : ∀ᵐ ε ∂μ,
      0 < olsSSE (fullDesign Z x) (Z *ᵥ γ + ε) := by
    filter_upwards [hpospre] with ε hε
    rw [hSSEscale ε]
    exact mul_pos (sq_pos_of_pos (by exact_mod_cast hσ)) hε
  exact ⟨by simpa [ν, μ] using hstatlaw, by simpa [μ] using hsspos⟩

end

end SAP.P039.WH.W1.P.T4_L3

theorem SAP.P039.WH.W1.T4_L3_proof : SAP.P039.WH.W1.T4_L3 :=
  SAP.P039.WH.W1.P.T4_L3.proof
