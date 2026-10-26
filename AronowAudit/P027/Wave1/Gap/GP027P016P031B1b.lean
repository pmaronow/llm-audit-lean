import AronowAudit.P027.P027_Audit
import AronowAudit.P027.Wave1.GaussianMoments
import AronowAudit.External.Causalean.Stat.CLT.ChiSquaredProjection
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.GaussianSquareMGF
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable

/-! ## Rounding and exact certificates -/

lemma GP027P016P031B1b_a3_rounding_implies_contrast_tail (H C H₀ C₀ R δ : ℝ)
    (hR : -1 ≤ R) (hH : |H-H₀| ≤ δ) (hC : |C-C₀| ≤ δ) :
    C-(1+R)*H ≤ C₀-(1+R)*H₀+δ*(2+R) := by
  have hHlo : -δ ≤ H-H₀ := (abs_le.mp hH).1
  have hChi : C-C₀ ≤ δ := (abs_le.mp hC).2
  have hmul : 0 ≤ (1+R)*(H-H₀+δ) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

private def GP027P016P031B1b_a3_ell (row : Fin 4) : ℝ :=
  -a3HighContrast row-(0.005:ℝ)*(2+contrastR (2*a3HighR row))

private def GP027P016P031B1b_a3_k (row : Fin 4) : ℝ :=
  let N : ℝ := (a3HighM row)*(2*a3HighR row)
  ((N-a3HighM row)*17.91/N^2)*contrastCoefficient (2*a3HighR row)

private def GP027P016P031B1b_a3_J : Fin 4 → ℤ := ![190,218,523,376]
private def GP027P016P031B1b_a3_h : Fin 4 → ℤ := ![1,5,1,5]

lemma GP027P016P031B1b_a3_floor_ceil_certificates (row : Fin 4) :
    0 < GP027P016P031B1b_a3_ell row ∧ 0 < GP027P016P031B1b_a3_k row ∧
    0 ≤ contrastR (2*a3HighR row) ∧
    ⌊GP027P016P031B1b_a3_ell row/(4*GP027P016P031B1b_a3_k row)⌋ = GP027P016P031B1b_a3_J row ∧
    ⌈((a3HighR row:ℝ)-1)/2⌉ = GP027P016P031B1b_a3_h row ∧
    GP027P016P031B1b_a3_h row < GP027P016P031B1b_a3_J row ∧
    GP027P016P031B1b_a3_J row-GP027P016P031B1b_a3_h row = (a3HighExponent row:ℤ) := by
  -- Rewrite integer floor/ceiling equalities to rational endpoint inequalities.
  fin_cases row <;>
    norm_num [GP027P016P031B1b_a3_ell, GP027P016P031B1b_a3_k, GP027P016P031B1b_a3_J, GP027P016P031B1b_a3_h, a3HighR, a3HighM,
      a3HighContrast, a3HighExponent, contrastR, contrastCoefficient,
      Int.floor_eq_iff, Int.ceil_eq_iff]

lemma GP027P016P031B1b_a3_average_contrast {Ξ : Type} {r m K : ℕ} (hr : 0 < r)
    (z : Fin K → Ξ → (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (ξ : Ξ) :
    (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) =
      (∑ i, periodicMeanC hr (z i ξ))/(K:ℝ) -
        (1+contrastR (2*r))*((∑ i, periodicMeanH hr (z i ξ))/(K:ℝ)) := by
  simp only [periodicContrast, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Transfer the contrast-tail estimate to the rounding-compatible event. -/
lemma GP027P016P031B1b_a3_probability_from_tail {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (row : Fin 4) (K : ℕ) (hK : 0 < K)
    (z : Fin K → Ξ →
      (Σ _ : Fin (a3HighR row) × Fin 2, Fin (a3HighM row)) → ℝ)
    (hr : 0 < a3HighR row)
    (hTail :
      (μ {ξ | (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) ≤ -GP027P016P031B1b_a3_ell row}).toReal ≤
        Real.exp (-GP027P016P031B1b_a3_ell row/(4*GP027P016P031B1b_a3_k row)) *
          (2:ℝ)^(((a3HighR row:ℝ)-1)/2) ∧
      (GP027P016P031B1b_a3_h row < GP027P016P031B1b_a3_J row →
        Real.exp (-GP027P016P031B1b_a3_ell row/(4*GP027P016P031B1b_a3_k row)) *
          (2:ℝ)^(((a3HighR row:ℝ)-1)/2) ≤
            (2:ℝ)^(-((GP027P016P031B1b_a3_J row-GP027P016P031B1b_a3_h row):ℝ)))) :
    (μ {ξ | |(∑ i, periodicMeanH hr (z i ξ))/(K:ℝ)-a3HighH row| ≤ 0.005 ∧
      |(∑ i, periodicMeanC hr (z i ξ))/(K:ℝ)-a3HighC row| ≤ 0.005}).toReal ≤
      ((2:ℝ)^(a3HighExponent row))⁻¹ := by
  have hc := GP027P016P031B1b_a3_floor_ceil_certificates row
  have hsub :
      {ξ | |(∑ i, periodicMeanH hr (z i ξ))/(K:ℝ)-a3HighH row| ≤ 0.005 ∧
        |(∑ i, periodicMeanC hr (z i ξ))/(K:ℝ)-a3HighC row| ≤ 0.005} ⊆
      {ξ | (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) ≤ -GP027P016P031B1b_a3_ell row} := by
    intro ξ hξ
    change (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) ≤ -GP027P016P031B1b_a3_ell row
    rw [GP027P016P031B1b_a3_average_contrast hr z ξ]
    have hb := GP027P016P031B1b_a3_rounding_implies_contrast_tail
      ((∑ i, periodicMeanH hr (z i ξ))/(K:ℝ))
      ((∑ i, periodicMeanC hr (z i ξ))/(K:ℝ))
      (a3HighH row) (a3HighC row) (contrastR (2*a3HighR row))
      0.005 (by linarith [hc.2.2.1]) hξ.1 hξ.2
    rw [(a3_high_contrast_arithmetic row).1] at hb
    dsimp [GP027P016P031B1b_a3_ell]
    linarith
  calc
    _ ≤ (μ {ξ | (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) ≤ -GP027P016P031B1b_a3_ell row}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ ≤ _ := hTail.1
    _ ≤ (2:ℝ)^(-((GP027P016P031B1b_a3_J row-GP027P016P031B1b_a3_h row):ℝ)) := hTail.2 hc.2.2.2.2.2.1
    _ = ((2:ℝ)^(a3HighExponent row))⁻¹ := by
      rw [← Int.cast_sub, hc.2.2.2.2.2.2]
      simp only [Int.cast_natCast, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_natCast]

/-! ## Analytic and probability helpers -/

lemma GP027P016P031B1b_contrast_tail_binary_comparison (t d : ℝ) (ht : 0 < t) (hd : 0 ≤ d)
    (h : (⌈d/2⌉ : ℤ) < ⌊t⌋) :
    Real.exp (-t)*(2:ℝ)^(d/2) ≤
      (2:ℝ)^(-(((⌊t⌋:ℤ)-(⌈d/2⌉:ℤ)):ℝ)) := by
  have hfloor : (⌊t⌋:ℝ) ≤ t := Int.floor_le t
  have hceil : d/2 ≤ (⌈d/2⌉:ℝ) := Int.le_ceil (d/2)
  have hh : (0:ℝ) ≤ (⌈d/2⌉:ℝ) := le_trans (by linarith) hceil
  have hJ : (0:ℝ) ≤ (⌊t⌋:ℝ) := by
    have h' : (⌈d/2⌉:ℝ) < (⌊t⌋:ℝ) := by exact_mod_cast h
    linarith
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloglt : Real.log 2 < 1 := by
    convert Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      (by norm_num : (2:ℝ) ≠ 1) using 1 <;> norm_num
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have hmul₁ : Real.log 2*(d/2) ≤ Real.log 2*(⌈d/2⌉:ℝ) :=
    mul_le_mul_of_nonneg_left hceil hlogpos.le
  have hmul₂ : Real.log 2*(⌊t⌋:ℝ) ≤ (⌊t⌋:ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hloglt.le hJ
  nlinarith

lemma GP027P016P031B1b_contrast_tail_exp_sum (d : ℕ) (v : Fin d → ℝ) :
    Real.exp ((∑ j, v j^2)/4) = ∏ j, Real.exp ((1/4:ℝ)*v j^2) := by
  rw [show (∑ j, v j^2)/4 = ∑ j, (1/4:ℝ)*v j^2 by
    rw [← Finset.mul_sum]; ring]
  exact Real.exp_sum _ _

lemma GP027P016P031B1b_contrast_tail_scalar_mgf :
    (∫ x : ℝ, Real.exp ((1/4:ℝ)*x^2) ∂gaussianReal 0 1) =
      (2:ℝ)^(1/(2:ℝ)) := by
  rw [StatLean.MultipleTesting.mgf_exp_sq_stdGaussian (by norm_num)]
  rw [show (1:ℝ)-2*(1/4) = 1/2 by norm_num,
    show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.sqrt_inv, inv_inv,
    Real.sqrt_eq_rpow]
  norm_num

lemma GP027P016P031B1b_contrast_tail_chi_squared_mgf (d : ℕ) :
    Integrable (fun x : ℝ => Real.exp (x/4)) (chiSquaredLaw d) ∧
    (∫ x : ℝ, Real.exp (x/4) ∂chiSquaredLaw d) = (2:ℝ)^((d:ℝ)/2) := by
  let ν : Measure (Fin d → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let S : (Fin d → ℝ) → ℝ := fun v => ∑ j, v j^2
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hExp : StronglyMeasurable (fun x : ℝ => Real.exp (x/4)) := by fun_prop
  have hprod : Integrable (fun v : Fin d → ℝ =>
      ∏ j, Real.exp ((1/4:ℝ)*v j^2)) ν :=
    Integrable.fintype_prod (fun _ =>
      StatLean.MultipleTesting.integrable_exp_sq_stdGaussian (by norm_num))
  have hcomp : Integrable ((fun x : ℝ => Real.exp (x/4)) ∘ S) ν := by
    simpa only [Function.comp_def, S, GP027P016P031B1b_contrast_tail_exp_sum] using hprod
  have hInt : Integrable (fun x : ℝ => Real.exp (x/4)) (ν.map S) :=
    (integrable_map_measure hExp.aestronglyMeasurable hS.aemeasurable).mpr hcomp
  refine ⟨hInt, ?_⟩
  change (∫ x : ℝ, Real.exp (x/4) ∂ν.map S) = _
  rw [integral_map hS.aemeasurable hExp.aestronglyMeasurable]
  simp only [S, GP027P016P031B1b_contrast_tail_exp_sum]
  dsimp [ν]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin d => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => Real.exp ((1/4:ℝ)*x^2))]
  simp only [GP027P016P031B1b_contrast_tail_scalar_mgf, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

lemma GP027P016P031B1b_contrast_tail_transfer_mgf {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (L : Ξ → ℝ) (hL : AEMeasurable L μ) (d : ℕ)
    (hlaw : μ.map L = chiSquaredLaw d) :
    Integrable (fun ξ => Real.exp (L ξ/4)) μ ∧
    (∫ ξ, Real.exp (L ξ/4) ∂μ) = (2:ℝ)^((d:ℝ)/2) := by
  have hmgf := GP027P016P031B1b_contrast_tail_chi_squared_mgf d
  have hInt : Integrable (fun x : ℝ => Real.exp (x/4)) (μ.map L) :=
    hlaw.symm ▸ hmgf.1
  refine ⟨hInt.comp_aemeasurable hL, ?_⟩
  rw [← integral_map hL hInt.aestronglyMeasurable, hlaw]
  exact hmgf.2

/-- The exponential average estimate, without any independence hypothesis. -/
lemma GP027P016P031B1b_contrast_tail_average_exp_le {K : ℕ} (hK : 0 < K) (L : Fin K → ℝ) :
    Real.exp (((∑ i, L i)/(K:ℝ))/4) ≤
      (∑ i, Real.exp (L i/4))/(K:ℝ) := by
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hw : (∑ _ : Fin K, (1/(K:ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hj := convexOn_exp.map_sum_le
    (t := Finset.univ) (w := fun _ : Fin K => 1/(K:ℝ))
    (p := fun i => L i/4)
    (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul, ← Finset.sum_mul] using hj

/-- Exponential Markov bound from the measurable low components, allowing
arbitrary dependence across the populations. -/
lemma GP027P016P031B1b_contrast_tail_dependent_average_markov {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (K : ℕ) (hK : 0 < K)
    (T L : Fin K → Ξ → ℝ) (k ℓ M : ℝ) (hk : 0 < k)
    (hLm : ∀ i, AEMeasurable (L i) μ)
    (hLower : ∀ i, ∀ᵐ ξ ∂μ, -k*L i ξ ≤ T i ξ)
    (hInt : ∀ i, Integrable (fun ξ => Real.exp (L i ξ/4)) μ)
    (hMean : ∀ i, (∫ ξ, Real.exp (L i ξ/4) ∂μ) ≤ M) :
    (μ {ξ | (∑ i, T i ξ)/(K:ℝ) ≤ -ℓ}).toReal ≤
      Real.exp (-ℓ/(4*k))*M := by
  let F : Ξ → ℝ := fun ξ => Real.exp (((∑ i, L i ξ)/(K:ℝ))/4)
  let G : Ξ → ℝ := fun ξ => (∑ i, Real.exp (L i ξ/4))/(K:ℝ)
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hGInt : Integrable G μ := by
    exact (integrable_finsetSum Finset.univ (fun i _ => hInt i)).div_const _
  have hFm : AEStronglyMeasurable F μ := by
    have hsum : AEMeasurable (fun ξ => ∑ i, L i ξ) μ := by
      exact Finset.aemeasurable_fun_sum Finset.univ (fun i _ => hLm i)
    exact ((hsum.div_const (K:ℝ)).div_const 4).exp.aestronglyMeasurable
  have hFG : ∀ ξ, F ξ ≤ G ξ := fun ξ =>
    GP027P016P031B1b_contrast_tail_average_exp_le hK (fun i => L i ξ)
  have hFInt : Integrable F μ := hGInt.mono hFm (by
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (by
        dsimp [G]
        exact div_nonneg (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)) hKr.le)]
    exact hFG ξ)
  have hGmean : (∫ ξ, G ξ ∂μ) ≤ M := by
    dsimp [G]
    rw [integral_div, integral_finsetSum Finset.univ (fun i _ => hInt i)]
    apply (div_le_iff₀ hKr).mpr
    calc
      _ ≤ ∑ _ : Fin K, M := Finset.sum_le_sum (fun i _ => hMean i)
      _ = M*(K:ℝ) := by simp [mul_comm]
  have hFmean : (∫ ξ, F ξ ∂μ) ≤ M :=
    (integral_mono_ae hFInt hGInt (ae_of_all _ hFG)).trans hGmean
  have hlow : ∀ᵐ ξ ∂μ, ∀ i : Fin K, -k*L i ξ ≤ T i ξ :=
    ae_all_iff.mpr hLower
  have hevent : ∀ᵐ ξ ∂μ,
      (∑ i, T i ξ)/(K:ℝ) ≤ -ℓ → Real.exp (ℓ/(4*k)) ≤ F ξ := by
    filter_upwards [hlow] with ξ hξ ht
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hξ i)
    rw [← Finset.mul_sum] at hs
    have hL : ℓ/k ≤ (∑ i, L i ξ)/(K:ℝ) := by
      apply (div_le_div_iff₀ hk hKr).mpr
      have ht' : (∑ i, T i ξ) ≤ -ℓ*(K:ℝ) := (div_le_iff₀ hKr).mp ht
      nlinarith
    dsimp [F]
    apply Real.exp_le_exp.mpr
    have heq : ℓ/(4*k) = (ℓ/k)/4 := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right hL (by norm_num)
  have hmeasure :
      (μ {ξ | (∑ i, T i ξ)/(K:ℝ) ≤ -ℓ}).toReal ≤
      (μ {ξ | Real.exp (ℓ/(4*k)) ≤ F ξ}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hevent)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ξ => (Real.exp_pos _).le)) hFInt (Real.exp (ℓ/(4*k)))
  have hbound :
      (μ {ξ | (∑ i, T i ξ)/(K:ℝ) ≤ -ℓ}).toReal ≤
        M/Real.exp (ℓ/(4*k)) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    calc
      _ ≤ (μ {ξ | Real.exp (ℓ/(4*k)) ≤ F ξ}).toReal * Real.exp (ℓ/(4*k)) :=
        mul_le_mul_of_nonneg_right hmeasure (Real.exp_pos _).le
      _ ≤ ∫ ξ, F ξ ∂μ := by
        change _ ≤ ∫ ξ, F ξ ∂μ
        convert hm using 1 <;> simp only [measureReal_def, mul_comm, F]
      _ ≤ M := hFmean
  calc
    _ ≤ M/Real.exp (ℓ/(4*k)) := hbound
    _ = Real.exp (-ℓ/(4*k))*M := by
      rw [div_eq_mul_inv, ← Real.exp_neg, neg_div]
      ring


lemma GP027P016P031B1b_contrast_tail_parameter_signs (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
    (σ2 : ℝ) (hσ : 0 < σ2) :
    let N : ℝ := (m:ℝ)*(2*r)
    0 < (N-m)*σ2/N^2 ∧ 0 < contrastCoefficient (2*r) ∧
      0 < ((N-m)*σ2/N^2)*contrastCoefficient (2*r) ∧
      ((r-1:ℕ):ℝ) = (r:ℝ)-1 := by
  have hr₁ : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hm₂ : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hrpos : (0:ℝ) < r := by linarith
  have hmpos : (0:ℝ) < m := by linarith
  have hN : (0:ℝ) < (m:ℝ)*(2*r) := by positivity
  have hNm : (0:ℝ) < (m:ℝ)*(2*r)-m := by
    have hp := mul_pos hmpos (show (0:ℝ) < 2*r-1 by linarith)
    nlinarith
  have ha : (0:ℝ) < (((m:ℝ)*(2*r)-m)*σ2)/((m:ℝ)*(2*r))^2 :=
    div_pos (mul_pos hNm hσ) (sq_pos_of_pos hN)
  have hc : 0 < contrastCoefficient (2*r) := by
    unfold contrastCoefficient
    exact div_pos (by positivity) (by nlinarith)
  exact ⟨ha, hc, mul_pos ha hc, by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]⟩

/-- Assemble the exponential and binary bounds from measurable low components. -/
lemma GP027P016P031B1b_contrast_tail_from_low_components {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (K : ℕ) (hK : 0 < K)
    (T : Fin K → Ξ → ℝ) (k ℓ : ℝ) (hk : 0 < k) (hℓ : 0 < ℓ) (d : ℕ)
    (hLow : ∀ i, ∃ L : Ξ → ℝ, AEMeasurable L μ ∧
      μ.map L = chiSquaredLaw d ∧ ∀ᵐ ξ ∂μ, -k*L ξ ≤ T i ξ) :
    let prob := (μ {ξ | (∑ i, T i ξ)/(K:ℝ) ≤ -ℓ}).toReal
    let J : ℤ := ⌊ℓ/(4*k)⌋
    let h : ℤ := ⌈(d:ℝ)/2⌉
    prob ≤ Real.exp (-ℓ/(4*k))*(2:ℝ)^((d:ℝ)/2) ∧
      (h < J → Real.exp (-ℓ/(4*k))*(2:ℝ)^((d:ℝ)/2) ≤
        (2:ℝ)^(-((J-h):ℝ))) := by
  dsimp only
  choose L hLm hLaw hLower using hLow
  have hmgf (i : Fin K) := GP027P016P031B1b_contrast_tail_transfer_mgf μ (L i) (hLm i) d (hLaw i)
  refine ⟨GP027P016P031B1b_contrast_tail_dependent_average_markov μ K hK T L k ℓ
    ((2:ℝ)^((d:ℝ)/2)) hk hLm hLower
    (fun i => (hmgf i).1) (fun i => (hmgf i).2.le), ?_⟩
  intro h
  simpa only [neg_div] using GP027P016P031B1b_contrast_tail_binary_comparison (ℓ/(4*k)) (d:ℝ)
    (div_pos hℓ (by positivity)) (Nat.cast_nonneg d) h


def GP027P016P031B1b_lowStandard {Ξ : Type} {r m : ℕ}
    (σ2 : ℝ) (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (ξ : Ξ) (i : Fin r) : ℝ :=
  (∑ j : Fin m, ε ⟨(i,0),j⟩ ξ) / Real.sqrt ((m:ℝ)*σ2)

lemma GP027P016P031B1b_lowStandard_law {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (r m : ℕ) (hm : 0 < m)
    (σ2 : ℝ) (hσ : 0 < σ2)
    (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (hε : GaussianNoise μ ε σ2) :
    AEMeasurable (GP027P016P031B1b_lowStandard σ2 ε) μ ∧
    μ.map (GP027P016P031B1b_lowStandard σ2 ε) =
      Measure.pi (fun _ : Fin r => gaussianReal 0 1) := by
  let s := Real.sqrt ((m:ℝ)*σ2)
  have hms : 0 < (m:ℝ)*σ2 := mul_pos (by exact_mod_cast hm) hσ
  have hs : s ≠ 0 := (Real.sqrt_pos.2 hms).ne'
  have hs2 : s^2 = (m:ℝ)*σ2 := Real.sq_sqrt hms.le
  have hg (k) : HasGaussianLaw (ε k) μ := by
    refine ⟨(hε.1 k).1, ?_⟩
    rw [(hε.1 k).2]
    infer_instance
  have hv := hε.2.hasGaussianLaw hg
  let A : ((Σ _ : Fin r × Fin 2, Fin m) → ℝ) →L[ℝ] (Fin r → ℝ) :=
    ContinuousLinearMap.pi fun i => s⁻¹ • ∑ j : Fin m, ContinuousLinearMap.proj ⟨(i,0),j⟩
  have hA (v : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (i : Fin r) :
      A v i = (∑ j : Fin m, v ⟨(i,0),j⟩)/s := by
    simp [A, div_eq_mul_inv, mul_comm]
  have hU : HasGaussianLaw (GP027P016P031B1b_lowStandard σ2 ε) μ := by
    convert hv.map_fun A using 1
    ext ξ i
    exact (hA (fun k => ε k ξ) i).symm
  have hM := gaussian_noise_moments μ ε σ2 hσ.le hε
  have hcov (k l) : cov[ε k, ε l; μ] = if k = l then σ2 else 0 := by
    rw [covariance_eq_sub (hg k).memLp_two (hg l).memLp_two]
    change outcomeE μ (fun ξ => ε k ξ * ε l ξ) -
      outcomeE μ (ε k)*outcomeE μ (ε l) = _
    rw [(hM.1 k).2, (hM.1 l).2, (hM.2 k l).2]
    ring
  have hmean (i : Fin r) : (∫ ξ, GP027P016P031B1b_lowStandard σ2 ε ξ i ∂μ) = 0 := by
    unfold GP027P016P031B1b_lowStandard
    rw [integral_div, integral_finsetSum _ (fun j _ => (hg _).integrable)]
    change (∑ j : Fin m, outcomeE μ (ε ⟨(i,0),j⟩)) / _ = 0
    simp only [(hM.1 _).2, Finset.sum_const_zero, zero_div]
  have hcovU (i l : Fin r) :
      cov[fun ξ => GP027P016P031B1b_lowStandard σ2 ε ξ i,
          fun ξ => GP027P016P031B1b_lowStandard σ2 ε ξ l; μ] =
        if i = l then 1 else 0 := by
    unfold GP027P016P031B1b_lowStandard
    rw [covariance_fun_div_left, covariance_fun_div_right,
      covariance_fun_sum_fun_sum (fun _ => (hg _).memLp_two) (fun _ => (hg _).memLp_two)]
    simp_rw [hcov]
    by_cases hil : i = l
    · subst l
      simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and, and_self, and_true,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (↑m * σ2) / s / s = 1
      rw [div_div, ← pow_two, hs2]
      exact div_self hms.ne'
    · have hne (j k : Fin m) :
          (Sigma.mk (i, (0:Fin 2)) j : Σ _ : Fin r × Fin 2, Fin m) ≠ ⟨(l,0),k⟩ := by
        intro h
        exact hil (congrArg (fun x => x.1.1) h)
      simp only [hne, ite_false, Finset.sum_const_zero, zero_div, hil]
  have hi : iIndepFun (fun i ξ => GP027P016P031B1b_lowStandard σ2 ε ξ i) μ :=
    hU.iIndepFun_of_covariance_eq_zero fun i l hil => by rw [hcovU, if_neg hil]
  refine ⟨hU.aemeasurable, ?_⟩
  rw [hi.map_fun_eq_pi_map (fun i => hU.aemeasurable.eval i)]
  congr 1
  funext i
  rw [(hU.eval i).map_eq_gaussianReal, hmean,
    ← covariance_self (hU.aemeasurable.eval i), hcovU]
  norm_num

def GP027P016P031B1b_centeredSq {r : ℕ} (v : Fin r → ℝ) : ℝ :=
  ∑ i, (v i - (∑ j, v j)/(r:ℝ))^2

lemma GP027P016P031B1b_centeredSq_law (r : ℕ) (hr : 0 < r) :
    (Measure.pi (fun _ : Fin r => gaussianReal 0 1)).map
      GP027P016P031B1b_centeredSq = chiSquaredLaw (r-1) := by
  let e : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun _ => 1)
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin r)) := Submodule.span ℝ {e}
  let S := Vᗮ
  have he : e ≠ 0 := by
    intro h
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin r) => x ⟨0,hr⟩) h
    norm_num [e] at hh
  have hdim : Module.finrank ℝ S = r-1 := by
    have h := V.finrank_add_finrank_orthogonal
    rw [show Module.finrank ℝ V = 1 from finrank_span_singleton he,
      finrank_euclideanSpace_fin] at h
    dsimp [S]
    omega
  have hnorm (v : Fin r → ℝ) : ‖S.starProjection (WithLp.toLp 2 v)‖^2 =
      GP027P016P031B1b_centeredSq v := by
    have he2 : ‖e‖^2 = (r:ℝ) := by simp [e, EuclideanSpace.real_norm_sq_eq]
    have hip : inner ℝ e (WithLp.toLp 2 v) = ∑ j, v j := by
      simp [e, PiLp.inner_apply]
    dsimp only [S, V]
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
      he2, hip, EuclideanSpace.real_norm_sq_eq]
    simp [e, GP027P016P031B1b_centeredSq]
  have hidem : S.starProjection ∘L S.starProjection = S.starProjection :=
    S.isIdempotentElem_starProjection
  have hlaw := Causalean.Stat.stdGaussian_map_normSq_orthogonalProjection
    S.starProjection (isSelfAdjoint_starProjection S) hidem
  rw [show LinearMap.range S.starProjection.toLinearMap = S from S.range_starProjection,
    hdim] at hlaw
  have hchi : Causalean.Stat.chiSqDist (r-1) = chiSquaredLaw (r-1) := by
    unfold Causalean.Stat.chiSqDist chiSquaredLaw
    rw [Causalean.Mathlib.stdGaussian_map_normSq_eq_pi, finrank_euclideanSpace_fin]
  rw [hchi] at hlaw
  rw [Causalean.Mathlib.stdGaussian, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)] at hlaw
  convert hlaw using 1
  congr 1
  funext v
  exact (hnorm v).symm

lemma GP027P016P031B1b_low_component {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (r m : ℕ) (hr : 0 < r) (hm : 0 < m)
    (σ2 : ℝ) (hσ : 0 < σ2)
    (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (hε : GaussianNoise μ ε σ2) :
    AEMeasurable (fun ξ => GP027P016P031B1b_centeredSq
      (GP027P016P031B1b_lowStandard σ2 ε ξ)) μ ∧
    μ.map (fun ξ => GP027P016P031B1b_centeredSq
      (GP027P016P031B1b_lowStandard σ2 ε ξ)) = chiSquaredLaw (r-1) := by
  have h := GP027P016P031B1b_lowStandard_law μ r m hm σ2 hσ ε hε
  have hmC : Measurable (@GP027P016P031B1b_centeredSq r) := by
    unfold GP027P016P031B1b_centeredSq
    fun_prop
  refine ⟨hmC.comp_aemeasurable h.1, ?_⟩
  change μ.map (GP027P016P031B1b_centeredSq ∘ GP027P016P031B1b_lowStandard σ2 ε) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hmC.aemeasurable h.1, h.2]
  exact GP027P016P031B1b_centeredSq_law r hr

lemma GP027P016P031B1b_centeredSq_eq {r : ℕ} (hr : 0 < r) (v : Fin r → ℝ) :
    GP027P016P031B1b_centeredSq v = (∑ i, v i^2) - (∑ i, v i)^2/(r:ℝ) := by
  have hrr : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold GP027P016P031B1b_centeredSq
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

lemma GP027P016P031B1b_centeredSq_affine {r : ℕ} (hr : 0 < r)
    (v : Fin r → ℝ) (b s : ℝ) :
    GP027P016P031B1b_centeredSq (fun i => (v i+b)/s) =
      GP027P016P031B1b_centeredSq v / s^2 := by
  have hrr : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsum : (∑ i, (v i+b)/s) = ((∑ j, v j)+(r:ℝ)*b)/s := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp
  unfold GP027P016P031B1b_centeredSq
  rw [hsum]
  calc
    _ = ∑ i : Fin r, (v i-(∑ j, v j)/r)^2/s^2 := by
      apply Finset.sum_congr rfl
      intro i _
      have hh : (v i+b)/s - ((∑ j, v j)+(r:ℝ)*b)/s/r =
          (v i-(∑ j, v j)/r)/s := by
        by_cases hs : s = 0
        · simp [hs]
        · field_simp [hrr, hs] <;> ring
      rw [hh, div_pow]
    _ = _ := (Finset.sum_div _ _ _).symm

lemma GP027P016P031B1b_contrast_lower (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
    (z : (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (hz : ∑ k, z k = 0) :
    -((((m:ℝ)*(2*r)-m)/((m:ℝ)*(2*r))^2)*contrastCoefficient (2*r)/(m:ℝ))*
      GP027P016P031B1b_centeredSq (fun i => groupTotal (fun _ => m) z (i,0)) ≤
      periodicContrast hr z := by
  let N : ℝ := (m:ℝ)*(2*r)
  let Y := groupTotal (fun _ : Fin r × Fin 2 => m) z
  let Q := ∑ k, z k^2
  let Lo := ∑ i : Fin r, Y (i,0)^2
  let Hi := ∑ i : Fin r, Y (i,1)^2
  have hmr : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrr : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hden : 18*(r:ℝ)-5 ≠ 0 := by
    have hh : (1:ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hN : N ≠ 0 := by dsimp [N]; positivity
  have hids := periodic_mean_identities r m hr hm z hz
  dsimp only at hids
  have hsum : (∑ g, Y g^2) = Lo+Hi := by
    simp only [Y, Lo, Hi, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]
  have hweights : (∑ g, Y g^2/phaseProb r g) = 6*r*Lo+(6*r/5)*Hi := by
    have hterm (i : Fin r) :
        Y (i,0)^2/phaseProb r (i,0)+Y (i,1)^2/phaseProb r (i,1) =
          (6*r)*Y (i,0)^2+(6*r/5)*Y (i,1)^2 := by
      norm_num [phaseProb]
      field_simp [hrr] <;> ring
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hQ : Lo+Hi ≤ (m:ℝ)*Q := by
    rw [← hsum]
    calc
      _ ≤ ∑ g : Fin r × Fin 2, (m:ℝ)*∑ j : Fin m, z ⟨g,j⟩^2 := by
        apply Finset.sum_le_sum
        intro g _
        simpa only [Y, groupTotal, Finset.card_univ, Fintype.card_fin] using
          (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin m => z ⟨g,j⟩))
      _ = (m:ℝ)*Q := by dsimp [Q]; rw [← Finset.mul_sum, Fintype.sum_sigma]
  have hsumY : (∑ i : Fin r, Y (i,0)) + (∑ i : Fin r, Y (i,1)) = 0 := by
    have ht : (∑ g : Fin r × Fin 2, Y g) = 0 := by
      dsimp [Y, groupTotal]
      rw [← Fintype.sum_sigma]
      exact hz
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib] using ht
  have hcenter : Hi-Lo =
      GP027P016P031B1b_centeredSq (fun i => Y (i,1)) -
      GP027P016P031B1b_centeredSq (fun i => Y (i,0)) := by
    rw [GP027P016P031B1b_centeredSq_eq hr, GP027P016P031B1b_centeredSq_eq hr]
    dsimp [Hi,Lo]
    have heq : (∑ i, Y (i,1)) = -(∑ i, Y (i,0)) := by linarith
    rw [heq, neg_sq]
    ring
  have hformula : periodicContrast hr z =
      ((N-m)/N^2)*(Q-(Lo+Hi)/m) +
        ((N-m)/N^2)*contrastCoefficient (2*r)/m*(Hi-Lo) := by
    unfold periodicContrast
    have hh : periodicMeanH hr z =
        ((6*r*Lo+(6*r/5)*Hi)-(Lo+Hi))/N^2 := by
      rw [hids.2.1, hids.1]
      change ((∑ g, Y g^2/phaseProb r g)/N^2) - (∑ g, Y g^2)/N^2 = _
      rw [hsum, hweights]
      ring
    have hc : periodicMeanC hr z = periodicMeanH hr z+(N-m)*Q/N^2 := by
      linarith [hids.2.2.2.1]
    rw [hc, hh]
    have hd : 9*(2*(r:ℝ))-5 = 18*r-5 := by ring
    simp only [contrastR, contrastCoefficient, hd]
    dsimp only [N]
    field_simp [hrr, hmr.ne', hden]
    have hinv : (-5+(r:ℝ)*18)*(-5+(r:ℝ)*18)⁻¹ = 1 :=
      mul_inv_cancel₀ (by intro he; apply hden; linarith)
    linear_combination -(Lo+Hi)*(10*(r:ℝ)-5)*hinv
  have hα : 0 ≤ (N-m)/N^2 := by
    have hh : (1:ℝ) ≤ r := by exact_mod_cast hr
    apply div_nonneg _ (sq_nonneg _)
    dsimp [N]
    nlinarith
  have hc : 0 ≤ contrastCoefficient (2*r) := by
    unfold contrastCoefficient
    apply div_nonneg (by positivity)
    have hh : (1:ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hW : 0 ≤ Q-(Lo+Hi)/m := by
    have hh : (Lo+Hi)/(m:ℝ) ≤ Q := (div_le_iff₀ hmr).2 (by nlinarith [hQ])
    linarith
  rw [hformula, hcenter]
  change -(((N-m)/N^2)*contrastCoefficient (2*r)/m)*
      GP027P016P031B1b_centeredSq (fun i => Y (i,0)) ≤ _
  have hp := mul_nonneg hα hW
  have hp2 := mul_nonneg (div_nonneg (mul_nonneg hα hc) hmr.le)
    (Finset.sum_nonneg (s := Finset.univ)
      (f := fun i : Fin r => (Y (i,1)-(∑ j, Y (j,1))/r)^2) (fun _ _ => sq_nonneg _))
  change 0 ≤ ((N-m)/N^2)*contrastCoefficient (2*r)/m*
    GP027P016P031B1b_centeredSq (fun i => Y (i,1)) at hp2
  nlinarith

lemma GP027P016P031B1b_actual_lower {Ξ : Type} (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
    (β σ2 : ℝ) (hσ : 0 < σ2)
    (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (ξ : Ξ) :
    let N : ℝ := (m:ℝ)*(2*r);
    -(((N-m)*σ2/N^2)*contrastCoefficient (2*r))*
      GP027P016P031B1b_centeredSq (GP027P016P031B1b_lowStandard σ2 ε ξ) ≤
      periodicContrast hr (centeredOutcomes phaseSize β ε ξ) := by
  let z := centeredOutcomes phaseSize β ε ξ
  let v : Fin r → ℝ := fun i => ∑ j : Fin m, ε ⟨(i,0),j⟩ ξ
  let b : ℝ := (m:ℝ)*(2*β -
    (∑ k, rawOutcomes phaseSize β ε ξ k)/
      (Fintype.card (Σ _ : Fin r × Fin 2, Fin m):ℝ))
  have hY (i : Fin r) : groupTotal (fun _ => m) z (i,0) = v i+b := by
    simp only [z, groupTotal, centeredOutcomes, rawOutcomes, phaseSize, ite_true,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [v,b,rawOutcomes]
    simp only [phaseSize, Finset.sum_add_distrib]
    ring
  have hCs : GP027P016P031B1b_centeredSq (fun i => groupTotal (fun _ => m) z (i,0)) =
      GP027P016P031B1b_centeredSq v := by
    simp_rw [hY]
    simpa only [div_one, one_pow] using GP027P016P031B1b_centeredSq_affine hr v b 1
  have hms : 0 < (m:ℝ)*σ2 := mul_pos (by exact_mod_cast (show 0 < m by omega)) hσ
  have hstd : GP027P016P031B1b_centeredSq (GP027P016P031B1b_lowStandard σ2 ε ξ) =
      GP027P016P031B1b_centeredSq v/((m:ℝ)*σ2) := by
    have h := GP027P016P031B1b_centeredSq_affine hr v 0 (Real.sqrt ((m:ℝ)*σ2))
    change GP027P016P031B1b_centeredSq (fun i => v i/Real.sqrt ((m:ℝ)*σ2)) = _
    simpa only [add_zero, Real.sq_sqrt hms.le] using h
  have hz : ∑ k, z k = 0 := centered_outcomes_zero
    (by simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
          Finset.card_univ, Fintype.card_prod, smul_eq_mul]; positivity)
    phaseSize β ε ξ
  have h := GP027P016P031B1b_contrast_lower r m hr hm z hz
  rw [hCs] at h
  dsimp only
  rw [hstd]
  convert h using 1
  field_simp
  <;> ring

theorem contrast_gaussian_tail_proof {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (r m K : ℕ)
    (hr : 0 < r) (hm : 2 ≤ m) (hK : 0 < K) (β σ2 ℓ : ℝ)
    (hσ : 0 < σ2) (hℓ : 0 < ℓ)
    (ε : Fin K → (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ)
    (hε : ∀ i, GaussianNoise μ (ε i) σ2) :
    let z := fun i => centeredOutcomes phaseSize β (ε i)
    let N : ℝ := m*(2*r)
    let a := (N-m)*σ2/N^2
    let c := contrastCoefficient (2*r)
    let k := a*c
    let d : ℝ := r-1
    let Tbar := fun ξ => (∑ i, periodicContrast hr (z i ξ))/(K:ℝ)
    let prob := (μ {ξ | Tbar ξ ≤ -ℓ}).toReal
    let J : ℤ := ⌊ℓ/(4*k)⌋
    let h : ℤ := ⌈d/2⌉
    prob ≤ Real.exp (-ℓ/(4*k)) * (2:ℝ)^(d/2) ∧
    (h < J → Real.exp (-ℓ/(4*k)) * (2:ℝ)^(d/2) ≤ (2:ℝ)^(-((J-h):ℝ))) := by
  dsimp only
  have hs := GP027P016P031B1b_contrast_tail_parameter_signs r m hr hm σ2 hσ
  dsimp only at hs
  have h := GP027P016P031B1b_contrast_tail_from_low_components μ K hK
    (fun i ξ => periodicContrast hr (centeredOutcomes phaseSize β (ε i) ξ))
    ((((m:ℝ)*(2*r)-m)*σ2/((m:ℝ)*(2*r))^2)*contrastCoefficient (2*r))
    ℓ hs.2.2.1 hℓ (r-1) (by
      intro i
      refine ⟨fun ξ => GP027P016P031B1b_centeredSq
        (GP027P016P031B1b_lowStandard σ2 (ε i) ξ), ?_, ?_, ?_⟩
      · exact (GP027P016P031B1b_low_component μ r m hr (by omega) σ2 hσ (ε i) (hε i)).1
      · exact (GP027P016P031B1b_low_component μ r m hr (by omega) σ2 hσ (ε i) (hε i)).2
      · exact ae_of_all μ (GP027P016P031B1b_actual_lower r m hr hm β σ2 hσ (ε i)))
  simpa only [hs.2.2.2] using h

theorem a3_high_rows_probability_bound_proof {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (row : Fin 4) (K : ℕ) (hK : 0 < K) (β : ℝ)
    (ε : Fin K → (Σ _ : Fin (a3HighR row) × Fin 2, Fin (a3HighM row)) → Ξ → ℝ)
    (hε : ∀ i, GaussianNoise μ (ε i) 17.91) :
    let hr : 0 < a3HighR row := by fin_cases row <;> norm_num [a3HighR]
    let z := fun i => centeredOutcomes phaseSize β (ε i)
    let Hbar := fun ξ => (∑ i, periodicMeanH hr (z i ξ))/(K:ℝ)
    let Cbar := fun ξ => (∑ i, periodicMeanC hr (z i ξ))/(K:ℝ)
    (μ {ξ | |Hbar ξ-a3HighH row| ≤ 0.005 ∧ |Cbar ξ-a3HighC row| ≤ 0.005}).toReal ≤
      ((2:ℝ)^(a3HighExponent row))⁻¹ := by
  let hr : 0 < a3HighR row := by fin_cases row <;> norm_num [a3HighR]
  have hm : 2 ≤ a3HighM row := by fin_cases row <;> norm_num [a3HighM]
  have hc := GP027P016P031B1b_a3_floor_ceil_certificates row
  dsimp only
  apply GP027P016P031B1b_a3_probability_from_tail μ row K hK
    (fun i => centeredOutcomes phaseSize β (ε i)) hr
  have ht := contrast_gaussian_tail_proof μ (a3HighR row) (a3HighM row) K
    hr hm hK β 17.91 (GP027P016P031B1b_a3_ell row) (by norm_num) hc.1 ε hε
  dsimp only at ht
  have hf := hc.2.2.2.1
  dsimp only [GP027P016P031B1b_a3_k] at hf
  rw [hf, hc.2.2.2.2.1] at ht
  exact ht

end
end AronowAudit.P027.Wave1
