import AronowAudit.P027.P027_Audit
import AronowAudit.External.StatLean.MultipleTesting.ForMathlib.GaussianSquareMGF
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
Draft for records 3, 6, 7 of the worker brief (mapper records 4, 7, 8).
No Lean executable was run. The first two records stop at explicit helper contracts:
the new Gaussian-law proof required by the approved dependency graph is not in
this checkout. In particular none of the three held declarations is used as a
proof. See the worker REPORT.md for the exact remaining dependency.
-/

namespace AronowAudit.P027.Wave1

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
attribute [local instance] Classical.propDecidable

/-! ## Record 3: rounding and exact certificates -/

lemma a3_rounding_implies_contrast_tail (H C H₀ C₀ R δ : ℝ)
    (hR : -1 ≤ R) (hH : |H-H₀| ≤ δ) (hC : |C-C₀| ≤ δ) :
    C-(1+R)*H ≤ C₀-(1+R)*H₀+δ*(2+R) := by
  have hHlo : -δ ≤ H-H₀ := (abs_le.mp hH).1
  have hChi : C-C₀ ≤ δ := (abs_le.mp hC).2
  have hmul : 0 ≤ (1+R)*(H-H₀+δ) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

private def a3_ell (row : Fin 4) : ℝ :=
  -a3HighContrast row-(0.005:ℝ)*(2+contrastR (2*a3HighR row))

private def a3_k (row : Fin 4) : ℝ :=
  let N : ℝ := (a3HighM row)*(2*a3HighR row)
  ((N-a3HighM row)*17.91/N^2)*contrastCoefficient (2*a3HighR row)

private def a3_J : Fin 4 → ℤ := ![190,218,523,376]
private def a3_h : Fin 4 → ℤ := ![1,5,1,5]

lemma a3_floor_ceil_certificates (row : Fin 4) :
    0 < a3_ell row ∧ 0 < a3_k row ∧
    0 ≤ contrastR (2*a3HighR row) ∧
    ⌊a3_ell row/(4*a3_k row)⌋ = a3_J row ∧
    ⌈((a3HighR row:ℝ)-1)/2⌉ = a3_h row ∧
    a3_h row < a3_J row ∧
    a3_J row-a3_h row = (a3HighExponent row:ℤ) := by
  -- Rewrite integer floor/ceiling equalities to rational endpoint inequalities.
  fin_cases row <;>
    norm_num [a3_ell, a3_k, a3_J, a3_h, a3HighR, a3HighM,
      a3HighContrast, a3HighExponent, contrastR, contrastCoefficient,
      Int.floor_eq_iff, Int.ceil_eq_iff]

lemma a3_average_contrast {Ξ : Type} {r m K : ℕ} (hr : 0 < r)
    (z : Fin K → Ξ → (Σ _ : Fin r × Fin 2, Fin m) → ℝ) (ξ : Ξ) :
    (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) =
      (∑ i, periodicMeanC hr (z i ξ))/(K:ℝ) -
        (1+contrastR (2*r))*((∑ i, periodicMeanH hr (z i ξ))/(K:ℝ)) := by
  simp only [periodicContrast, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Assembly helper only. Its explicit `hTail` argument must be supplied by the
new Gaussian tail proof; this is not the requested unconditional final theorem. -/
lemma a3_probability_from_tail {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (row : Fin 4) (K : ℕ) (hK : 0 < K)
    (z : Fin K → Ξ →
      (Σ _ : Fin (a3HighR row) × Fin 2, Fin (a3HighM row)) → ℝ)
    (hr : 0 < a3HighR row)
    (hTail :
      (μ {ξ | (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) ≤ -a3_ell row}).toReal ≤
        Real.exp (-a3_ell row/(4*a3_k row)) *
          (2:ℝ)^(((a3HighR row:ℝ)-1)/2) ∧
      (a3_h row < a3_J row →
        Real.exp (-a3_ell row/(4*a3_k row)) *
          (2:ℝ)^(((a3HighR row:ℝ)-1)/2) ≤
            (2:ℝ)^(-((a3_J row-a3_h row):ℝ)))) :
    (μ {ξ | |(∑ i, periodicMeanH hr (z i ξ))/(K:ℝ)-a3HighH row| ≤ 0.005 ∧
      |(∑ i, periodicMeanC hr (z i ξ))/(K:ℝ)-a3HighC row| ≤ 0.005}).toReal ≤
      ((2:ℝ)^(a3HighExponent row))⁻¹ := by
  have hc := a3_floor_ceil_certificates row
  have hsub :
      {ξ | |(∑ i, periodicMeanH hr (z i ξ))/(K:ℝ)-a3HighH row| ≤ 0.005 ∧
        |(∑ i, periodicMeanC hr (z i ξ))/(K:ℝ)-a3HighC row| ≤ 0.005} ⊆
      {ξ | (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) ≤ -a3_ell row} := by
    intro ξ hξ
    change (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) ≤ -a3_ell row
    rw [a3_average_contrast hr z ξ]
    have hb := a3_rounding_implies_contrast_tail
      ((∑ i, periodicMeanH hr (z i ξ))/(K:ℝ))
      ((∑ i, periodicMeanC hr (z i ξ))/(K:ℝ))
      (a3HighH row) (a3HighC row) (contrastR (2*a3HighR row))
      0.005 (by linarith [hc.2.2.1]) hξ.1 hξ.2
    rw [(a3_high_contrast_arithmetic row).1] at hb
    dsimp [a3_ell]
    linarith
  calc
    _ ≤ (μ {ξ | (∑ i, periodicContrast hr (z i ξ))/(K:ℝ) ≤ -a3_ell row}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ ≤ _ := hTail.1
    _ ≤ (2:ℝ)^(-((a3_J row-a3_h row):ℝ)) := hTail.2 hc.2.2.2.2.2.1
    _ = ((2:ℝ)^(a3HighExponent row))⁻¹ := by
      rw [← Int.cast_sub, hc.2.2.2.2.2.2]
      simp only [Int.cast_natCast, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_natCast]

/-! ## Record 6: analytic and probability helpers -/

lemma contrast_tail_binary_comparison (t d : ℝ) (ht : 0 < t) (hd : 0 ≤ d)
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

lemma contrast_tail_exp_sum (d : ℕ) (v : Fin d → ℝ) :
    Real.exp ((∑ j, v j^2)/4) = ∏ j, Real.exp ((1/4:ℝ)*v j^2) := by
  rw [show (∑ j, v j^2)/4 = ∑ j, (1/4:ℝ)*v j^2 by
    rw [← Finset.mul_sum]; ring]
  exact Real.exp_sum _ _

lemma contrast_tail_scalar_mgf :
    (∫ x : ℝ, Real.exp ((1/4:ℝ)*x^2) ∂gaussianReal 0 1) =
      (2:ℝ)^(1/(2:ℝ)) := by
  rw [StatLean.MultipleTesting.mgf_exp_sq_stdGaussian (by norm_num)]
  rw [show (1:ℝ)-2*(1/4) = 1/2 by norm_num,
    show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.sqrt_inv, inv_inv,
    Real.sqrt_eq_rpow]
  norm_num

lemma contrast_tail_chi_squared_mgf (d : ℕ) :
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
    simpa only [Function.comp_def, S, contrast_tail_exp_sum] using hprod
  have hInt : Integrable (fun x : ℝ => Real.exp (x/4)) (ν.map S) :=
    (integrable_map_measure hExp.aestronglyMeasurable hS.aemeasurable).mpr hcomp
  refine ⟨hInt, ?_⟩
  change (∫ x : ℝ, Real.exp (x/4) ∂ν.map S) = _
  rw [integral_map hS.aemeasurable hExp.aestronglyMeasurable]
  simp only [S, contrast_tail_exp_sum]
  dsimp [ν]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin d => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => Real.exp ((1/4:ℝ)*x^2))]
  simp only [contrast_tail_scalar_mgf, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

lemma contrast_tail_transfer_mgf {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (L : Ξ → ℝ) (hL : AEMeasurable L μ) (d : ℕ)
    (hlaw : μ.map L = chiSquaredLaw d) :
    Integrable (fun ξ => Real.exp (L ξ/4)) μ ∧
    (∫ ξ, Real.exp (L ξ/4) ∂μ) = (2:ℝ)^((d:ℝ)/2) := by
  have hmgf := contrast_tail_chi_squared_mgf d
  have hInt : Integrable (fun x : ℝ => Real.exp (x/4)) (μ.map L) :=
    hlaw.symm ▸ hmgf.1
  refine ⟨hInt.comp_aemeasurable hL, ?_⟩
  rw [← integral_map hL hInt.aestronglyMeasurable, hlaw]
  exact hmgf.2

/-- The exponential average estimate, without any independence hypothesis. -/
lemma contrast_tail_average_exp_le {K : ℕ} (hK : 0 < K) (L : Fin K → ℝ) :
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

/-- All hypotheses here are explicit helper inputs. `hLower` will be supplied by
an actual low-component construction, not by the held Gaussian-law declaration. -/
lemma contrast_tail_dependent_average_markov {Ξ : Type} [MeasurableSpace Ξ]
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
    contrast_tail_average_exp_le hK (fun i => L i ξ)
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
      _ ≤ ∫ ξ, F ξ ∂μ := by simpa [F, measureReal_def, mul_comm] using hm
      _ ≤ M := hFmean
  calc
    _ ≤ M/Real.exp (ℓ/(4*k)) := hbound
    _ = Real.exp (-ℓ/(4*k))*M := by
      rw [div_eq_mul_inv, ← Real.exp_neg, neg_div]
      ring


lemma contrast_tail_parameter_signs (r m : ℕ) (hr : 0 < r) (hm : 2 ≤ m)
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

/-- Complete tail assembly once measurable chi-square low components and their
pointwise contrast lower bounds have been constructed. This helper explicitly
records the one input which is still missing for the unconditional node. -/
lemma contrast_tail_from_low_components {Ξ : Type} [MeasurableSpace Ξ]
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
  have hmgf (i : Fin K) := contrast_tail_transfer_mgf μ (L i) (hLm i) d (hLaw i)
  refine ⟨contrast_tail_dependent_average_markov μ K hK T L k ℓ
    ((2:ℝ)^((d:ℝ)/2)) hk hLm hLower
    (fun i => (hmgf i).1) (fun i => (hmgf i).2.le), ?_⟩
  intro h
  simpa only [neg_div] using contrast_tail_binary_comparison (ℓ/(4*k)) (d:ℝ)
    (div_pos hℓ (by positivity)) (Nat.cast_nonneg d) h

/- The unconditional contrast_gaussian_tail_proof is deliberately not asserted:
its low-component input has not yet been proved in this worktree. -/

/-! ## Record 7: the periodic systematic bridge -/

lemma periodic_prefix_sum (n j : ℕ) (hj : j ≤ n) (c : ℝ) :
    (∑ i : Fin n, if i.val < j then c else 0) = (j:ℝ)*c := by
  induction n generalizing j with
  | zero =>
      have : j = 0 := by omega
      subst j
      simp
  | succ n ih =>
      cases j with
      | zero => simp
      | succ j =>
          have hj' : j ≤ n := by omega
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Nat.zero_lt_succ, if_true, Fin.val_succ,
            Nat.succ_lt_succ_iff]
          rw [ih j hj']
          push_cast
          ring

/-- Base-Q comparison, used only with bounded within-block offsets. -/
lemma periodic_index_lex (Q a b i j : ℕ) (ha : a < Q) (hb : b < Q) :
    a+Q*i < b+Q*j ↔ i < j ∨ (i = j ∧ a < b) := by
  constructor
  · intro h
    by_cases hij : i < j
    · exact Or.inl hij
    · right
      have hji : j ≤ i := le_of_not_gt hij
      have heq : i = j := by
        by_contra hne
        have hstep : j+1 ≤ i := by omega
        have hmul : Q*(j+1) ≤ Q*i := Nat.mul_le_mul_left Q hstep
        nlinarith
      exact ⟨heq, by simpa [heq] using h⟩
  · rintro (hij | ⟨rfl, hab⟩)
    · have hstep : i+1 ≤ j := by omega
      have hmul : Q*(i+1) ≤ Q*j := Nat.mul_le_mul_left Q hstep
      nlinarith
    · omega

lemma periodic_offset_lt {r : ℕ} (g : Fin r × Fin 2) :
    2*g.1.val+g.2.val < 2*r := by
  have hi := g.1.isLt
  have hb := g.2.isLt
  omega

lemma periodic_block_term {r m : ℕ}
    (g : Fin r × Fin 2) (j : Fin m)
    (k : Σ _ : Fin r × Fin 2, Fin m) :
    (if phaseIndex ⟨g,j⟩ < phaseIndex k then phaseSize ⟨g,j⟩ else 0) =
      (if j.val < k.2.val then (if g.2 = 0 then (2:ℝ) else 10) else 0) +
      (if j = k.2 then
        (if 2*g.1.val+g.2.val < 2*k.1.1.val+k.1.2.val then
          (if g.2 = 0 then (2:ℝ) else 10) else 0) else 0) := by
  have hlex := periodic_index_lex (2*r) (2*g.1.val+g.2.val)
    (2*k.1.1.val+k.1.2.val) j.val k.2.val
    (periodic_offset_lt g) (periodic_offset_lt k.1)
  simp only [phaseIndex, phaseSize]
  simp only [hlex]
  by_cases hj : j.val < k.2.val
  · have hjne : j ≠ k.2 := by intro h; subst j; omega
    simp [hj, hjne]
  · by_cases heq : j = k.2
    · subst j
      simp
    · have hvne : j.val ≠ k.2.val := fun h => heq (Fin.ext h)
      simp [hj, heq, hvne]

lemma periodic_phase_prefix {r : ℕ} (g : Fin r × Fin 2) :
    (∑ h : Fin r × Fin 2,
      if 2*h.1.val+h.2.val < 2*g.1.val+g.2.val then
        (if h.2 = 0 then (2:ℝ) else 10) else 0) = phaseStartLeft g := by
  rcases g with ⟨i,b⟩
  have hpair (a : Fin r) :
      (∑ t : Fin 2,
        if 2*a.val+t.val < 2*i.val+b.val then
          (if t = 0 then (2:ℝ) else 10) else 0) =
        (if a.val < i.val then (12:ℝ) else 0) +
          (if a = i then (if b = 0 then (0:ℝ) else 2) else 0) := by
    fin_cases b <;> simp only [Fin.sum_univ_two] <;>
      norm_num <;> split_ifs <;> norm_num [Fin.ext_iff] at * <;> omega
  rw [Fintype.sum_prod_type]
  simp_rw [hpair]
  rw [Finset.sum_add_distrib, periodic_prefix_sum r i.val (Nat.le_of_lt i.isLt)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, phaseStartLeft]
  ring

lemma periodic_predecessor_sum {r m : ℕ}
    (k : Σ _ : Fin r × Fin 2, Fin m) :
    (∑ a : Σ _ : Fin r × Fin 2, Fin m,
      if phaseIndex a < phaseIndex k then phaseSize a else 0) =
        phaseStartLeft k.1+12*r*(k.2:ℝ) := by
  have hblock (g : Fin r × Fin 2) :
      (∑ j : Fin m,
        if phaseIndex ⟨g,j⟩ < phaseIndex k then phaseSize ⟨g,j⟩ else 0) =
      (k.2:ℝ)*(if g.2 = 0 then (2:ℝ) else 10) +
        (if 2*g.1.val+g.2.val < 2*k.1.1.val+k.1.2.val then
          (if g.2 = 0 then (2:ℝ) else 10) else 0) := by
    simp_rw [periodic_block_term]
    rw [Finset.sum_add_distrib,
      periodic_prefix_sum m k.2.val (Nat.le_of_lt k.2.isLt)]
    simp
  rw [Fintype.sum_sigma]
  simp_rw [hblock]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, periodic_phase_prefix]
  have htotal :
      (∑ g : Fin r × Fin 2, if g.2 = 0 then (2:ℝ) else 10) = 12*r := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_two]
    <;> ring
  rw [htotal]
  ring

/-- Uniqueness of a block for a point in half-open consecutive grid intervals. -/
lemma periodic_grid_unique (Q x : ℝ) (hQ : 0 < Q) (i j : ℕ)
    (hi₀ : Q*(i:ℝ) ≤ x) (hi₁ : x < Q*((i:ℝ)+1))
    (hj₀ : Q*(j:ℝ) ≤ x) (hj₁ : x < Q*((j:ℝ)+1)) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · have hstep : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hij)
    have hmul := mul_le_mul_of_nonneg_left hstep hQ.le
    nlinarith
  · exact hij
  · have hstep : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hji)
    have hmul := mul_le_mul_of_nonneg_left hstep hQ.le
    nlinarith

lemma periodic_pair_bounds {r : ℕ} (g : Fin r × Fin 2) :
    12*(g.1:ℝ) ≤ phaseStartLeft g ∧
    phaseStartLeft g+(if g.2 = 0 then (2:ℝ) else 10) ≤ 12*((g.1:ℝ)+1) := by
  rcases g with ⟨i,b⟩
  fin_cases b <;> norm_num [phaseStartLeft] <;> linarith

lemma periodic_interval_bounds {r : ℕ} (g : Fin r × Fin 2) :
    0 ≤ phaseStartLeft g ∧
    phaseStartLeft g+(if g.2 = 0 then (2:ℝ) else 10) ≤ 12*r := by
  have hpair := periodic_pair_bounds g
  have hi : (g.1:ℝ)+1 ≤ (r:ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt g.1.isLt)
  constructor
  · exact le_trans (by positivity) hpair.1
  · linarith [hpair.2]

lemma periodic_start_unique {r : ℕ} (g h : Fin r × Fin 2) (u : ℝ)
    (hg₀ : phaseStartLeft g ≤ u)
    (hg₁ : u < phaseStartLeft g+(if g.2 = 0 then 2 else 10))
    (hh₀ : phaseStartLeft h ≤ u)
    (hh₁ : u < phaseStartLeft h+(if h.2 = 0 then 2 else 10)) : g = h := by
  have bg := periodic_pair_bounds g
  have bh := periodic_pair_bounds h
  have hi : g.1.val = h.1.val := periodic_grid_unique 12 u (by norm_num)
    g.1.val h.1.val (le_trans bg.1 hg₀) (lt_of_lt_of_le hg₁ bg.2)
    (le_trans bh.1 hh₀) (lt_of_lt_of_le hh₁ bh.2)
  rcases g with ⟨i,b⟩
  rcases h with ⟨j,c⟩
  have hij : i = j := Fin.ext hi
  subst j
  have hbc : b = c := by
    fin_cases b <;> fin_cases c <;>
      norm_num [phaseStartLeft] at hg₀ hg₁ hh₀ hh₁ ⊢ <;> linarith
  subst c
  rfl

lemma periodic_start_partition (r : ℕ) (hr : 0 < r) (u : ℝ)
    (hu₀ : 0 ≤ u) (hu₁ : u < 12*r) :
    ∃! g : Fin r × Fin 2,
      phaseStartLeft g ≤ u ∧
        u < phaseStartLeft g+(if g.2 = 0 then 2 else 10) := by
  have hu12 : 0 ≤ u/12 := div_nonneg hu₀ (by norm_num)
  have hfloor : ⌊u/12⌋₊ < r := (Nat.floor_lt hu12).mpr (by
    apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 12)).mpr
    nlinarith)
  let i : Fin r := ⟨⌊u/12⌋₊, hfloor⟩
  have hleft : 12*(i:ℝ) ≤ u := by
    have hf := Nat.floor_le hu12
    change (⌊u/12⌋₊:ℝ) ≤ u/12 at hf
    dsimp [i]
    linarith
  have hright : u < 12*((i:ℝ)+1) := by
    have hf := Nat.lt_floor_add_one (u/12)
    dsimp [i]
    linarith
  have hex : ∃ g : Fin r × Fin 2,
      phaseStartLeft g ≤ u ∧
        u < phaseStartLeft g+(if g.2 = 0 then 2 else 10) := by
    by_cases hlow : u < 12*(i:ℝ)+2
    · refine ⟨(i,0), ?_⟩
      simpa [phaseStartLeft] using And.intro hleft hlow
    · refine ⟨(i,1), ?_⟩
      norm_num [phaseStartLeft]
      constructor <;> linarith
  obtain ⟨g,hg⟩ := hex
  refine ⟨g,hg,?_⟩
  intro h hh
  exact periodic_start_unique h g u hh.1 hh.2 hg.1 hg.2

lemma periodic_selection_equivalence (r m : ℕ) (hr : 0 < r)
    (g : Fin r × Fin 2) (u : ℝ)
    (hg₀ : phaseStartLeft g ≤ u)
    (hg₁ : u < phaseStartLeft g+(if g.2 = 0 then 2 else 10))
    (k : Σ _ : Fin r × Fin 2, Fin m) :
    ((∃ j : Fin m,
      (∑ a : Σ _ : Fin r × Fin 2, Fin m,
        if phaseIndex a < phaseIndex k then phaseSize a else 0) ≤
          u+(j:ℝ)*(12*r) ∧
      u+(j:ℝ)*(12*r) <
        (∑ a : Σ _ : Fin r × Fin 2, Fin m,
          if phaseIndex a < phaseIndex k then phaseSize a else 0)+phaseSize k) ↔
      (phaseOriginal r m hr).selected g k = true) := by
  have hQ : (0:ℝ) < 12*r := by positivity
  have bg := periodic_interval_bounds g
  have bk := periodic_interval_bounds k.1
  have hu₀ : 0 ≤ u := le_trans bg.1 hg₀
  have hu₁ : u < 12*r := lt_of_lt_of_le hg₁ bg.2
  simp only [phaseOriginal, liftDesign, phaseGrouped, oneDraw]
  simp only [decide_eq_true_eq]
  simp only [periodic_predecessor_sum]
  constructor
  · rintro ⟨j,hj₀,hj₁⟩
    have hjblock₀ : (12*(r:ℝ))*(j:ℝ) ≤ u+(j:ℝ)*(12*r) := by nlinarith
    have hjblock₁ : u+(j:ℝ)*(12*r) < (12*(r:ℝ))*((j:ℝ)+1) := by nlinarith
    have hkblock₀ : (12*(r:ℝ))*(k.2:ℝ) ≤ u+(j:ℝ)*(12*r) := by
      nlinarith [bk.1]
    have hkblock₁ : u+(j:ℝ)*(12*r) < (12*(r:ℝ))*((k.2:ℝ)+1) := by
      change _ < phaseStartLeft k.1+12*r*(k.2:ℝ)+
        (if k.1.2 = 0 then (2:ℝ) else 10) at hj₁
      nlinarith [bk.2]
    have hjk : j = k.2 := Fin.ext (periodic_grid_unique (12*r)
      (u+(j:ℝ)*(12*r)) hQ j.val k.2.val
      hjblock₀ hjblock₁ hkblock₀ hkblock₁)
    subst j
    have hk₀ : phaseStartLeft k.1 ≤ u := by nlinarith [hj₀]
    have hk₁ : u < phaseStartLeft k.1+(if k.1.2 = 0 then 2 else 10) := by
      change _ < phaseStartLeft k.1+12*r*(k.2:ℝ)+
        (if k.1.2 = 0 then (2:ℝ) else 10) at hj₁
      nlinarith [hj₁]
    exact periodic_start_unique g k.1 u hg₀ hg₁ hk₀ hk₁
  · intro hgk
    refine ⟨k.2, ?_, ?_⟩
    · have h := hg₀
      rw [hgk] at h
      nlinarith
    · have h := hg₁
      rw [hgk] at h
      change _ < phaseStartLeft k.1+12*r*(k.2:ℝ)+
        (if k.1.2 = 0 then (2:ℝ) else 10)
      nlinarith

/-- Exact original statement, including all four conjuncts and all endpoints. -/
theorem periodic_systematic_bridge_proof (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    (∀ k : Σ _ : Fin r × Fin 2, Fin m,
      (∑ a : Σ _ : Fin r × Fin 2, Fin m, if phaseIndex a < phaseIndex k then phaseSize a else 0) =
        phaseStartLeft k.1+12*r*(k.2:ℝ)) ∧
    (∀ u : ℝ, 0 ≤ u → u < 12*r → ∃! g : Fin r × Fin 2,
      phaseStartLeft g ≤ u ∧ u < phaseStartLeft g+(if g.2 = 0 then 2 else 10)) ∧
    (∀ (g : Fin r × Fin 2) (u : ℝ),
      phaseStartLeft g ≤ u → u < phaseStartLeft g+(if g.2 = 0 then 2 else 10) →
      ∀ k : Σ _ : Fin r × Fin 2, Fin m,
        ((∃ j : Fin m, (∑ a : Σ _ : Fin r × Fin 2, Fin m, if phaseIndex a < phaseIndex k then phaseSize a else 0) ≤
          u+(j:ℝ)*(12*r) ∧ u+(j:ℝ)*(12*r) <
          (∑ a : Σ _ : Fin r × Fin 2, Fin m, if phaseIndex a < phaseIndex k then phaseSize a else 0)+phaseSize k) ↔
          (phaseOriginal r m hr).selected g k = true)) ∧
    (∀ g, phaseProb r g = (if g.2 = 0 then 2 else 10)/(12*r)) := by
  refine ⟨periodic_predecessor_sum, periodic_start_partition r hr,
    periodic_selection_equivalence r m hr, ?_⟩
  intro g
  have hrr : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold phaseProb
  split_ifs <;> field_simp [hrr] <;> ring

example : type_of% @AronowAudit.P027.periodic_systematic_bridge :=
  periodic_systematic_bridge_proof

end
end AronowAudit.P027.Wave1
