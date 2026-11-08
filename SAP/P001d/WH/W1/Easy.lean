import SAP.P001d.Defs.WholeW1
import SAP.P001d.Bridge
import AronowAudit.P039.P039_Regression

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W1

/-- Instantiation, normalization and positivity of the two covariance estimates. -/
theorem whole66 : T66WholeStatement := by
  intro n K hn X Y hinter hX
  let β := olsCoef X Y
  let e := Y - X.mulVec β
  let s2 := wholeEmpiricalVariance e
  let A : Matrix (Fin (K+1)) (Fin (K+1)) ℝ := fun j k =>
    (∑ i, X i j * X i k) / (n : ℝ)
  let B : Matrix (Fin (K+1)) (Fin (K+1)) ℝ := fun j k =>
    (∑ i, (e i)^2 * X i j * X i k) / (n : ℝ)
  have hfit := AronowAudit.P001.ols_correct_rows_solution_residuals X Y hX hinter
  have hsum : ∑ i, e i = 0 := hfit.2.2
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs : s2 = (∑ i, (e i)^2) / ((n : ℝ) - 1) := by
    dsimp [s2, wholeEmpiricalVariance]
    rw [hsum]
    simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero]
    field_simp
  have hs0 : 0 ≤ s2 := by
    rw [hs]
    exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg (e i))) hn1.le
  have hA : A = (n : ℝ)⁻¹ • (X.transpose * X) := by
    ext j k
    simp only [A, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hB : B = (n : ℝ)⁻¹ • (X.transpose * Matrix.diagonal (fun i => (e i)^2) * X) := by
    ext j k
    change (∑ i, (e i)^2 * X i j * X i k) / (n : ℝ) =
      (n : ℝ)⁻¹ * ((X.transpose * Matrix.diagonal (fun i => (e i)^2)) * X) j k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    rw [div_eq_mul_inv, mul_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hInv : A⁻¹ = (n : ℝ) • (X.transpose * X)⁻¹ := by
    rw [hA]
    simpa only [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv] using
      Matrix.inv_smul' (X.transpose * X) (Units.mk0 (n : ℝ)⁻¹ (inv_ne_zero hnR)) hX
  have hR : (n : ℝ)⁻¹ • (A⁻¹ * B * A⁻¹) = robustCov X e := by
    rw [hInv, hB]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hnR, one_smul, robustCov]
  have hC : (s2 / (n : ℝ)) • A⁻¹ = classicalCov X s2 := by
    rw [hInv]
    simp only [smul_smul, div_mul_cancel₀ _ hnR, classicalCov]
  have hG : (X.transpose * X).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self X
  have hM : (X.transpose * Matrix.diagonal (fun i => (e i)^2) * X).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosSemidef.diagonal (fun i => sq_nonneg (e i))).conjTranspose_mul_mul_same X
  have hr : (robustCov X e).PosSemidef := by
    have h := hM.conjTranspose_mul_mul_same (X.transpose * X)⁻¹
    simpa only [hG.inv.isHermitian.eq, robustCov] using h
  have hc : (classicalCov X s2).PosSemidef := hG.inv.smul hs0
  refine ⟨hfit.1, ?_, hs, hs0, hA, hB, hR, hC, ?_⟩
  · rw [hsum, zero_div]
  · intro k
    refine ⟨hr.diag_nonneg, hc.diag_nonneg, ?_, ?_⟩
    · rw [hR]; rfl
    · rw [hC]; rfl

/-- The logarithm of the strictly positive displayed normal density. -/
theorem density_log (m s y : ℝ) (hs : 0 < s) :
    0 < normalDensity m s y ∧
    Real.log (normalDensity m s y) =
      Real.log (1 / (s * Real.sqrt (2 * Real.pi))) - (y-m)^2 / (2*s^2) ∧
    Real.log (normalDensity m s y) =
      -Real.log s - Real.log (2*Real.pi)/2 - (y-m)^2 / (2*s^2) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 hp
  have hden : 0 < s * Real.sqrt (2 * Real.pi) := mul_pos hs hsp
  have hlog : Real.log (normalDensity m s y) =
      Real.log (1 / (s * Real.sqrt (2 * Real.pi))) - (y-m)^2 / (2*s^2) := by
    rw [normalDensity, Real.log_div (Real.exp_pos _).ne' hden.ne', Real.log_exp,
      Real.log_div (by norm_num) hden.ne', Real.log_one]
    ring
  refine ⟨by unfold normalDensity; positivity, hlog, ?_⟩
  rw [hlog, Real.log_div (by norm_num) hden.ne', Real.log_one,
    Real.log_mul hs.ne' hsp.ne', Real.log_sqrt hp.le]
  ring

/-- The product, logarithm, optimizer equivalence and full-rank formula. -/
theorem whole76 : T76WholeStatement := by
  intro n K X Y
  have hd (b : Fin (K+1) → ℝ) (s : ℝ) (hs : 0 < s) :=
    fun i : Fin n => density_log ((X.mulVec b) i) s (Y i) hs
  have hpos (b : Fin (K+1) → ℝ) (s : ℝ) (hs : 0 < s) :
      0 < wholeNormalLikelihood X Y b s :=
    Finset.prod_pos (fun i _ => (hd b s hs i).1)
  have hsum (b : Fin (K+1) → ℝ) (s : ℝ) (hs : 0 < s) :
      Real.log (wholeNormalLikelihood X Y b s) =
        ∑ i, (Real.log (1 / (s * Real.sqrt (2 * Real.pi))) -
          (Y i - (X.mulVec b) i)^2 / (2 * s^2)) := by
    rw [wholeNormalLikelihood, Real.log_prod (fun i _ => (hd b s hs i).1.ne')]
    exact Finset.sum_congr rfl (fun i _ => (hd b s hs i).2.1)
  have hlog (b : Fin (K+1) → ℝ) (s : ℝ) (hs : 0 < s) :
      Real.log (wholeNormalLikelihood X Y b s) = normalLogLikelihood X Y b s := by
    rw [wholeNormalLikelihood, Real.log_prod (fun i _ => (hd b s hs i).1.ne')]
    simp_rw [(hd b s hs _).2.2]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, normalLogLikelihood, olsRSS]
    ring
  have he (b : Fin (K+1) → ℝ) (s : ℝ) (hs : 0 < s) :
      (∀ c, normalLogLikelihood X Y c s ≤ normalLogLikelihood X Y b s) ↔
        (∀ c, olsRSS X Y b ≤ olsRSS X Y c) :=
    AronowAudit.P001.normal_fixed_scale_ml_is_ols X Y b s hs
  have hl (b : Fin (K+1) → ℝ) (s : ℝ) (hs : 0 < s) :
      (∀ c, wholeNormalLikelihood X Y c s ≤ wholeNormalLikelihood X Y b s) ↔
        (∀ c, normalLogLikelihood X Y c s ≤ normalLogLikelihood X Y b s) := by
    simp only [← hlog _ s hs, Real.log_le_log_iff (hpos _ s hs) (hpos _ s hs)]
  refine ⟨?_, fun b s hs => ⟨hl b s hs, he b s hs⟩, ?_, ?_, ?_⟩
  · intro b s hs
    refine ⟨?_, hpos b s hs, hsum b s hs, hlog b s hs⟩
    apply Finset.prod_congr rfl
    intro i _
    unfold normalDensity
    ring
  · intro b s t hs ht
    exact (hl b s hs).trans ((he b s hs).trans ((he b t ht).symm.trans (hl b t ht).symm))
  · intro hX s hs
    have hinj : Function.Injective X.mulVec := by
      intro a b hab
      have h := congrArg X.transpose.mulVec hab
      simp only [Matrix.mulVec_mulVec] at h
      exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hX) h
    have hls := AronowAudit.P039.full_rank_ols_unique X Y hinj
    have heq (b : Fin (K+1) → ℝ) :
        (∀ c, wholeNormalLikelihood X Y c s ≤ wholeNormalLikelihood X Y b s) ↔
          b = olsCoef X Y := by
      rw [hl b s hs, he b s hs]
      constructor
      · intro hb
        apply hls.2 b
        simpa only [AronowAudit.P039.IsLeastSquares, AronowAudit.P039.squaredLength,
          dotProduct, Pi.sub_apply, olsRSS, pow_two] using hb
      · rintro rfl
        simpa only [AronowAudit.P039.IsLeastSquares, AronowAudit.P039.squaredLength,
          AronowAudit.P039.ols, dotProduct, Pi.sub_apply, olsCoef, olsRSS, pow_two] using hls.1
    refine ⟨heq, olsCoef X Y, (heq _).mpr rfl, fun b hb => (heq b).mp hb⟩
  · intro hn b
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [div_le_div_iff_of_pos_right hnR]

/-- Finite atomic integration needs no measurability of the integrand away from
the observations. In particular it applies to every chosen fitted CEF. -/
theorem empirical_integral {d n : ℕ} (hn : 0 < n) (x : Fin n → Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) :
    IsProbabilityMeasure (wholeEmpiricalLaw x) ∧
    Integrable f (wholeEmpiricalLaw x) ∧
    (∫ z, f z ∂wholeEmpiricalLaw x) = (1/(n : ℝ)) * ∑ i, f (x i) := by
  have hf (i : Fin n) : Integrable f (Measure.dirac (x i)) := integrable_dirac (by simp)
  have hsum : Integrable f (∑ i, Measure.dirac (x i)) :=
    integrable_finsetSum_measure.mpr (fun i _ => hf i)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnE : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨?_⟩, hsum.smul_measure (by simp), ?_⟩
  · simp only [wholeEmpiricalLaw, Measure.smul_apply, smul_eq_mul,
      Measure.finsetSum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [ENNReal.ofReal_div_of_pos hnR]
    simpa using ENNReal.inv_mul_cancel hnE (by simp)
  · rw [wholeEmpiricalLaw, integral_smul_measure,
      integral_finsetSum_measure (fun i _ => hf i)]
    simp only [integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal (by positivity :
      (0 : ℝ) ≤ 1/(n : ℝ))]

/-- Uniform branch probabilities and the empirical APD formula. -/
theorem whole69 : T69WholeStatement := by
  constructor
  · intro Ω _ μ _ X1 X2 Y h1 h2 hY hi hl1 hl2 hm
    have h := AronowAudit.P001.apd_pda_different_correct_coordinate μ X1 X2 Y
      h1 h2 hY hi hl1 hl2 ((Bridge.cef_iff _ _ _ _).mp hm)
    have hp : prob μ {ω | X2 ω ≤ 4/5} = 4/5 := by
      have hs : Set.Iic (4/5 : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 (4/5 : ℝ) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨hx, h0, _h1⟩
          exact ⟨h0, hx⟩
        · rintro ⟨h0, hx⟩
          exact ⟨hx, h0, by linarith⟩
      change (μ (X2 ⁻¹' Set.Iic (4/5 : ℝ))).toReal = 4/5
      rw [← Measure.map_apply h2 measurableSet_Iic, hl2]
      change (AronowAudit.P001.uniformLaw 0 1 (Set.Iic (4/5 : ℝ))).toReal = 4/5
      rw [AronowAudit.P001.uniformLaw_zero_one_eq_restrict,
        Measure.restrict_apply measurableSet_Iic, hs, Real.volume_Icc]
      norm_num
    have hpc : prob μ {ω | 4/5 < X2 ω} = 1/5 := by
      have hc := probReal_compl_eq_one_sub (μ := μ) (h2 measurableSet_Iic :
        MeasurableSet {ω | X2 ω ≤ (4/5 : ℝ)})
      change prob μ {ω | X2 ω ≤ 4/5}ᶜ = 1 - prob μ {ω | X2 ω ≤ 4/5} at hc
      have he : {ω | X2 ω ≤ (4/5 : ℝ)}ᶜ = {ω | 4/5 < X2 ω} := by ext; simp
      rw [he, hp] at hc
      norm_num at hc ⊢
      exact hc
    have hd (x y : ℝ) : HasDerivAt (fun t => apdExample t y)
        (if y ≤ 4/5 then -1 else 9) x := by
      by_cases hy : y ≤ 4/5
      · simp only [apdExample, ite_eq_left hy]
        exact (hasDerivAt_id x).neg
      · simp only [apdExample, ite_eq_right hy]
        simpa using (hasDerivAt_id x).const_mul 9
    have hdi : Integrable (fun ω => deriv (fun t => apdExample t (X2 ω)) (X1 ω)) μ := by
      simp_rw [fun x y => (hd x y).deriv]
      exact Integrable.of_bound
        ((measurable_const.piecewise (h2 measurableSet_Iic) measurable_const).aestronglyMeasurable)
        9 (ae_of_all _ (fun ω => by split_ifs <;> norm_num))
    refine ⟨hd, hp, hpc, h.2.1, h.2.2.1, hdi, ?_, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2⟩
    have hapd : (∫ ω, deriv (fun t => apdExample t (X2 ω)) (X1 ω) ∂μ) = 1 :=
      h.2.2.2.1
    rw [hapd, hp, hpc]
    norm_num
  · intro d n hn x mhat k _hd
    exact empirical_integral hn x (fun z => wholePartial mhat z k)

end SAP.P001d.WH.W1
