import AronowAudit.External.Causalean.Stat.Coupling.Monotone.ProductLoss.Optimality
import AronowAudit.External.Causalean.Stat.Quantile.Transport
import AronowAudit.P022.Wave1.SharpBounds.N1
import AronowAudit.P022.Wave1.SharpBounds.N2
import AronowAudit.P022.Wave1.SharpBounds.N5
import Mathlib.Probability.Moments.Covariance

/-! Bridges between finite empirical CDF conventions and the general quantile library. -/

open MeasureTheory ProbabilityTheory Set Causalean.Stat AronowAudit.P022
open AronowAudit.P022.Wave1
open scoped BigOperators

noncomputable section

/-- The treatment marginal CDF is the CDF of the first marginal measure. -/
theorem TailB_lawCDF_eq_cdf_fst (H : JointLaw) (x : ℝ) :
    lawCDF H true x = cdf ((H : Measure (ℝ × ℝ)).map Prod.fst) x := by
  rw [cdf_eq_real, measureReal_def, Measure.map_apply measurable_fst measurableSet_Iic]
  rfl

/-- The control marginal CDF is the CDF of the second marginal measure. -/
theorem TailB_lawCDF_eq_cdf_snd (H : JointLaw) (x : ℝ) :
    lawCDF H false x = cdf ((H : Measure (ℝ × ℝ)).map Prod.snd) x := by
  rw [cdf_eq_real, measureReal_def, Measure.map_apply measurable_snd measurableSet_Iic]
  rfl

/-- Equality of both marginal CDFs is exactly equality of both marginal measures. -/
theorem TailB_compatibleLaws_iff_marginals (H J : JointLaw) :
    J ∈ compatibleLaws H ↔
      (J : Measure (ℝ × ℝ)).map Prod.fst = (H : Measure (ℝ × ℝ)).map Prod.fst ∧
      (J : Measure (ℝ × ℝ)).map Prod.snd = (H : Measure (ℝ × ℝ)).map Prod.snd := by
  constructor
  · intro h
    constructor
    · apply Measure.eq_of_cdf
      ext x
      simpa only [← TailB_lawCDF_eq_cdf_fst] using h true x
    · apply Measure.eq_of_cdf
      ext x
      simpa only [← TailB_lawCDF_eq_cdf_snd] using h false x
  · rintro ⟨h1, h0⟩ t x
    cases t
    · simp only [TailB_lawCDF_eq_cdf_snd, h0]
    · simp only [TailB_lawCDF_eq_cdf_fst, h1]

/-- Compatibility transports both means, including the totalized integral convention. -/
theorem TailB_lawMean_eq_of_compatible (H J : JointLaw) (h : J ∈ compatibleLaws H)
    (t : Bool) : lawMean J t = lawMean H t := by
  obtain ⟨h1, h0⟩ := (TailB_compatibleLaws_iff_marginals H J).mp h
  cases t
  · change (∫ p, p.2 ∂(J : Measure (ℝ × ℝ))) = ∫ p, p.2 ∂(H : Measure (ℝ × ℝ))
    calc
      _ = ∫ x : ℝ, x ∂((J : Measure (ℝ × ℝ)).map Prod.snd) :=
        (integral_map measurable_snd.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = ∫ x : ℝ, x ∂((H : Measure (ℝ × ℝ)).map Prod.snd) := by rw [h0]
      _ = _ := integral_map measurable_snd.aemeasurable measurable_id.aestronglyMeasurable
  · change (∫ p, p.1 ∂(J : Measure (ℝ × ℝ))) = ∫ p, p.1 ∂(H : Measure (ℝ × ℝ))
    calc
      _ = ∫ x : ℝ, x ∂((J : Measure (ℝ × ℝ)).map Prod.fst) :=
        (integral_map measurable_fst.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = ∫ x : ℝ, x ∂((H : Measure (ℝ × ℝ)).map Prod.fst) := by rw [h1]
      _ = _ := integral_map measurable_fst.aemeasurable measurable_id.aestronglyMeasurable

/-- The covariance definition agrees with the product-minus-means formula under L2. -/
theorem TailB_lawCovariance_eq_sub (J : JointLaw)
    (h1 : MemLp (fun z : ℝ × ℝ => z.1) 2 (J : Measure (ℝ × ℝ)))
    (h0 : MemLp (fun z : ℝ × ℝ => z.2) 2 (J : Measure (ℝ × ℝ))) :
    lawCovariance J = (∫ z, z.1 * z.2 ∂(J : Measure (ℝ × ℝ))) -
      lawMean J true * lawMean J false := by
  simpa only [covariance, lawCovariance, lawMean, Bool.false_eq_true, if_false, if_true,
    Pi.mul_apply] using covariance_eq_sub h1 h0

/-- The countermonotone product expectation has the reflected-quantile form. -/
theorem TailB_product_expectation_countermonotoneCoupling (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∫ z, z.1 * z.2 ∂countermonotoneCoupling μ ν) =
      ∫ u in Ioo (0 : ℝ) 1, quantile μ u * quantile ν (1 - u) := by
  have hr : Measurable (fun u : ℝ => 1 - u) := measurable_const.sub measurable_id
  have hν : AEMeasurable (quantile ν) (unifOI.map (fun u : ℝ => 1 - u)) := by
    rw [map_one_sub_unifOI]
    exact aemeasurable_quantile_unifOI ν
  unfold countermonotoneCoupling
  rw [integral_map]
  · rfl
  · exact (aemeasurable_quantile_unifOI μ).prodMk (hν.comp_measurable hr)
  · fun_prop

/-- Open-unit and interval integrals agree without an integrability premise. -/
theorem TailB_integral_Ioo_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ u in Ioo (0 : ℝ) 1, f u) = ∫ u in (0 : ℝ)..1, f u := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]

/-- The finite empirical marginal measure. -/
noncomputable def TailB_empiricalLaw {N : ℕ} [NeZero N] (y : Fin N → ℝ) :
    ProbabilityMeasure ℝ :=
  (SharpBounds.unitLaw N).map y

/-- Its CDF is the literal finite indicator average. -/
theorem TailB_cdf_empiricalLaw {N : ℕ} [NeZero N] (y : Fin N → ℝ) (x : ℝ) :
    cdf (TailB_empiricalLaw y : Measure ℝ) x = empiricalCDF y x := by
  rw [cdf_eq_real, measureReal_def, TailB_empiricalLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_of_finite y) measurableSet_Iic, SharpBounds.measure_unitLaw]
  rfl

private theorem TailB_empiricalCDF_sorted_brackets {N : ℕ} (y : Fin N → ℝ) (j : Fin N) :
    ((j : ℝ) + 1) / N ≤ empiricalCDF y (sortedValues y j) ∧
    ∀ x < sortedValues y j, empiricalCDF y x ≤ (j : ℝ) / N := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := j.isLt; omega)
  have hm := (SharpBounds.n2_proof y).2.2
  have cdf (x : ℝ) : empiricalCDF y x =
      (∑ i : Fin N, if sortedValues y i ≤ x then (1 : ℝ) else 0) / N := by
    rw [← SharpBounds.cdf_perm SharpBounds.n1_proof (SharpBounds.n2_proof y).1 x]
    simp only [empiricalCDF, finiteMean, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  have hic : (∑ i : Fin N, if i ≤ j then (1 : ℝ) else 0) = (j : ℝ) + 1 := by
    rw [← Finset.sum_filter]
    simp [Finset.filter_ge_eq_Iic]
  have hio : (∑ i : Fin N, if i < j then (1 : ℝ) else 0) = (j : ℝ) := by
    rw [← Finset.sum_filter]
    simp [Finset.filter_gt_eq_Iio]
  constructor
  · rw [cdf, ← hic]
    apply div_le_div_of_nonneg_right _ hN.le
    apply Finset.sum_le_sum
    intro i _
    by_cases hij : i ≤ j
    · simp [hij, hm hij]
    · simp [hij]
      split_ifs <;> norm_num
  · intro x hx
    rw [cdf, ← hio]
    apply div_le_div_of_nonneg_right _ hN.le
    apply Finset.sum_le_sum
    intro i _
    by_cases hij : i < j
    · simp [hij]
      split_ifs <;> norm_num
    · have hnot : ¬sortedValues y i ≤ x := by
        have := hm (le_of_not_gt hij)
        linarith
      simp [hij, hnot]

/-- On every interior level, the ceiling-rank quantile equals the general inverse CDF.
Repeated observations and jumps at atoms are allowed. -/
theorem TailB_empiricalQuantile_eq_quantile {N : ℕ} [NeZero N] (y : Fin N → ℝ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    empiricalQuantile y u = quantile (TailB_empiricalLaw y : Measure ℝ) u := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  let r := Nat.ceil ((N : ℝ) * u)
  have hr : 0 < r := Nat.ceil_pos.mpr (mul_pos hN hu0)
  have hrN : r ≤ N := Nat.ceil_le.mpr (by nlinarith)
  let j : Fin N := ⟨r - 1, by omega⟩
  have hjr : j.val + 1 = r := by dsimp [j]; omega
  have hcell := (Nat.ceil_eq_iff (ne_of_gt hr)).mp (show Nat.ceil ((N : ℝ) * u) = r from rfl)
  have hlo : (j : ℝ) / N < u := (div_lt_iff₀ hN).mpr (by simpa [j, mul_comm] using hcell.1)
  have hup : u ≤ ((j : ℝ) + 1) / N := by
    apply (le_div_iff₀ hN).mpr
    have he : (j : ℝ) + 1 = r := by exact_mod_cast hjr
    rw [he]
    simpa [mul_comm] using hcell.2
  have hq : empiricalQuantile y u = sortedValues y j := rfl
  rw [hq]
  apply le_antisymm
  · by_contra hlt
    have hlt' : quantile (TailB_empiricalLaw y : Measure ℝ) u < sortedValues y j :=
      lt_of_not_ge hlt
    have hb := (TailB_empiricalCDF_sorted_brackets y j).2 _ hlt'
    have hc := le_cdf_quantile (μ := (TailB_empiricalLaw y : Measure ℝ)) hu1
    rw [TailB_cdf_empiricalLaw] at hc
    linarith
  · apply quantile_le_of_le_cdf hu0
    rw [TailB_cdf_empiricalLaw]
    exact hup.trans (TailB_empiricalCDF_sorted_brackets y j).1

/-- The empirical/general quantile bridge on the fixed uniform-level space. -/
theorem TailB_empiricalQuantile_eq_quantile_ae {N : ℕ} [NeZero N] (y : Fin N → ℝ) :
    empiricalQuantile y =ᵐ[unifOI] quantile (TailB_empiricalLaw y : Measure ℝ) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  exact TailB_empiricalQuantile_eq_quantile y hu.1 hu.2

/-- Any single-quantile integral uses the same endpoint and inverse-CDF conventions. -/
theorem TailB_empiricalQuantile_integral_eq {N : ℕ} [NeZero N] (y : Fin N → ℝ)
    (f : ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, f (empiricalQuantile y u)) =
      ∫ u in Ioo (0 : ℝ) 1, f (quantile (TailB_empiricalLaw y : Measure ℝ) u) := by
  rw [← TailB_integral_Ioo_eq_intervalIntegral]
  exact integral_congr_ae ((TailB_empiricalQuantile_eq_quantile_ae y).fun_comp f)

/-- Integrals against the finite empirical law are exact finite averages. -/
theorem TailB_integral_empiricalLaw {N : ℕ} [NeZero N] (y : Fin N → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(TailB_empiricalLaw y : Measure ℝ)) = finiteMean (fun i => f (y i)) := by
  rw [TailB_empiricalLaw, ProbabilityMeasure.toMeasure_map,
    integral_map_of_stronglyMeasurable (measurable_of_finite _) hf.stronglyMeasurable,
    SharpBounds.integral_unitLaw]

/-- Aligned and reflected finite quantile products use the same general quantiles. -/
theorem TailB_empiricalQuantile_product_integral_eq {m k : ℕ} [NeZero m] [NeZero k]
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) :
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u *
      empiricalQuantile b (if B = .H then u else 1 - u)) =
    ∫ u in Ioo (0 : ℝ) 1, quantile (TailB_empiricalLaw a : Measure ℝ) u *
      quantile (TailB_empiricalLaw b : Measure ℝ) (if B = .H then u else 1 - u) := by
  rw [← TailB_integral_Ioo_eq_intervalIntegral]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  rw [TailB_empiricalQuantile_eq_quantile a hu.1 hu.2]
  cases B
  · simp only [if_true]
    rw [TailB_empiricalQuantile_eq_quantile b hu.1 hu.2]
  · simp only [reduceCtorEq, if_false]
    rw [TailB_empiricalQuantile_eq_quantile b (by linarith [hu.2]) (by linarith [hu.1])]

/-- The finite sharp-covariance formula expressed in general quantiles. -/
theorem TailB_sharpCovariance_eq_quantile {m k : ℕ} [NeZero m] [NeZero k]
    (a : Fin m → ℝ) (b : Fin k → ℝ) (B : BoundSide) :
    sharpCovariance a b B =
      (∫ u in Ioo (0 : ℝ) 1, quantile (TailB_empiricalLaw a : Measure ℝ) u *
        quantile (TailB_empiricalLaw b : Measure ℝ) (if B = .H then u else 1 - u)) -
      finiteMean a * finiteMean b := by
  rw [sharpCovariance, TailB_empiricalQuantile_product_integral_eq]

/-- General L2 Frechet bounds, with attained extrema over laws with the same marginals. -/
theorem TailB_frechet_covariance_L2
    (H : AronowAudit.P022.JointLaw)
    (h1 : MemLp (fun z : ℝ × ℝ => z.1) 2 (H : Measure (ℝ × ℝ)))
    (h0 : MemLp (fun z : ℝ × ℝ => z.2) 2 (H : Measure (ℝ × ℝ))) :
    let μ := (H : Measure (ℝ × ℝ)).map Prod.fst
    let ν := (H : Measure (ℝ × ℝ)).map Prod.snd
    let cplus := (∫ u in Set.Ioo (0 : ℝ) 1,
      Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν u) -
        AronowAudit.P022.lawMean H true * AronowAudit.P022.lawMean H false
    let cminus := (∫ u in Set.Ioo (0 : ℝ) 1,
      Causalean.Stat.quantile μ u * Causalean.Stat.quantile ν (1-u)) -
        AronowAudit.P022.lawMean H true * AronowAudit.P022.lawMean H false
    sSup (AronowAudit.P022.lawCovariance '' AronowAudit.P022.compatibleLaws H) = cplus ∧
    sInf (AronowAudit.P022.lawCovariance '' AronowAudit.P022.compatibleLaws H) = cminus ∧
    (∃ J ∈ AronowAudit.P022.compatibleLaws H, AronowAudit.P022.lawCovariance J = cplus) ∧
    (∃ J ∈ AronowAudit.P022.compatibleLaws H, AronowAudit.P022.lawCovariance J = cminus) := by
  let μ := (H : Measure (ℝ × ℝ)).map Prod.fst
  let ν := (H : Measure (ℝ × ℝ)).map Prod.snd
  have hμ : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).mpr h1
  have hν : MemLp (fun x : ℝ => x) 2 ν :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).mpr h0
  let cplus := (∫ u in Ioo (0 : ℝ) 1, quantile μ u * quantile ν u) -
    lawMean H true * lawMean H false
  let cminus := (∫ u in Ioo (0 : ℝ) 1, quantile μ u * quantile ν (1-u)) -
    lawMean H true * lawMean H false
  change sSup (lawCovariance '' compatibleLaws H) = cplus ∧
    sInf (lawCovariance '' compatibleLaws H) = cminus ∧
    (∃ J ∈ compatibleLaws H, lawCovariance J = cplus) ∧
    (∃ J ∈ compatibleLaws H, lawCovariance J = cminus)
  have coupling (J : JointLaw) (hJ : J ∈ compatibleLaws H) :
      IsCoupling (J : Measure (ℝ × ℝ)) μ ν :=
    ⟨inferInstance, (TailB_compatibleLaws_iff_marginals H J).mp hJ |>.1,
      (TailB_compatibleLaws_iff_marginals H J).mp hJ |>.2⟩
  have cov (J : JointLaw) (hJ : J ∈ compatibleLaws H) :
      lawCovariance J = (∫ z, z.1 * z.2 ∂(J : Measure (ℝ × ℝ))) -
        lawMean H true * lawMean H false := by
    rw [TailB_lawCovariance_eq_sub J
      (coupling_fst_memLp (coupling J hJ) hμ)
      (coupling_snd_memLp (coupling J hJ) hν),
      TailB_lawMean_eq_of_compatible H J hJ true,
      TailB_lawMean_eq_of_compatible H J hJ false]
  have bounds (J : JointLaw) (hJ : J ∈ compatibleLaws H) :
      cminus ≤ lawCovariance J ∧ lawCovariance J ≤ cplus := by
    rw [cov J hJ]
    constructor
    · exact sub_le_sub_right ((countermonotone_le_product_expectation
        (coupling J hJ) hμ hν).trans_eq' (TailB_product_expectation_countermonotoneCoupling μ ν)) _
    · exact sub_le_sub_right ((product_expectation_le_comonotone
        (coupling J hJ) hμ hν).trans_eq (product_expectation_comonotoneCoupling μ ν hμ hν)) _
  let JP : JointLaw := ⟨comonotoneCoupling μ ν,
    (isCoupling_comonotoneCoupling μ ν).isProbabilityMeasure⟩
  let JM : JointLaw := ⟨countermonotoneCoupling μ ν,
    (isCoupling_countermonotoneCoupling μ ν).isProbabilityMeasure⟩
  have hp : JP ∈ compatibleLaws H := (TailB_compatibleLaws_iff_marginals H JP).mpr
    ⟨(isCoupling_comonotoneCoupling μ ν).map_fst,
      (isCoupling_comonotoneCoupling μ ν).map_snd⟩
  have hm : JM ∈ compatibleLaws H := (TailB_compatibleLaws_iff_marginals H JM).mpr
    ⟨(isCoupling_countermonotoneCoupling μ ν).map_fst,
      (isCoupling_countermonotoneCoupling μ ν).map_snd⟩
  have hvp : lawCovariance JP = cplus := by
    rw [cov JP hp]
    exact congrArg (fun r => r - lawMean H true * lawMean H false)
      (product_expectation_comonotoneCoupling μ ν hμ hν)
  have hvm : lawCovariance JM = cminus := by
    rw [cov JM hm]
    exact congrArg (fun r => r - lawMean H true * lawMean H false)
      (TailB_product_expectation_countermonotoneCoupling μ ν)
  refine ⟨?_, ?_, ⟨JP, hp, hvp⟩, ⟨JM, hm, hvm⟩⟩
  · apply IsGreatest.csSup_eq
    refine ⟨⟨JP, hp, hvp⟩, ?_⟩
    rintro r ⟨J, hJ, rfl⟩
    exact (bounds J hJ).2
  · apply IsLeast.csInf_eq
    refine ⟨⟨JM, hm, hvm⟩, ?_⟩
    rintro r ⟨J, hJ, rfl⟩
    exact (bounds J hJ).1

