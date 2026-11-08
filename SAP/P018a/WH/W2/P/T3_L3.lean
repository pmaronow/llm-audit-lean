import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.Wave1.Gap.GP0181B1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

noncomputable section
namespace SAP.P018a.WH.W2.P.T3_L3

open Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

lemma signSum_fourth_from_mixed (hM : SAP.P018a.WholeFourthSignMoment) (N : ℕ) :
    (∫ ω, (SAP.P018a.wholeSignSum ω)^4 ∂ SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) =
      3 * (N : ℝ)^2 - 2 * (N : ℝ) := by
  classical
  let μ := SAP.P018a.unitSampleLaw SAP.P018a.signKernel N
  let x : Fin N → (Fin N → Bool) → ℝ := fun i ω => SAP.P018a.signValue (ω i)
  haveI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N)
    exact AronowAudit.P018.Wave1.printed_sign_probability N
  have hpoint (ω : Fin N → Bool) :
      (SAP.P018a.wholeSignSum ω)^4 =
        ∑ i, ∑ j, ∑ k, ∑ l, x i ω * x j ω * x k ω * x l ω := by
    dsimp [SAP.P018a.wholeSignSum, x]
    calc
      (∑ i, SAP.P018a.signValue (ω i))^4 =
          (∑ i, SAP.P018a.signValue (ω i)) * (∑ j, SAP.P018a.signValue (ω j)) *
            (∑ k, SAP.P018a.signValue (ω k)) * (∑ l, SAP.P018a.signValue (ω l)) := by ring
      _ = ∑ i, ∑ j, ∑ k, ∑ l,
          SAP.P018a.signValue (ω i) * SAP.P018a.signValue (ω j) *
            SAP.P018a.signValue (ω k) * SAP.P018a.signValue (ω l) := by
        conv_lhs => simp only [Finset.sum_mul, Finset.mul_sum]
        simp only [mul_comm, mul_left_comm, mul_assoc]
  have hexpand :
      (∫ ω, (SAP.P018a.wholeSignSum ω)^4 ∂ μ) =
        ∑ i, ∑ j, ∑ k, ∑ l, ∫ ω, x i ω * x j ω * x k ω * x l ω ∂ μ := by
    calc
      _ = ∫ ω, ∑ i, ∑ j, ∑ k, ∑ l, x i ω * x j ω * x k ω * x l ω ∂ μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = _ := by
        have hsum (F : Fin N → (Fin N → Bool) → ℝ) :
            (∫ ω, ∑ i, F i ω ∂ μ) = ∑ i, ∫ ω, F i ω ∂ μ := by
          exact integral_finsetSum _ (fun i hi =>
            AronowAudit.P018.Wave1.printed_finite_integrable μ (F i))
        calc
          (∫ ω, ∑ i, ∑ j, ∑ k, ∑ l, x i ω * x j ω * x k ω * x l ω ∂ μ) =
              ∑ i, ∫ ω, ∑ j, ∑ k, ∑ l, x i ω * x j ω * x k ω * x l ω ∂ μ := hsum _
          _ = ∑ i, ∑ j, ∫ ω, ∑ k, ∑ l, x i ω * x j ω * x k ω * x l ω ∂ μ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hsum _
          _ = ∑ i, ∑ j, ∑ k, ∫ ω, ∑ l, x i ω * x j ω * x k ω * x l ω ∂ μ := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            exact hsum _
          _ = ∑ i, ∑ j, ∑ k, ∑ l, ∫ ω, x i ω * x j ω * x k ω * x l ω ∂ μ := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            exact hsum _
  have hmom (i j k l : Fin N) :
      (∫ ω, x i ω * x j ω * x k ω * x l ω ∂ μ) =
        (if i=j ∧ k=l then 1 else 0) + (if i=k ∧ j=l then 1 else 0) +
          (if i=l ∧ j=k then 1 else 0) - (if i=j ∧ j=k ∧ k=l then 2 else 0) := by
    simpa [μ, x] using hM N i j k l
  rw [hexpand]
  simp_rw [hmom]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq]
  have hc1 (i j k : Fin N) :
      (#{l : Fin N | i = j ∧ k = l} : ℝ) = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · simp [hij]
      have hs : Finset.univ.filter (fun l : Fin N => k = l) = ({k} : Finset (Fin N)) := by
        ext l
        simp [eq_comm]
      rw [hs]
      simp
    · simp [hij]
  have hc2 (i j k : Fin N) :
      (#{l : Fin N | i = k ∧ j = l} : ℝ) = if i = k then 1 else 0 := by
    by_cases hik : i = k
    · simp [hik]
      have hs : Finset.univ.filter (fun l : Fin N => j = l) = ({j} : Finset (Fin N)) := by
        ext l
        simp [eq_comm]
      rw [hs]
      simp
    · simp [hik]
  have hc3 (i j k : Fin N) :
      (#{l : Fin N | i = l ∧ j = k} : ℝ) = if j = k then 1 else 0 := by
    by_cases hjk : j = k
    · simp [hjk]
      have hs : Finset.univ.filter (fun l : Fin N => i = l) = ({i} : Finset (Fin N)) := by
        ext l
        simp [eq_comm]
      rw [hs]
      simp
    · simp [hjk]
  simp only [hc1, hc2, hc3]
  have hdiag1 (i j k : Fin N) :
      (∑ l : Fin N, if i = j ∧ j = k ∧ k = l then (2 : ℝ) else 0) =
        if i = j ∧ j = k then 2 else 0 := by
    by_cases hij : i = j <;> by_cases hjk : j = k <;> simp_all
  have hdiag2 (i j : Fin N) :
      (∑ k : Fin N, if i = j ∧ j = k then (2 : ℝ) else 0) =
        if i = j then 2 else 0 := by
    by_cases hij : i = j <;> simp_all
  simp_rw [hdiag1, hdiag2]
  simp [Finset.sum_const, Fintype.card_fin, Finset.sum_ite_eq', Finset.sum_ite_eq]
  <;> ring

lemma signSquare_variance (hM : SAP.P018a.WholeFourthSignMoment) (N : ℕ) :
    ProbabilityTheory.variance (fun ω => (SAP.P018a.wholeSignSum ω)^2)
        (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) =
      2 * (N : ℝ) * ((N : ℝ)-1) := by
  let μ := SAP.P018a.unitSampleLaw SAP.P018a.signKernel N
  haveI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N)
    exact AronowAudit.P018.Wave1.printed_sign_probability N
  have h4 := signSum_fourth_from_mixed hM N
  have hLaw : SAP.P018a.unitSampleLaw SAP.P018a.signKernel N =
      AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N := by
    rfl
  have h2 : (∫ ω, (SAP.P018a.wholeSignSum ω)^2 ∂ μ) = (N : ℝ) := by
    rw [show μ = SAP.P018a.unitSampleLaw SAP.P018a.signKernel N from rfl, hLaw]
    simpa [SAP.P018a.wholeSignSum, AronowAudit.P018.Wave1.printed_S,
      SAP.P018a.signValue, AronowAudit.P018.signValue] using
      (AronowAudit.P018.Wave1.printed_S_second N)
  have h4sq : (∫ ω, ((SAP.P018a.wholeSignSum ω)^2)^2 ∂ μ) =
      3 * (N : ℝ)^2 - 2 * (N : ℝ) := by
    calc
      _ = ∫ ω, (SAP.P018a.wholeSignSum ω)^4 ∂ μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by ring)
      _ = _ := by simpa [μ] using h4
  rw [ProbabilityTheory.variance_eq_sub
    (AronowAudit.P018.Wave1.printed_finite_L2 μ (fun ω => (SAP.P018a.wholeSignSum ω)^2))]
  simp only [Pi.pow_apply]
  rw [h4sq, h2]
  ring

lemma scaledVariance_formula (hM : SAP.P018a.WholeFourthSignMoment)
    {N : ℕ} (hN : 4 ≤ N) :
    ProbabilityTheory.variance
        (fun ω => (N : ℝ) * SAP.P018a.wholeSignVariance ω)
        (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N) =
      32 * ((N : ℝ)-2)^2 * ((N : ℝ)-3)^2 /
        ((N : ℝ)^3 * ((N : ℝ)-1)^3) := by
  let μ := SAP.P018a.unitSampleLaw SAP.P018a.signKernel N
  let X : (Fin N → Bool) → ℝ := fun ω => (SAP.P018a.wholeSignSum ω)^2
  haveI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      (AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N)
    exact AronowAudit.P018.Wave1.printed_sign_probability N
  have hn : (N : ℝ) ≠ 0 := by
    have hn' : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by
    have hn' : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hpoint (ω : Fin N → Bool) :
      (N : ℝ) * SAP.P018a.wholeSignVariance ω =
        AronowAudit.P018.Wave1.printed_A N *
          (1 - (SAP.P018a.wholeSignSum ω / (N : ℝ))^2) := by
    change (N : ℝ) * AronowAudit.P018.sampleVariance AronowAudit.P018.members
        (AronowAudit.P018.design AronowAudit.P018.signKernel ω)
        (AronowAudit.P018.response AronowAudit.P018.signKernel ω) 0 0 =
      (4 * ((N : ℝ)-2) * ((N : ℝ)-3) / ((N : ℝ)-1)^2) *
        (1 - (AronowAudit.P018.Wave1.printed_S ω / (N : ℝ))^2)
    exact AronowAudit.P018.Wave1.printed_scaled_sandwich hN ω
  have hXlp : MemLp X 2 μ :=
    AronowAudit.P018.Wave1.printed_finite_L2 μ X
  have hvar :
      ProbabilityTheory.variance
        (fun ω => (N : ℝ) * SAP.P018a.wholeSignVariance ω) μ =
        (AronowAudit.P018.Wave1.printed_A N)^2 *
          (((N : ℝ)^2)⁻¹)^2 *
            ProbabilityTheory.variance X μ := by
    have hy : (fun ω => (N : ℝ) * SAP.P018a.wholeSignVariance ω) =
        fun ω => AronowAudit.P018.Wave1.printed_A N *
          (1 - ((N : ℝ)^2)⁻¹ * X ω) := by
      funext ω
      rw [hpoint]
      congr 2
      field_simp [hn]
      <;> ring
    rw [hy, ProbabilityTheory.variance_const_mul]
    rw [show (fun ω => 1 - ((N : ℝ)^2)⁻¹ * X ω) =
        fun ω => 1 - (((N : ℝ)^2)⁻¹ * X ω) from rfl]
    rw [ProbabilityTheory.variance_const_sub
      ((hXlp.const_mul (((N : ℝ)^2)⁻¹)).aestronglyMeasurable) 1]
    rw [ProbabilityTheory.variance_const_mul]
    ring
  rw [hvar, signSquare_variance hM N]
  dsimp [AronowAudit.P018.Wave1.printed_A]
  field_simp [hn, hn1]
  <;> ring

lemma scaledVariance_limit (hM : SAP.P018a.WholeFourthSignMoment) :
    Tendsto (fun N : ℕ =>
      ProbabilityTheory.variance
        (fun ω => (N : ℝ) * SAP.P018a.wholeSignVariance ω)
        (SAP.P018a.unitSampleLaw SAP.P018a.signKernel N)) atTop (𝓝 0) := by
  have hA2 : Tendsto (fun N : ℕ => (AronowAudit.P018.Wave1.printed_A N)^2)
      atTop (𝓝 16) := by
    convert AronowAudit.P018.Wave1.printed_A_limit.pow 2 using 1 <;> norm_num
  have hone : Tendsto (fun N : ℕ => 1 - (N : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      AronowAudit.P018.Wave1.printed_inv_n_limit
  have hlim : Tendsto (fun N : ℕ => (2 : ℝ) *
      (AronowAudit.P018.Wave1.printed_A N)^2 * ((N : ℝ)⁻¹)^2 *
        (1 - (N : ℝ)⁻¹)) atTop (𝓝 0) := by
    have h := (((tendsto_const_nhds (x := (2 : ℝ))).mul hA2).mul
      (AronowAudit.P018.Wave1.printed_inv_n_limit.pow 2)).mul hone
    simpa using h
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 4] with N hN
  rw [scaledVariance_formula hM hN]
  have hn : (N : ℝ) ≠ 0 := by
    have hn' : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hn1 : (N : ℝ)-1 ≠ 0 := by
    have hn' : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  dsimp [AronowAudit.P018.Wave1.printed_A]
  field_simp [hn, hn1]
  <;> ring

end SAP.P018a.WH.W2.P.T3_L3

theorem SAP.P018a.WH.W2.T3_L3_proof : SAP.P018a.WH.W2.T3_L3 := by
  intro hM
  refine ⟨?_, ?_, ?_⟩
  · intro N
    constructor
    · exact SAP.P018a.WH.W2.P.T3_L3.signSum_fourth_from_mixed hM N
    · exact SAP.P018a.WH.W2.P.T3_L3.signSquare_variance hM N
  · intro N hN
    exact SAP.P018a.WH.W2.P.T3_L3.scaledVariance_formula hM hN
  · exact SAP.P018a.WH.W2.P.T3_L3.scaledVariance_limit hM
