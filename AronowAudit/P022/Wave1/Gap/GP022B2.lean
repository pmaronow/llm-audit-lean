import AronowAudit.P022.P022_Variance
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT
import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Group.MinMax

/-! Finite sampling variance for injected blocks and threshold indicators. -/

namespace AronowAudit.P022.Wave1

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false

noncomputable section




/-! ## Exact finite sampling variance -/

/-- The centered second moment of any injected block of positions. This is
also applicable to strict threshold indicators. -/
lemma cdf_variance_corrected_block_moments (d : Design) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (z : Fin d.N → ℝ) :
    designExpectation d (fun π => finiteMean (fun j => z (π (e j)))) = finiteMean z ∧
    designExpectation d (fun π =>
      (finiteMean (fun j => z (π (e j))) - finiteMean z) ^ 2) =
      ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) * finiteVariance z := by
  classical
  letI : NeZero s := ⟨ne_of_gt hs⟩
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hN : (0 : ℝ) < d.N := by exact_mod_cast hNnat
  have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · unfold designExpectation finiteMean
    rw [Finset.expect_comm]
    simp_rw [permutation_eval_mean hNnat]
    exact Fintype.expect_const _
  · let μ : ℝ := finiteMean z
    let w : Fin d.N → ℝ := fun i => z i - μ
    have hsumz : (∑ i, z i) = (d.N : ℝ) * μ := by
      simpa only [Fintype.card_fin, μ, finiteMean] using
        (Fintype.card_mul_expect z).symm
    have hw : ∑ i, w i = 0 := by
      dsimp [w]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hsumz]
      ring
    have hsumw : (∑ i, w i ^ 2) = (d.N : ℝ) * finiteVariance z := by
      simpa only [Fintype.card_fin, finiteVariance, finiteMean, w, μ] using
        (Fintype.card_mul_expect (fun i => w i ^ 2)).symm
    have hcenter : ∀ π : Assignment d,
        finiteMean (fun j => z (π (e j))) - finiteMean z =
          (∑ j, w (π (e j))) / (s : ℝ) := by
      intro π
      change (𝔼 j : Fin s, z (π (e j))) - μ =
        (∑ j : Fin s, (z (π (e j)) - μ)) / (s : ℝ)
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
        Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp [ne_of_gt hsR]
      <;> ring
    have hblock := StatLean.HypothesisTesting.avg_perm_blockSum_sq
      (show 2 ≤ d.N by have := d.population_min; omega) e he w hw
    have havg : designExpectation d (fun π => (∑ j, w (π (e j))) ^ 2) =
        (s : ℝ) * ((d.N : ℝ) - s) / ((d.N : ℝ) * ((d.N : ℝ) - 1)) *
          ∑ i, w i ^ 2 := by
      simpa only [designExpectation, Fintype.expect_eq_sum_div_card,
        div_eq_inv_mul] using hblock
    calc
      designExpectation d (fun π =>
          (finiteMean (fun j => z (π (e j))) - finiteMean z) ^ 2) =
          designExpectation d (fun π => (∑ j, w (π (e j))) ^ 2 / (s : ℝ) ^ 2) := by
        unfold designExpectation
        apply Finset.expect_congr rfl
        intro π _
        rw [hcenter π, div_pow]
      _ = designExpectation d (fun π => (∑ j, w (π (e j))) ^ 2) / (s : ℝ) ^ 2 := by
        unfold designExpectation
        exact (Finset.expect_div _ _ _).symm
      _ = ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) * finiteVariance z := by
        rw [havg, hsumw]
        field_simp [ne_of_gt hN, ne_of_gt hN₁, ne_of_gt hsR]
        <;> ring

lemma cdf_variance_corrected_block_variance (d : Design) {s : ℕ} (hs : 0 < s)
    (e : Fin s → Fin d.N) (he : Function.Injective e) (z : Fin d.N → ℝ) :
    designVariance d (fun π => finiteMean (fun j => z (π (e j)))) =
      ((d.N : ℝ) - s) / (((d.N : ℝ) - 1) * s) * finiteVariance z := by
  have h := cdf_variance_corrected_block_moments d hs e he z
  unfold designVariance
  rw [h.1]
  exact h.2

lemma cdf_variance_corrected_bernoulli_upper (N s : ℕ) (p : ℝ)
    (hN : 1 < (N : ℝ)) (hs : 0 < (s : ℝ)) (hsN : s ≤ N) :
    ((N : ℝ) - s) / (((N : ℝ) - 1) * s) * p * (1 - p) ≤
      ((N : ℝ) - s) / (4 * ((N : ℝ) - 1) * s) := by
  have hdiff : (0 : ℝ) ≤ (N : ℝ) - s := by
    have hh : (s : ℝ) ≤ N := by exact_mod_cast hsN
    linarith
  have hcoef : 0 ≤ ((N : ℝ) - s) / (((N : ℝ) - 1) * s) :=
    div_nonneg hdiff (mul_nonneg (by linarith) hs.le)
  have hb := mul_le_mul_of_nonneg_left (bernoulli_variance_bound p).1 hcoef
  calc
    ((N : ℝ) - s) / (((N : ℝ) - 1) * s) * p * (1 - p) =
        ((N : ℝ) - s) / (((N : ℝ) - 1) * s) * (p * (1 - p)) := by ring
    _ ≤ ((N : ℝ) - s) / (((N : ℝ) - 1) * s) * (1 / 4) := hb
    _ = ((N : ℝ) - s) / (4 * ((N : ℝ) - 1) * s) := by
      field_simp [ne_of_gt hs, ne_of_gt (sub_pos.mpr hN)]
      <;> ring

theorem cdf_variance_corrected_proof (d : Design) (y1 y0 : Fin d.N → ℝ) (x : ℝ) :
    let G := empiricalCDF y1 x
    let F := empiricalCDF y0 x
    let Gh := fun π => empiricalCDF (observedTreatment d y1 π) x
    let Fh := fun π => empiricalCDF (observedControl d y0 π) x
    designExpectation d Gh = G ∧ designExpectation d Fh = F ∧
    designVariance d Gh = ((d.N : ℝ) - d.m) / (((d.N : ℝ) - 1) * d.m) * G * (1 - G) ∧
    designVariance d Fh = ((d.N : ℝ) - d.k) / (((d.N : ℝ) - 1) * d.k) * F * (1 - F) ∧
    designVariance d Gh ≤ ((d.N : ℝ) - d.m) / (4 * ((d.N : ℝ) - 1) * d.m) ∧
    designVariance d Fh ≤ ((d.N : ℝ) - d.k) / (4 * ((d.N : ℝ) - 1) * d.k) := by
  classical
  dsimp only
  have hN : 0 < d.N := by have := d.population_min; omega
  have hm : 0 < d.m := by have := d.treatment_min; omega
  have hk : 0 < d.k := by have := d.control_min; omega
  let e1 : Fin d.m → Fin d.N := fun i =>
    ⟨i.val, by have hi := i.isLt; have := d.sample_le; omega⟩
  let e0 : Fin d.k → Fin d.N := fun i =>
    ⟨d.m + i.val, by have hi := i.isLt; have := d.sample_le; omega⟩
  have he1 : Function.Injective e1 := by
    intro i j hij
    have hv := congrArg Fin.val hij
    exact Fin.ext hv
  have he0 : Function.Injective e0 := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp [e0] at hv
    omega
  have hv1 := cdf_variance_corrected_block_variance d hm e1 he1
    (fun i => if y1 i ≤ x then (1 : ℝ) else 0)
  have hv0 := cdf_variance_corrected_block_variance d hk e0 he0
    (fun i => if y0 i ≤ x then (1 : ℝ) else 0)
  rw [indicator_population_variance hN y1 x] at hv1
  rw [indicator_population_variance hN y0 x] at hv0
  have ht : designVariance d (fun π => empiricalCDF (observedTreatment d y1 π) x) =
      ((d.N : ℝ) - d.m) / (((d.N : ℝ) - 1) * d.m) *
        empiricalCDF y1 x * (1 - empiricalCDF y1 x) := by
    rw [mul_assoc, ← hv1]
    rfl
  have hc : designVariance d (fun π => empiricalCDF (observedControl d y0 π) x) =
      ((d.N : ℝ) - d.k) / (((d.N : ℝ) - 1) * d.k) *
        empiricalCDF y0 x * (1 - empiricalCDF y0 x) := by
    rw [mul_assoc, ← hv0]
    rfl
  have hNR : 1 < (d.N : ℝ) := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  refine ⟨(sampled_cdfs_unbiased d y1 y0 x).1,
    (sampled_cdfs_unbiased d y1 y0 x).2, ht, hc, ?_, ?_⟩
  · rw [ht]
    exact cdf_variance_corrected_bernoulli_upper d.N d.m (empiricalCDF y1 x) hNR
      (by exact_mod_cast hm) (by have := d.sample_le; omega)
  · rw [hc]
    exact cdf_variance_corrected_bernoulli_upper d.N d.k (empiricalCDF y0 x) hNR
      (by exact_mod_cast hk) (by have := d.sample_le; omega)







end

end AronowAudit.P022.Wave1
