import AronowAudit.P022.P022_Variance
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT
import Mathlib.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Group.MinMax

/-!
Draft dd-GP022B2. No Lean process was run.

Integration dependencies, intentionally not replaced by held declarations:
* `lemma2_corrected_explicit_proof`, the new Wave1 proof of the explicit lemma;
* `bounded_direct_finite_proof`, the new Wave1 proof of the finite direct bound;
* `proposition2_corrected_finite_bounded_raw_quantile_product`, the bounded empirical quantile
  product/CDF identity described immediately before its use below.
These three names are unresolved in this checkout; see the run report. All
remaining arguments are supplied here, including the complete injected-block
variance bridge. No extra hypothesis is added to any of the four target types.
-/

namespace AronowAudit.P022.Wave1

open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
set_option autoImplicit false

noncomputable section

/-! ## Record 7: finite bound to the asymptotic bound -/

lemma bounded_direct_asymptotic_size_atTop (S : ExperimentSequence) :
    Tendsto (fun q => ((S.design q).N : ℝ)) atTop atTop := by
  have hshift : Tendsto (fun q : ℕ => q + 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat 4).2 tendsto_id
  simpa only [S.size, Function.comp_def] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hshift

lemma bounded_direct_asymptotic_control_ratio (S : ExperimentSequence) (θ ρ : ℝ)
    (hm : Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N)
      atTop (𝓝 (θ * ρ)))
    (hn : Tendsto (fun q => (((S.design q).m : ℝ) + (S.design q).k) /
      (S.design q).N) atTop (𝓝 θ)) :
    Tendsto (fun q => ((S.design q).k : ℝ) / (S.design q).N)
      atTop (𝓝 (θ * (1 - ρ))) := by
  convert hn.sub hm using 1
  · funext q
    ring
  · ring

lemma bounded_direct_asymptotic_eventual_sizes (S : ExperimentSequence) (θ ρ c : ℝ)
    (hm : Tendsto (fun q => ((S.design q).m : ℝ) / (S.design q).N)
      atTop (𝓝 (θ * ρ)))
    (hn : Tendsto (fun q => (((S.design q).m : ℝ) + (S.design q).k) /
      (S.design q).N) atTop (𝓝 θ))
    (hc : c < min (θ * ρ) (θ * (1 - ρ))) :
    ∀ᶠ q in atTop, c * (S.design q).N ≤ (S.design q).m ∧
      c * (S.design q).N ≤ (S.design q).k := by
  have hmc : c < θ * ρ := lt_of_lt_of_le hc (min_le_left _ _)
  have hkc : c < θ * (1 - ρ) := lt_of_lt_of_le hc (min_le_right _ _)
  have hme := hm.eventually (eventually_gt_nhds hmc)
  have hke := (bounded_direct_asymptotic_control_ratio S θ ρ hm hn).eventually
    (eventually_gt_nhds hkc)
  filter_upwards [hme, hke] with q hmq hkq
  have hN : (0 : ℝ) < (S.design q).N := by
    exact_mod_cast (show 0 < (S.design q).N by
      have := (S.design q).population_min
      omega)
  exact ⟨((lt_div_iff₀ hN).mp hmq).le, ((lt_div_iff₀ hN).mp hkq).le⟩

/-! ## Record 9: exact finite sampling variance -/

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

example : type_of% @AronowAudit.P022.cdf_variance_corrected := cdf_variance_corrected_proof

/-! ## Record 10: the seven-term decomposition and finite budget -/

lemma proposition2_corrected_finite_empiricalCDF_mono {s : ℕ} (a : Fin s → ℝ) :
    Monotone (empiricalCDF a) := by
  classical
  intro x y hxy
  unfold empiricalCDF finiteMean
  apply Finset.expect_le_expect
  intro i _
  by_cases hix : a i ≤ x
  · simp only [if_pos hix, if_pos (hix.trans hxy), le_refl]
  · simp only [if_neg hix]
    split_ifs <;> norm_num

lemma proposition2_corrected_finite_cdfDistance_bdd {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) :
    BddAbove (Set.range (fun x => |empiricalCDF a x - empiricalCDF b x|)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨ha₀, ha₁⟩ := empirical_cdf_bounds hm a x
  obtain ⟨hb₀, hb₁⟩ := empirical_cdf_bounds hk b x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma proposition2_corrected_finite_cdfDistance_pointwise {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (x : ℝ) :
    |empiricalCDF a x - empiricalCDF b x| ≤
      cdfDistance (empiricalCDF a) (empiricalCDF b) := by
  exact le_csSup (proposition2_corrected_finite_cdfDistance_bdd hm hk a b) ⟨x, rfl⟩

lemma proposition2_corrected_finite_cdfDistance_nonneg {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) :
    0 ≤ cdfDistance (empiricalCDF a) (empiricalCDF b) :=
  (abs_nonneg _).trans (proposition2_corrected_finite_cdfDistance_pointwise hm hk a b 0)

/-- Every inner min-CDF integral is integrable. This uses monotonicity,
so no continuity at the empirical jumps is needed. -/
lemma proposition2_corrected_finite_inner_integrable {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (C x : ℝ) :
    IntervalIntegrable (fun y => min (empiricalCDF a x) (empiricalCDF b y))
      volume (-C) C := by
  have hmono : Monotone (fun y => min (empiricalCDF a x) (empiricalCDF b y)) :=
    monotone_const.min (proposition2_corrected_finite_empiricalCDF_mono b)
  exact hmono.intervalIntegrable

lemma proposition2_corrected_finite_outer_integrable {m k : ℕ} (a : Fin m → ℝ) (b : Fin k → ℝ)
    (C : ℝ) (hC : 0 ≤ C) :
    IntervalIntegrable (fun x => ∫ y in (-C)..C,
      min (empiricalCDF a x) (empiricalCDF b y)) volume (-C) C := by
  have hmono : Monotone (fun x => ∫ y in (-C)..C,
      min (empiricalCDF a x) (empiricalCDF b y)) := by
    intro x x' hxx'
    apply intervalIntegral.integral_mono (by linarith : -C ≤ C)
      (proposition2_corrected_finite_inner_integrable a b C x)
      (proposition2_corrected_finite_inner_integrable a b C x')
    intro y
    exact min_le_min ((proposition2_corrected_finite_empiricalCDF_mono a) hxx') le_rfl
  exact hmono.intervalIntegrable

/-- Linearity for the actual iterated CDF integral in T7. -/
lemma proposition2_corrected_finite_double_integral_sub {m k N : ℕ}
    (a : Fin m → ℝ) (b : Fin k → ℝ) (y1 y0 : Fin N → ℝ)
    (C : ℝ) (hC : 0 ≤ C) :
    (∫ x in (-C)..C, ∫ y in (-C)..C,
      min (empiricalCDF a x) (empiricalCDF b y) -
        min (empiricalCDF y1 x) (empiricalCDF y0 y)) =
      (∫ x in (-C)..C, ∫ y in (-C)..C,
        min (empiricalCDF a x) (empiricalCDF b y)) -
      (∫ x in (-C)..C, ∫ y in (-C)..C,
        min (empiricalCDF y1 x) (empiricalCDF y0 y)) := by
  have hinner : ∀ x,
      (∫ y in (-C)..C, min (empiricalCDF a x) (empiricalCDF b y) -
        min (empiricalCDF y1 x) (empiricalCDF y0 y)) =
      (∫ y in (-C)..C, min (empiricalCDF a x) (empiricalCDF b y)) -
        (∫ y in (-C)..C, min (empiricalCDF y1 x) (empiricalCDF y0 y)) := by
    intro x
    exact intervalIntegral.integral_sub
      (proposition2_corrected_finite_inner_integrable a b C x)
      (proposition2_corrected_finite_inner_integrable y1 y0 C x)
  simp_rw [hinner]
  exact intervalIntegral.integral_sub
    (proposition2_corrected_finite_outer_integrable a b C hC)
    (proposition2_corrected_finite_outer_integrable y1 y0 C hC)

/-- A deterministic identity for the defined finite-population correction. -/
lemma proposition2_corrected_finite_marginal_as_variance {s : ℕ} (N : ℕ) (a : Fin s → ℝ) :
    marginalVarianceEstimate N a =
      (((N : ℝ) - 1) / N) *
        ((s : ℝ) * finiteVariance a / ((s : ℝ) - 1)) := by
  have hsum : (∑ i, (a i - finiteMean a) ^ 2) =
      (s : ℝ) * finiteVariance a := by
    simpa only [Fintype.card_fin, finiteVariance, finiteMean] using
      (Fintype.card_mul_expect (fun i => (a i - finiteMean a) ^ 2)).symm
  unfold marginalVarianceEstimate sampleVariance
  rw [hsum]

/-
Required shared result (the new proof is not present in this checkout):

proposition2_corrected_finite_bounded_raw_quantile_product
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Fin m → ℝ) (b : Fin k → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ C) (hb : ∀ j, |b j| ≤ C) :
    (∫ u in (0 : ℝ)..1, empiricalQuantile a u * empiricalQuantile b u) =
      -C ^ 2 + C * (finiteMean a + finiteMean b) +
        ∫ x in (-C)..C, ∫ y in (-C)..C,
          min (empiricalCDF a x) (empiricalCDF b y)

Its proof requires the empirical quantile law (including measurability,
rank-cell integration and marginal means), and bounded Fubini applied to
X = C - ∫_{-C}^C 1{X ≤ x} dx. It holds also for C = 0. The exact places
using it are the two applications below; no held covariance theorem is used.
-/

/-- A finite union bound expressed directly in the actual assignment average. -/
lemma proposition2_corrected_finite_finite_union_bound (d : Design) (E : Assignment d → Prop)
    (F : Fin 7 → Assignment d → Prop) (h : ∀ π, E π → ∃ j, F j π) :
    designProbability d E ≤ ∑ j, designProbability d (F j) := by
  classical
  unfold designProbability designExpectation
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro π _
  by_cases hE : E π
  · rw [if_pos hE]
    obtain ⟨j, hj⟩ := h π hE
    calc
      (1 : ℝ) = if F j π then 1 else 0 := by rw [if_pos hj]
      _ ≤ ∑ i : Fin 7, if F i π then (1 : ℝ) else 0 := by
        exact Finset.single_le_sum (f := fun i : Fin 7 => if F i π then (1 : ℝ) else 0)
          (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  · rw [if_neg hE]
    apply Finset.sum_nonneg
    intro j _
    dsimp only
    split_ifs <;> norm_num

lemma proposition2_corrected_finite_last_integral_sup_bound (d : Design) (y1 y0 : Fin d.N → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (π : Assignment d) :
    |lastIntegralTerm d y1 y0 C π| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) *
        max (cdfDistance (empiricalCDF (observedTreatment d y1 π)) (empiricalCDF y1))
          (cdfDistance (empiricalCDF (observedControl d y0 π)) (empiricalCDF y0)) := by
  have hNnat : 0 < d.N := by have := d.population_min; omega
  have hmnat : 0 < d.m := by have := d.treatment_min; omega
  have hknat : 0 < d.k := by have := d.control_min; omega
  have hN : (0 : ℝ) < d.N := by exact_mod_cast hNnat
  have hN₁ : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hh : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  let a := observedTreatment d y1 π
  let b := observedControl d y0 π
  let M := max (cdfDistance (empiricalCDF a) (empiricalCDF y1))
    (cdfDistance (empiricalCDF b) (empiricalCDF y0))
  let f : ℝ → ℝ → ℝ := fun x y =>
    min (empiricalCDF a x) (empiricalCDF b y) -
      min (empiricalCDF y1 x) (empiricalCDF y0 y)
  have hpoint : ∀ x y, |f x y| ≤ M := by
    intro x y
    exact (abs_min_sub_min_le_max _ _ _ _).trans
      (max_le_max
        (proposition2_corrected_finite_cdfDistance_pointwise hmnat hNnat a y1 x)
        (proposition2_corrected_finite_cdfDistance_pointwise hknat hNnat b y0 y))
  have hlen : |C - -C| = 2 * C := by
    rw [abs_of_nonneg (by linarith : 0 ≤ C - -C)]
    ring
  have hinner : ∀ x, |∫ y in (-C)..C, f x y| ≤ M * (2 * C) := by
    intro x
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -C) (b := C) (f := f x) (C := M)
      (fun y _ => by simpa only [Real.norm_eq_abs] using hpoint x y)
    simpa only [Real.norm_eq_abs, hlen] using h
  have houter : |∫ x in (-C)..C, ∫ y in (-C)..C, f x y| ≤
      (M * (2 * C)) * (2 * C) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -C) (b := C) (f := fun x => ∫ y in (-C)..C, f x y)
      (C := M * (2 * C))
      (fun x _ => by simpa only [Real.norm_eq_abs] using hinner x)
    simpa only [Real.norm_eq_abs, hlen] using h
  have hcoef : 0 ≤ 2 * (d.N : ℝ) / ((d.N : ℝ) - 1) := by positivity
  change |(2 * (d.N : ℝ) / ((d.N : ℝ) - 1)) *
    (∫ x in (-C)..C, ∫ y in (-C)..C, f x y)| ≤
      (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) * M
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    (2 * (d.N : ℝ) / ((d.N : ℝ) - 1)) *
        |∫ x in (-C)..C, ∫ y in (-C)..C, f x y| ≤
        (2 * (d.N : ℝ) / ((d.N : ℝ) - 1)) * ((M * (2 * C)) * (2 * C)) :=
      mul_le_mul_of_nonneg_left houter hcoef
    _ = (8 * d.N * C ^ 2 / ((d.N : ℝ) - 1)) * M := by ring

end

end AronowAudit.P022.Wave1
