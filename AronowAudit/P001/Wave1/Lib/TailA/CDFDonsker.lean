import AronowAudit.P001.Wave1.Lib.TailA.DonskerSource
import AronowAudit.P001.Wave1.Lib.TailA.CDFTangent
import AronowAudit.P001.Wave1.Lib.TailA.OuterReadout
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Order.LeftRightLim

/-! The half-line Donsker law in the uniform-norm path space. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace AronowAudit.P001.Wave1.TailA

open AsymptoticStatistics.EmpiricalProcess
universe u v
set_option maxHeartbeats 1000000

/-- The CDF defined by threshold probabilities agrees with the Mathlib probability CDF. -/
theorem cdf_donsker_cdf (P : Measure ℝ) [IsProbabilityMeasure P] :
    cdf P id = ProbabilityTheory.cdf P := by
  funext t
  simpa [cdf, prob, measureReal_def, Set.Iic_def] using
    (ProbabilityTheory.cdf_eq_real P t).symm

/-- Every finite linear combination of donor coordinates is Gaussian. -/
theorem cdf_donor_gaussian (P : Measure ℝ)
    {ν : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν)
    (r : ℕ) (x a : Fin r → ℝ) :
    HasGaussianLaw (fun z : LinfF halfLineIndicatorClass =>
      ∑ j, a j * z (halfLineIndex (x j))) ν := by
  classical
  let L : (Fin r → ℝ) →L[ℝ] ℝ := ∑ j, a j • ContinuousLinearMap.proj j
  have hg := (hν.isGaussian_fdd r (fun j => halfLineIndex (x j))).map L
  simpa [L, Function.comp_def] using hg

/-- Donor coordinates have square-integrable Gaussian laws. -/
theorem cdf_donor_coordinate_L2 (P : Measure ℝ)
    {ν : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν) (x : ℝ) :
    MemLp (fun z : LinfF halfLineIndicatorClass => z (halfLineIndex x)) 2 ν := by
  have hg := cdf_donor_gaussian P hν 1 (fun _ => x) (fun _ => 1)
  simpa using hg.memLp_two

/-- The covariance fields identify the exact scalar Gaussian projections. -/
theorem cdf_donor_projection (P : Measure ℝ) [IsProbabilityMeasure P]
    {ν : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν)
    (r : ℕ) (x a : Fin r → ℝ) :
    let v := ∑ j, ∑ k, a j * (ProbabilityTheory.cdf P (min (x j) (x k)) -
      ProbabilityTheory.cdf P (x j) * ProbabilityTheory.cdf P (x k)) * a k
    0 ≤ v ∧ ν.map (fun z => ∑ j, a j * z (halfLineIndex (x j))) =
      gaussianReal 0 ⟨max v 0, le_max_right _ _⟩ := by
  classical
  let Y : LinfF halfLineIndicatorClass → ℝ := fun z => ∑ j, a j * z (halfLineIndex (x j))
  let v := ∑ j, ∑ k, a j * (ProbabilityTheory.cdf P (min (x j) (x k)) -
    ProbabilityTheory.cdf P (x j) * ProbabilityTheory.cdf P (x k)) * a k
  have hp := hν.isProbabilityMeasure
  have hg : HasGaussianLaw Y ν := cdf_donor_gaussian P hν r x a
  have hL2 (j) := cdf_donor_coordinate_L2 P hν (x j)
  have hm : (∫ z, Y z ∂ν) = 0 := by
    rw [show Y = (fun z => ∑ j, a j * z (halfLineIndex (x j))) from rfl,
      integral_finset_sum _ (fun j _ => (hL2 j).integrable (by norm_num) |>.const_mul (a j))]
    simp_rw [integral_const_mul, hν.mean, mul_zero]
    simp
  have hs : (∫ z, (Y z) ^ 2 ∂ν) = v := by
    have he (z) : (Y z) ^ 2 =
        ∑ j, ∑ k, a j * (z (halfLineIndex (x j)) * z (halfLineIndex (x k))) * a k := by
      simp [Y, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    simp_rw [he]
    have hprod (j k : Fin r) : Integrable (fun z : LinfF halfLineIndicatorClass =>
        a j * (z (halfLineIndex (x j)) * z (halfLineIndex (x k))) * a k) ν := by
      simpa only [Pi.mul_apply] using
        (((hL2 j).integrable_mul (hL2 k)).const_mul (a j)).mul_const (a k)
    rw [integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ fun k _ => hprod j k)]
    dsimp only [v]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finset_sum Finset.univ (fun k _ => hprod j k)]
    simp_rw [integral_mul_const, integral_const_mul, halfLine_bridge_covariance P hν]
  have hv : variance Y ν = v := by
    rw [variance_eq_integral hg.aemeasurable, hm]
    simpa using hs
  have hv0 : 0 ≤ v := hv ▸ variance_nonneg Y ν
  refine ⟨hv0, ?_⟩
  rw [hg.map_eq_gaussianReal, hm, hv]
  congr 1

/-- The half-line intrinsic semimetric is the square root of CDF distance. -/
theorem cdf_donor_dist (P : Measure ℝ) [IsProbabilityMeasure P] (s t : ℝ) :
    distL2 P (halfLineIndicator s) (halfLineIndicator t) =
      Real.sqrt |ProbabilityTheory.cdf P s - ProbabilityTheory.cdf P t| := by
  have hL := (halfLineIndicator_memLp P s 2).sub (halfLineIndicator_memLp P t 2)
  have hi : (∫ y, (halfLineIndicator s y - halfLineIndicator t y) ^ 2 ∂P) =
      |ProbabilityTheory.cdf P s - ProbabilityTheory.cdf P t| := by
    have he (y) : (halfLineIndicator s y - halfLineIndicator t y) ^ 2 =
        halfLineIndicator s y + halfLineIndicator t y - 2 *
          (halfLineIndicator s y * halfLineIndicator t y) := by
      by_cases hs : y ≤ s <;> by_cases ht : y ≤ t <;>
        norm_num [halfLineIndicator, hs, ht]
    simp_rw [he]
    have hsum : Integrable (fun y => halfLineIndicator s y + halfLineIndicator t y) P :=
      ((halfLineIndicator_memLp P s 1).integrable le_rfl).add
        ((halfLineIndicator_memLp P t 1).integrable le_rfl)
    have hmul : Integrable (fun y => 2 * (halfLineIndicator s y * halfLineIndicator t y)) P := by
      simpa only [Pi.mul_apply] using ((halfLineIndicator_memLp P s 2).integrable_mul
        (halfLineIndicator_memLp P t 2)).const_mul 2
    rw [integral_sub hsum hmul,
      integral_add ((halfLineIndicator_memLp P s 1).integrable le_rfl)
        ((halfLineIndicator_memLp P t 1).integrable le_rfl),
      integral_const_mul, integral_halfLineIndicator_mul,
      integral_halfLineIndicator, integral_halfLineIndicator]
    rcases le_total s t with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr (monotone_cdf P h))]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr (monotone_cdf P h))]; ring
  rw [distL2_eq_eLpNorm hL.aestronglyMeasurable,
    hL.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have he : (fun y => ‖(halfLineIndicator s - halfLineIndicator t) y‖ ^
      (2 : ℝ≥0∞).toReal) = fun y => (halfLineIndicator s y - halfLineIndicator t y)^2 := by
    funext y
    norm_num [Real.norm_eq_abs, Real.rpow_two]
  rw [he, hi, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _)]
  norm_num [Real.sqrt_eq_rpow]

/-- Donor path continuity is uniform continuity in the CDF semimetric. -/
theorem cdf_donor_uniform (P : Measure ℝ) [IsProbabilityMeasure P]
    {ν : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν) :
    ∀ᵐ z ∂ν, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ,
      |ProbabilityTheory.cdf P x - ProbabilityTheory.cdf P y| < δ →
        |z (halfLineIndex x) - z (halfLineIndex y)| < ε := by
  filter_upwards [hν.ucPaths] with z hz
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hz ε hε
  refine ⟨δ^2, sq_pos_of_pos hδ, fun x y hxy => hd _ _ ?_⟩
  change distL2 P (halfLineIndicator x) (halfLineIndicator y) < δ
  rw [cdf_donor_dist]
  exact (Real.sqrt_lt' hδ).2 hxy

/-- At either endpoint CDF value, the corresponding donor coordinate is zero almost surely. -/
theorem cdf_donor_zero (P : Measure ℝ) [IsProbabilityMeasure P]
    {ν : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν)
    (x : ℝ) (hx : ProbabilityTheory.cdf P x = 0 ∨ ProbabilityTheory.cdf P x = 1) :
    ∀ᵐ z ∂ν, z (halfLineIndex x) = 0 := by
  have hp := hν.isProbabilityMeasure
  have hL := cdf_donor_coordinate_L2 P hν x
  have hv : variance (fun z : LinfF halfLineIndicatorClass => z (halfLineIndex x)) ν = 0 := by
    rw [variance_eq_sub hL, hν.mean]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, pow_two]
    change (∫ z : LinfF halfLineIndicatorClass,
      z (halfLineIndex x) * z (halfLineIndex x) ∂ν) = 0
    rw [halfLine_bridge_covariance P hν, min_self]
    rcases hx with hx | hx <;> simp [hx]
  simpa only [hν.mean] using ae_eq_integral_of_variance_eq_zero hL hv

/-- A single representative of each endpoint fiber makes the endpoint assertion simultaneous. -/
theorem cdf_donor_endpoint_fiber (P : Measure ℝ) [IsProbabilityMeasure P]
    {ν : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν)
    (q : ℝ) (hq : q = 0 ∨ q = 1) :
    ∀ᵐ z ∂ν, ∀ x, ProbabilityTheory.cdf P x = q → z (halfLineIndex x) = 0 := by
  classical
  by_cases hex : ∃ x, ProbabilityTheory.cdf P x = q
  · obtain ⟨t, ht⟩ := hex
    have ht01 : ProbabilityTheory.cdf P t = 0 ∨ ProbabilityTheory.cdf P t = 1 := by
      rcases hq with hq | hq <;> simp [ht, hq]
    filter_upwards [cdf_donor_uniform P hν, cdf_donor_zero P hν t ht01] with z hz hzt
    intro x hx
    have he : z (halfLineIndex x) = z (halfLineIndex t) := by
      by_contra hne
      have hε : 0 < |z (halfLineIndex x) - z (halfLineIndex t)| :=
        abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨δ, hδ, hd⟩ := hz _ hε
      exact (lt_irrefl _ (hd x t (by simpa [hx, ht] using hδ)))
    exact he.trans hzt
  · exact ae_of_all ν (fun z x hx => (hex ⟨x, hx⟩).elim)

/-- The transported donor law is supported on the CDF tangent space. -/
theorem cdf_donor_tangent [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    {ν : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν) :
    (ν.map halfLineLinfEquiv) (CDFTangent (cdf P id))ᶜ = 0 := by
  apply ae_iff.mp
  apply (ae_map_iff halfLineLinfEquiv.continuous.measurable.aemeasurable
    (cdf_tangent_closed (cdf P id)).measurableSet).2
  filter_upwards [cdf_donor_uniform P hν,
    cdf_donor_endpoint_fiber P hν 0 (Or.inl rfl),
    cdf_donor_endpoint_fiber P hν 1 (Or.inr rfl)] with z hz h0 h1
  rw [cdf_donsker_cdf]
  refine ⟨hz, fun x hx => ?_⟩
  rcases hx with hx | hx
  · exact h0 x hx
  · exact h1 x hx

/-- The reindexed donor is the supplied-law bridge specification, including tangent support. -/
theorem cdf_donor_bridge [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    {ν : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν) :
    IsCDFBridge (cdf P id) (ν.map halfLineLinfEquiv) := by
  refine ⟨cdf_donor_tangent P hν, ?_⟩
  intro r x a
  have hc (s t : ℝ) : ProbabilityTheory.cdf P (min s t) =
      min (ProbabilityTheory.cdf P s) (ProbabilityTheory.cdf P t) :=
    (monotone_cdf P).map_min
  have hm : Measurable (fun h : KolmogorovSpace => ∑ j, a j * h (x j)) := by
    apply Finset.measurable_sum
    intro j hj
    exact measurable_const.mul (cdf_evaluation (x j)).continuous.measurable
  rw [Measure.map_map hm halfLineLinfEquiv.continuous.measurable]
  have he : (fun h : KolmogorovSpace => ∑ j, a j * h (x j)) ∘
      (halfLineLinfEquiv : LinfF halfLineIndicatorClass → KolmogorovSpace) =
      fun z => ∑ j, a j * z (halfLineIndex (x j)) := rfl
  rw [he]
  simpa only [cdf_donsker_cdf, hc] using
    cdf_donor_projection P hν r x a


/-- The actual empirical CDF has exactly the literature's normalized-count formula. -/
theorem cdf_donsker_empirical_formula {Ω : Type u} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cdf (empirical X n ω) id = AronowAudit.Literature.empiricalRealCDF X n ω := by
  classical
  funext t
  unfold cdf prob empirical AronowAudit.Literature.empiricalRealCDF
  simp only [id_eq, Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [ENNReal.toReal_sum (fun i hi => measure_ne_top (Measure.dirac (X i ω)) _)]
  have hd (i : ℕ) : Measure.dirac (X i ω) {y : ℝ | y ≤ t} =
      if X i ω ≤ t then (1 : ℝ≥0∞) else 0 := by
    change Measure.dirac (X i ω) (Iic t) = _
    rw [Measure.dirac_apply' _ measurableSet_Iic]
    rfl
  simp_rw [hd]
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_one, ENNReal.toReal_zero,
    div_eq_mul_inv, mul_comm]

/-- Normalized finite counts lie in the unit interval, also at sample size zero. -/
theorem cdf_donsker_empirical_bound {Ω : Type u} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ) :
    0 ≤ AronowAudit.Literature.empiricalRealCDF X n ω t ∧
      AronowAudit.Literature.empiricalRealCDF X n ω t ≤ 1 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [AronowAudit.Literature.empiricalRealCDF]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i hi => by split_ifs <;> norm_num) hn0.le
  · apply (div_le_one hn0).mpr
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i hi => by split_ifs <;> norm_num
      _ = _ := by simp

/-- The literature embedding never takes its fallback on an empirical CDF. -/
theorem cdf_donsker_empirical_embedding {Ω : Type u}
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    AronowAudit.Literature.boundedRealEmbedding
      (AronowAudit.Literature.empiricalRealCDF X n ω) t =
        AronowAudit.Literature.empiricalRealCDF X n ω t := by
  have hb : Memℓp (AronowAudit.Literature.empiricalRealCDF X n ω) ∞ := by
    refine memℓp_infty ⟨1, ?_⟩
    rintro y ⟨x, rfl⟩
    change ‖AronowAudit.Literature.empiricalRealCDF X n ω x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (cdf_donsker_empirical_bound X n ω x).1]
    exact (cdf_donsker_empirical_bound X n ω x).2
  simp [AronowAudit.Literature.boundedRealEmbedding, hb]


/-- The half-line empirical process and the empirical CDF process are equal as bounded paths. -/
theorem cdf_donsker_path {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure ℝ) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hmem : Memℓp (fun f : halfLineIndicatorClass =>
      empiricalProcess P n (fun i : Fin n => X i.val ω) (f : ℝ → ℝ)) ∞) :
    halfLineLinfEquiv (empiricalProcessLinf (fun i : Fin n => X i.val ω) hmem) =
      Real.sqrt n • (AronowAudit.Literature.boundedRealEmbedding
        (AronowAudit.Literature.empiricalRealCDF X n ω) - kolmogorovEmbed (cdf P id)) := by
  classical
  apply lp.ext
  funext t
  change empiricalProcess P n (fun i : Fin n => X i.val ω) (halfLineIndicator t) = _
  rw [empiricalProcess_halfLine_eq]
  change Real.sqrt n * (empiricalCDF n (fun i : Fin n => X i.val ω) t -
      ProbabilityTheory.cdf P t) = Real.sqrt n *
    (AronowAudit.Literature.boundedRealEmbedding
      (AronowAudit.Literature.empiricalRealCDF X n ω) t - kolmogorovEmbed (cdf P id) t)
  rw [cdf_donsker_empirical_embedding, kolmogorov_embedding_preserves_cdf_supporting,
    cdf_donsker_cdf]
  congr 2
  have he : (∑ i : Fin n, halfLineIndicator t (X i.val ω)) =
      ∑ i ∈ Finset.range n, if X i ω ≤ t then (1 : ℝ) else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => halfLineIndicator t (X i ω))]
    simp only [halfLineIndicator, Set.indicator_apply, mem_Iic, Pi.one_apply]
  unfold empiricalCDF empiricalAvg AronowAudit.Literature.empiricalRealCDF
  rw [he]
  ring

/-- The empirical CDF element and the bounded normalized-count path are identical. -/
theorem cdf_donsker_empirical_element {Ω : Type u} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    empiricalCDFElement X n ω = AronowAudit.Literature.boundedRealEmbedding
      (AronowAudit.Literature.empiricalRealCDF X n ω) := by
  rw [empiricalCDFElement, cdf_donsker_empirical_formula]
  rfl

/-- The donor's law is tight, tangent-supported, and is a CDF Gaussian bridge. -/
theorem cdf_donsker_law [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    ∃ ν : Measure KolmogorovSpace, IsProbabilityMeasure ν ∧
      IsTightMeasureSet ({ν} : Set (Measure KolmogorovSpace)) ∧
      IsCDFBridge (cdf P id) ν ∧
      ∀ {Ξ : Type} [MeasurableSpace Ξ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
        (X : ℕ → Ξ → ℝ), IID ρ X → ρ.map (X 0) = P →
        OuterWeakLimit ρ (fun n ω => Real.sqrt n •
          (AronowAudit.Literature.boundedRealEmbedding
            (AronowAudit.Literature.empiricalRealCDF X n ω) - kolmogorovEmbed (cdf P id))) ν := by
  obtain ⟨κ, hκ, hprocess⟩ := half_line_donsker_source P
  have hprob := hκ.isProbabilityMeasure
  let ν : Measure KolmogorovSpace := κ.map halfLineLinfEquiv
  have hνprob : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  refine ⟨ν, hνprob, ?_, cdf_donor_bridge P hκ, ?_⟩
  · simpa only [image_singleton] using hκ.tight.map halfLineLinfEquiv.continuous
  · intro Ξ mΞ ρ pρ X hiid hlaw
    obtain ⟨hmem, hlim⟩ := hprocess ρ X hiid.1 hiid.2.1 hiid.2.2 hlaw
    have hlim' := hlim.continuous_comp halfLineLinfEquiv.continuous
    apply (outer_weak_donor_iff ρ _ ν).mpr
    simpa only [Function.comp_def, cdf_donsker_path P X] using hlim'

/-- Bounded real maps have a nonempty set of integrable majorant means. -/
theorem cdf_outer_majorants_nonempty {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (C : ℝ) (hZ : ∀ ω, |Z ω| ≤ C) :
    {r | ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ ω, Z ω ≤ g ω) ∧ mean μ g = r}.Nonempty := by
  refine ⟨C, (fun _ => C), measurable_const, integrable_const C,
    (fun ω => (abs_le.mp (hZ ω)).2), ?_⟩
  simp [mean]

/-- Boundedness also bounds the majorant means below. -/
theorem cdf_outer_majorants_bdd {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (C : ℝ) (hZ : ∀ ω, |Z ω| ≤ C) :
    BddBelow {r | ∃ g : Ω → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ ω, Z ω ≤ g ω) ∧ mean μ g = r} := by
  refine ⟨-C, ?_⟩
  rintro r ⟨g, hgm, hgi, hg, rfl⟩
  have hi := integral_mono (integrable_const (-C) : Integrable (fun _ : Ω => -C) μ)
    hgi (fun ω => (abs_le.mp (hZ ω)).1.trans (hg ω))
  simpa [mean] using hi

/-- Inner expectation is bounded above by outer expectation, for arbitrary bounded maps. -/
theorem cdf_outer_inner_le {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ)
    (C : ℝ) (hZ : ∀ ω, |Z ω| ≤ C) :
    -outerMean μ (fun ω => -Z ω) ≤ outerMean μ Z := by
  have hneg (ω) : |-Z ω| ≤ C := by simpa using hZ ω
  apply le_csInf (cdf_outer_majorants_nonempty μ Z C hZ)
  rintro r ⟨g, hgm, hgi, hg, rfl⟩
  have hle : -mean μ g ≤ outerMean μ (fun ω => -Z ω) := by
    apply le_csInf (cdf_outer_majorants_nonempty μ (fun ω => -Z ω) C hneg)
    rintro s ⟨k, hkm, hki, hk, rfl⟩
    have hi := integral_mono hgi.neg hki (fun ω => by
      change -g ω ≤ k ω
      linarith [hg ω, hk ω])
    simpa only [Pi.neg_apply, integral_neg, mean] using hi
  linarith

/-- Pullback of majorants gives the upper bound needed for sample-space transport. -/
theorem cdf_outer_pullback_le {Ω : Type u} {Ξ : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (S : Ω → Ξ) (hS : Measurable S) (hlaw : μ.map S = ρ)
    (Z : Ξ → ℝ) (C : ℝ) (hZ : ∀ ξ, |Z ξ| ≤ C) :
    outerMean μ (fun ω => Z (S ω)) ≤ outerMean ρ Z := by
  apply le_csInf (cdf_outer_majorants_nonempty ρ Z C hZ)
  rintro r ⟨g, hgm, hgi, hg, rfl⟩
  apply csInf_le (cdf_outer_majorants_bdd μ (fun ω => Z (S ω)) C (fun ω => hZ (S ω)))
  refine ⟨(fun ω => g (S ω)), hgm.comp hS, ?_, (fun ω => hg (S ω)), ?_⟩
  · exact (integrable_map_measure hgm.aestronglyMeasurable hS.aemeasurable).mp
      (hlaw.symm ▸ hgi)
  · exact (integral_map hS.aemeasurable (hlaw.symm ▸ hgm.aestronglyMeasurable)).symm.trans
      (congrArg (fun m => ∫ ξ, g ξ ∂m) hlaw)

/-- Upper and lower majorant bounds transport an outer weak limit across universes. -/
theorem cdf_outer_sample_transport {Ω : Type u} {Ξ : Type v} {E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [TopologicalSpace E] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (S : Ω → Ξ) (hS : Measurable S) (hlaw : μ.map S = ρ)
    (Z : ℕ → Ξ → E) (ν : Measure E) (hZ : OuterWeakLimit ρ Z ν) :
    OuterWeakLimit μ (fun n ω => Z n (S ω)) ν := by
  intro f hf hb
  obtain ⟨C, hC⟩ := hb
  have hn (x) : |-f x| ≤ C := by simpa using hC x
  have hu (n) := cdf_outer_pullback_le μ ρ S hS hlaw
    (fun ξ => f (Z n ξ)) C (fun ξ => hC (Z n ξ))
  have hl (n) := neg_le_neg (cdf_outer_pullback_le μ ρ S hS hlaw
    (fun ξ => -f (Z n ξ)) C (fun ξ => hn (Z n ξ)))
  have hm (n) := cdf_outer_inner_le μ (fun ω => f (Z n (S ω))) C
    (fun ω => hC (Z n (S ω)))
  have ht := hZ f hf ⟨C, hC⟩
  exact ⟨ht.2.squeeze ht.1 (fun n => (hl n).trans (hm n)) hu,
    ht.2.squeeze ht.1 hl (fun n => (hm n).trans (hu n))⟩

/-- The exact tangent-supported empirical-CDF Donsker theorem, on arbitrary sample universes. -/
theorem cdf_donsker_supported {Ω : Type u} [MeasurableSpace Ω]
    [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hiid : IID μ X) :
    ∃ ν : Measure KolmogorovSpace, IsProbabilityMeasure ν ∧
      IsTightMeasureSet ({ν} : Set (Measure KolmogorovSpace)) ∧
      IsCDFBridge (cdf μ (X 0)) ν ∧
      OuterWeakLimit μ (fun n ω => Real.sqrt n •
        (empiricalCDFElement X n ω - kolmogorovEmbed (cdf μ (X 0)))) ν := by
  let P : Measure ℝ := μ.map (X 0)
  have hP : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let ρ : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => P)
  let Y : ℕ → (ℕ → ℝ) → ℝ := fun i z => z i
  have hY : IID ρ Y := by
    refine ⟨fun i => measurable_pi_apply i, ?_, ?_⟩
    · exact iIndepFun_infinitePi (P := fun _ : ℕ => P) (X := fun _ (x : ℝ) => x)
        (fun _ => measurable_id)
    · intro i
      exact ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
        by simp only [Y, ρ, Measure.infinitePi_map_eval]⟩
  have hY0 : ρ.map (Y 0) = P := Measure.infinitePi_map_eval _ 0
  obtain ⟨ν, hp, ht, hb, hw⟩ := cdf_donsker_law P
  have hcanon := hw ρ Y hY hY0
  let S : Ω → (ℕ → ℝ) := fun ω i => X i ω
  have hS : Measurable S := measurable_pi_iff.mpr hiid.1
  have hSmap : μ.map S = ρ := by
    rw [hiid.2.1.map_fun_eq_infinitePi_map hiid.1]
    congr 1
    funext i
    exact (hiid.2.2 i).map_eq
  have htrans := cdf_outer_sample_transport μ ρ S hS hSmap _ ν hcanon
  have hF : cdf μ (X 0) = cdf P id := CondP001cd_cdf_law μ (X 0) (hiid.1 0)
  refine ⟨ν, hp, ht, hF.symm ▸ hb, ?_⟩
  have he (n : ℕ) (ω : Ω) : AronowAudit.Literature.boundedRealEmbedding
      (AronowAudit.Literature.empiricalRealCDF Y n (S ω)) = empiricalCDFElement X n ω := by
    rw [cdf_donsker_empirical_element]
    rfl
  simp_rw [he] at htrans
  simpa only [hF] using htrans


end AronowAudit.P001.Wave1.TailA
