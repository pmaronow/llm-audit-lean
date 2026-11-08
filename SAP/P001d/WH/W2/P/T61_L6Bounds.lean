import SAP.P001d.WH.W2.Leaves
import AronowAudit.External.StatLean.ComputationalStatistics.Resampling.BootstrapMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W2.P.T61_L6

open SAP.P001d
open AronowAudit.P001.TailA

local instance instDecidableT61 (p : Prop) : Decidable p := Classical.propDecidable p

private def signIndicator (z : ℝ) : ℝ := if z ≤ 0 then 1 else 0

private lemma whole_sign_eq_mcEstimate {n : ℕ} (x : Fin n → ℝ) :
    SAP.P001d.wholeEmpiricalCDF x 0 =
      StatLean.ComputationalStatistics.mcEstimate signIndicator x := by
  unfold SAP.P001d.wholeEmpiricalCDF
    StatLean.ComputationalStatistics.mcEstimate signIndicator
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp [div_eq_mul_inv, mul_comm]

private lemma resampling_sign_deviation_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    AronowAudit.P001.prob (UniformResampling n)
      {a | (1/8 : ℝ) ≤ |SAP.P001d.wholeEmpiricalCDF
        (AronowAudit.P001.resample x a) 0 -
        SAP.P001d.wholeEmpiricalCDF x 0|} ≤ 16/(n : ℝ) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let P := StatLean.ComputationalStatistics.empiricalMeasure x
  let Q := Measure.pi fun _ : Fin n => P
  let F : (Fin n → ℝ) → ℝ := StatLean.ComputationalStatistics.mcEstimate signIndicator
  have hgmeas : Measurable signIndicator := by
    unfold signIndicator
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  have hg : StronglyMeasurable signIndicator := hgmeas.stronglyMeasurable
  have hgbounds (z : ℝ) : signIndicator z ∈ Set.Icc (0 : ℝ) 1 := by
    unfold signIndicator
    split_ifs <;> norm_num
  have hgLp : MemLp signIndicator 2 P :=
    memLp_of_bounded (ae_of_all P hgbounds) hg.aestronglyMeasurable 2
  have hmean : AronowAudit.P001.mean Q F =
      SAP.P001d.wholeEmpiricalCDF x 0 := by
    calc
      AronowAudit.P001.mean Q F =
          ∫ y, (n : ℝ)⁻¹ * ∑ i : Fin n, signIndicator (y i) ∂Q := rfl
      _ = ∫ z, signIndicator z ∂P :=
        StatLean.ComputationalStatistics.integral_avg_eval_pi (hgLp.integrable one_le_two)
      _ = StatLean.ComputationalStatistics.mcEstimate signIndicator x :=
        StatLean.ComputationalStatistics.integral_empiricalMeasure hg
      _ = SAP.P001d.wholeEmpiricalCDF x 0 :=
        (whole_sign_eq_mcEstimate x).symm
  have hvarEq : ProbabilityTheory.variance F Q =
      ProbabilityTheory.variance signIndicator P / (n : ℝ) :=
    StatLean.ComputationalStatistics.variance_avg_eval_pi hgLp
  have hvarG : ProbabilityTheory.variance signIndicator P ≤ (1/4 : ℝ) := by
    calc
      ProbabilityTheory.variance signIndicator P ≤ ((1 - 0) / 2)^2 :=
        ProbabilityTheory.variance_le_sq_of_bounded (ae_of_all P hgbounds)
          hgmeas.aemeasurable
      _ = 1/4 := by norm_num
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hvar : ProbabilityTheory.variance F Q ≤ 1/(4*(n : ℝ)) := by
    rw [hvarEq]
    have := div_le_div_of_nonneg_right hvarG hnR.le
    convert this using 1 <;> field_simp
  have hFbounds (y : Fin n → ℝ) : F y ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [F, StatLean.ComputationalStatistics.mcEstimate]
    constructor
    · apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      exact Finset.sum_nonneg fun i _ => (hgbounds (y i)).1
    · have hs : (∑ i : Fin n, signIndicator (y i)) ≤ (n : ℝ) := by
        calc
          (∑ i : Fin n, signIndicator (y i)) ≤ ∑ _i : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => (hgbounds (y i)).2
          _ = n := by simp
      calc
        (n : ℝ)⁻¹ * ∑ i : Fin n, signIndicator (y i) ≤
            (n : ℝ)⁻¹ * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg n))
        _ = 1 := by field_simp [ne_of_gt hnR]
  have hFmeas : Measurable F := by
    change Measurable (fun y : Fin n → ℝ => (n : ℝ)⁻¹ *
      ∑ i : Fin n, signIndicator (y i))
    exact measurable_const.mul (Finset.univ.measurable_sum fun i _ =>
      hgmeas.comp (measurable_pi_apply i))
  have hFlp : MemLp F 2 Q :=
    memLp_of_bounded (ae_of_all Q hFbounds) hFmeas.aestronglyMeasurable 2
  have hcheb := AronowAudit.P001.chebyshev_probability Q F hFlp (1/8 : ℝ) (by norm_num)
  have hcheb' : AronowAudit.P001.prob Q
      {y | (1/8 : ℝ) ≤ |F y - SAP.P001d.wholeEmpiricalCDF x 0|} ≤
        ProbabilityTheory.variance F Q / (1/8 : ℝ)^2 := by
    simpa only [hmean, AronowAudit.P001.var] using hcheb
  have hsample : Q = (UniformResampling n).map
      (AronowAudit.P001.resample x) :=
    AronowAudit.P001.TailA.empirical_value_law_eq_index_map x
  have hdist : Q.map F = (UniformResampling n).map
      (fun a => F (AronowAudit.P001.resample x a)) := by
    rw [hsample]
    exact Measure.map_map hFmeas
      (Measurable.of_discrete (f := AronowAudit.P001.resample x))
  let E : Set ℝ := {z | (1/8 : ℝ) ≤ |z - SAP.P001d.wholeEmpiricalCDF x 0|}
  have hE : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_le measurable_const
      ((measurable_id.sub_const _).abs)
  have hprobEq : AronowAudit.P001.prob (UniformResampling n)
      {a | F (AronowAudit.P001.resample x a) ∈ E} =
      AronowAudit.P001.prob Q {y | F y ∈ E} := by
    unfold AronowAudit.P001.prob
    have hh := congrArg (fun ν : Measure ℝ => ν E) hdist
    rw [Measure.map_apply hFmeas hE,
      Measure.map_apply (Measurable.of_discrete (f := fun a => F (AronowAudit.P001.resample x a))) hE] at hh
    exact congrArg ENNReal.toReal hh.symm
  have hfinal : AronowAudit.P001.prob (UniformResampling n)
      {a | F (AronowAudit.P001.resample x a) ∈ E} ≤ 16/(n : ℝ) := by
    rw [hprobEq]
    calc
      AronowAudit.P001.prob Q {y | F y ∈ E} ≤ ProbabilityTheory.variance F Q / (1/8 : ℝ)^2 := hcheb'
      _ ≤ (1/(4*(n : ℝ))) / (1/8 : ℝ)^2 := by
        gcongr
      _ = 16/(n : ℝ) := by norm_num; ring
  simpa only [F, whole_sign_eq_mcEstimate, Set.mem_setOf_eq, E] using hfinal


lemma resampling_bad_branch_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ)
    (hp : SAP.P001d.wholeEmpiricalCDF x 0 ∈ Set.Icc (3/8 : ℝ) (5/8)) :
    AronowAudit.P001.prob (UniformResampling n)
      {a | SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) 0 ∉
        Set.Icc (1/4 : ℝ) (3/4)} ≤ 16/(n : ℝ) := by
  have hsub : {a | SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) 0 ∉
      Set.Icc (1/4 : ℝ) (3/4)} ⊆
      {a | (1/8 : ℝ) ≤ |SAP.P001d.wholeEmpiricalCDF
        (AronowAudit.P001.resample x a) 0 - SAP.P001d.wholeEmpiricalCDF x 0|} := by
    intro a ha
    simp only [Set.mem_Icc, not_and_or, not_le] at ha hp
    rcases ha with hq | hq
    · have hnonneg : 0 ≤ SAP.P001d.wholeEmpiricalCDF x 0 -
          SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) 0 := by linarith
      change (1/8 : ℝ) ≤ |SAP.P001d.wholeEmpiricalCDF
        (AronowAudit.P001.resample x a) 0 - SAP.P001d.wholeEmpiricalCDF x 0|
      have hnonpos : SAP.P001d.wholeEmpiricalCDF
          (AronowAudit.P001.resample x a) 0 - SAP.P001d.wholeEmpiricalCDF x 0 ≤ 0 := by linarith
      change (1/8 : ℝ) ≤ |SAP.P001d.wholeEmpiricalCDF
        (AronowAudit.P001.resample x a) 0 - SAP.P001d.wholeEmpiricalCDF x 0|
      rw [abs_of_nonpos hnonpos]
      linarith
    · have hnonneg : 0 ≤ SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) 0 -
          SAP.P001d.wholeEmpiricalCDF x 0 := by linarith
      change (1/8 : ℝ) ≤ |SAP.P001d.wholeEmpiricalCDF
        (AronowAudit.P001.resample x a) 0 - SAP.P001d.wholeEmpiricalCDF x 0|
      rw [abs_of_nonneg hnonneg]
      linarith
  have hmono : AronowAudit.P001.prob (UniformResampling n)
      {a | SAP.P001d.wholeEmpiricalCDF (AronowAudit.P001.resample x a) 0 ∉
        Set.Icc (1/4 : ℝ) (3/4)} ≤
      AronowAudit.P001.prob (UniformResampling n)
      {a | (1/8 : ℝ) ≤ |SAP.P001d.wholeEmpiricalCDF
        (AronowAudit.P001.resample x a) 0 - SAP.P001d.wholeEmpiricalCDF x 0|} := by
    unfold AronowAudit.P001.prob
    apply ENNReal.toReal_mono (measure_ne_top (UniformResampling n) _)
    exact measure_mono hsub
  exact hmono.trans (resampling_sign_deviation_bound hn x)

private lemma bootstrap_test_pair_bound {n : ℕ} (hn : 0 < n)
    (T U : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (f : ℝ → ℝ) (C : ℝ)
    (hC : ∀ z, |f z| ≤ C) :
    |SAP.P001d.bootstrapTestMean T x f - SAP.P001d.bootstrapTestMean U x f| ≤ 2*C := by
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hC 0)
  have hdiff (z w : ℝ) : |f z - f w| ≤ 2*C := by
    calc
      |f z - f w| ≤ |f z| + |f w| := abs_sub _ _
      _ ≤ C+C := add_le_add (hC z) (hC w)
      _ = 2*C := by ring
  have hden : 0 < (n : ℝ)^n := pow_pos (by exact_mod_cast hn) _
  have hbasic : |SAP.P001d.bootstrapTestMean T x f -
      SAP.P001d.bootstrapTestMean U x f| ≤
      (∑ a : Fin n → Fin n, |f (Real.sqrt n * (T (fun i => x (a i))-T x)) -
        f (Real.sqrt n * (U (fun i => x (a i))-U x))|)/(n : ℝ)^n := by
    change |(∑ a : Fin n → Fin n, f (Real.sqrt n *
        (T (fun i => x (a i))-T x)))/(n : ℝ)^n -
      (∑ a : Fin n → Fin n, f (Real.sqrt n *
        (U (fun i => x (a i))-U x)))/(n : ℝ)^n| ≤ _
    rw [← sub_div, abs_div, abs_of_pos hden, ← Finset.sum_sub_distrib]
    apply div_le_div_of_nonneg_right _ hden.le
    exact Finset.abs_sum_le_sum_abs
      (fun a : Fin n → Fin n => f (Real.sqrt n * (T (fun i => x (a i))-T x)) -
        f (Real.sqrt n * (U (fun i => x (a i))-U x))) Finset.univ
  calc
    _ ≤ (∑ _a : Fin n → Fin n, (2*C : ℝ))/(n : ℝ)^n := by
      apply hbasic.trans
      apply div_le_div_of_nonneg_right _ hden.le
      exact Finset.sum_le_sum fun a _ => hdiff _ _
    _ = 2*C := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul]
      norm_cast
      rw [div_eq_mul_inv]
      field_simp [ne_of_gt hden]
      <;> ring

end SAP.P001d.WH.W2.P.T61_L6
