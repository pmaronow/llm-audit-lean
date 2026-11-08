import SAP.P017.Defs
import SAP.P017.Bridge
import AronowAudit.P017.P017_Audit
import AronowAudit.P017.Wave1.Gap.GLP017B1
import AronowAudit.P017.Wave1.Gap.GLP017B2
import AronowAudit.P017.Wave1.Gap.GLP017B4
import AronowAudit.P017.Wave1.Gap.GP017B1
import AronowAudit.P017.Wave1.Gap.GP017B1b
import AronowAudit.P017.Wave1.Gap.GP017B2
import AronowAudit.P017.Wave1.Gap.GP017B3
import AronowAudit.P017.Wave1.Checks.FidP017Contracts
import SAP.P017.WH.W1.Proofs.T14
import SAP.P017.WH.W1.Proofs.T15
import SAP.P017.WH.W1.Proofs.T2
import SAP.P017.WH.W1.Proofs.T3
import SAP.P017.WH.W2.Proofs.T11
import SAP.P017.WH.W2.Proofs.T12
import SAP.P017.WH.W3.Proofs.T7

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u1 u2 u3 u4 u5

open MeasureTheory ProbabilityTheory Filter Set AronowAudit.P017
open scoped BigOperators Topology ENNReal NNReal Classical

theorem SAP.P017.T1 : SAP.P017.T1Statement := by
  exact SAP.P017.Bridge.T1_correspondence.mpr
    AronowAudit.P017.Wave1.uniform_ipw_counterexample_proof

theorem SAP.P017.T2 : SAP.P017.T2WholeStatement.{u1} := SAP.P017.WH.W1.T2_whole

theorem SAP.P017.T3 : SAP.P017.T3WholeStatement.{u1, u2} := SAP.P017.WH.W1.T3_whole

theorem SAP.P017.T4 : SAP.P017.T4Statement.{u1, u2} := by
  apply SAP.P017.Bridge.T4_correspondence.mpr
  intro Ω mΩ G hG τ hτm hτi hc
  have hr := interior_radius_representation G τ hτm hτi hc
  refine ⟨hr.1, ?_, ?_, ?_, weighted_support_consequences G τ hτm hτi, ?_⟩
  · intro d hd hsmall
    refine ⟨hr.2 d hd hsmall,
      fun x => clipReal_distance _ d x hd.le,
      fun x => clipReal_eq_self_iff _ d x hd.le, ?_, ?_⟩
    · intro Ξ mΞ P hP hat
      refine ⟨(interior_radius_finite_companions P hat _ d hd).2.2, ?_⟩
      intro hhm hcond
      exact interior_radius_corollary P hat hhm _ d hd hcond
    · intro c hdc
      exact smaller_radius_changes_target _ c d hd hdc
  · intro hfinite
    have hp := ENNReal.toReal_pos hc.ne' hfinite
    exact ⟨half_pos hp,
      (ENNReal.ofReal_lt_iff_lt_toReal (half_pos hp).le hfinite).mpr (half_lt_self hp)⟩
  · intro htop d hd
    simp [htop]
  · exact (AronowAudit.P017.Wave1.corrected_proposition1_proof G τ hτm hτi hc
      (Measure.dirac (0 : ℝ)) (fun _ _ => 0) (fun _ => measurable_const)).2.2.1

theorem SAP.P017.T5 : SAP.P017.T5Statement := by
  exact SAP.P017.Bridge.T5_correspondence.mpr
    AronowAudit.P017.Wave1.normal_shift_probability_counterexample_proof

theorem SAP.P017.T6 : SAP.P017.T6Statement := by
  apply SAP.P017.Bridge.T6_correspondence.mpr
  have h := AronowAudit.P017.Wave1.normal_shift_mse_counterexample_proof
  have hhm : ∀ n, Measurable (AronowAudit.P017.shiftedNormalMean n) := by
    intro n
    unfold AronowAudit.P017.shiftedNormalMean AronowAudit.P017.normalMean AronowAudit.P017.sampleMean
    fun_prop
  have hlim := AronowAudit.P017.Wave1.corrected_proposition4_limits_proof
    (AronowAudit.P017.iidSamples AronowAudit.P017.normalPopulation) AronowAudit.P017.shiftedNormalMean AronowAudit.P017.normalZ AronowAudit.P017.normalEpsilon 0 1 1
    (by norm_num) (by norm_num) hhm h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
  refine ⟨h, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨(shifted_25_central (AronowAudit.P017.normalMean 25 s) hs).1,
      (shifted_25_central (AronowAudit.P017.normalMean 25 s) hs).2.1⟩
  · exact hlim.1
  · have heq : (fun n s => 0 + AronowAudit.P017.normalZ n s / AronowAudit.P017.sqrtN n -
        AronowAudit.P017.clipReal 0 1 (AronowAudit.P017.shiftedNormalMean n s)) = AronowAudit.P017.shiftedDifference := by
      funext n s
      unfold AronowAudit.P017.shiftedDifference AronowAudit.P017.normalZ
      by_cases hn : n = 0
      · simp [hn, AronowAudit.P017.normalMean, AronowAudit.P017.sampleMean, AronowAudit.P017.sqrtN]
      · have hs : AronowAudit.P017.sqrtN n ≠ 0 := by
          apply ne_of_gt
          unfold AronowAudit.P017.sqrtN
          exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
        simp [hs]
    simpa only [heq] using hlim.2

theorem SAP.P017.T7 : SAP.P017.T7WholeStatement_W3 := SAP.P017.WH.W3.T7_whole

theorem SAP.P017.T8 : SAP.P017.T8Statement.{u1, u2, u3} := by
  apply SAP.P017.Bridge.T8_correspondence.mpr
  refine ⟨@AronowAudit.P017.Wave1.corrected_proposition4_finite_proof,
    @AronowAudit.P017.Wave1.corrected_proposition4_limits_proof, ?_, @infinite_radius_facts⟩
  intro μ c x y
  calc
    |x - AronowAudit.P017.clipReal μ c y| = |AronowAudit.P017.residual μ c x + (AronowAudit.P017.clipReal μ c x - AronowAudit.P017.clipReal μ c y)| := by
      congr 1
      unfold AronowAudit.P017.residual
      ring
    _ ≤ _ := abs_add_le _ _

theorem SAP.P017.T9 : SAP.P017.T9SamplingStatement := by
  apply SAP.P017.Bridge.T9Sampling_correspondence.mpr
  intro h
  obtain ⟨hτm, hτi, _, _, _, hc, hOm, hnormal, hfactor, hbad⟩ :=
    AronowAudit.P017.Wave1.proposition1_printed_empirical_counterexample
  have hhm : ∀ n, Measurable (AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand n) := by
    intro n
    unfold AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand
      AronowAudit.P017.ipwObserved AronowAudit.P017.ipwY0 AronowAudit.P017.ipwY1
    fun_prop
  have hHm : Measurable (fun F : Measure (ℝ × ℝ) =>
      ∫ z : ℝ × ℝ, (2 * z.1 * z.2 - 2 * (1 - z.1) * z.2) ∂F) := by
    let κ : ProbabilityTheory.Kernel (Measure (ℝ × ℝ)) (ℝ × ℝ) :=
      ⟨id, measurable_id⟩
    have hf : StronglyMeasurable (fun z : ℝ × ℝ =>
        2 * z.1 * z.2 - 2 * (1 - z.1) * z.2) :=
      (show Measurable (fun z : ℝ × ℝ =>
        2 * z.1 * z.2 - 2 * (1 - z.1) * z.2) from by fun_prop).stronglyMeasurable
    exact (hf.integral_kernel (κ := κ)).measurable
  have hclaims := h AronowAudit.P017.ipwPopulation AronowAudit.P017.ipwEffect
    hτm hτi hc AronowAudit.P017.ipwObserved hOm
    (AronowAudit.P017.iidSamples AronowAudit.P017.ipwPopulation)
    (fun s => s) measurable_id (by simpa using Measure.map_id)
    (AronowAudit.P017.sampleMean AronowAudit.P017.ipwSummand)
    (fun _ F => ∫ z : ℝ × ℝ, (2 * z.1 * z.2 - 2 * (1 - z.1) * z.2) ∂F)
    (fun _ _ => hHm) hhm hfactor hnormal
  let s : ℕ → ℝ × (ℝ × ℝ) := fun _ => (1 / 2, (-1, 0))
  have hs : s ∈ AronowAudit.P017.ipwBadEvent (-1) 1 := by
    intro i hi
    exact ⟨rfl, rfl⟩
  have hnot := ((hbad 1 (by norm_num)).2.2.2 s hs).2.2.2
  exact hnot (hclaims 1 (by norm_num) s)

theorem SAP.P017.T10 : SAP.P017.T10Statement.{u1, u2, u3, u4, u5} := by
  exact SAP.P017.Bridge.T10_correspondence.mpr
    ⟨@corollary1_corrected, @full_real_support, @positive_support_negative_estimates⟩

theorem SAP.P017.T11 : SAP.P017.T11WholeStatement := SAP.P017.WH.W2.T11_whole

theorem SAP.P017.T12 : SAP.P017.T12WholeStatement := SAP.P017.WH.W2.T12_whole

theorem SAP.P017.T13 : SAP.P017.T13Statement.{u1, u2, u3} := by
  apply SAP.P017.Bridge.T13_correspondence.mpr
  refine ⟨@corrected_zero_error_sentence, ?_,
    @AronowAudit.P017.Wave1.normal_plus_remainder_failure_bound_proof⟩
  intro p hp hplim
  obtain ⟨hm, hi, hmu, hS, hc, hnormal, hN, hrest⟩ :=
    AronowAudit.P017.Wave1.arbitrary_outlier_sequence_proof p hp hplim
  refine ⟨hm, hi, hmu, hS, hc, hnormal, ?_⟩
  intro n hn
  obtain ⟨hu, hflag, hind, hZ, hdec, hrem, hnotS, hout, hnonzero, hprob, hrestN⟩ := hN n hn
  exact ⟨by rw [hout]; exact hflag, hprob⟩

theorem SAP.P017.T14 : SAP.P017.T14WholeStatement.{u1, u2} := SAP.P017.WH.W1.T14_whole

theorem SAP.P017.T15 : SAP.P017.T15WholeStatement.{u1, u2} := SAP.P017.WH.W1.T15_whole

theorem SAP.P017.T16 : SAP.P017.T16Statement.{u1, u2} := by
  apply SAP.P017.Bridge.T16_correspondence.mpr
  intro Ω Ξ mΩ mΞ G hG τ hτm hτi P hP hat hh
  exact ⟨proposition2 G τ hτm hτi P hat hh, fun n ω => clipTarget_distance _ _ _⟩
