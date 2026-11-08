import SAP.P017.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace SAP.P017.WH.W1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

noncomputable section

theorem T7_assembly : T7WholeStatement.{u, v} := by
  have hmain : T7Statement.{u, v} := by
    apply SAP.P017.Bridge.T7_correspondence.mpr
    intro Ω Ξ mΩ mΞ G hG τ hτm hτi hc P hP hat hh
    have h := AronowAudit.P017.corrected_proposition3 G τ hτm hτi hc P hat hh
    have hz : ∀ n ω, AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ)
        (AronowAudit.P017.effectRadius G τ) (hat n ω) →
        hat n ω - AronowAudit.P017.clipTarget (AronowAudit.P017.populationMean G τ)
          (AronowAudit.P017.effectRadius G τ) (hat n ω) = 0 := by
      intro n ω hω
      rw [(AronowAudit.P017.clipTarget_eq_self_iff _ _ _).mpr hω, sub_self]
    refine ⟨h, hz, ?_, ?_, AronowAudit.P017.proposition3 G τ hτm hτi hc P hat hh⟩
    · intro n η a hη ha
      have hsub : {ω | |hat n ω - AronowAudit.P017.clipTarget
          (AronowAudit.P017.populationMean G τ) (AronowAudit.P017.effectRadius G τ)
          (hat n ω)| > η * a} ⊆
          {ω | ¬ AronowAudit.P017.inside (AronowAudit.P017.populationMean G τ)
            (AronowAudit.P017.effectRadius G τ) (hat n ω)} := by
        intro ω hω hin
        change η * a < |hat n ω - AronowAudit.P017.clipTarget _ _ _| at hω
        rw [hz n ω hin, abs_zero] at hω
        exact (not_lt_of_ge (mul_pos hη ha).le) hω
      exact ⟨hsub, measureReal_mono hsub (measure_ne_top P _)⟩
    · by_cases htop : AronowAudit.P017.effectRadius G τ = ⊤
      · simp [AronowAudit.P017.inside, htop, AronowAudit.P017.pr]
      · simpa only [AronowAudit.P017.inside, ENNReal.ofReal_le_iff_le_toReal htop, not_le] using
          h.2.1 (AronowAudit.P017.effectRadius G τ).toReal (ENNReal.toReal_pos hc.ne' htop)
  obtain ⟨hm, hi, hμ, hS, hc, _⟩ :=
    AronowAudit.P017.Wave1.normal_shift_probability_counterexample_proof
  have hμ' : populationMean normalPopulation normalEffect = 0 := hμ
  have hzero : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun n => sqrtN n * slowDet n 0) atTop atTop := by
    apply ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    simp only [sqrtN, slowDet, Real.sqrt_eq_rpow]
    rw [← Real.rpow_add hnR]
    norm_num
  refine ⟨hmain, hm, hi, hμ', hS, hc, fun _ => measurable_const, ?_, ?_⟩
  · rw [hμ']
    intro b hb
    have hlt : ∀ᶠ n : ℕ in atTop, |(n : ℝ) ^ (-(1 / 4 : ℝ))| < b := by
      exact hzero.abs.eventually (Iio_mem_nhds (by simpa only [abs_zero] using hb))
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [hlt] with n hn
    have hevent : {ω : ℝ | |slowDet n ω - 0| > b} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω
      change ¬ b < |(n : ℝ) ^ (-(1 / 4 : ℝ)) - 0|
      simpa only [sub_zero] using not_lt_of_ge hn.le
    rw [hevent]
    simp [pr]
  · rw [hμ']
    intro htight
    obtain ⟨M, hM, hbound⟩ := htight (1 / 2) (by norm_num)
    obtain ⟨n, hn, hnM⟩ := (hbound.and (hscaled.eventually_gt_atTop M)).exists
    have hnM' : M < |sqrtN n * (slowDet n 0 - 0)| := by
      simpa only [sub_zero, abs_of_pos (hM.trans hnM)] using hnM
    have hevent : {ω : ℝ | |sqrtN n * (slowDet n ω - 0)| > M} = univ := by
      ext ω
      change (M < |sqrtN n * (slowDet n ω - 0)|) ↔ True
      exact iff_true_intro hnM'
    change pr (Measure.dirac (0 : ℝ)) {ω | |sqrtN n * (slowDet n ω - 0)| > M} < 1 / 2 at hn
    rw [hevent] at hn
    norm_num [pr] at hn


end
end SAP.P017.WH.W1
