import SAP.P017.Defs.WholeW3
import AronowAudit.P017.P017_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace SAP.P017.WH.W3

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

noncomputable section

/-! There are no unproved leaves. The only asymptotic-normality step is the
existing `AronowAudit.P017.root_normal_tight_and_consistent`. All extensions
of the clipping argument are short event inclusions and probability squeezes,
proved below, including infinite radius and arbitrary scale values at zero. -/

/-- Assemble the corrected whole claim without leaf hypotheses. Establish the
exact clipping facts first. Under consistency the outside probability tends
to zero, so event bounds give every positive-sequence rate and the scaled
actual-error limit. Invoke Definition 1 only for root-n tightness and consistency. -/
theorem T7_assembly : T7WholeStatement_W3.{u, v} := by
  intro Ω Ξ mΩ mΞ G hG τ _hτm _hτi hc P hP hat _hhm
  let μ := populationMean G τ
  let c := effectRadius G τ
  change ClippingFactsW3 P hat μ c ∧
    (Consistent P hat μ → ClippingLimitsW3 P hat μ c) ∧
    (RootNNormal P hat μ →
      BoundedInProbability P (fun n ω => sqrtN n * (hat n ω - μ)) ∧
      ClippingLimitsW3 P hat μ c)
  have hself (x : ℝ) : clipTarget μ c x = x ↔ inside μ c x :=
    AronowAudit.P017.clipTarget_eq_self_iff μ c x
  have hzero (n : ℕ) (ω : Ξ) (hin : inside μ c (hat n ω)) :
      ClippingErrorW3 hat μ c n ω = 0 := by
    change hat n ω - clipTarget μ c (hat n ω) = 0
    rw [(hself (hat n ω)).mpr hin, sub_self]
  have hbound (n : ℕ) (t : ℝ) (ht : 0 < t) :
      {ω | |ClippingErrorW3 hat μ c n ω| > t} ⊆
        {ω | ¬ inside μ c (hat n ω)} ∧
      pr P {ω | |ClippingErrorW3 hat μ c n ω| > t} ≤
        pr P {ω | ¬ inside μ c (hat n ω)} := by
    have hsub : {ω | |ClippingErrorW3 hat μ c n ω| > t} ⊆
        {ω | ¬ inside μ c (hat n ω)} := by
      intro ω h hin
      change t < |ClippingErrorW3 hat μ c n ω| at h
      rw [hzero n ω hin, abs_zero] at h
      exact (not_lt_of_ge ht.le) h
    exact ⟨hsub, measureReal_mono hsub (measure_ne_top P _)⟩
  have hfacts : ClippingFactsW3 P hat μ c := by
    refine ⟨?_, ?_, ?_⟩
    · intro n _hn ω
      change hat n ω - clipTarget μ c (hat n ω) = 0 ↔ inside μ c (hat n ω)
      rw [sub_eq_zero, eq_comm]
      exact hself (hat n ω)
    · intro n _hn η a hη ha
      exact hbound n (η * a) (mul_pos hη ha)
    · intro htop n _hn ω
      simp [ClippingErrorW3, clipTarget, htop]
  have hlimits (hh : Consistent P hat μ) : ClippingLimitsW3 P hat μ c := by
    have hout : Tendsto (fun n => pr P {ω | ¬ inside μ c (hat n ω)})
        atTop (𝓝 0) := by
      by_cases htop : c = ⊤
      · simp only [inside, htop, le_top, not_true_eq_false, ofPred_false, pr,
          measureReal_empty]
        exact tendsto_const_nhds
      · simpa only [inside, ENNReal.ofReal_le_iff_le_toReal htop, not_le] using
          hh c.toReal (ENNReal.toReal_pos hc.ne' htop)
    refine ⟨hh, hout, ?_, ?_⟩
    · intro a ha η hη
      apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hout
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact (hbound n (η * a n) (mul_pos hη (ha n hn))).2
    · intro η hη
      apply squeeze_zero (fun _ => measureReal_nonneg) _ hout
      intro n
      apply measureReal_mono (h₂ := measure_ne_top P _)
      intro ω h hin
      change η * 1 < |sqrtN n * ClippingErrorW3 hat μ c n ω| at h
      rw [hzero n ω hin, mul_zero, abs_zero, mul_one] at h
      exact (not_lt_of_ge hη.le) h
  refine ⟨hfacts, hlimits, ?_⟩
  intro hh
  have hb : BoundedInProbability P (fun n ω => sqrtN n * (hat n ω - μ)) ∧
      Consistent P hat μ :=
    AronowAudit.P017.root_normal_tight_and_consistent P hat μ hh
  exact ⟨hb.1, hlimits hb.2⟩

end
end SAP.P017.WH.W3
