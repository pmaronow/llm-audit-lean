import SAP.P006a.WH.W2.Leaves
import AronowAudit.P006.Wave1.Gap.RepairT6T7

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a.WH.W2.P.T8_L3

end SAP.P006a.WH.W2.P.T8_L3

theorem SAP.P006a.WH.W2.T8_L3_proof : SAP.P006a.WH.W2.T8_L3 := by
  intro Ω mΩ hstd μ hμ m hm T H p hT hH hp hpb hcoin hTH hpH hi
  letI : MeasurableSpace Ω := mΩ
  letI : StandardBorelSpace Ω := hstd
  let b : Ω → ℝ := fun ω => bit (T ω)
  have hT0 : Measurable[mΩ] T := hT.mono hm le_rfl
  have hH0 : Measurable[mΩ] H := hH.mono hm le_rfl
  have hb : Measurable b := by
    exact (measurable_of_countable bit).comp hT0
  have hbnd (ω : Ω) : ‖b ω‖ ≤ 1 := by
    dsimp [b]
    cases T ω <;> norm_num [bit]
  have hpbnd (ω : Ω) : ‖p ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hpb ω).1]
    exact (hpb ω).2
  have hb_indicator : (fun ω => Set.indicator (T ⁻¹' ({true} : Set Bool))
      (fun _ => (1 : ℝ)) ω) = b := by
    funext ω
    cases h : T ω <;> simp [b, Set.indicator, bit, h]
  have hjoint (A : Set ℝ) :
      (fun ω => Set.indicator
        (T ⁻¹' ({true} : Set Bool) ∩ H ⁻¹' A) (fun _ => (1 : ℝ)) ω) =
        fun ω => b ω * Set.indicator (H ⁻¹' A) (fun _ => (1 : ℝ)) ω := by
    classical
    funext ω
    have htmem : ω ∈ T ⁻¹' ({true} : Set Bool) ↔ T ω = true := by simp
    have hAmem : ω ∈ H ⁻¹' A ↔ H ω ∈ A := by rfl
    cases h : T ω <;> simp [Set.indicator, htmem, hAmem, b, bit, h]
  have hCI := (condIndepFun_iff_condExp_inter_preimage_eq_mul hT0 hH0).mp hi
  have hInd (A : Set ℝ) (hA : MeasurableSet A) :
      μ[(fun ω => b ω * Set.indicator (H ⁻¹' A) (fun _ => (1 : ℝ)) ω) | m] =ᵐ[μ]
        fun ω => p ω * μ[fun η => Set.indicator (H ⁻¹' A)
          (fun _ => (1 : ℝ)) η | m] ω := by
    have hRaw := hCI ({true} : Set Bool) A (measurableSet_singleton true) hA
    have hRewritten :
        μ[(fun ω => b ω * Set.indicator (H ⁻¹' A) (fun _ => (1 : ℝ)) ω) | m] =ᵐ[μ]
          fun ω => μ[(fun η => b η) | m] ω *
            μ[fun η => Set.indicator (H ⁻¹' A) (fun _ => (1 : ℝ)) η | m] ω := by
      simpa only [hjoint, hb_indicator] using hRaw
    filter_upwards [hRewritten, hcoin] with ω heq hpω
    rw [hpω] at heq
    exact heq
  let s : ℕ → SimpleFunc ℝ ℝ :=
    SimpleFunc.approxOn id measurable_id Set.univ 0
      (Set.mem_univ 0)
  have hs_bound (n : ℕ) (ω : Ω) :
      ‖s n (H ω)‖ ≤ ‖H ω‖ + ‖H ω‖ := by
    simpa [s] using
      SimpleFunc.norm_approxOn_zero_le measurable_id (Set.mem_univ 0) (H ω) n
  have hs_tendsto (ω : Ω) :
      Tendsto (fun n => s n (H ω)) atTop (𝓝 (H ω)) :=
    by simpa [s] using
      SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ _) (by simp : H ω ∈ closure Set.univ)
  have hseqB (n : ℕ) : Integrable (fun ω => b ω * s n (H ω)) μ := by
    exact AronowAudit.P006.Wave1.RepairT6T7_mul_integrable hb
      (fun ω => hbnd ω) (((s n).comp H hH0).integrable_of_isFiniteMeasure)
  have hseqP (n : ℕ) : Integrable (fun ω => p ω * s n (H ω)) μ := by
    exact AronowAudit.P006.Wave1.RepairT6T7_mul_integrable
      (hp.mono hm le_rfl) (fun ω => hpbnd ω)
      (((s n).comp H hH0).integrable_of_isFiniteMeasure)
  have hsimple (n : ℕ) :
      μ[(fun ω => b ω * s n (H ω)) | m] =ᵐ[μ]
        μ[(fun ω => p ω * s n (H ω)) | m] := by
    have hExt := AronowAudit.P006.Wave1.RepairT6T7_binary_conditional_moment_extension
      hm hb hp (fun ω => hbnd ω) (fun ω => hpbnd ω) hH0 hInd
      (s n).measurable (((s n).comp H hH0).integrable_of_isFiniteMeasure)
    have hPull := condExp_mul_of_stronglyMeasurable_left hp.stronglyMeasurable
      (hseqP n) (((s n).comp H hH0).integrable_of_isFiniteMeasure)
    exact hExt.trans hPull.symm
  have hboundB (n : ℕ) :
      ∀ᵐ ω ∂μ, ‖b ω * s n (H ω)‖ ≤ 2 * ‖b ω * H ω‖ := by
    filter_upwards [] with ω
    cases h : T ω
    · simp [b, bit, h]
    · simpa [b, bit, h, two_mul] using hs_bound n ω
  have hboundP (n : ℕ) :
      ∀ᵐ ω ∂μ, ‖p ω * s n (H ω)‖ ≤ 2 * ‖p ω * H ω‖ := by
    filter_upwards [] with ω
    calc
      ‖p ω * s n (H ω)‖ ≤ ‖p ω‖ * ‖s n (H ω)‖ := norm_mul_le _ _
      _ ≤ ‖p ω‖ * (‖H ω‖ + ‖H ω‖) :=
        mul_le_mul_of_nonneg_left (hs_bound n ω) (norm_nonneg _)
      _ = 2 * ‖p ω * H ω‖ := by rw [norm_mul]; ring
  have hlimit := tendsto_condExp_unique
      (fun n ω => b ω * s n (H ω))
      (fun n ω => p ω * s n (H ω))
      (fun ω => b ω * H ω)
      (fun ω => p ω * H ω)
      hseqB hseqP
      (Eventually.of_forall fun ω => tendsto_const_nhds.mul (hs_tendsto ω))
      (Eventually.of_forall fun ω => tendsto_const_nhds.mul (hs_tendsto ω))
      (fun ω => 2 * ‖b ω * H ω‖) (hTH.norm.const_mul 2)
      (fun ω => 2 * ‖p ω * H ω‖) (hpH.norm.const_mul 2)
      (fun n => hboundB n) (fun n => hboundP n) hsimple
  have hsub := condExp_sub hTH hpH m
  have hsub' :
      μ[(fun ω => b ω * H ω) - (fun ω => p ω * H ω) | m] =ᵐ[μ]
        μ[(fun ω => b ω * H ω) | m] - μ[(fun ω => p ω * H ω) | m] := by
    simpa [b] using hsub
  have hdiff : (fun ω => (b ω - p ω) * H ω) =
      (fun ω => b ω * H ω) - (fun ω => p ω * H ω) := by
    funext ω
    change (b ω - p ω) * H ω = b ω * H ω - p ω * H ω
    ring
  rw [hdiff]
  filter_upwards [hsub', hlimit] with ω hs heq
  dsimp only [Pi.sub_apply] at hs
  rw [heq] at hs
  simpa using hs
