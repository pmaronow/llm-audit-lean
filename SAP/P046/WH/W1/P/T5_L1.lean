import SAP.P046.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W1.P.T5_L1

open MeasureTheory Filter Topology SAP.P046
open scoped ENNReal

lemma tendsto_mul_iff_zero {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    Tendsto (fun n => c * u n) atTop (𝓝 0) ↔ Tendsto u atTop (𝓝 0) := by
  constructor
  · intro h
    have hcinv : c⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hc0
    have hs := ENNReal.Tendsto.const_mul (a := c⁻¹) h (Or.inr hcinv)
    convert hs using 1
    · funext n
      exact (ENNReal.inv_mul_cancel_left hc0 hct).symm
    · simp
  · intro h
    have hs := ENNReal.Tendsto.const_mul (a := c) h (Or.inr hct)
    simpa using hs

end SAP.P046.WH.W1.P.T5_L1

namespace SAP.P046.WH.W1

open SAP.P046.WH.W1.P.T5_L1
open MeasureTheory Filter Topology
open scoped ENNReal

theorem T5_L1_proof : SAP.P046.WH.W1.T5_L1 := by
  intro M hM
  have hqUpper := AronowAudit.P046.Wave1.risk_expansion_q_bounds
    (Bridge.toStudy M) (Bridge.valid_to hM)
  have hq : ∀ᵐ o ∂M.law, M.delta ≤ q M (W o) ∧ q M (W o) ≤ M.delta⁻¹ := by
    filter_upwards [hM.positivity, hqUpper] with o ho hupper
    rcases ho with ⟨hδπ, hπ⟩
    have hπpos : 0 < M.pi (W o) := lt_trans hM.delta_pos hδπ
    have hπlt : M.pi (W o) < 1 := by linarith [hπ, hM.delta_pos]
    have hπle : M.pi (W o) ≤ 1 := le_of_lt hπlt
    have hδcomp : M.delta ≤ 1 - M.pi (W o) := by linarith
    constructor
    · dsimp [q]
      apply (le_div_iff₀ hπpos).2
      calc
        M.delta * M.pi (W o) ≤ M.delta * 1 :=
          mul_le_mul_of_nonneg_left hπle hM.delta_pos.le
        _ = M.delta := by ring
        _ ≤ 1 - M.pi (W o) := hδcomp
    · simpa [Bridge.toStudy, SAP.P046.q, AronowAudit.P046.q,
      SAP.P046.W, AronowAudit.P046.W] using hupper.2
  have hnorm : ∀ g : ℝ → ℝ, Measurable g →
      ENNReal.ofReal M.delta * wholeL2Sq M g ≤ wholeWeightedSq M g ∧
        wholeWeightedSq M g ≤ ENNReal.ofReal M.delta⁻¹ * wholeL2Sq M g := by
    intro g hg
    let f : (ℝ × (Bool × (Bool × Bool))) → ℝ≥0∞ :=
      fun o => ENNReal.ofReal ((g (W o)) ^ 2)
    have hf : Measurable f := by
      dsimp [f]
      exact ENNReal.measurable_ofReal.comp ((hg.comp measurable_fst).pow_const 2)
    constructor
    · change ENNReal.ofReal M.delta * (∫⁻ o, f o ∂M.law) ≤
        ∫⁻ o, ENNReal.ofReal (q M (W o) * (g (W o)) ^ 2) ∂M.law
      rw [← lintegral_const_mul (ENNReal.ofReal M.delta) hf]
      apply lintegral_mono_ae
      filter_upwards [hq] with o ho
      change ENNReal.ofReal M.delta * ENNReal.ofReal ((g (W o)) ^ 2) ≤ _
      rw [← ENNReal.ofReal_mul hM.delta_pos.le]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right ho.1 (sq_nonneg _)
    · change (∫⁻ o, ENNReal.ofReal (q M (W o) * (g (W o)) ^ 2) ∂M.law) ≤
        ENNReal.ofReal M.delta⁻¹ * (∫⁻ o, f o ∂M.law)
      rw [← lintegral_const_mul (ENNReal.ofReal M.delta⁻¹) hf]
      apply lintegral_mono_ae
      filter_upwards [hq] with o ho
      change ENNReal.ofReal (q M (W o) * (g (W o)) ^ 2) ≤
        ENNReal.ofReal M.delta⁻¹ * ENNReal.ofReal ((g (W o)) ^ 2)
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hM.delta_pos.le)]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right ho.2 (sq_nonneg _)
  refine ⟨hq, hnorm, ?_⟩
  intro u hu
  let c : ℝ≥0∞ := ENNReal.ofReal M.delta
  let d : ℝ≥0∞ := ENNReal.ofReal M.delta⁻¹
  have hcpos : 0 < c := by
    dsimp [c]
    exact ENNReal.ofReal_pos.mpr hM.delta_pos
  have hc0 : c ≠ 0 := ne_of_gt hcpos
  have hct : c ≠ ∞ := by
    dsimp [c]
    exact ENNReal.ofReal_ne_top
  have hdt : d ≠ ∞ := by
    dsimp [d]
    exact ENNReal.ofReal_ne_top
  have hsqueeze (k : ℕ) :
      c * wholeL2Sq M (u k) ≤ wholeWeightedSq M (u k) ∧
        wholeWeightedSq M (u k) ≤ d * wholeL2Sq M (u k) := by
    simpa [c, d] using hnorm (u k) (hu k)
  constructor
  · intro hw
    have hcL2 : Tendsto (fun k => c * wholeL2Sq M (u k)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hw
        (fun k => (zero_le : (0 : ℝ≥0∞) ≤ c * wholeL2Sq M (u k)))
        (fun k => (hsqueeze k).1)
    exact (tendsto_mul_iff_zero hc0 hct).1 hcL2
  · intro hl2
    have hdL2 : Tendsto (fun k => d * wholeL2Sq M (u k)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := d) hl2 (Or.inr hdt)
      simpa [d] using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdL2
      (fun k => (zero_le : (0 : ℝ≥0∞) ≤ wholeWeightedSq M (u k)))
      (fun k => (hsqueeze k).2)

end SAP.P046.WH.W1

