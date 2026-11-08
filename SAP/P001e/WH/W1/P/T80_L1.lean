import SAP.P001e.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

theorem SAP.P001e.WH.W1.T80_L1_proof : SAP.P001e.WH.W1.T80_L1 := by
  intro Ω hΩ μ hμ Y R hY hR a b hab hYae hRae
  let Y0 : Ω → ℝ := fun ω => max a (min b (Y ω))
  let R0 : Ω → ℝ := fun ω => if R ω = 1 then 1 else 0
  have hY0 : Measurable Y0 := by
    dsimp [Y0]
    exact measurable_const.max (measurable_const.min hY)
  have hR0 : Measurable R0 := by
    dsimp [R0]
    exact Measurable.ite (hR (measurableSet_singleton (1 : ℝ))) measurable_const measurable_const
  have hY0bound : ∀ ω, Y0 ω ∈ Icc a b := by
    intro ω
    dsimp [Y0]
    exact ⟨le_max_left _ _, (max_le_iff.mpr ⟨hab, min_le_left _ _⟩)⟩
  have hR0binary : ∀ ω, R0 ω = 0 ∨ R0 ω = 1 := by
    intro ω
    dsimp [R0]
    split_ifs <;> simp
  have hY0ae : Y0 =ᵐ[μ] Y := by
    filter_upwards [hYae] with ω hω
    dsimp [Y0]
    rw [min_eq_right hω.2, max_eq_right hω.1]
  have hR0ae : R0 =ᵐ[μ] R := by
    filter_upwards [hRae] with ω hω
    dsimp [R0]
    rcases hω with hω | hω
    · simp [hω]
    · simp [hω]

  have hdonor := AronowAudit.P001.missing_data_bounds_and_sharpness
    μ Y0 R0 hY0 hR0 a b hY0bound hR0binary
  dsimp only [AronowAudit.P001.mean] at hdonor
  let L0 := ∫ ω, AronowAudit.P001.missingEndpoint
    (AronowAudit.P001.censored (Y0 ω) (R0 ω)) (R0 ω) a ∂μ
  let U0 := ∫ ω, AronowAudit.P001.missingEndpoint
    (AronowAudit.P001.censored (Y0 ω) (R0 ω)) (R0 ω) b ∂μ
  let L := ∫ ω, completeMissing (recordedOutcome (Y ω) (R ω)) (R ω) a ∂μ
  let U := ∫ ω, completeMissing (recordedOutcome (Y ω) (R ω)) (R ω) b ∂μ
  have hL0L : L0 = L := by
    apply integral_congr_ae
    filter_upwards [hY0ae, hR0ae] with ω hy hr
    simp [L0, L, AronowAudit.P001.missingEndpoint, AronowAudit.P001.censored,
      completeMissing, recordedOutcome, hy, hr]
  have hU0U : U0 = U := by
    apply integral_congr_ae
    filter_upwards [hY0ae, hR0ae] with ω hy hr
    simp [U0, U, AronowAudit.P001.missingEndpoint, AronowAudit.P001.censored,
      completeMissing, recordedOutcome, hy, hr]
  have hmean0 : (∫ ω, Y0 ω ∂μ) = (∫ ω, Y ω ∂μ) := by
    apply integral_congr_ae
    exact hY0ae
  rcases hdonor with ⟨hlo, hhi, hsharp⟩
  have hlo' : L ≤ ∫ ω, Y ω ∂μ := by
    change L0 ≤ ∫ ω, Y0 ω ∂μ at hlo
    rw [← hL0L, ← hmean0]
    exact hlo
  have hhi' : (∫ ω, Y ω ∂μ) ≤ U := by
    change (∫ ω, Y0 ω ∂μ) ≤ U0 at hhi
    rw [← hmean0, ← hU0U]
    exact hhi
  refine ⟨?_, ?_, ?_⟩
  · simpa [L, SAP.P001e.expectation] using hlo'
  · simpa [U, SAP.P001e.expectation] using hhi'
  · intro c hc
    have hc' : c ∈ Icc L0 U0 := by
      have hcLU : c ∈ Icc L U := by
        simpa [L, U, SAP.P001e.expectation] using hc
      rw [hL0L, hU0U]
      exact hcLU
    obtain ⟨Y', hY'm, hY'bounds, hY'mean, hY'rec⟩ := hsharp c hc'
    refine ⟨Y', hY'm, hY'bounds, ?_, ?_⟩
    · change (∫ ω, Y' ω ∂μ) = c at hY'mean ⊢
      simpa [AronowAudit.P001.mean] using hY'mean
    · have hrec : (fun ω => recordedOutcome (Y' ω) (R0 ω)) =ᵐ[μ]
          (fun ω => recordedOutcome (Y0 ω) (R0 ω)) := by
        filter_upwards [] with ω
        simpa [AronowAudit.P001.censored, recordedOutcome] using congrFun hY'rec ω
      filter_upwards [hrec, hY0ae, hR0ae] with ω hrecω hy hr
      have hb : R ω = 0 ∨ R ω = 1 := by
        simpa [hr] using hR0binary ω
      rcases hb with hzero | hone
      · simp [recordedOutcome, hzero]
      · have hy' : Y' ω = Y ω := by
          have hrec' : Y' ω = Y0 ω ∨ R0 ω = 0 := by
            simpa [recordedOutcome] using hrecω
          rcases hrec' with heq | hmiss
          · simpa [hy] using heq
          · rw [hr, hone] at hmiss
            norm_num at hmiss
        simp [recordedOutcome, hone, hy']

