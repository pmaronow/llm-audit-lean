import SAP.P032.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P032.Bridge

open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- Specialize the existing intercept fit and simplify its one-column weights. -/
theorem interceptFit {R M : Type*} [Fintype R] [Fintype M]
    [DecidableEq R] [DecidableEq M] (d : R → DyadData M)
    (hn : (Fintype.card R : ℝ) ≠ 0) (u : R → ℝ) : interceptFitStatement u := by
  have h := AronowAudit.P032.intercept_fit_certificate hn (fun r => toAuditDyad (d r)) u
  refine ⟨h.2.2.1, h.2.2.2.1, ?_⟩
  change (AronowAudit.P032.interceptDesign : Matrix R (Fin 1) ℝ) *ᵥ
    (AronowAudit.P032.bread AronowAudit.P032.interceptDesign *ᵥ (fun _ => (1 : ℝ))) = _
  rw [h.2.1]
  ext r
  simp [AronowAudit.P032.interceptDesign, Matrix.mulVec, dotProduct]

/-- Definitional transport of the finite formulas, plus deletion of the empty prefix. -/
theorem fourReplication {Ω : Type*} [MeasurableSpace Ω] : fourReplicationStatement Ω := by
  intro μ hμ block hmeas hind hlaw
  constructor
  · intro m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hn : (Fintype.card (Fin m × Fin 4) : ℝ) ≠ 0 := by
      simp [Fintype.card_prod, hm0]
    exact ⟨fun ω => interceptFit (fourReplicatedDyads m) hn _,
      AronowAudit.P032.four_replicated_finite μ block hmeas hind hlaw m hm⟩
  · exact (AronowAudit.P032.four_replicated_limit μ block hmeas hind hlaw).comp
      (tendsto_add_atTop_nat 1)

/-- The six-edge transport uses the same positive-sample convention. -/
theorem sixReplication {Ω : Type*} [MeasurableSpace Ω] : sixReplicationStatement Ω := by
  intro μ hμ block hmeas hind hlaw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hn : (Fintype.card (Fin m × Fin 6) : ℝ) ≠ 0 := by
      simp [Fintype.card_prod, hm0]
    exact ⟨fun ω => interceptFit (sixReplicatedDyads m) hn _,
      AronowAudit.P032.six_replicated_finite μ block hmeas hind hlaw m hm⟩
  · have h := (AronowAudit.P032.six_replicated_moments μ block hmeas hind hlaw 1 (by decide)).2
    norm_num at h
    exact h
  · have h := AronowAudit.P032.six_replicated_moments μ block hmeas hind hlaw 1 (by decide)
    change (∫ ω, AronowAudit.P032.interceptDCR (AronowAudit.P032.replicatedSixDyads 1)
      (AronowAudit.P032.sixSequenceErrors block 1 ω) ∂μ) <
      variance (fun ω => AronowAudit.P032.sampleMean
        (AronowAudit.P032.sixSequenceErrors block 1 ω)) μ
    rw [h.1, h.2]
    norm_num
  · filter_upwards [AronowAudit.P032.six_replicated_limit μ block hmeas hind hlaw] with ω hω
    exact hω.comp (tendsto_add_atTop_nat 1)

end
end SAP.P032.Bridge
