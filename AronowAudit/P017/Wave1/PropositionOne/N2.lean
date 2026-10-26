import AronowAudit.P017.Wave1.PropositionOne.N1

set_option autoImplicit false

namespace AronowAudit.P017.Wave1.PropositionOne

open AronowAudit.P017 MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

theorem n2_proof : N2 := by
  change Ioo (0 : ℝ) 1 ⊆ effectSupport ipwPopulation ipwEffect
  rw [effectSupport, effect_eq_fst, fst_law]
  intro x hx
  apply (Measure.mem_support_iff_forall x).mpr
  intro U hU
  have hinter : U ∩ Ioo (0 : ℝ) 1 ∈ 𝓝 x :=
    inter_mem hU (isOpen_Ioo.mem_nhds hx)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hinter
  have hball01 : Metric.ball x ε ⊆ Ioo (0 : ℝ) 1 :=
    fun y hy => (hball hy).2
  have hballU : Metric.ball x ε ⊆ U := fun y hy => (hball hy).1
  have hpos : 0 < uniform01 (Metric.ball x ε) := by
    rw [uniform01, Measure.restrict_apply measurableSet_ball,
      inter_eq_left.mpr hball01, Real.ball_eq_Ioo, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact hpos.trans_le (measure_mono hballU)

end

end AronowAudit.P017.Wave1.PropositionOne
