import SAP.P029b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set
open SAP.P029b

theorem SAP.P029b.WH.W1.T18_L2_proof : SAP.P029b.WH.W1.T18_L2 := by
  intro Ω X _ _ μ hμ U Z b hiv hb hbi hYi hnorm
  have hivA : AronowAudit.P029.IVAssumptions μ
      (fun ω => SAP.P029b.Bridge.toUnit (U ω)) Z := by
    rw [SAP.P029b.Bridge.iv_eq μ U Z]
    exact hiv
  have hweight (z : Bool) :
      mCE μ (fun ω => b (U ω).x) {ω | Z ω = z} =
        ∫ ω, b (U ω).x ∂μ := by
    simpa [AronowAudit.P029.mCE, SAP.P029b.mCE,
      AronowAudit.P029.mP, SAP.P029b.mP, SAP.P029b.Bridge.toUnit] using
      (AronowAudit.P029.Wave1.GP029B3b_appendix_observed_mean hivA z
        (fun t : X × Bool × Bool × ℝ × ℝ => b t.1) (hb.comp measurable_fst)
        (fun ω => b (U ω).x) hbi (fun _ _ => rfl))
  let F (z : Bool) : X × Bool × Bool × ℝ × ℝ → ℝ := fun t =>
    b t.1 * (if (if z then t.2.2.1 else t.2.1)
      then t.2.2.2.2 else t.2.2.2.1)
  have hF (z : Bool) : Measurable (F z) := by
    cases z <;> dsimp only [F, Bool.false_eq_true, ite_false, ite_true]
    · exact (hb.comp measurable_fst).mul (Measurable.ite
        ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
        (by fun_prop) (by fun_prop))
    · exact (hb.comp measurable_fst).mul (Measurable.ite
        ((measurable_fst.comp (measurable_snd.comp measurable_snd))
          (measurableSet_singleton true)) (by fun_prop) (by fun_prop))
  have hmean (z : Bool) :
      mCE μ (fun ω => b (U ω).x * (U ω).outcome (Z ω)) {ω | Z ω = z} =
        ∫ ω, b (U ω).x * (U ω).outcome z ∂μ := by
    simpa [AronowAudit.P029.mCE, SAP.P029b.mCE,
      AronowAudit.P029.mP, SAP.P029b.mP, SAP.P029b.Bridge.toUnit, F,
      SAP.P029b.PotentialUnit.outcome, SAP.P029b.PotentialUnit.receipt] using
      (AronowAudit.P029.Wave1.GP029B3b_appendix_observed_mean hivA z
        (F z) (hF z) (fun ω => b (U ω).x * (U ω).outcome (Z ω)) (hYi z)
        (by
          intro ω hω
          rw [hω]
          rfl))
  have hnodefier : ∀ᵐ ω ∂μ, ¬ (U ω).defier := by
    rcases hiv with ⟨_, _, _, _, _, _, _, _, _, _, _, hdefier, _⟩
    have hzero : μ {ω | (U ω).defier} = 0 := hdefier
    simpa only [ae_iff, not_not] using hzero
  have hpoint : ∀ᵐ ω ∂μ,
      b (U ω).x * (U ω).outcome true - b (U ω).x * (U ω).outcome false =
        b (U ω).x * (if (U ω).complier then (U ω).tau else 0) := by
    filter_upwards [hnodefier] with ω hω
    rw [← mul_sub]
    have hω' : ¬ (SAP.P029b.Bridge.toUnit (U ω)).defier := by
      simpa [SAP.P029b.Bridge.toUnit, SAP.P029b.PotentialUnit.defier,
        AronowAudit.P029.PotentialUnit.defier] using hω
    have hu := AronowAudit.P029.unit_itt_identities
      (SAP.P029b.Bridge.toUnit (U ω)) hω'
    exact congrArg (fun q : ℝ => b (U ω).x * q) hu.2
  have hcomplierInt : Integrable
      (fun ω => b (U ω).x * (if (U ω).complier then (U ω).tau else 0)) μ := by
    exact ((hYi true).sub (hYi false)).congr hpoint
  refine ⟨hcomplierInt, ?_⟩
  simp only [mArm, hmean, hweight, ← sub_div]
  rw [← integral_sub (hYi true) (hYi false)]
  congr 1
  apply integral_congr_ae
  exact hpoint
