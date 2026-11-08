import SAP.P006b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.WH.W1.P.T17_L1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

end
end SAP.P006b.WH.W1.P.T17_L1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

theorem SAP.P006b.WH.W1.T17_L1_proof : SAP.P006b.WH.W1.T17_L1 := by
  intro Ω mΩ K n E hE p hp hsum hmass π hπ i
  let hS := SAP.P006b.WH.W1.outcome_design E hE hπ
  letI : IsProbabilityMeasure (E.law π) := hS.law_probability
  letI : IsProbabilityMeasure E.PX := hS.px_probability
  obtain ⟨hX, hY0, hY1, hT⟩ := hS.measurable_units i
  have hbit : Measurable (fun ω => SAP.P006b.bit (E.T π i ω)) :=
    (measurable_of_finite SAP.P006b.bit).comp hT
  have hnotbit : Measurable (fun ω => 1 - SAP.P006b.bit (E.T π i ω)) :=
    measurable_const.sub hbit
  have hbnd : ∀ ω, ‖SAP.P006b.bit (E.T π i ω)‖ ≤ 1 := by
    intro ω
    cases E.T π i ω <;> norm_num [SAP.P006b.bit]
  have hnotbnd : ∀ ω, ‖1 - SAP.P006b.bit (E.T π i ω)‖ ≤ 1 := by
    intro ω
    cases E.T π i ω <;> norm_num [SAP.P006b.bit]
  have hI0 := AronowAudit.P006.Wave1.RepairT6T7_mul_integrable hbit hbnd (hS.integrable_units i).1
  have hI1 := AronowAudit.P006.Wave1.RepairT6T7_mul_integrable hbit hbnd (hS.integrable_units i).2
  have hI0not := AronowAudit.P006.Wave1.RepairT6T7_mul_integrable hnotbit hnotbnd (hS.integrable_units i).1
  have hobs : (fun ω => E.observed π ω i) =
      (fun ω => SAP.P006b.bit (E.T π i ω) * E.Y1 i ω +
        (1 - SAP.P006b.bit (E.T π i ω)) * E.Y0 i ω) := by
    funext ω
    cases ht : E.T π i ω <;> simp [SAP.P006b.Experiment.observed, SAP.P006b.bit, ht]
  have hobsI : Integrable (fun ω => E.observed π ω i) (E.law π) := by
    rw [hobs]
    exact hI1.add hI0not
  have htreated := AronowAudit.P006.Wave1.RepairT6T7_unit_outcome_moments
    (SAP.P006b.Bridge.toProject E) hS hπ i
  have hG : E.covariateSigma i ≤ mΩ := hX.comap_le
  have htotal : (∫ ω, E.Y0 i ω ∂E.law π) = ∫ ω, E.μ0 (E.X i ω) ∂E.law π := by
    exact AronowAudit.P006.Wave1.T2_total_moment (E.law π) hG (hS.conditional_means i).1
  have htreatInt : (∫ ω, SAP.P006b.bit (E.T π i ω) * E.Y0 i ω ∂E.law π) =
      ∫ ω, π (E.X i ω) * E.μ0 (E.X i ω) ∂E.law π := by
    exact AronowAudit.P006.Wave1.T2_total_moment (E.law π) hG htreated.1
  have hcovμ : (∫ ω, E.μ0 (E.X i ω) ∂E.law π) = ∫ u, E.μ0 u ∂E.PX :=
    (hS.covariate_law i).comp hS.means_measurable.1 |>.integral_eq
  have hcovπμ : (∫ ω, π (E.X i ω) * E.μ0 (E.X i ω) ∂E.law π) =
      ∫ u, π u * E.μ0 u ∂E.PX :=
    (hS.covariate_law i).comp (hπ.1.mul hS.means_measurable.1) |>.integral_eq
  have hmassInt : (∫ u, (1 - π u) * E.μ0 u ∂E.PX) =
      finiteA p E.μ0 (fun u => 1 - π u) := by
    rw [integral_fintype (Integrable.of_finite : Integrable (fun u : Fin K => (1-π u)*E.μ0 u) E.PX)]
    simp only [Measure.real, hmass, smul_eq_mul]
    simp only [finiteA]
    congr 1
    ext u
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hfalseMeas : MeasurableSet {ω | E.T π i ω = false} :=
    hT (measurableSet_singleton false)
  have hY0Int : Integrable (fun ω => E.Y0 i ω) (E.law π) :=
    (hS.integrable_units i).1
  have huntreatY0 : (∫ ω in {ω | E.T π i ω = false}, E.Y0 i ω ∂E.law π) =
      finiteA p E.μ0 (fun u => 1 - π u) := by
    rw [← integral_indicator hfalseMeas]
    have hevent : (fun ω => ({ω | E.T π i ω = false}).indicator
        (fun ω => E.Y0 i ω) ω) =
        (fun ω => (1 - SAP.P006b.bit (E.T π i ω)) * E.Y0 i ω) := by
      funext ω
      cases ht : E.T π i ω <;> simp [ht, SAP.P006b.bit]
    rw [hevent]
    have hsub : (fun ω => (1 - SAP.P006b.bit (E.T π i ω)) * E.Y0 i ω) =
        (fun ω => E.Y0 i ω - SAP.P006b.bit (E.T π i ω) * E.Y0 i ω) := by
      funext ω
      ring
    rw [hsub]
    have hsubInt : (∫ ω, E.Y0 i ω - SAP.P006b.bit (E.T π i ω) * E.Y0 i ω ∂E.law π) =
        (∫ ω, E.Y0 i ω ∂E.law π) - ∫ ω, SAP.P006b.bit (E.T π i ω) * E.Y0 i ω ∂E.law π :=
      integral_sub hY0Int hI0
    rw [hsubInt]
    rw [htotal, hcovμ, htreatInt, hcovπμ]
    have hrewrite : (∫ u, E.μ0 u ∂E.PX) - (∫ u, π u * E.μ0 u ∂E.PX) =
        ∫ u, (1 - π u) * E.μ0 u ∂E.PX := by
      have hμ0Int : Integrable (fun u : Fin K => E.μ0 u) E.PX := hS.means_integrable.1
      have hπbound : ∀ u : Fin K, ‖π u‖ ≤ 1 := by
        intro u
        simpa [Real.norm_eq_abs, abs_of_nonneg (hπ.2 u).1] using (hπ.2 u).2
      have hπμInt : Integrable (fun u : Fin K => π u * E.μ0 u) E.PX :=
        AronowAudit.P006.Wave1.RepairT6T7_mul_integrable hπ.1 hπbound hμ0Int
      calc
        _ = ∫ u, E.μ0 u - π u * E.μ0 u ∂E.PX := (integral_sub hμ0Int hπμInt).symm
        _ = ∫ u, (1 - π u) * E.μ0 u ∂E.PX := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun u => by ring)
    rw [hrewrite, hmassInt]
  have hobsUntreat : (∫ ω in {ω | E.T π i ω = false}, E.observed π ω i ∂E.law π) =
      finiteA p E.μ0 (fun u => 1 - π u) := by
    have heq : (fun ω => ({ω | E.T π i ω = false}).indicator
      (fun ω => E.observed π ω i) ω) = (fun ω => ({ω | E.T π i ω = false}).indicator
      (fun ω => E.Y0 i ω) ω) := by
      funext ω
      cases ht : E.T π i ω <;> simp [ht, SAP.P006b.Experiment.observed]
    rw [← integral_indicator hfalseMeas]
    change (∫ ω, ({ω | E.T π i ω = false}).indicator
      (fun ω => E.observed π ω i) ω ∂E.law π) = _
    rw [heq, integral_indicator hfalseMeas, huntreatY0]
  have htreatedProb : (∫ ω, SAP.P006b.bit (E.T π i ω) ∂E.law π) = ∫ u, π u ∂E.PX := by
    have hh := AronowAudit.P006.Wave1.T2_total_moment (E.law π) hG (hS.bernoulli i)
    exact hh.trans ((hS.covariate_law i).comp hπ.1).integral_eq
  have hmassEq : (E.law π {ω | E.T π i ω = false}).toReal =
      finiteMass p (fun u => 1 - π u) := by
    have heventMeas : MeasurableSet {ω | E.T π i ω = false} := hfalseMeas
    have hprob : (E.law π {ω | E.T π i ω = false}).toReal =
        1 - ∫ ω, SAP.P006b.bit (E.T π i ω) ∂E.law π := by
      have htrueMeas : MeasurableSet {ω | E.T π i ω = true} :=
        hT (measurableSet_singleton true)
      have hcomplement : {ω | E.T π i ω = false} = {ω | E.T π i ω = true}ᶜ := by
        ext ω
        cases E.T π i ω <;> simp
      have hmeasure := measureReal_compl htrueMeas (μ := E.law π)
      have hbitEvent : (fun ω => SAP.P006b.bit (E.T π i ω)) =
          ({ω | E.T π i ω = true}).indicator (fun _ => (1 : ℝ)) := by
        funext ω
        cases ht : E.T π i ω <;> simp [ht, SAP.P006b.bit]
      have hbitint : (∫ ω, SAP.P006b.bit (E.T π i ω) ∂E.law π) =
          ((E.law π) {ω | E.T π i ω = true}).toReal := by
        calc
          _ = ∫ ω, ({ω | E.T π i ω = true}).indicator (fun _ => (1 : ℝ)) ω ∂E.law π := by
            apply integral_congr_ae
            exact Eventually.of_forall (fun ω => congrFun hbitEvent ω)
          _ = ((E.law π) {ω | E.T π i ω = true}).toReal := by
            simpa only [Measure.real, smul_eq_mul, mul_one] using
              (integral_indicator_const (μ := E.law π) (1 : ℝ) htrueMeas)
      calc
        _ = (E.law π).real {ω | E.T π i ω = true}ᶜ := by rw [hcomplement]; rfl
        _ = (E.law π).real Set.univ - (E.law π).real {ω | E.T π i ω = true} :=
          measureReal_compl htrueMeas
        _ = 1 - ∫ ω, SAP.P006b.bit (E.T π i ω) ∂E.law π := by
          rw [hbitint]
          simp [Measure.real]
    rw [hprob, htreatedProb]
    rw [show (∫ u, π u ∂E.PX) = ∑ u, p u * π u by
      rw [integral_fintype (Integrable.of_finite : Integrable π E.PX)]
      simp only [Measure.real, hmass, smul_eq_mul]
      ]
    simp only [finiteMass]
    calc
      1 - ∑ u, p u * π u = (∑ u, p u) - ∑ u, p u * π u := by rw [hsum]
      _ = ∑ u, (p u - p u * π u) := by
        rw [← Finset.sum_sub_distrib]
      _ = ∑ u, p u * (1 - π u) := by congr 1; ext u; ring
  exact ⟨hobsI, hmassEq, hobsUntreat⟩
