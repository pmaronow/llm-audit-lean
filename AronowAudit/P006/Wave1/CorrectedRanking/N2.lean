import AronowAudit.P006.Wave1.CorrectedRanking.N1

set_option autoImplicit false
universe u v
namespace AronowAudit.P006.Wave1.CorrectedRanking
open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section

/-- Standing suffices for integrability of the actual unweighted treated reward. -/
lemma reward_integrable {Ω : Type v} {C : Type u} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (hS : Standing E) (π : C → ℝ)
    (hπ : Admissible π) (i : Fin n) :
    Integrable (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω))
      (E.law π) := by
  have hT := (hS.measurable_units π hπ i).2.2.2
  obtain ⟨_, hY1, hhat⟩ := hS.integrable_units π hπ i
  have h := (integrable_bit_mul hT hY1).sub (integrable_bit_mul hT hhat)
  apply h.congr
  exact Eventually.of_forall (fun ω => by
    cases ht : E.T π i ω <;> simp [Experiment.observed, ht, bit])

theorem n2_proof : N2.{u,v} := by
  classical
  intro h1 Ω C _ _ n E hS hU π hπ i
  let μ := E.law π
  let T : Ω → ℝ := fun ω => bit (E.T π i ω)
  let b : Ω → ℝ := fun ω => E.μ0 (E.X i ω)
  let a : Ω → ℝ := fun ω => T ω * E.Y1 i ω
  let d : Ω → ℝ := fun ω => T ω * b ω
  let c : Ω → ℝ := fun ω => T ω * (E.μhat π ω (E.X i ω) - b ω)
  haveI : IsProbabilityMeasure μ := hS.law_probability π hπ
  have hX := (hS.measurable_units π hπ i).1
  have hT := (hS.measurable_units π hπ i).2.2.2
  have hm : E.covariateSigma i ≤ (inferInstance : MeasurableSpace Ω) := hX.comap_le
  have hb : Integrable b μ :=
    ((hS.covariate_law π hπ i).comp hS.means_measurable.1).integrable_iff.2
      hS.means_integrable.1
  have hbsm : StronglyMeasurable[(E.covariateSigma i)] b :=
    (hS.means_measurable.1.comp (comap_measurable (E.X i))).stronglyMeasurable
  have ha : Integrable a μ := integrable_bit_mul hT (hS.integrable_units π hπ i).2.1
  have hd : Integrable d μ := integrable_bit_mul hT hb
  have hc : Integrable c μ := integrable_bit_mul hT ((hS.integrable_units π hπ i).2.2.sub hb)
  have hTi : Integrable T μ := integrable_bit hT
  have hpull : μ[d | (E.covariateSigma i)] =ᵐ[μ] fun ω => b ω * π (E.X i ω) := by
    have hmul : Integrable (b * T) μ :=
      hd.congr (Eventually.of_forall fun ω => by show T ω * b ω = b ω * T ω; ring)
    have h := condExp_mul_of_stronglyMeasurable_left hbsm hmul hTi
    have hB := hS.bernoulli π hπ i
    have hcomm : μ[d | (E.covariateSigma i)] =ᵐ[μ] μ[b * T | (E.covariateSigma i)] := by
      apply condExp_congr_ae
      exact Eventually.of_forall (fun ω => mul_comm _ _)
    filter_upwards [hcomm, h, hB] with ω hcomm h hB
    simpa only [Pi.mul_apply, T] using hcomm.trans (h.trans (congrArg (fun z => b ω * z) hB))
  have hcond : μ[(a - d) - c | (E.covariateSigma i)] =ᵐ[μ]
      fun ω => (π (E.X i ω) * E.μ1 (E.X i ω) - b ω * π (E.X i ω)) - 0 := by
    have hsub1 := condExp_sub ha hd (E.covariateSigma i)
    have hsub2 := condExp_sub (ha.sub hd) hc (E.covariateSigma i)
    have hA := h1 E hS π hπ i
    have hC := hU π hπ i
    filter_upwards [hsub1, hsub2, hA, hpull, hC] with ω hsd hsc hA hd hC
    simp only [Pi.sub_apply] at hsd hsc
    rw [hsc, hsd, hA, hd, hC]
  have hrewrite : (fun ω => (E.observed π ω i - E.μhat π ω (E.X i ω)) * bit (E.T π i ω)) =
      (a - d) - c := by
    funext ω
    dsimp [a, d, c, T, b]
    cases ht : E.T π i ω <;> simp [Experiment.observed, ht, bit] <;> ring
  rw [hrewrite]
  filter_upwards [hcond] with ω h
  rw [h]
  dsimp [b, Experiment.τ]
  ring

end
end AronowAudit.P006.Wave1.CorrectedRanking
