import SAP.P028.WH.W1.Donors
import AronowAudit.P029.P029_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W1
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge
noncomputable section
open Classical

variable {Ω : Type*} [MeasurableSpace Ω]

theorem wholeX_formula (M : WholeCausalData Ω) (z : Bool) (ω : Ω) :
    wholeX M z ω = AronowAudit.P028.potentialArmOutcome z (M.S ω, M.Y false ω, M.Y true ω) := by
  unfold wholeX treatment AronowAudit.P028.potentialArmOutcome
  split_ifs <;> simp_all

theorem wholeX_measurable (M : WholeCausalData Ω) (z : Bool) : Measurable (wholeX M z) := by
  have hf : wholeX M z = fun ω => AronowAudit.P028.potentialArmOutcome z (M.S ω, M.Y false ω, M.Y true ω) :=
    funext (wholeX_formula M z)
  rw [hf]
  exact (AronowAudit.P028.potential_arm_measurable z).comp
    (M.measurableS.prodMk ((M.measurableY false).prodMk (M.measurableY true)))

theorem wholeX_independent (M : WholeCausalData Ω) (z : Bool) : IndepFun (wholeX M z) M.Z M.μ := by
  have h := M.randomAssignment.comp (AronowAudit.P028.potential_arm_measurable z) measurable_id
  simpa only [Function.comp_def, id_eq, ← wholeX_formula] using h

theorem wholeX_on_arm (M : WholeCausalData Ω) (z : Bool) (ω : Ω) (hω : ω ∈ wholeArm M z) :
    wholeX M z ω = wholeY M ω := by
  change M.Z ω = z at hω
  simp [wholeX, wholeY, wholeD, hω]

theorem wholeX_on_compliers (M : WholeCausalData Ω) (d : Bool) (ω : Ω) (hω : ω ∈ wholeComplier M) :
    wholeX M d ω = M.Y d ω := by
  change M.S ω = 2 at hω
  simp [wholeX, treatment, hω]

def repairedModel (M : WholeCausalData Ω) (hi : ∀ z, Integrable (wholeX M z) M.μ) : CausalModel Ω where
  μ := M.μ
  probability := M.probability
  S := M.S
  Y := wholeX M
  Z := M.Z
  measurableS := M.measurableS
  measurableY := wholeX_measurable M
  integrableY := hi
  measurableZ := M.measurableZ
  randomAssignment := by
    let f : Fin 3 × ℝ × ℝ → Fin 3 × ℝ × ℝ := fun v =>
      (v.1, AronowAudit.P028.potentialArmOutcome false v, AronowAudit.P028.potentialArmOutcome true v)
    have hf : Measurable f := measurable_fst.prodMk
      ((AronowAudit.P028.potential_arm_measurable false).prodMk
        (AronowAudit.P028.potential_arm_measurable true))
    have h := M.randomAssignment.comp hf measurable_id
    simpa only [Function.comp_def, id_eq, f, ← wholeX_formula] using h
  armPositive := M.armPositive
  nonzeroFirstStage := M.nonzeroFirstStage

theorem repaired_observed (M : WholeCausalData Ω) (hi : ∀ z, Integrable (wholeX M z) M.μ) :
    observedY (repairedModel M hi) = wholeY M := by
  funext ω
  change wholeX M (treatment (M.S ω) (M.Z ω)) ω = M.Y (treatment (M.S ω) (M.Z ω)) ω
  unfold wholeX
  rcases AronowAudit.P028.stratum_cases (M.S ω) with h | h | h <;> simp [treatment,h]

theorem repaired_complierMean (M : WholeCausalData Ω) (hi : ∀ z, Integrable (wholeX M z) M.μ) (d : Bool) :
    complierMean (repairedModel M hi) d = wholeC M d := by
  unfold complierMean wholeC eventMean
  congr 1
  apply setIntegral_congr_fun (M.measurableS (measurableSet_singleton 2))
  exact wholeX_on_compliers M d

theorem repaired_cace (M : WholeCausalData Ω) (hi : ∀ z, Integrable (wholeX M z) M.μ) :
    cace (repairedModel M hi) = wholeCACE M := by
  unfold cace wholeCACE eventMean
  congr 1
  apply setIntegral_congr_fun (M.measurableS (measurableSet_singleton 2))
  intro ω hω
  change wholeX M true ω - wholeX M false ω = M.Y true ω - M.Y false ω
  rw [wholeX_on_compliers M true ω hω, wholeX_on_compliers M false ω hω]

/-- Transfer all outcome conclusions from the integrable model whose two
potentials are the fixed-assignment realized outcomes. No value of an unused
counterfactual is changed inside a complier or observed mean. -/
theorem localLate (M : WholeCausalData Ω) (hi : ∀ z, Integrable (wholeX M z) M.μ) :
    (∀ d, IntegrableOn (M.Y d) (wholeComplier M) M.μ) ∧
    IntegrableOn (fun ω => M.Y true ω - M.Y false ω) (wholeComplier M) M.μ ∧
    wholeCACE M = wholeC M true - wholeC M false ∧
    wholeE M true - wholeE M false = wholeP M * wholeCACE M ∧
    wholeCACE M = (wholeE M true - wholeE M false) / wholeP M ∧
    wholeCACE M = (wholeE M true - wholeE M false) / wholeStage M := by
  let N := repairedModel M hi
  have hc : ∀ d, IntegrableOn (M.Y d) (wholeComplier M) M.μ := by
    intro d
    exact (hi d).integrableOn.congr_fun (wholeX_on_compliers M d)
      (M.measurableS (measurableSet_singleton 2))
  have he : ∀ z, armMean N z = wholeE M z := by
    intro z
    change eventMean M.μ (observedY N) (wholeArm M z) = _
    rw [repaired_observed]; rfl
  have h := AronowAudit.P028.late_identity (toAudit N)
  have hd := AronowAudit.P028.cace_difference (toAudit N)
  change cace N = complierMean N true - complierMean N false at hd
  rw [repaired_cace, repaired_complierMean, repaired_complierMean] at hd
  change _ ∧ _ ∧ armMean N true - armMean N false = wholeP M * cace N ∧
    cace N = (armMean N true - armMean N false) / wholeP M ∧
    cace N = (armMean N true - armMean N false) / wholeStage M at h
  rw [he true, he false, repaired_cace] at h
  exact ⟨hc, (hc true).sub (hc false), hd, h.2.2⟩

/-- An outcome-free model transports the existing treatment first-stage proof. -/
def treatmentModel (M : WholeCausalData Ω) : CausalModel Ω where
  μ := M.μ
  probability := M.probability
  S := M.S
  Y := fun _ _ => 0
  Z := M.Z
  measurableS := M.measurableS
  measurableY := fun _ => measurable_const
  integrableY := fun _ => integrable_zero _ _ _
  measurableZ := M.measurableZ
  randomAssignment := by
    have h := M.randomAssignment.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_const) :
        Measurable (fun v : Fin 3 × ℝ × ℝ => (v.1,(0:ℝ),(0:ℝ)))) measurable_id
    exact h
  armPositive := M.armPositive
  nonzeroFirstStage := M.nonzeroFirstStage

theorem treatmentFacts (M : WholeCausalData Ω) :
    (∫ ω, realBit (treatment (M.S ω) true) - realBit (treatment (M.S ω) false) ∂M.μ) = wholeP M ∧
    wholeStage M = wholeP M ∧ 0 < wholeP M ∧ wholeP M ≤ 1 := by
  let A := toAudit (treatmentModel M)
  exact ⟨(AronowAudit.P028.first_stage_population A).1,
    AronowAudit.P028.observed_first_stage A, (AronowAudit.P028.first_stage_population A).2,
    AronowAudit.P028.complier_probability_le_one A⟩

theorem sampleMean_measurable (n : ℕ) (v : WholeSample n → Fin n → ℝ)
    (hv : ∀ i, Measurable (fun s => v s i)) (z : Bool) :
    Measurable (fun s => wholeSampleMean (v s) s.2.2 z) := by
  have hz (i : Fin n) : Measurable (fun s : WholeSample n => s.2.2 i) :=
    (measurable_pi_apply i).comp measurable_snd.snd
  unfold wholeSampleMean
  apply Measurable.div
  · apply Finset.measurable_sum
    intro i _
    exact Measurable.ite ((measurableSet_singleton z).preimage (hz i))
      (hv i) measurable_const
  · apply Finset.measurable_sum
    intro i _
    exact Measurable.ite ((measurableSet_singleton z).preimage (hz i))
      measurable_const measurable_const

theorem empiricalClause : wholeEmpiricalClause := by
  intro n
  have he (z : Bool) : Measurable (fun s : WholeSample n => wholeSampleE s z) :=
    sampleMean_measurable n (fun s => s.1) (fun i => (measurable_pi_apply i).comp measurable_fst) z
  have hd (z : Bool) : Measurable (fun s : WholeSample n =>
      wholeSampleMean (fun i => realBit (s.2.1 i)) s.2.2 z) := by
    apply sampleMean_measurable
    intro i
    exact (Measurable.of_discrete : Measurable realBit).comp ((measurable_pi_apply i).comp measurable_snd.fst)
  have hp : Measurable (wholeSampleP (n := n)) := (hd true).sub (hd false)
  refine ⟨he, hp, ((he true).sub (he false)).div hp, ?_, ?_⟩
  · intro s h0 h1 hs
    have ht : wholeSampleCount s true = ∑ i, AronowAudit.P029.bit (s.2.2 i) := by
      apply Finset.sum_congr rfl; intro i _
      cases s.2.2 i <;> rfl
    have hf : wholeSampleCount s false = (n : ℝ) - ∑ i, AronowAudit.P029.bit (s.2.2 i) := by
      have hh : ∀ i, (if s.2.2 i = false then (1 : ℝ) else 0) = 1-AronowAudit.P029.bit (s.2.2 i) := by
        intro i; cases s.2.2 i <;> norm_num [AronowAudit.P029.bit]
      simp [wholeSampleCount, hh, Finset.sum_sub_distrib]
    have hs' : AronowAudit.P029.sampleArm (fun _ => 1) (fun i => AronowAudit.P029.bit (s.2.1 i)) s.2.2 true -
        AronowAudit.P029.sampleArm (fun _ => 1) (fun i => AronowAudit.P029.bit (s.2.1 i)) s.2.2 false ≠ 0 := by
      simpa only [AronowAudit.P029.sampleArm, AronowAudit.P029.bit, one_mul,
        wholeSampleP, wholeSampleMean, realBit] using hs
    have hx : AronowAudit.P029.sampleCross s.2.2 (fun i => AronowAudit.P029.bit (s.2.1 i)) ≠ 0 := by
      intro hz
      have hh := AronowAudit.P029.sample_wald_bivariate_2sls
        (fun i => AronowAudit.P029.bit (s.2.1 i)) s.2.1 s.2.2 (ht ▸ h1) (by linarith [hf]) hs'
      have hw : AronowAudit.P029.sampleWald (fun _ => 1)
          (fun i => AronowAudit.P029.bit (s.2.1 i)) s.2.1 s.2.2 = 1 := div_self hs'
      rw [hw,hz,zero_div] at hh
      norm_num at hh
    refine ⟨hx, ?_⟩
    have hh := AronowAudit.P029.sample_wald_bivariate_2sls s.1 s.2.1 s.2.2
      (ht ▸ h1) (by linarith [hf]) hs'
    simpa only [AronowAudit.P029.sampleArm, AronowAudit.P029.sampleWald,
      AronowAudit.P029.sampleCross, AronowAudit.P029.bit, one_mul,
      wholeSampleWald, wholeSampleE, wholeSampleMean, wholeSampleP, wholeSampleCross, realBit] using hh
  · intro s t h0 h1 hp'
    simp only [wholeSampleWald, h0, h1, hp']

end
end SAP.P028.WH.W1
