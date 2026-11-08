import SAP.P028.Defs.WholeW2
import SAP.P028.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W2

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

universe u

/-- Independence transfers integrability from a positive assignment arm to the
population. Prove this by composing independence with the real indicator of
`Z = z`. The product of X and that indicator is integrable by
`IntegrableOn.integrable_indicator`. Apply
`IndepFun.integrable_left_of_integrable_op` with multiplication and c = 1;
positivity of the arm says its indicator is not almost everywhere zero.
This is the only new analytic step; no moment of X outside the arm is assumed. -/
def T9_L1 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (Z : Ω → Bool) (z : Bool),
    Measurable X → Measurable Z → IndepFun X Z μ →
    0 < μ.real {ω | Z ω = z} →
    IntegrableOn X {ω | Z ω = z} μ → Integrable X μ

variable {Ω : Type u} [MeasurableSpace Ω]

private theorem stratum_measurable (M : T9Model Ω) (s : Fin 3) :
    MeasurableSet {ω | M.S ω = s} := M.measurableS (measurableSet_singleton s)

private theorem arm_measurable (M : T9Model Ω) (z : Bool) :
    MeasurableSet (M.armEvent z) := M.measurableZ (measurableSet_singleton z)

private theorem observed_integrable (M : T9Model Ω) (h : T9FiniteCells M) :
    Integrable M.observedY M.μ := by
  have hi := ((h false false).2.union (h true false).2).union
    ((h false true).2.union (h true true).2)
  have he : (M.cellEvent false false ∪ M.cellEvent true false) ∪
      (M.cellEvent false true ∪ M.cellEvent true true) = Set.univ := by
    ext ω
    cases hd : M.observedD ω <;> cases hz : M.Z ω <;>
      simp [T9Model.cellEvent, hd, hz]
  rw [he] at hi
  exact integrableOn_univ.mp hi

private def fixedArm (M : T9Model Ω) (z : Bool) (ω : Ω) : ℝ :=
  AronowAudit.P028.potentialArmOutcome z (M.S ω, M.Y false ω, M.Y true ω)

private theorem fixedArm_value (M : T9Model Ω) (z : Bool) (ω : Ω) :
    fixedArm M z ω = M.Y (treatment (M.S ω) z) ω := by
  rcases AronowAudit.P028.stratum_cases (M.S ω) with hs | hs | hs <;>
    cases z <;> simp [fixedArm, AronowAudit.P028.potentialArmOutcome, treatment, hs]

private theorem fixedArm_integrable (h1 : T9_L1.{u}) (M : T9Model Ω)
    (ho : Integrable M.observedY M.μ) (z : Bool) : Integrable (fixedArm M z) M.μ := by
  have hvec : Measurable (fun ω => (M.S ω, M.Y false ω, M.Y true ω)) :=
    M.measurableS.prodMk ((M.measurableY false).prodMk (M.measurableY true))
  have hm : Measurable (fixedArm M z) :=
    (AronowAudit.P028.potential_arm_measurable z).comp hvec
  have hind : IndepFun (fixedArm M z) M.Z M.μ :=
    M.randomAssignment.comp (AronowAudit.P028.potential_arm_measurable z) measurable_id
  have hi : IntegrableOn (fixedArm M z) (M.armEvent z) M.μ :=
    ho.integrableOn.congr_fun (fun ω hω => by
      change M.Z ω = z at hω
      rw [fixedArm_value]
      simp [T9Model.observedY, T9Model.observedD, hω]) (arm_measurable M z)
  exact h1 Ω M.μ (fixedArm M z) M.Z z hm M.measurableZ hind (M.armPositive z) hi

/-- Set only Y(0) on always-takers and Y(1) on never-takers to zero. -/
private def maskedY (M : T9Model Ω) (d : Bool) (ω : Ω) : ℝ :=
  if M.S ω = (if d then 1 else 0) then 0 else M.Y d ω

private theorem masked_integrable (h1 : T9_L1.{u}) (M : T9Model Ω)
    (ho : Integrable M.observedY M.μ) (d : Bool) : Integrable (maskedY M d) M.μ := by
  have hi := (fixedArm_integrable h1 M ho d).indicator
    (stratum_measurable M (if d then 1 else 0)).compl
  convert hi using 1
  funext ω
  rcases AronowAudit.P028.stratum_cases (M.S ω) with hs | hs | hs <;>
    cases d <;>
    simp [maskedY, fixedArm, AronowAudit.P028.potentialArmOutcome, Set.indicator, hs]

private def completion (M : T9Model Ω)
    (hi : ∀ d, Integrable (maskedY M d) M.μ) : CausalModel Ω where
  μ := M.μ
  probability := M.probability
  S := M.S
  Y := maskedY M
  Z := M.Z
  measurableS := M.measurableS
  measurableY := fun d => measurable_const.ite
    (stratum_measurable M (if d then 1 else 0)) (M.measurableY d)
  integrableY := hi
  measurableZ := M.measurableZ
  randomAssignment := by
    have hf : Measurable (fun v : Fin 3 × ℝ × ℝ =>
        (v.1, (if v.1 = 0 then (0 : ℝ) else v.2.1),
          (if v.1 = 1 then (0 : ℝ) else v.2.2))) :=
      measurable_fst.prodMk
        ((measurable_const.ite (measurable_fst (measurableSet_singleton 0))
          measurable_snd.fst).prodMk
        (measurable_const.ite (measurable_fst (measurableSet_singleton 1))
          measurable_snd.snd))
    simpa only [Function.comp_def, id_eq, maskedY, Bool.false_eq_true, ite_false, ite_true]
      using M.randomAssignment.comp hf measurable_id
  armPositive := M.armPositive
  nonzeroFirstStage := M.nonzeroFirstStage

private theorem masked_complier (M : T9Model Ω) (d : Bool) :
    Set.EqOn (maskedY M d) (M.Y d) M.complierEvent := by
  intro ω hω
  change M.S ω = 2 at hω
  cases d <;> simp [maskedY, hω]

private theorem masked_always (M : T9Model Ω) :
    Set.EqOn (maskedY M true) (M.Y true) M.alwaysEvent := by
  intro ω hω
  change M.S ω = 0 at hω
  simp [maskedY, hω]

private theorem masked_never (M : T9Model Ω) :
    Set.EqOn (maskedY M false) (M.Y false) M.neverEvent := by
  intro ω hω
  change M.S ω = 1 at hω
  simp [maskedY, hω]

private theorem completion_observed (M : T9Model Ω)
    (hi : ∀ d, Integrable (maskedY M d) M.μ) :
    observedY (completion M hi) = M.observedY := by
  funext ω
  rcases AronowAudit.P028.stratum_cases (M.S ω) with hs | hs | hs <;>
    cases hz : M.Z ω <;>
    simp [observedY, observedD, completion, maskedY, treatment,
      T9Model.observedY, T9Model.observedD, hs, hz]

private theorem eventMean_congr (μ : Measure Ω) (f g : Ω → ℝ) (E : Set Ω)
    (hE : MeasurableSet E) (hfg : Set.EqOn f g E) :
    eventMean μ f E = eventMean μ g E := by
  unfold eventMean
  rw [setIntegral_congr_fun hE hfg]

private theorem model_conclusions (h1 : T9_L1.{u}) (M : T9Model Ω)
    (h : T9FiniteCells M) : T9Conclusions M := by
  have ho := observed_integrable M h
  have hi := masked_integrable h1 M ho
  let N := completion M hi
  have hy : observedY N = M.observedY := completion_observed M hi
  have hP : complierProbability N = M.complierProbability := rfl
  have hπ : cellProbability N = M.cellProbability := rfl
  have hcm : complierMean N = M.complierMean := by
    funext d
    exact eventMean_congr M.μ (maskedY M d) (M.Y d) M.complierEvent
      (stratum_measurable M 2) (masked_complier M d)
  have harm : armMean N = M.armMean := by
    funext z
    change eventMean M.μ (observedY N) (M.armEvent z) = M.armMean z
    rw [hy]
    rfl
  have hcell : cellMean N = M.cellMean := by
    funext d z
    change eventMean M.μ (observedY N) (M.cellEvent d z) = M.cellMean d z
    rw [hy]
    rfl
  have hmean : noncomplierMean N = M.noncomplierMean := by
    change eventMean M.μ (observedY N) M.noncomplierEvent = M.noncomplierMean
    rw [hy]
    rfl
  have hamean : eventMean N.μ (N.Y true) (alwaysEvent N) =
      eventMean M.μ (M.Y true) M.alwaysEvent :=
    eventMean_congr M.μ (maskedY M true) (M.Y true) M.alwaysEvent
      (stratum_measurable M 0) (masked_always M)
  have hnmean : eventMean N.μ (N.Y false) (neverEvent N) =
      eventMean M.μ (M.Y false) M.neverEvent :=
    eventMean_congr M.μ (maskedY M false) (M.Y false) M.neverEvent
      (stratum_measurable M 1) (masked_never M)
  have hc : corollaryFormulas N :=
    AronowAudit.P028.corollary1 (Bridge.toAudit N) (fun d z => (h d z).1)
  simp only [corollaryFormulas, hP, hπ, hcm, harm, hcell, hmean, hamean, hnmean] at hc
  rcases hc with ⟨hqA, hrN, hpqr, ha, hn, hnc, h0, hshift, htreated⟩
  have hp : 0 < M.complierProbability :=
    (AronowAudit.P028.first_stage_population (Bridge.toAudit N)).2
  have hq : 0 < M.cellProbability true false :=
    div_pos (h true false).1 (M.armPositive false)
  have hr : 0 < M.cellProbability false true :=
    div_pos (h false true).1 (M.armPositive true)
  have hsumpos := add_pos hq hr
  have hsum : M.cellProbability true false + M.cellProbability false true =
      1 - M.complierProbability := by linarith [hpqr]
  have hnprob : M.μ.real M.noncomplierEvent = 1 - M.complierProbability :=
    AronowAudit.P028.noncomplier_event_probability (Bridge.toAudit N)
  have hpartition : M.cellProbability false true + M.cellProbability true true = 1 :=
    AronowAudit.P028.cell_probability_partition (Bridge.toAudit N) true
  have hfirst : M.complierProbability = t9MassFromCells M.cellProbability := by
    unfold t9MassFromCells
    linarith [hpqr, hpartition]
  have harm_cells : ∀ z, M.armMean z = t9ArmFromCells M.cellProbability M.cellMean z := by
    intro z
    have hw0 : cellProbability N false z * cellMean N false z = jointOutcomeMoment N false z :=
      AronowAudit.P028.weighted_cell_mean (Bridge.toAudit N) false z (h false z).1
    have hw1 : cellProbability N true z * cellMean N true z = jointOutcomeMoment N true z :=
      AronowAudit.P028.weighted_cell_mean (Bridge.toAudit N) true z (h true z).1
    have hpart : jointOutcomeMoment N false z + jointOutcomeMoment N true z = armMean N z :=
      AronowAudit.P028.arm_joint_moment_partition (Bridge.toAudit N) z
    have he : armMean N z = ∑ d : Bool, cellProbability N d z * cellMean N d z := by
      simp only [Fintype.sum_bool]
      linarith
    simpa only [harm, hπ, hcell, t9ArmFromCells] using he
  have hmixture : ∀ z, M.complierProbability * M.complierMean z +
      (1 - M.complierProbability) * M.noncomplierMean = M.armMean z := by
    have hncnum := (eq_div_iff (ne_of_gt hsumpos)).mp hnc
    have hc0num := (eq_div_iff (ne_of_gt hp)).mp h0
    have hc1num := (eq_div_iff (ne_of_gt hp)).mp htreated
    intro z
    rw [← hsum]
    cases z <;> nlinarith
  refine {
    observed_integrable := ho
    complier_integrable := fun d => (hi d).integrableOn.congr_fun
      (masked_complier M d) (stratum_measurable M 2)
    always_integrable := (hi true).integrableOn.congr_fun
      (masked_always M) (stratum_measurable M 0)
    never_integrable := (hi false).integrableOn.congr_fun
      (masked_never M) (stratum_measurable M 1)
    noncomplier_integrable := ho.integrableOn
    complier_positive := hp
    always_positive := hqA ▸ hq
    never_positive := hrN ▸ hr
    noncomplier_positive := by linarith [hnprob, hsum]
    pure_sum_positive := hsumpos
    arm_reconstruction := harm_cells
    always_probability := hqA
    never_probability := hrN
    complier_probability := hpqr
    noncomplier_probability := hnprob.trans hsum.symm
    observable_first_stage := hfirst
    always_mean := ha
    never_mean := hn
    noncomplier_mean := hnc
    mixture := hmixture
    control_mean := h0
    treated_shift := hshift
    treated_mean := htreated
    identified_mean := ?_ }
  intro d
  unfold t9MeanFromCells
  rw [← harm_cells d, ← hfirst]
  cases d
  · exact h0
  · exact htreated

/-- Apply the integrability-transfer leaf, complete only unused counterfactual
outcomes, and transport the existing corollary. Equality to the explicit
eight-number reconstruction gives the two-model identification assertion. -/
theorem T9_assembly (h1 : T9_L1.{u}) : T9WholeStatement.{u} := by
  constructor
  · intro Ω _ M h
    exact model_conclusions h1 M h
  · intro Ω Ξ _ _ M N hM hN hπ hm d
    have hπ' : M.cellProbability = N.cellProbability := funext fun d => funext (hπ d)
    have hm' : M.cellMean = N.cellMean := funext fun d => funext (hm d)
    rw [(model_conclusions h1 M hM).identified_mean d,
      (model_conclusions h1 N hN).identified_mean d, hπ', hm']

end

end SAP.P028.WH.W2
