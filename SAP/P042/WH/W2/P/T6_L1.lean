import SAP.P042.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P042.WH.W2.P.T6_L1

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

private def compliantResponse (x : Bool × (ℝ × ℝ)) : ℝ :=
  if x.1 then x.2.2 else x.2.1

end

end SAP.P042.WH.W2.P.T6_L1

open SAP.P042.WH.W2.P.T6_L1
open MeasureTheory ProbabilityTheory

theorem SAP.P042.WH.W2.T6_L1_proof : SAP.P042.WH.W2.T6_L1 := by
  unfold SAP.P042.WH.W2.T6_L1 SAP.P042.RandomizedContactW2
  intro Ω mΩ μ hμ Z c hZ hc hZpos hCpos Y hYm hYi hind
  dsimp only
  let A : Set Ω := {ω | c ω = true}
  let EZ (z : Bool) : Set Ω := {ω | Z ω = z}
  let X : Ω → ℝ := fun ω => Y ω (c ω)
  let Y0 : Ω → ℝ := fun ω => Y ω false
  let Y1 : Ω → ℝ := fun ω => Y ω true
  let V : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
  let F : Ω → ℝ := fun ω => if Z ω && c ω then 1 else 0
  let π : ℝ := SAP.P042.eventProbabilityW2 μ A
  let CACE : ℝ := SAP.P042.eventMeanW2 μ (fun ω => Y ω true - Y ω false) A
  let ITT : ℝ := ∫ ω, X ω - Y0 ω ∂μ
  let Δ : ℝ := SAP.P042.eventMeanW2 μ (fun ω => SAP.P042.randomContactOutcomeW2 Y c Z ω) (EZ true) -
    SAP.P042.eventMeanW2 μ (fun ω => SAP.P042.randomContactOutcomeW2 Y c Z ω) (EZ false)
  change ITT = π * CACE ∧ Δ = ITT ∧
    SAP.P042.eventMeanW2 μ F (EZ true) = π ∧
    SAP.P042.eventMeanW2 μ F (EZ false) = 0 ∧
    CACE = Δ / SAP.P042.eventMeanW2 μ F (EZ true)

  have hA : MeasurableSet A := by
    exact (measurableSet_singleton true).preimage hc
  have hEt (z : Bool) : MeasurableSet (EZ z) := by
    exact (measurableSet_singleton z).preimage hZ

  let W : Ω → Bool × (ℝ × ℝ) := fun ω => (c ω, (Y0 ω, Y1 ω))
  have hW : Measurable W := hc.prodMk ((hYm false).prodMk (hYm true))
  have hR : Measurable compliantResponse := by
    unfold compliantResponse
    exact Measurable.ite ((measurableSet_singleton true).preimage measurable_fst)
      (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
  have hXeq : X = compliantResponse ∘ W := by
    funext ω
    cases hcw : c ω <;> simp [X, W, Y0, Y1, compliantResponse, hcw]
  have hXmeas : Measurable X := by
    rw [hXeq]
    exact hR.comp hW
  have hXint : Integrable X μ := by
    have hpw : X = A.piecewise Y1 Y0 := by
      funext ω
      cases hcw : c ω <;> simp [X, A, Y1, Y0, Set.piecewise, hcw]
    rw [hpw]
    apply Integrable.piecewise hA
    · exact ((hYi true).integrableOn (s := Set.univ)).mono_set (Set.subset_univ A)
    · exact ((hYi false).integrableOn (s := Set.univ)).mono_set (Set.subset_univ Aᶜ)
  have hY0int : Integrable Y0 μ := by simpa [Y0] using hYi false

  have hXind : IndepFun Z X μ := by
    have h := hind.comp measurable_id hR
    rw [hXeq]
    simpa only [Function.comp_def, id_eq] using h
  have hY0ind : IndepFun Z Y0 μ := by
    have h := hind.comp measurable_id (measurable_fst.comp measurable_snd)
    simpa only [Function.comp_def, W, Y0, id_eq] using h
  have hXarm (z : Bool) :
      SAP.P042.eventMeanW2 μ X (EZ z) = ∫ ω, X ω ∂μ := by
    exact AronowAudit.P029.Wave1.LateIdentity.n1_proof μ Z X hZ hXint hXind z (hZpos z)
  have hY0arm :
      SAP.P042.eventMeanW2 μ Y0 (EZ false) = ∫ ω, Y0 ω ∂μ := by
    exact AronowAudit.P029.Wave1.LateIdentity.n1_proof μ Z Y0 hZ hY0int hY0ind false (hZpos false)

  have hpwITT : (fun ω => X ω - Y0 ω) =
      A.indicator (fun ω => Y1 ω - Y0 ω) := by
    funext ω
    cases hcw : c ω <;> simp [X, Y0, Y1, A, hcw]
  have hintITT :
      ∫ ω, X ω - Y0 ω ∂μ = ∫ ω in A, Y1 ω - Y0 ω ∂μ := by
    rw [hpwITT, integral_indicator hA]
  have hπpos : 0 < π := by simpa [π, A] using hCpos
  have hITT : ITT = π * CACE := by
    dsimp [ITT, CACE, SAP.P042.eventMeanW2]
    rw [hintITT]
    change (∫ ω in A, Y ω true - Y ω false ∂μ) =
      π * ((∫ ω in A, Y ω true - Y ω false ∂μ) / π)
    field_simp [ne_of_gt hπpos]

  have hObsTrue :
      SAP.P042.eventMeanW2 μ (fun ω => SAP.P042.randomContactOutcomeW2 Y c Z ω) (EZ true) =
        SAP.P042.eventMeanW2 μ X (EZ true) := by
    unfold SAP.P042.eventMeanW2
    congr 1
    apply setIntegral_congr_fun (hEt true)
    intro ω hω
    have hzω : Z ω = true := by simpa [EZ] using hω
    simp [SAP.P042.randomContactOutcomeW2, X, hzω]
  have hObsFalse :
      SAP.P042.eventMeanW2 μ (fun ω => SAP.P042.randomContactOutcomeW2 Y c Z ω) (EZ false) =
        SAP.P042.eventMeanW2 μ Y0 (EZ false) := by
    unfold SAP.P042.eventMeanW2
    congr 1
    apply setIntegral_congr_fun (hEt false)
    intro ω hω
    have hzω : Z ω = false := by simpa [EZ] using hω
    simp [SAP.P042.randomContactOutcomeW2, Y0, hzω]
  have hDelta : Δ = ITT := by
    dsimp [Δ, ITT]
    rw [hObsTrue, hObsFalse, hXarm true, hY0arm]
    exact (integral_sub hXint hY0int).symm

  have hVint : Integrable V μ := by
    dsimp [V]
    exact (integrable_const (1 : ℝ)).indicator hA
  have hZc : IndepFun Z c μ := by
    have h := hind.comp measurable_id measurable_fst
    simpa only [Function.comp_def, W, id_eq] using h
  let q : Bool → ℝ := fun b => if b = true then 1 else 0
  have hq : Measurable q := Measurable.of_discrete
  have hVeq : V = q ∘ c := by
    funext ω
    cases hcw : c ω <;> simp [V, q, A, hcw]
  have hVind : IndepFun Z V μ := by
    have h := hZc.comp measurable_id hq
    rw [hVeq]
    simpa only [Function.comp_def, id_eq] using h
  have hVarm (z : Bool) :
      SAP.P042.eventMeanW2 μ V (EZ z) = ∫ ω, V ω ∂μ := by
    exact AronowAudit.P029.Wave1.LateIdentity.n1_proof μ Z V hZ hVint hVind z (hZpos z)
  have hVintegral : ∫ ω, V ω ∂μ = π := by
    dsimp [V, π, SAP.P042.eventProbabilityW2, Measure.real_def]
    exact integral_indicator_one hA

  have hFtrue : SAP.P042.eventMeanW2 μ F (EZ true) = π := by
    calc
      SAP.P042.eventMeanW2 μ F (EZ true) =
          SAP.P042.eventMeanW2 μ V (EZ true) := by
            unfold SAP.P042.eventMeanW2
            congr 1
            apply setIntegral_congr_fun (hEt true)
            intro ω hω
            have hzω : Z ω = true := by simpa [EZ] using hω
            cases hcw : c ω <;> simp [F, V, A, hzω, hcw]
      _ = ∫ ω, V ω ∂μ := hVarm true
      _ = π := hVintegral
  have hFfalse : SAP.P042.eventMeanW2 μ F (EZ false) = 0 := by
    have hFzero : ∫ ω in EZ false, F ω ∂μ = 0 := by
      calc
        ∫ ω in EZ false, F ω ∂μ = ∫ ω in EZ false, (fun _ : Ω => 0) ω ∂μ := by
          apply setIntegral_congr_fun (hEt false)
          intro ω hω
          have hzω : Z ω = false := by simpa [EZ] using hω
          simp [F, hzω]
        _ = 0 := by simp
    unfold SAP.P042.eventMeanW2
    rw [hFzero]
    simp

  refine ⟨hITT, hDelta, hFtrue, hFfalse, ?_⟩
  rw [hFtrue, hDelta, hITT]
  dsimp [CACE]
  exact (mul_div_cancel_left₀ _ (ne_of_gt hπpos)).symm
