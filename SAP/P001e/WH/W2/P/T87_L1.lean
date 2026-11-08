import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W2.P.T87_L1

theorem transport_cef_ae {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (Z Z' : Ω → E) (V V' : Ω → ℝ) (f g : E → ℝ)
    (hZ : Measurable Z) (hZ' : Measurable Z') (hf : Measurable f)
    (hZae : Z =ᵐ[μ] Z') (hV : V =ᵐ[μ] V')
    (hcomp : (fun ω => f (Z' ω)) =ᵐ[μ] fun ω => g (Z ω))
    (hsrc : IsConditionalMean μ Z V g) : IsConditionalMean μ Z' V' f := by
  refine ⟨hf, hsrc.2.1.congr hV, hsrc.2.2.1.congr hcomp.symm, ?_⟩
  intro A hA
  have hpre : Z ⁻¹' A =ᵐ[μ] Z' ⁻¹' A := by
    filter_upwards [hZae] with ω hω
    simpa [hω]
  calc
    (∫ ω in Z' ⁻¹' A, V' ω ∂μ) = ∫ ω in Z ⁻¹' A, V' ω ∂μ :=
      setIntegral_congr_set hpre.symm
    _ = ∫ ω in Z ⁻¹' A, V ω ∂μ := by
      apply setIntegral_congr_ae (hZ hA)
      filter_upwards [hV] with ω hω _
      exact hω.symm
    _ = ∫ ω in Z ⁻¹' A, g (Z ω) ∂μ := hsrc.2.2.2 A hA
    _ = ∫ ω in Z' ⁻¹' A, g (Z ω) ∂μ := setIntegral_congr_set hpre
    _ = ∫ ω in Z' ⁻¹' A, f (Z' ω) ∂μ := by
      apply setIntegral_congr_ae (hZ' hA)
      filter_upwards [hcomp] with ω hω _
      exact hω.symm

end SAP.P001e.WH.W2.P.T87_L1

theorem SAP.P001e.WH.W2.T87_L1_proof : SAP.P001e.WH.W2.T87_L1 := by
  intro Ω E _ _ μ hμ X hX Y R hY hR hi hb m hm
  let B₁ : Set Ω := {ω | R ω = 1}
  let B₀ : Set Ω := {ω | R ω = 0}
  let Rhat : Ω → ℝ := fun ω => if R ω = 1 then 1 else 0
  have hB₁ : MeasurableSet B₁ := hR (measurableSet_singleton 1)
  have hB₀ : MeasurableSet B₀ := hR (measurableSet_singleton 0)
  have hRhat : Measurable Rhat := by
    exact measurable_const.ite (hR (measurableSet_singleton 1)) measurable_const
  have hRhat_bin : ∀ ω, Rhat ω = 0 ∨ Rhat ω = 1 := by
    intro ω
    by_cases h : R ω = 1 <;> simp [Rhat, h]
  have hset₁ : B₁ =ᵐ[μ] {ω | Rhat ω = 1} := by
    filter_upwards [hb] with ω hω
    rcases hω with h0 | h1
    · simp [B₁, Rhat, h0]
    · simp [B₁, Rhat, h1]
  have hrestr₁ : μ.restrict {ω | Rhat ω = 1} = μ.restrict B₁ :=
    Measure.restrict_congr_set hset₁.symm
  have hmhat : IsConditionalMean (μ.restrict {ω | Rhat ω = 1}) X Y m := by
    rw [hrestr₁]
    exact hm

  have hresp_eq : (fun ω => recordedOutcome (Y ω) (R ω)) =ᵐ[μ.restrict B₁] Y := by
    apply (ae_restrict_iff' hB₁).2
    filter_upwards [hb] with ω hω
    intro hmem
    rcases hω with h0 | h1
    · exact False.elim (by have : R ω = 1 := hmem; rw [h0] at this; norm_num at this)
    · simp [recordedOutcome, h1]
  have hresp : IsConditionalMean (μ.restrict B₁) X
      (fun ω => recordedOutcome (Y ω) (R ω)) m :=
    SAP.P001e.WH.W2.P.T87_L1.transport_cef_ae
      (μ.restrict B₁) X X Y (fun ω => recordedOutcome (Y ω) (R ω)) m m
      hX hX hm.1 (Filter.Eventually.of_forall fun _ => rfl) hresp_eq.symm
      (Filter.Eventually.of_forall fun _ => rfl) hm

  have hnonresp_eq : (fun ω => recordedOutcome (Y ω) (R ω)) =ᵐ[μ.restrict B₀]
      fun _ => (-99 : ℝ) := by
    apply (ae_restrict_iff' hB₀).2
    filter_upwards [hb] with ω hω
    intro hmem
    rcases hω with h0 | h1
    · simp [recordedOutcome, h0]
    · exact False.elim (by have : R ω = 0 := hmem; rw [h1] at this; norm_num at this)
  have hconst : IsConditionalMean (μ.restrict B₀) X (fun _ => (-99 : ℝ))
      (fun _ => (-99 : ℝ)) := by
    exact SAP.P001e.WH.W2.conditionalMean_of_eq (μ.restrict B₀) X
      (fun _ => (-99 : ℝ)) (fun _ => (-99 : ℝ)) measurable_const
      (integrable_const (-99 : ℝ)) rfl
  have hnonresp : IsConditionalMean (μ.restrict B₀) X
      (fun ω => recordedOutcome (Y ω) (R ω)) (fun _ => (-99 : ℝ)) :=
    SAP.P001e.WH.W2.P.T87_L1.transport_cef_ae
      (μ.restrict B₀) X X (fun _ => (-99 : ℝ))
      (fun ω => recordedOutcome (Y ω) (R ω)) (fun _ => (-99 : ℝ)) (fun _ => (-99 : ℝ))
      hX hX measurable_const (Filter.Eventually.of_forall fun _ => rfl) hnonresp_eq.symm
      (Filter.Eventually.of_forall fun _ => rfl) hconst

  let Zhat : Ω → ℝ × E := fun ω => (Rhat ω, X ω)
  let Z : Ω → ℝ × E := fun ω => (R ω, X ω)
  let G : ℝ × E → ℝ := fun rx => if rx.1 = 1 then m rx.2 else -99
  let F : ℝ × E → ℝ := fun rx => rx.1 * m rx.2 - 99 * (1 - rx.1)
  have hZhat : Measurable Zhat := Measurable.prodMk hRhat hX
  have hZ : Measurable Z := Measurable.prodMk hR hX
  have hG : Measurable G := by
    exact Measurable.ite (measurable_fst (measurableSet_singleton 1))
      (hm.1.comp measurable_snd) measurable_const
  have hF : Measurable F := by
    exact (measurable_fst.mul (hm.1.comp measurable_snd)).sub
      (measurable_const.mul (measurable_const.sub measurable_fst))
  have hZae : Zhat =ᵐ[μ] Z := by
    filter_upwards [hb] with ω hω
    rcases hω with h0 | h1
    · simp [Zhat, Z, Rhat, h0]
    · simp [Zhat, Z, Rhat, h1]
  have hout : (fun ω => recordedOutcome (Y ω) (R ω)) =ᵐ[μ]
      fun ω => AronowAudit.P001.censored (Y ω) (Rhat ω) := by
    filter_upwards [hb] with ω hω
    rcases hω with h0 | h1
    · simp [recordedOutcome, AronowAudit.P001.censored, Rhat, h0]
    · simp [recordedOutcome, AronowAudit.P001.censored, Rhat, h1]
  have hcomp : (fun ω => F (Z ω)) =ᵐ[μ] fun ω => G (Zhat ω) := by
    filter_upwards [hb] with ω hω
    rcases hω with h0 | h1
    · simp [F, G, Z, Zhat, Rhat, h0]
    · simp [F, G, Z, Zhat, Rhat, h1]
  have hdonor := AronowAudit.P001.Wave1.stable_outcomes_respondent_cef_proof
    μ X hX Y Rhat hY hRhat hi hRhat_bin m hmhat
  have hpop : IsConditionalMean μ Zhat
      (fun ω => AronowAudit.P001.censored (Y ω) (Rhat ω)) G := by
    change IsConditionalMean μ (fun ω => (Rhat ω, X ω))
      (fun ω => AronowAudit.P001.censored (Y ω) (Rhat ω))
      (fun rx => if rx.1 = 1 then m rx.2 else -99)
    exact hdonor.2
  have hpopulation := SAP.P001e.WH.W2.P.T87_L1.transport_cef_ae
    μ Zhat Z (fun ω => AronowAudit.P001.censored (Y ω) (Rhat ω))
      (fun ω => recordedOutcome (Y ω) (R ω)) F G hZhat hZ hF hZae hout.symm hcomp hpop
  exact ⟨hresp, hnonresp, hpopulation⟩
