import SAP.P006a.Defs.WholeW2
import SAP.P006a.Bridge
import AronowAudit.P006.Wave1.Gap.GP006B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace SAP.P006a.WH.W2
noncomputable section

/-- Normalizing a score by the positive sample size preserves every best response. -/
theorem normalizedBestW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) (b : C → ℝ)
    (hb : IsBest PiSet E.expectedTT b) : IsBest PiSet (normalizedTT E) b := by
  refine ⟨hb.1, fun π hπ => ?_⟩
  exact (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr E.hn)).mpr (hb.2 π hπ)

/-- The attained maximum makes the supremum in regret an ordinary finite maximum. -/
theorem regretEqW2 {P : Type} (PiSet : Set P) (V : P → ℝ) (b s : P)
    (hs : IsBest PiSet V s) : regret PiSet V b = V s - V b := by
  have hmax : bestValue PiSet V = V s := AronowAudit.P006.bestValue_eq hs
  exact congrArg (fun r => r - V b) hmax

/-- The deterministic two-error argument, including the displayed triangle bound. -/
theorem proposition10OfErrorW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (PiSet : Set (C → ℝ)) (ε : ℝ)
    (he : ∀ π ∈ PiSet, |normalizedTT E π - E.V π| ≤ ε) :
    Proposition10ConclusionW2 E PiSet ε := by
  refine ⟨he, ?_⟩
  intro b s hb hs
  have hr := regretEqW2 PiSet E.V b s hs
  have horder := (normalizedBestW2 E PiSet b hb).2 s hs.1
  have ha := le_abs_self (E.V s - normalizedTT E s)
  have hb' := le_abs_self (normalizedTT E b - E.V b)
  have heS : |E.V s - normalizedTT E s| ≤ ε := by
    simpa only [abs_sub_comm] using he s hs.1
  exact ⟨hr, by rw [hr]; linarith, by linarith [he b hb.1]⟩

/-- The main theorem needs only the already proved local outcome and selected-score
identities. In particular no Standing object for the evaluated estimator is constructed. -/
theorem informationBoundW2 : InformationBoundW2 := by
  intro Ω X U _ _ _ n E PiSet hPiSet hS b0 hM _hX hR hU
  have hn : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr E.hn).ne'
  have ha : Measurable (fun c : X × U => b0 c.1) := hM.1.comp measurable_fst
  have hid (π : (X × U) → ℝ) (hπ : π ∈ PiSet) :
      normalizedTT E π = ∫ c, π c * (E.μ1 c - b0 c.1) ∂E.PX := by
    have hs := AronowAudit.P006.Wave1.RepairT6T7_actual_treated_score
      (Bridge.experiment E) (Bridge.policyDesign (hS π hπ)) (hPiSet π hπ)
      ha hM.2.1 (hR π hπ) (hU π hπ)
    change E.expectedTT π = (n : ℝ) * _ at hs
    unfold normalizedTT
    rw [hs, mul_div_cancel_left₀ _ hn]
    rfl
  have hpolicy (π : (X × U) → ℝ) (hπ : π ∈ PiSet) :
      normalizedTT E π = (∫ c, π c * (E.μ1 c - b0 c.1) ∂E.PX) ∧
      |normalizedTT E π - E.V π| = |∫ c, π c * (E.μ0 c - b0 c.1) ∂E.PX| ∧
      |normalizedTT E π - E.V π| ≤ marginalHeterogeneity E b0 := by
    have hbias := AronowAudit.P006.Wave1.T8_information_integral_bias_bound
      E.PX E.μ1 E.μ0 (fun c => b0 c.1) π (hS π hπ).means_integrable.2
      (hS π hπ).means_integrable.1 hM.2.1 (hPiSet π hπ)
    have hw := AronowAudit.P006.Wave1.RepairT6T7_actual_welfare
      (Bridge.experiment E) (Bridge.policyDesign (hS π hπ)) (hPiSet π hπ)
    change E.V π = ∫ c, π c * (E.μ1 c - E.μ0 c) ∂E.PX at hw
    have hd : normalizedTT E π - E.V π =
        ∫ c, π c * (E.μ0 c - b0 c.1) ∂E.PX := by
      rw [hid π hπ, hw]
      exact hbias.1
    refine ⟨hid π hπ, congrArg abs hd, ?_⟩
    rw [hd]
    simpa only [marginalHeterogeneity, abs_sub_comm] using hbias.2
  refine ⟨hpolicy, ?_⟩
  intro γ hγ b s hb hs
  have he : ∀ π ∈ PiSet, |normalizedTT E π - E.V π| ≤ γ :=
    fun π hπ => ((hpolicy π hπ).2.2).trans hγ
  have hreg := (proposition10OfErrorW2 E PiSet γ he).2 b s hb hs
  exact ⟨hreg.1, hreg.2.1.trans hreg.2.2⟩

/-- On the full H-in-L1 domain, the factorization equivalence is just
conditional-expectation subtraction and measurable pull-out. -/
theorem factorizationAtW2 {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω)
    (T : Ω → Bool) (H p : Ω → ℝ) (hp : Measurable[m] p)
    (hTH : Integrable (fun ω => bit (T ω) * H ω) μ)
    (hpH : Integrable (fun ω => p ω * H ω) μ) (hH : Integrable H μ) :
    ((μ[(fun ω => (bit (T ω) - p ω) * H ω) | m] =ᵐ[μ] (fun _ => 0)) ↔
      (μ[(fun ω => bit (T ω) * H ω) | m] =ᵐ[μ]
        (fun ω => p ω * μ[H | m] ω))) := by
  have hsplit : (fun ω => (bit (T ω) - p ω) * H ω) =
      (fun ω => bit (T ω) * H ω) - (fun ω => p ω * H ω) := by
    ext ω
    simp only [Pi.sub_apply]
    ring
  have hsub := condExp_sub hTH hpH m
  have hpull : μ[(fun ω => p ω * H ω) | m] =ᵐ[μ]
      (fun ω => p ω * μ[H | m] ω) :=
    condExp_mul_of_stronglyMeasurable_left hp.stronglyMeasurable hpH hH
  rw [hsplit]
  constructor
  · intro hz
    filter_upwards [hsub, hpull, hz] with ω hs hp' hz'
    dsimp only [Pi.sub_apply] at hs
    rw [hp'] at hs
    linarith
  · intro heq
    filter_upwards [hsub, hpull, heq] with ω hs hp' heq'
    dsimp only [Pi.sub_apply] at hs
    rw [hp'] at hs
    linarith

/-- After the sum identity is supplied, the n-times criterion is finite-dimensional
algebra. A common evaluation law equates the weighted means by integral transport. -/
theorem qualifiedAtW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) (hπ : Admissible π)
    (hsum : E.expectedTT π = ∑ i, (OutcomeMeanW2 E π - EvaluationMeanW2 E π i)) :
    E.expectedTT π = ∑ i, (OutcomeMeanW2 E π - EvaluationMeanW2 E π i) ∧
    ((∀ i, E.expectedTT π = (n : ℝ) * (OutcomeMeanW2 E π - EvaluationMeanW2 E π i)) ↔
      (∀ i j, EvaluationMeanW2 E π i = EvaluationMeanW2 E π j)) ∧
    (∀ D : Measure (C × ℝ),
      (∀ i, IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω)))
        id (E.law π) D) → ∀ i j, EvaluationMeanW2 E π i = EvaluationMeanW2 E π j) := by
  have hn : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr E.hn).ne'
  refine ⟨hsum, ⟨?_, ?_⟩, ?_⟩
  · intro h i j
    have hdiff : OutcomeMeanW2 E π - EvaluationMeanW2 E π i =
        OutcomeMeanW2 E π - EvaluationMeanW2 E π j :=
      mul_left_cancel₀ hn ((h i).symm.trans (h j))
    linarith
  · intro h i
    rw [hsum]
    simp_rw [h _ i]
    simp [mul_sub]
  · intro D hc i j
    have hm : Measurable (fun z : C × ℝ => π z.1 * z.2) :=
      (hπ.1.comp measurable_fst).mul measurable_snd
    exact ((hc i).comp hm).integral_eq.trans (((hc j).comp hm).integral_eq.symm)

/-- A finite common-law error implies L1 of the estimator evaluations, locally.
This implication is never used to strengthen the main theorem's moment domain. -/
theorem evaluatedIntegrableW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) (S : PolicyDesign E π)
    (D : Measure (C × ℝ))
    (hc : ∀ i, IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω)))
      id (E.law π) D)
    (he : Integrable (fun z => |z.2 - E.μ0 z.1|) D) :
    ∀ i, Integrable (fun ω => E.μhat π ω (E.X i ω)) (E.law π) := by
  let i0 : Fin n := ⟨0, E.hn⟩
  have hfst : IdentDistrib (fun z : C × ℝ => z.1) id D E.PX :=
    ((hc i0).comp measurable_fst).symm.trans (S.covariate_law i0)
  have hm0 : Integrable (fun z : C × ℝ => E.μ0 z.1) D :=
    (hfst.comp S.means_measurable.1).integrable_iff.mpr S.means_integrable.1
  have hH := AronowAudit.P006.Wave1.T8_lemma2_signed_residual_integrable
    D E.μ0 S.means_measurable.1 hm0 he
  intro i
  exact ((hc i).comp measurable_snd).integrable_iff.mpr hH

/-- Transfer the local score and welfare to the joint evaluation law and apply
the existing integral bias bound. The sum identity is the only new input. -/
theorem commonLawErrorAtW2 {Ω C : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    {n : ℕ} (E : Experiment Ω C n) (π : C → ℝ) (hπ : Admissible π)
    (S : PolicyDesign E π) (D : Measure (C × ℝ))
    (hc : ∀ i, IdentDistrib (fun ω => (E.X i ω, E.μhat π ω (E.X i ω)))
      id (E.law π) D)
    (he : Integrable (fun z => |z.2 - E.μ0 z.1|) D)
    (hsum : E.expectedTT π = ∑ i, (OutcomeMeanW2 E π - EvaluationMeanW2 E π i)) :
    |normalizedTT E π - E.V π| ≤ EvaluationErrorW2 E D := by
  let i0 : Fin n := ⟨0, E.hn⟩
  have hn : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr E.hn).ne'
  have hfst : IdentDistrib (fun z : C × ℝ => z.1) id D E.PX :=
    ((hc i0).comp measurable_fst).symm.trans (S.covariate_law i0)
  have hm0 : Integrable (fun z : C × ℝ => E.μ0 z.1) D :=
    (hfst.comp S.means_measurable.1).integrable_iff.mpr S.means_integrable.1
  have hm1 : Integrable (fun z : C × ℝ => E.μ1 z.1) D :=
    (hfst.comp S.means_measurable.2).integrable_iff.mpr S.means_integrable.2
  have hH := AronowAudit.P006.Wave1.T8_lemma2_signed_residual_integrable
    D E.μ0 S.means_measurable.1 hm0 he
  have hπD : AronowAudit.P006.Admissible (fun z : C × ℝ => π z.1) :=
    ⟨hπ.1.comp measurable_fst, fun z => hπ.2 z.1⟩
  have heval (i : Fin n) : EvaluationMeanW2 E π i = ∫ z, π z.1 * z.2 ∂D :=
    ((hc i).comp ((hπ.1.comp measurable_fst).mul measurable_snd)).integral_eq
  have hscore : E.expectedTT π =
      (n : ℝ) * (OutcomeMeanW2 E π - ∫ z, π z.1 * z.2 ∂D) := by
    rw [hsum]
    simp_rw [heval]
    simp [mul_sub]
  have hnorm : normalizedTT E π = ∫ z, π z.1 * (E.μ1 z.1 - z.2) ∂D := by
    unfold normalizedTT
    rw [hscore, mul_div_cancel_left₀ _ hn]
    have hy : (∫ z : C × ℝ, π z.1 * E.μ1 z.1 ∂D) = OutcomeMeanW2 E π :=
      (hfst.comp (hπ.1.mul S.means_measurable.2)).integral_eq
    rw [← hy, ← integral_sub
      (AronowAudit.P006.Wave1.T7_policy_mul hm1 hπD)
      (AronowAudit.P006.Wave1.T7_policy_mul hH hπD)]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by dsimp; ring)
  have hwelfare : E.V π = ∫ z, π z.1 * (E.μ1 z.1 - E.μ0 z.1) ∂D := by
    have hw := AronowAudit.P006.Wave1.RepairT6T7_actual_welfare
      (Bridge.experiment E) (Bridge.policyDesign S) hπ
    change E.V π = ∫ c, π c * (E.μ1 c - E.μ0 c) ∂E.PX at hw
    rw [hw]
    exact ((hfst.comp (hπ.1.mul
      (S.means_measurable.2.sub S.means_measurable.1))).integral_eq).symm
  have hbias := AronowAudit.P006.Wave1.T8_information_integral_bias_bound D
    (fun z => E.μ1 z.1) (fun z => E.μ0 z.1) (fun z => z.2)
    (fun z => π z.1) hm1 hm0 hH hπD
  rw [hnorm, hwelfare, hbias.1]
  simpa only [EvaluationErrorW2, abs_sub_comm] using hbias.2

end
end SAP.P006a.WH.W2
