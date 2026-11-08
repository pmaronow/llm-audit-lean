import SAP.P001g.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.WH.W1.P.T117_L1V2

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

lemma integral_mul_cef {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (D : Ω → ℝ) (p : E → ℝ) (hcef : SAP.P001g.IsCEF μ X D p)
    (g : E → ℝ) (hg : Measurable g) (C : ℝ) (hgb : ∀ x, ‖g x‖ ≤ C) :
    ∫ ω, g (X ω) * D ω ∂μ = ∫ ω, p (X ω) * g (X ω) ∂μ := by
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    measurable_iff_comap_le.mpr le_rfl
  have hgX : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (fun ω => g (X ω)) := (hg.comp hXm).stronglyMeasurable
  have hgX' : AEStronglyMeasurable (fun ω => g (X ω)) μ := (hg.comp hX).aestronglyMeasurable
  have hDint : Integrable D μ := hcef.2.1
  have hpXint : Integrable (fun ω => p (X ω)) μ := hcef.2.2.1
  have hprodD : Integrable (fun ω => g (X ω) * D ω) μ :=
    hDint.bdd_mul hgX' (Filter.Eventually.of_forall fun ω => hgb (X ω))
  have hprodP' : Integrable (fun ω => p (X ω) * g (X ω)) μ :=
    hpXint.mul_bdd hgX' (Filter.Eventually.of_forall fun ω => hgb (X ω))
  have hprodP : Integrable (fun ω => g (X ω) * p (X ω)) μ :=
    hprodP'.congr (Filter.Eventually.of_forall fun ω => by ring)
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := MeasurableSpace.comap X inferInstance) hgX hprodD hDint
  have hcond := AronowAudit.P001.isCEF_condExp μ X hX D p hcef
  calc
    ∫ ω, g (X ω) * D ω ∂μ =
      ∫ ω, condExp (MeasurableSpace.comap X inferInstance) μ
        (fun ω => g (X ω) * D ω) ω ∂μ :=
      (integral_condExp hX.comap_le (f := fun ω => g (X ω) * D ω)).symm
    _ = ∫ ω, g (X ω) * condExp (MeasurableSpace.comap X inferInstance) μ D ω ∂μ :=
      integral_congr_ae hpull
    _ = ∫ ω, g (X ω) * p (X ω) ∂μ :=
      integral_congr_ae (hcond.mono fun ω hω => by
        change p (X ω) = condExp (MeasurableSpace.comap X inferInstance) μ D ω at hω
        change g (X ω) * condExp (MeasurableSpace.comap X inferInstance) μ D ω =
          g (X ω) * p (X ω)
        exact congrArg (fun z => g (X ω) * z) hω.symm)
    _ = ∫ ω, p (X ω) * g (X ω) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

end

end SAP.P001g.WH.W1.P.T117_L1V2

open MeasureTheory ProbabilityTheory Set
open SAP.P001g.WH.W1.P.T117_L1V2
open scoped ENNReal NNReal

theorem SAP.P001g.WH.W1.T117_L1V2_proof : SAP.P001g.WH.W1.T117_L1V2 := by
  intro Ω E _ _ μ hμ X hX D hD hDb p hp ε hεpos hεp m hm hArm
  rcases hp with ⟨hpmeas, hDint, hpXint, hcefId⟩
  let S : Set Ω := {ω | D ω = 1}
  have hS : MeasurableSet S := measurableSet_eq_fun (hD) measurable_const
  have hArmNorm : Integrable (fun ω => |m (X ω)|) (μ.restrict S) := hArm.abs
  have hArmIntegral : 0 ≤ ∫ ω in S, |m (X ω)| ∂μ :=
    integral_nonneg fun ω => abs_nonneg _
  let trunc : ℕ → Ω → ℝ := fun n ω => min (|m (X ω)|) (n : ℝ)
  have htruncMeas : ∀ n, Measurable (trunc n) := by
    intro n
    exact (hm.abs.comp hX).min measurable_const
  have htruncNonneg : ∀ n ω, 0 ≤ trunc n ω := by
    intro n ω
    exact le_min (abs_nonneg _) (Nat.cast_nonneg _)
  have htruncLe : ∀ n ω, trunc n ω ≤ |m (X ω)| := by
    intro n ω
    exact min_le_left _ _
  have htruncBound : ∀ n ω, ‖trunc n ω‖ ≤ (n : ℝ) := by
    intro n ω
    rw [Real.norm_eq_abs, abs_of_nonneg (htruncNonneg n ω)]
    exact min_le_right _ _
  have htruncInt : ∀ n, Integrable (trunc n) μ := by
    intro n
    refine (integrable_const (n : ℝ)).mono' (htruncMeas n).aestronglyMeasurable ?_
    filter_upwards with ω
    exact (htruncBound n ω)
  have htruncArmInt : ∀ n, Integrable (trunc n) (μ.restrict S) := by
    intro n
    exact (htruncInt n).mono_measure (Measure.restrict_le_self)
  have htruncLEarm : ∀ n, ∫ ω, trunc n ω ∂μ ≤
      (∫ ω in S, |m (X ω)| ∂μ) / ε := by
    intro n
    have hmix := integral_mul_cef μ X hX D p ⟨hpmeas, hDint, hpXint, hcefId⟩
      (fun x => min (|m x|) (n : ℝ)) ((hm.abs).min measurable_const) (n : ℝ) (by
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg _))]
        exact min_le_right _ _)
    have hOverlap : ∀ᵐ ω ∂μ, ε * trunc n ω ≤ p (X ω) * trunc n ω := by
      filter_upwards [hεp] with ω hω
      exact mul_le_mul_of_nonneg_right (le_of_lt hω) (htruncNonneg n ω)
    have hprodPint : Integrable (fun ω => p (X ω) * trunc n ω) μ := by
      apply hpXint.mul_bdd (htruncMeas n).aestronglyMeasurable
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (htruncNonneg n ω)]
      exact min_le_right _ _
    have hleftInt : Integrable (fun ω => ε * trunc n ω) μ := (htruncInt n).const_mul ε
    have hglobal := integral_mono_ae hleftInt hprodPint hOverlap
    have hglobal' : ε * (∫ ω, trunc n ω ∂μ) ≤ ∫ ω, p (X ω) * trunc n ω ∂μ := by
      simpa [integral_const_mul] using hglobal
    have hSprod : (fun ω => trunc n ω * D ω) =ᵐ[μ] indicator S (trunc n) := by
      filter_upwards [hDb] with ω hω
      rcases hω with h0 | h1
      · simp [S, h0]
      · simp [S, h1]
    have htreated : ∫ ω, p (X ω) * trunc n ω ∂μ = ∫ ω in S, trunc n ω ∂μ := by
      calc
        ∫ ω, p (X ω) * trunc n ω ∂μ = ∫ ω, trunc n ω * D ω ∂μ := hmix.symm
        _ = ∫ ω, indicator S (trunc n) ω ∂μ := integral_congr_ae hSprod
        _ = ∫ ω in S, trunc n ω ∂μ := integral_indicator hS
    have hArmComp : ∫ ω in S, trunc n ω ∂μ ≤ ∫ ω in S, |m (X ω)| ∂μ :=
      integral_mono_ae (htruncArmInt n) hArmNorm (Filter.Eventually.of_forall fun ω => htruncLe n ω)
    have hmul : ε * (∫ ω, trunc n ω ∂μ) ≤ ∫ ω in S, |m (X ω)| ∂μ :=
      hglobal'.trans (htreated ▸ hArmComp)
    exact (le_div_iff₀ hεpos).2 (by nlinarith [hmul])
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (trunc n ω)
  have hFmeas : ∀ n, Measurable (F n) := fun n => (htruncMeas n).ennreal_ofReal
  have hFmono : Monotone F := by
    intro n k hnk ω
    apply ENNReal.ofReal_le_ofReal
    dsimp [F, trunc]
    exact min_le_min le_rfl (by exact_mod_cast hnk)
  have hFbound : ∀ n, ∫⁻ ω, F n ω ∂μ ≤ ENNReal.ofReal ((∫ ω in S, |m (X ω)| ∂μ) / ε) := by
    intro n
    have hnorm : ENNReal.ofReal (∫ ω, trunc n ω ∂μ) = ∫⁻ ω, F n ω ∂μ := by
      rw [show F n = fun ω => ENNReal.ofReal (trunc n ω) from rfl]
      exact ofReal_integral_eq_lintegral_ofReal (htruncInt n)
        (Filter.Eventually.of_forall fun ω => htruncNonneg n ω)
    rw [← hnorm]
    exact ENNReal.ofReal_le_ofReal (htruncLEarm n)
  have hFsup : ∀ ω, (⨆ n, F n ω) = ENNReal.ofReal |m (X ω)| := by
    intro ω
    apply le_antisymm
    · refine iSup_le fun n => ?_
      apply ENNReal.ofReal_le_ofReal
      exact min_le_left _ _
    · obtain ⟨n, hn⟩ := exists_nat_ge |m (X ω)|
      have heq : min (|m (X ω)|) (n : ℝ) = |m (X ω)| :=
        min_eq_left (by exact_mod_cast hn)
      rw [← heq]
      exact le_iSup_of_le n le_rfl
  have hlimit : ∫⁻ ω, ‖m (X ω)‖ₑ ∂μ ≤
      ENNReal.ofReal ((∫ ω in S, |m (X ω)| ∂μ) / ε) := by
    calc
      ∫⁻ ω, ‖m (X ω)‖ₑ ∂μ = ∫⁻ ω, ⨆ n, F n ω ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with ω
        rw [hFsup ω, Real.enorm_eq_ofReal_abs]
      _ = ⨆ n, ∫⁻ ω, F n ω ∂μ := lintegral_iSup hFmeas hFmono
      _ ≤ ENNReal.ofReal ((∫ ω in S, |m (X ω)| ∂μ) / ε) := iSup_le hFbound
  have hfin : ∫⁻ ω, ‖m (X ω)‖ₑ ∂μ < ⊤ :=
    lt_of_le_of_lt hlimit ENNReal.ofReal_lt_top
  exact ⟨(hm.comp hX).aestronglyMeasurable, (hasFiniteIntegral_iff_enorm).2 hfin⟩
