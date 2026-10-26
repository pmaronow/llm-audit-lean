import AronowAudit.P029.P029_Audit
import AronowAudit.P015.P015_ConvergenceCompletion
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Independence.Integration

/-!
Population identities, ICSW consistency, and the complier covariate law.
-/

namespace AronowAudit.P029.Wave1

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

section AppendixHelpers

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {U : Ω → PotentialUnit X} {Z : Ω → Bool}

lemma GP029B3b_appendix_complier_measurable (hiv : IVAssumptions μ U Z) :
    MeasurableSet {ω | (U ω).complier} := by
  exact (hiv.2.1 (measurableSet_singleton false)).inter
    (hiv.2.2.1 (measurableSet_singleton true))

lemma GP029B3b_appendix_tau_integrable (hiv : IVAssumptions μ U Z) :
    Integrable (fun ω => (U ω).tau) μ := by
  rcases hiv with ⟨_, _, _, _, _, _, hy0, hy1, _⟩
  exact hy1.sub hy0

lemma GP029B3b_appendix_indicator_integrable (hiv : IVAssumptions μ U Z) :
    Integrable (fun ω => if (U ω).complier then (1 : ℝ) else 0) μ := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using!
    (integrable_const (1 : ℝ)).indicator (GP029B3b_appendix_complier_measurable hiv)

lemma GP029B3b_appendix_effect_integrable (hiv : IVAssumptions μ U Z) :
    Integrable (fun ω => if (U ω).complier then (U ω).tau else 0) μ := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using!
    (GP029B3b_appendix_tau_integrable hiv).indicator (GP029B3b_appendix_complier_measurable hiv)

lemma GP029B3b_appendix_indicator_integral (hiv : IVAssumptions μ U Z) :
    (∫ ω, if (U ω).complier then (1 : ℝ) else 0 ∂μ) =
      mP μ {ω | (U ω).complier} := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, mP, Measure.real] using
    (integral_indicator_one (μ := μ) (GP029B3b_appendix_complier_measurable hiv))

lemma GP029B3b_appendix_effect_integral (hiv : IVAssumptions μ U Z) :
    (∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ) =
      ∫ ω in {ω | (U ω).complier}, (U ω).tau ∂μ := by
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using!
    (integral_indicator (μ := μ) (f := fun ω => (U ω).tau)
      (GP029B3b_appendix_complier_measurable hiv))

/-- Tower and integrability for both supplied versions. -/
lemma GP029B3b_appendix_score_tower (hiv : IVAssumptions μ U Z)
    {c m : X → ℝ} (hv : ScoreVersions μ U c m) :
    Integrable (fun ω => c (U ω).x) μ ∧
    Integrable (fun ω => c (U ω).x * m (U ω).x) μ ∧
    (∫ ω, c (U ω).x ∂μ) = mP μ {ω | (U ω).complier} ∧
    (∫ ω, c (U ω).x * m (U ω).x ∂μ) =
      ∫ ω in {ω | (U ω).complier}, (U ω).tau ∂μ := by
  have hG : covariateSigma U ≤ ‹MeasurableSpace Ω› := hiv.1.comap_le
  have hiq : Integrable (fun ω => c (U ω).x) μ :=
    integrable_condExp.congr hv.2.2.1.symm
  have hiqm : Integrable (fun ω => c (U ω).x * m (U ω).x) μ :=
    integrable_condExp.congr hv.2.2.2.symm
  refine ⟨hiq, hiqm, ?_, ?_⟩
  · calc
      (∫ ω, c (U ω).x ∂μ) =
          ∫ ω, condExp (covariateSigma U) μ
            (fun ω => if (U ω).complier then (1 : ℝ) else 0) ω ∂μ :=
        integral_congr_ae hv.2.2.1
      _ = ∫ ω, if (U ω).complier then (1 : ℝ) else 0 ∂μ := integral_condExp hG
      _ = _ := GP029B3b_appendix_indicator_integral hiv
  · calc
      (∫ ω, c (U ω).x * m (U ω).x ∂μ) =
          ∫ ω, condExp (covariateSigma U) μ
            (fun ω => if (U ω).complier then (U ω).tau else 0) ω ∂μ :=
        integral_congr_ae hv.2.2.2
      _ = ∫ ω, if (U ω).complier then (U ω).tau else 0 ∂μ := integral_condExp hG
      _ = _ := GP029B3b_appendix_effect_integral hiv

/-- Integral pull-out, stated with the two actual integrability premises. -/
lemma GP029B3b_appendix_integral_pullout (hiv : IVAssumptions μ U Z)
    {f w : Ω → ℝ} (hw : StronglyMeasurable[covariateSigma U] w)
    (hf : Integrable f μ) (hwf : Integrable (fun ω => w ω * f ω) μ) :
    (∫ ω, w ω * f ω ∂μ) =
      ∫ ω, w ω * condExp (covariateSigma U) μ f ω ∂μ := by
  have hG : covariateSigma U ≤ ‹MeasurableSpace Ω› := hiv.1.comap_le
  calc
    (∫ ω, w ω * f ω ∂μ) =
        ∫ ω, condExp (covariateSigma U) μ (fun ω => w ω * f ω) ω ∂μ :=
      (integral_condExp hG).symm
    _ = _ := integral_congr_ae
      (condExp_mul_of_stronglyMeasurable_left hw hwf hf)

/-- Positive masses of both assignment arms. -/
lemma GP029B3b_appendix_arm_pos (hiv : IVAssumptions μ U Z) (z : Bool) :
    0 < mP μ {ω | Z ω = z} := by
  rcases hiv with ⟨_, _, _, _, _, hZ, _, _, _, he0, he1, _⟩
  cases z
  · have hcompl : {ω | Z ω = false} = {ω | Z ω = true}ᶜ := by
      ext ω
      cases Z ω <;> simp
    have hm : mP μ {ω | Z ω = false} = 1 - mP μ {ω | Z ω = true} := by
      change μ.real {ω | Z ω = false} = 1 - μ.real {ω | Z ω = true}
      rw [hcompl]
      simpa only [probReal_univ] using (measureReal_compl (μ := μ) (s := {ω | Z ω = true}) (hZ (measurableSet_singleton true)))
    linarith
  · exact he0

/-- Randomization for an arbitrary measurable function of the full latent tuple.
The equality on the arm allows the left side to use an observed response. -/
lemma GP029B3b_appendix_observed_mean (hiv : IVAssumptions μ U Z) (z : Bool)
    (F : X × Bool × Bool × ℝ × ℝ → ℝ) (hF : Measurable F)
    (v : Ω → ℝ)
    (hFi : Integrable (fun ω => F ((U ω).x, (U ω).d0, (U ω).d1,
      (U ω).y0, (U ω).y1)) μ)
    (hon : ∀ ω, Z ω = z → v ω = F ((U ω).x, (U ω).d0, (U ω).d1,
      (U ω).y0, (U ω).y1)) :
    mCE μ v {ω | Z ω = z} =
      ∫ ω, F ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1) ∂μ := by
  rcases hiv with ⟨hx, hd0, hd1, hy0, hy1, hZ, hi0, hi1, hind, hrest⟩
  have hz : MeasurableSet {ω | Z ω = z} := hZ (measurableSet_singleton z)
  have hI : Measurable (fun b : Bool => if b = z then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_singleton z) measurable_const measurable_const
  have hT : Measurable (fun ω => ((U ω).x, (U ω).d0, (U ω).d1,
      (U ω).y0, (U ω).y1)) := hx.prodMk (hd0.prodMk (hd1.prodMk (hy0.prodMk hy1)))
  have hind' := hind.comp hI hF
  have hfactor : (∫ ω in {ω | Z ω = z},
      F ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1) ∂μ) =
      mP μ {ω | Z ω = z} *
        ∫ ω, F ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1) ∂μ := by
    have hmul := hind'.integral_fun_mul_eq_mul_integral
      (hI.comp hZ).aestronglyMeasurable (hF.comp hT).aestronglyMeasurable
    have hleft : (fun ω => (if Z ω = z then (1 : ℝ) else 0) *
        F ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)) =
        {ω | Z ω = z}.indicator (fun ω =>
          F ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)) := by
      funext ω; by_cases hh : Z ω = z <;> simp [hh]
    change (∫ ω, (if Z ω = z then (1 : ℝ) else 0) *
        F ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1) ∂μ) =
      (∫ ω, if Z ω = z then (1 : ℝ) else 0 ∂μ) *
        (∫ ω, F ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1) ∂μ) at hmul
    rw [hleft, integral_indicator hz] at hmul
    have hmass : (∫ ω, if Z ω = z then (1 : ℝ) else 0 ∂μ) =
        mP μ {ω | Z ω = z} := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, mP, Measure.real] using
        (integral_indicator_one (μ := μ) hz)
    rwa [hmass] at hmul
  have hon' : (∫ ω in {ω | Z ω = z}, v ω ∂μ) =
      ∫ ω in {ω | Z ω = z},
        F ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1) ∂μ := by
    exact setIntegral_congr_fun hz (fun ω hω => hon ω hω)
  unfold mCE
  rw [hon', hfactor]
  exact mul_div_cancel_left₀ _ (ne_of_gt (GP029B3b_appendix_arm_pos
    ⟨hx, hd0, hd1, hy0, hy1, hZ, hi0, hi1, hind, hrest⟩ z))

/-- Fixed-arm outcome regularity; only a choice between two L1 functions. -/
lemma GP029B3b_appendix_outcome_integrable (hiv : IVAssumptions μ U Z) (z : Bool) :
    Integrable (fun ω => (U ω).outcome z) μ := by
  rcases hiv with ⟨_, hd0, hd1, _, _, _, hi0, hi1, _⟩
  cases z
  · change Integrable (fun ω => if (U ω).d0 = true then (U ω).y1 else (U ω).y0) μ
    exact Integrable.piecewise (s := {ω | (U ω).d0 = true})
      (hd0 (measurableSet_singleton true)) hi1.integrableOn hi0.integrableOn
  · change Integrable (fun ω => if (U ω).d1 = true then (U ω).y1 else (U ω).y0) μ
    exact Integrable.piecewise (s := {ω | (U ω).d1 = true})
      (hd1 (measurableSet_singleton true)) hi1.integrableOn hi0.integrableOn

lemma GP029B3b_appendix_receipt_integrable (hiv : IVAssumptions μ U Z) (z : Bool) :
    Integrable (fun ω => bit ((U ω).receipt z)) μ := by
  rcases hiv with ⟨_, hd0, hd1, _, _, _, _⟩
  cases z
  · change Integrable (fun ω => if (U ω).d0 = true then (1 : ℝ) else 0) μ
    exact Integrable.piecewise (s := {ω | (U ω).d0 = true})
      (hd0 (measurableSet_singleton true))
      (integrable_const (μ := μ) (1 : ℝ)).integrableOn
      (integrable_const (μ := μ) (0 : ℝ)).integrableOn
  · change Integrable (fun ω => if (U ω).d1 = true then (1 : ℝ) else 0) μ
    exact Integrable.piecewise (s := {ω | (U ω).d1 = true})
      (hd1 (measurableSet_singleton true))
      (integrable_const (μ := μ) (1 : ℝ)).integrableOn
      (integrable_const (μ := μ) (0 : ℝ)).integrableOn

/-- Weighted observed differences, with all response integrability obtained
from the bound on the latent covariate weight. -/
lemma GP029B3b_appendix_weighted_differences (hiv : IVAssumptions μ U Z)
    (b : X → ℝ) (hb : Measurable b) (K : ℝ)
    (hbound : ∀ᵐ ω ∂μ, ‖b (U ω).x‖ ≤ K) :
    (mArm μ Z (fun ω => b (U ω).x) (fun ω => (U ω).outcome (Z ω)) true -
      mArm μ Z (fun ω => b (U ω).x) (fun ω => (U ω).outcome (Z ω)) false) =
      (∫ ω, b (U ω).x * (if (U ω).complier then (U ω).tau else 0) ∂μ) /
        (∫ ω, b (U ω).x ∂μ) ∧
    (mArm μ Z (fun ω => b (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) true -
      mArm μ Z (fun ω => b (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) false) =
      (∫ ω, b (U ω).x * (if (U ω).complier then (1 : ℝ) else 0) ∂μ) /
        (∫ ω, b (U ω).x ∂μ) := by
  have hbm := hb.comp hiv.1
  have hbi : Integrable (fun ω => b (U ω).x) μ :=
    Integrable.of_bound hbm.aestronglyMeasurable K hbound
  have hYi (z : Bool) : Integrable (fun ω => b (U ω).x * (U ω).outcome z) μ :=
    (GP029B3b_appendix_outcome_integrable hiv z).bdd_mul hbm.aestronglyMeasurable hbound
  have hDi (z : Bool) : Integrable (fun ω => b (U ω).x * bit ((U ω).receipt z)) μ :=
    (GP029B3b_appendix_receipt_integrable hiv z).bdd_mul hbm.aestronglyMeasurable hbound
  let TY (z : Bool) : X × Bool × Bool × ℝ × ℝ → ℝ :=
    fun t => b t.1 * (if (if z then t.2.2.1 else t.2.1) then t.2.2.2.2 else t.2.2.2.1)
  let TD (z : Bool) : X × Bool × Bool × ℝ × ℝ → ℝ :=
    fun t => b t.1 * bit (if z then t.2.2.1 else t.2.1)
  have hTY (z : Bool) : Measurable (TY z) := by
    cases z <;> dsimp only [TY, Bool.false_eq_true, ite_false, ite_true]
    · exact (hb.comp measurable_fst).mul (Measurable.ite
        ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
        (by fun_prop) (by fun_prop))
    · exact (hb.comp measurable_fst).mul (Measurable.ite
        ((measurable_fst.comp (measurable_snd.comp measurable_snd))
          (measurableSet_singleton true)) (by fun_prop) (by fun_prop))
  have hTD (z : Bool) : Measurable (TD z) := by
    cases z <;> dsimp only [TD, Bool.false_eq_true, ite_false, ite_true, bit]
    · exact (hb.comp measurable_fst).mul (Measurable.ite
        ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
        measurable_const measurable_const)
    · exact (hb.comp measurable_fst).mul (Measurable.ite
        ((measurable_fst.comp (measurable_snd.comp measurable_snd))
          (measurableSet_singleton true)) measurable_const measurable_const)
  have hw (z : Bool) : mCE μ (fun ω => b (U ω).x) {ω | Z ω = z} =
      ∫ ω, b (U ω).x ∂μ := by
    exact GP029B3b_appendix_observed_mean hiv z (fun t => b t.1) (hb.comp measurable_fst)
      _ hbi (fun _ _ => rfl)
  have hy (z : Bool) : mCE μ (fun ω => b (U ω).x * (U ω).outcome (Z ω))
      {ω | Z ω = z} = ∫ ω, b (U ω).x * (U ω).outcome z ∂μ := by
    apply GP029B3b_appendix_observed_mean hiv z (TY z) (hTY z) _ (hYi z)
    intro ω hω; rw [hω]; rfl
  have hd (z : Bool) : mCE μ (fun ω => b (U ω).x * bit ((U ω).receipt (Z ω)))
      {ω | Z ω = z} = ∫ ω, b (U ω).x * bit ((U ω).receipt z) ∂μ := by
    apply GP029B3b_appendix_observed_mean hiv z (TD z) (hTD z) _ (hDi z)
    intro ω hω; rw [hω]; rfl
  have hnodef : ∀ᵐ ω ∂μ, ¬ (U ω).defier := by
    have hn := hiv.2.2.2.2.2.2.2.2.2.2.2.1
    simpa only [ae_iff, not_not] using hn
  constructor
  · simp only [mArm, hy, hw, ← sub_div]
    rw [← integral_sub (hYi true) (hYi false)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hnodef] with ω hω
    rw [← mul_sub, (unit_itt_identities (U ω) hω).2]
  · simp only [mArm, hd, hw, ← sub_div]
    rw [← integral_sub (hDi true) (hDi false)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hnodef] with ω hω
    rw [← mul_sub, (unit_itt_identities (U ω) hω).1]

end AppendixHelpers


theorem appendix_population_identities_proof {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (hiv : IVAssumptions μ U Z)
    (c m : X → ℝ) (hv : ScoreVersions μ U c m)
    (ε : ℝ) (he : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1) :
    mP μ {ω | (U ω).complier} * mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
      (∫ ω, c (U ω).x * m (U ω).x ∂μ) ∧
    mP μ {ω | (U ω).complier} = (∫ ω, c (U ω).x ∂μ) ∧
    (mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) true -
      mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => (U ω).outcome (Z ω)) false) =
        (∫ ω, m (U ω).x ∂μ)/(∫ ω, 1/c (U ω).x ∂μ) ∧
    (mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) true -
      mArm μ Z (fun ω => 1/c (U ω).x) (fun ω => bit ((U ω).receipt (Z ω))) false) =
        1/(∫ ω, 1/c (U ω).x ∂μ) ∧
    mWald μ U Z (fun ω => 1/c (U ω).x) = (∫ ω, m (U ω).x ∂μ) ∧
    (A1Versions μ U m → mWald μ U Z (fun ω => 1/c (U ω).x) = (∫ ω, (U ω).tau ∂μ)) := by
  have hG : covariateSigma U ≤ ‹MeasurableSpace Ω› := hiv.1.comap_le
  have hC := GP029B3b_appendix_complier_measurable hiv
  obtain ⟨hiq, hiqm, hq, hqm⟩ := GP029B3b_appendix_score_tower hiv hv
  let w : Ω → ℝ := fun ω => 1 / c (U ω).x
  have hwm : Measurable w := measurable_const.div (hv.1.comp hiv.1)
  have hwG : StronglyMeasurable[covariateSigma U] w := by
    have hxG : Measurable[covariateSigma U] (fun ω => (U ω).x) :=
      Measurable.of_comap_le le_rfl
    exact (measurable_const.div (hv.1.comp hxG)).stronglyMeasurable
  have hwb : ∀ᵐ ω ∂μ, ‖w ω‖ ≤ 1 / ε := by
    filter_upwards [hpos] with ω hω
    have hq0 : 0 < c (U ω).x := lt_trans he hω.1
    dsimp only [w]
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hq0)]
    exact (one_div_le_one_div_of_le he hω.1.le)
  have hwi : Integrable w μ := Integrable.of_bound hwm.aestronglyMeasurable (1 / ε) hwb
  have hw1 : ∀ᵐ ω ∂μ, 1 ≤ w ω := by
    filter_upwards [hpos] with ω hω
    have hq0 : 0 < c (U ω).x := lt_trans he hω.1
    exact (le_div_iff₀ hq0).mpr (by simpa using hω.2)
  have hW1 : 1 ≤ ∫ ω, w ω ∂μ := by
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      (integral_mono_ae (integrable_const (1 : ℝ)) hwi hw1)
  have hW : (∫ ω, w ω ∂μ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hW1)
  have hπ : 0 < mP μ {ω | (U ω).complier} := by
    have hε : ε ≤ ∫ ω, c (U ω).x ∂μ := by
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
        (integral_mono_ae (integrable_const ε) hiq (hpos.mono fun _ hω => hω.1.le))
    rw [hq] at hε
    exact lt_of_lt_of_le he hε
  have hnorm : mP μ {ω | (U ω).complier} *
      mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
        ∫ ω in {ω | (U ω).complier}, (U ω).tau ∂μ := by
    unfold mCE
    field_simp [ne_of_gt hπ]
  have hwq : (fun ω => w ω * c (U ω).x) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    filter_upwards [hpos] with ω hω
    dsimp only [w]
    field_simp [ne_of_gt (lt_trans he hω.1)]
  have hwqm : (fun ω => w ω * (c (U ω).x * m (U ω).x)) =ᵐ[μ]
      (fun ω => m (U ω).x) := by
    filter_upwards [hwq] with ω hω
    simpa only [← mul_assoc, hω, one_mul]
  have him : Integrable (fun ω => m (U ω).x) μ :=
    (hiqm.bdd_mul hwm.aestronglyMeasurable hwb).congr hwqm
  have hwCi : Integrable (fun ω => w ω *
      (if (U ω).complier then (1 : ℝ) else 0)) μ :=
    (GP029B3b_appendix_indicator_integrable hiv).bdd_mul hwm.aestronglyMeasurable hwb
  have hwCti : Integrable (fun ω => w ω *
      (if (U ω).complier then (U ω).tau else 0)) μ :=
    (GP029B3b_appendix_effect_integrable hiv).bdd_mul hwm.aestronglyMeasurable hwb
  have hwC : (∫ ω, w ω * (if (U ω).complier then (1 : ℝ) else 0) ∂μ) = 1 := by
    calc
      _ = ∫ ω, w ω * condExp (covariateSigma U) μ
          (fun ω => if (U ω).complier then (1 : ℝ) else 0) ω ∂μ :=
        GP029B3b_appendix_integral_pullout hiv hwG (GP029B3b_appendix_indicator_integrable hiv) hwCi
      _ = ∫ ω, w ω * c (U ω).x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hv.2.2.1] with ω hω
        rw [hω]
      _ = ∫ _ : Ω, (1 : ℝ) ∂μ := integral_congr_ae hwq
      _ = 1 := by simp
  have hwCt : (∫ ω, w ω * (if (U ω).complier then (U ω).tau else 0) ∂μ) =
      ∫ ω, m (U ω).x ∂μ := by
    calc
      _ = ∫ ω, w ω * condExp (covariateSigma U) μ
          (fun ω => if (U ω).complier then (U ω).tau else 0) ω ∂μ :=
        GP029B3b_appendix_integral_pullout hiv hwG (GP029B3b_appendix_effect_integrable hiv) hwCti
      _ = ∫ ω, w ω * (c (U ω).x * m (U ω).x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hv.2.2.2] with ω hω
        rw [hω]
      _ = _ := integral_congr_ae hwqm
  obtain ⟨hY, hD⟩ := GP029B3b_appendix_weighted_differences hiv (fun x => 1 / c x)
    (measurable_const.div hv.1) (1 / ε) hwb
  change (mArm μ Z w (fun ω => (U ω).outcome (Z ω)) true -
      mArm μ Z w (fun ω => (U ω).outcome (Z ω)) false) =
      (∫ ω, w ω * (if (U ω).complier then (U ω).tau else 0) ∂μ) /
        (∫ ω, w ω ∂μ) at hY
  change (mArm μ Z w (fun ω => bit ((U ω).receipt (Z ω))) true -
      mArm μ Z w (fun ω => bit ((U ω).receipt (Z ω))) false) =
      (∫ ω, w ω * (if (U ω).complier then (1 : ℝ) else 0) ∂μ) /
        (∫ ω, w ω ∂μ) at hD
  rw [hwCt] at hY
  rw [hwC] at hD
  have hwal : mWald μ U Z w = ∫ ω, m (U ω).x ∂μ := by
    unfold mWald
    rw [hY, hD]
    field_simp [hW]
  refine ⟨hnorm.trans hqm.symm, hq.symm, hY, hD, hwal, ?_⟩
  intro hA1
  have hA : (∫ ω, m (U ω).x ∂μ) = ∫ ω, (U ω).tau ∂μ := by
    calc
      _ = ∫ ω, condExp (covariateSigma U) μ (fun ω => (U ω).tau) ω ∂μ :=
        integral_congr_ae hA1
      _ = _ := integral_condExp hG
  exact hwal.trans hA

/-- The observed and latent joint variables are measurable. -/
lemma GP029B3b_joint_measurable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {U : Ω → PotentialUnit X} {Z : Ω → Bool}
    (hiv : IVAssumptions μ U Z) : Measurable (jointVariables U Z) :=
  (hiv.1.prodMk (hiv.2.1.prodMk (hiv.2.2.1.prodMk
    (hiv.2.2.2.1.prodMk hiv.2.2.2.2.1)))).prodMk hiv.2.2.2.2.2.1

lemma GP029B3b_iid_average {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : ℕ → Ω → PotentialUnit X}
    {Z : ℕ → Ω → Bool} {c m : X → ℝ} {s : ℕ → ℕ → Ω → ℝ}
    (h : ICSWConditions μ U Z c m s)
    (F : (X × Bool × Bool × ℝ × ℝ) × Bool → ℝ) (hF : Measurable F)
    (hi : Integrable (fun ω => F (jointVariables (U 0) (Z 0) ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ i : Fin (n+1), F (jointVariables (U i) (Z i) ω)) / (n+1))
      atTop (𝓝 (∫ ω, F (jointVariables (U 0) (Z 0) ω) ∂μ)) := by
  have hlln := strong_law_ae_real
    (fun i ω => F (jointVariables (U i) (Z i) ω)) hi
    (fun i j hij => (h.independent.indepFun hij).comp hF hF)
    (fun i => (h.identical i).comp hF)
  filter_upwards [hlln] with ω hω
  have ht := hω.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, ← Fin.sum_univ_eq_sum_range, Nat.cast_add,
    Nat.cast_one] using ht

lemma GP029B3b_mean_error_bound (n : ℕ) (p t v : Fin (n+1) → ℝ)
    (ε r : ℝ) (he : 0 < ε) (hr0 : 0 ≤ r) (hr : r < ε/2)
    (hp : ∀ i, ε < p i) (herr : ∀ i, |t i - p i| ≤ r) :
    |(∑ i, (1 / t i) * v i) / (n+1) - (∑ i, (1 / p i) * v i) / (n+1)| ≤
      (2*r/ε^2) * ((∑ i, |v i|) / (n+1)) := by
  have hN : (0 : ℝ) < n+1 := by positivity
  calc
    _ = |∑ i, (1 / t i - 1 / p i) * v i| / (n+1) := by
      rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hN]
      congr 2
      apply Finset.sum_congr rfl
      intro i _; ring
    _ ≤ (∑ i, |(1 / t i - 1 / p i) * v i|) / (n+1) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hN.le
    _ ≤ (∑ i, (2*r/ε^2) * |v i|) / (n+1) := by
      apply div_le_div_of_nonneg_right _ hN.le
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (inverse_score_accuracy (p i) (t i) ε r he (hp i) hr0 hr (herr i)).2
        (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Uniform score accuracy controls substitution in each integrable iid moment.
Every subsequence has a further subsequence where the score error vanishes
almost surely; the iid absolute moment controls the substitution error there. -/
lemma GP029B3b_raw_mean_limit {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : ℕ → Ω → PotentialUnit X}
    {Z : ℕ → Ω → Bool} {c m : X → ℝ} {s : ℕ → ℕ → Ω → ℝ}
    (h : ICSWConditions μ U Z c m s)
    (F : (X × Bool × Bool × ℝ × ℝ) × Bool → ℝ) (hF : Measurable F)
    (hi : Integrable (fun ω => F (jointVariables (U 0) (Z 0) ω)) μ) :
    TendstoInMeasure μ
      (fun n ω => (∑ i : Fin (n+1), (1/s n i ω) *
        F (jointVariables (U i) (Z i) ω)) / (n+1)) atTop
      (fun _ => ∫ ω, (1/c (U 0 ω).x) * F (jointVariables (U 0) (Z 0) ω) ∂μ) := by
  obtain ⟨ε, he, hq⟩ := h.overlap
  have hw : ∀ᵐ ω ∂μ, ‖1/c (U 0 ω).x‖ ≤ 1/ε := by
    filter_upwards [hq 0] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (lt_trans he hω.1))]
    exact one_div_le_one_div_of_le he hω.1.le
  have hwi : Integrable (fun ω => (1/c (U 0 ω).x) *
      F (jointVariables (U 0) (Z 0) ω)) μ :=
    hi.bdd_mul (measurable_const.div ((h.score 0).1.comp (h.iv 0).1)).aestronglyMeasurable hw
  let G : (X × Bool × Bool × ℝ × ℝ) × Bool → ℝ := fun t => (1/c t.1.1) * F t
  have hG : Measurable G :=
    (measurable_const.div ((h.score 0).1.comp (measurable_fst.comp measurable_fst))).mul hF
  have hlln := GP029B3b_iid_average h G hG hwi
  have habs := GP029B3b_iid_average h (fun t => |F t|) hF.abs hi.abs
  have hm (n : ℕ) : Measurable (fun ω => (∑ i : Fin (n+1),
      (1/s n i ω) * F (jointVariables (U i) (Z i) ω)) / (n+1)) := by
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun i _ =>
      (measurable_const.div (h.estimated_measurable n i)).mul
        (hF.comp (GP029B3b_joint_measurable (h.iv i))))
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => (hm n).aestronglyMeasurable)).2
  intro ns hns
  obtain ⟨ks, hks, heae⟩ := (h.uniform_consistency.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ks, hks, ?_⟩
  have hqa : ∀ᵐ ω ∂μ, ∀ i, ε < c (U i ω).x ∧ c (U i ω).x ≤ 1 := ae_all_iff.mpr hq
  filter_upwards [hlln, habs, heae, hqa] with ω hl ha herr hω
  let a : ℕ → ℕ := fun k => ns (ks k)
  have hat : Tendsto a atTop atTop := hns.tendsto_atTop.comp hks.tendsto_atTop
  have hsmall : ∀ᶠ k in atTop, uniformScoreError U c s (a k) ω < ε/2 :=
    herr.eventually (gt_mem_nhds (by linarith))
  have hupper : ∀ᶠ k in atTop,
      |(∑ i : Fin (a k+1), (1/s (a k) i ω) * F (jointVariables (U i) (Z i) ω)) / (a k+1) -
        (∑ i : Fin (a k+1), (1/c (U i ω).x) * F (jointVariables (U i) (Z i) ω)) / (a k+1)| ≤
      (2 * uniformScoreError U c s (a k) ω / ε^2) *
        ((∑ i : Fin (a k+1), |F (jointVariables (U i) (Z i) ω)|) / (a k+1)) := by
    filter_upwards [hsmall] with k hk
    have hmax (i : Fin (a k+1)) : |s (a k) i ω - c (U i ω).x| ≤
        uniformScoreError U c s (a k) ω :=
      Finset.le_sup' (fun j : ℕ => |s (a k) j ω - c (U j ω).x|) (Finset.mem_range.mpr i.isLt)
    exact GP029B3b_mean_error_bound (a k) _ _ _ ε _ he
      ((abs_nonneg _).trans (hmax ⟨0, by omega⟩)) hk
      (fun i => (hω i).1) hmax
  have hb : Tendsto
      (fun k => (2 * uniformScoreError U c s (a k) ω / ε^2) *
        ((∑ i : Fin (a k+1), |F (jointVariables (U i) (Z i) ω)|) / (a k+1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, a, mul_zero, zero_div, zero_mul] using!
      ((tendsto_const_nhds.mul herr).div_const (ε^2)).mul (ha.comp hat)
  have hdiff : Tendsto
      (fun k => (∑ i : Fin (a k+1), (1/s (a k) i ω) * F (jointVariables (U i) (Z i) ω)) / (a k+1) -
        (∑ i : Fin (a k+1), (1/c (U i ω).x) * F (jointVariables (U i) (Z i) ω)) / (a k+1))
      atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2
      (squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hupper hb)
  have ht := hdiff.add (hl.comp hat)
  simpa only [G, jointVariables, Function.comp_def, sub_add_cancel, zero_add, a] using ht

lemma GP029B3b_inverse_mean {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → PotentialUnit X}
    {Z : Ω → Bool} {c m : X → ℝ} (hiv : IVAssumptions μ U Z)
    (hv : ScoreVersions μ U c m) (ε : ℝ) (he : 0 < ε)
    (hq : ∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1) :
    Integrable (fun ω => 1/c (U ω).x) μ ∧ 0 < ∫ ω, 1/c (U ω).x ∂μ := by
  have hw : ∀ᵐ ω ∂μ, ‖1/c (U ω).x‖ ≤ 1/ε := by
    filter_upwards [hq] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (lt_trans he hω.1))]
    exact one_div_le_one_div_of_le he hω.1.le
  have hi : Integrable (fun ω => 1/c (U ω).x) μ :=
    Integrable.of_bound (measurable_const.div (hv.1.comp hiv.1)).aestronglyMeasurable _ hw
  refine ⟨hi, lt_of_lt_of_le zero_lt_one ?_⟩
  have hle : ∀ᵐ ω ∂μ, (1 : ℝ) ≤ 1/c (U ω).x := by
    filter_upwards [hq] with ω hω
    exact (le_div_iff₀ (lt_trans he hω.1)).mpr (by simpa using hω.2)
  simpa using integral_mono_ae (integrable_const (1 : ℝ)) hi hle

/-- The normalized empirical arm moments converge to the observed population
arm mean; randomization and overlap make the limiting weight mass positive. -/
lemma GP029B3b_arm_limit {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : ℕ → Ω → PotentialUnit X}
    {Z : ℕ → Ω → Bool} {c m : X → ℝ} {s : ℕ → ℕ → Ω → ℝ}
    (h : ICSWConditions μ U Z c m s) (z : Bool)
    (F : X × Bool × Bool × ℝ × ℝ → ℝ) (hF : Measurable F)
    (hi : Integrable (fun ω => F ((U 0 ω).x, (U 0 ω).d0, (U 0 ω).d1,
      (U 0 ω).y0, (U 0 ω).y1)) μ)
    (v : ℕ → Ω → ℝ)
    (hon : ∀ i ω, Z i ω = z → v i ω = F ((U i ω).x, (U i ω).d0, (U i ω).d1,
      (U i ω).y0, (U i ω).y1)) :
    TendstoInMeasure μ
      (fun n ω => sampleArm (fun i : Fin (n+1) => 1/s n i ω)
        (fun i => v i ω) (fun i => Z i ω) z) atTop
      (fun _ => mArm μ (Z 0) (fun ω => 1/c (U 0 ω).x) (v 0) z) := by
  let G : (X × Bool × Bool × ℝ × ℝ) × Bool → ℝ :=
    fun t => if t.2 = z then F t.1 else 0
  let H : (X × Bool × Bool × ℝ × ℝ) × Bool → ℝ :=
    fun t => if t.2 = z then 1 else 0
  have hG : Measurable G := Measurable.ite (measurable_snd (measurableSet_singleton z))
    (hF.comp measurable_fst) measurable_const
  have hH : Measurable H := Measurable.ite (measurable_snd (measurableSet_singleton z))
    measurable_const measurable_const
  have hz : MeasurableSet {ω | Z 0 ω = z} := (h.iv 0).2.2.2.2.2.1 (measurableSet_singleton z)
  have hgi : Integrable (fun ω => G (jointVariables (U 0) (Z 0) ω)) μ := by
    apply (hi.indicator hz).congr
    filter_upwards [] with ω
    simp only [G, jointVariables, Set.indicator_apply, Set.mem_ofPred_eq]
  have hhi : Integrable (fun ω => H (jointVariables (U 0) (Z 0) ω)) μ := by
    apply ((integrable_const (μ := μ) (1 : ℝ)).indicator hz).congr
    filter_upwards [] with ω
    simp only [H, jointVariables, Set.indicator_apply, Set.mem_ofPred_eq]
  let A := fun n ω => (∑ i : Fin (n+1), (1/s n i ω) * G (jointVariables (U i) (Z i) ω)) / (n+1)
  let B := fun n ω => (∑ i : Fin (n+1), (1/s n i ω) * H (jointVariables (U i) (Z i) ω)) / (n+1)
  let a := ∫ ω, (1/c (U 0 ω).x) * G (jointVariables (U 0) (Z 0) ω) ∂μ
  let b := ∫ ω, (1/c (U 0 ω).x) * H (jointVariables (U 0) (Z 0) ω) ∂μ
  have hA : TendstoInMeasure μ A atTop (fun _ => a) := GP029B3b_raw_mean_limit h G hG hgi
  have hB : TendstoInMeasure μ B atTop (fun _ => b) := GP029B3b_raw_mean_limit h H hH hhi
  have ha : a = ∫ ω in {ω | Z 0 ω = z}, (1/c (U 0 ω).x) * v 0 ω ∂μ := by
    rw [← integral_indicator hz]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases hh : Z 0 ω = z
      · simp [G, jointVariables, hh, hon 0 ω hh]
      · simp [G, jointVariables, hh])
  have hb : b = ∫ ω in {ω | Z 0 ω = z}, 1/c (U 0 ω).x ∂μ := by
    rw [← integral_indicator hz]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases hh : Z 0 ω = z <;> simp [H, jointVariables, hh])
  obtain ⟨ε, he, hq⟩ := h.overlap
  obtain ⟨hwi, hW⟩ := GP029B3b_inverse_mean (h.iv 0) (h.score 0) ε he (hq 0)
  have hpop := GP029B3b_appendix_observed_mean (h.iv 0) z (fun t => 1/c t.1)
    (measurable_const.div ((h.score 0).1.comp measurable_fst))
    (fun ω => 1/c (U 0 ω).x) hwi (fun _ _ => rfl)
  have hp := GP029B3b_appendix_arm_pos (h.iv 0) z
  have hbpos : 0 < b := by
    rw [hb]
    have hi : (∫ ω in {ω | Z 0 ω = z}, 1/c (U 0 ω).x ∂μ) =
        (∫ ω, 1/c (U 0 ω).x ∂μ) * mP μ {ω | Z 0 ω = z} :=
      (div_eq_iff (ne_of_gt hp)).mp hpop
    rw [hi]
    exact mul_pos hW hp
  have hlim := AronowAudit.P015.ConvergenceCompletion.div_limit μ hA hB (ne_of_gt hbpos)
  have hratio : a/b = mArm μ (Z 0) (fun ω => 1/c (U 0 ω).x) (v 0) z := by
    rw [ha, hb]
    unfold mArm mCE
    exact (div_div_div_cancel_right₀ (ne_of_gt hp) _ _).symm
  have hsample (n : ℕ) (ω : Ω) : A n ω / B n ω =
      sampleArm (fun i : Fin (n+1) => 1/s n i ω) (fun i => v i ω) (fun i => Z i ω) z := by
    have hN : (n+1 : ℝ) ≠ 0 := by positivity
    dsimp only [A, B]
    rw [div_div_div_cancel_right₀ hN]
    unfold sampleArm
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hh : Z i ω = z
    · simp [G, jointVariables, hh, hon i ω hh]
    · simp [G, jointVariables, hh]
  simpa only [hsample, hratio] using hlim

lemma GP029B3b_response_measurable {X : Type*} [MeasurableSpace X] (z : Bool) :
    Measurable (fun t : X × Bool × Bool × ℝ × ℝ =>
      if (if z then t.2.2.1 else t.2.1) then t.2.2.2.2 else t.2.2.2.1) ∧
    Measurable (fun t : X × Bool × Bool × ℝ × ℝ =>
      bit (if z then t.2.2.1 else t.2.1)) := by
  cases z
  · constructor
    · exact Measurable.ite
        ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
        (by fun_prop) (by fun_prop)
    · exact Measurable.ite
        ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
        measurable_const measurable_const
  · constructor
    · exact Measurable.ite
        ((measurable_fst.comp (measurable_snd.comp measurable_snd))
          (measurableSet_singleton true)) (by fun_prop) (by fun_prop)
    · exact Measurable.ite
        ((measurable_fst.comp (measurable_snd.comp measurable_snd))
          (measurableSet_singleton true)) measurable_const measurable_const

set_option maxHeartbeats 400000 in
/-- The general ICSW limit follows from the four arm means and the nonzero
population receipt contrast. No topological assumptions on covariates enter. -/
lemma GP029B3b_icsw_limit {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : ℕ → Ω → PotentialUnit X}
    {Z : ℕ → Ω → Bool} {c m : X → ℝ} {s : ℕ → ℕ → Ω → ℝ}
    (h : ICSWConditions μ U Z c m s) :
    TendstoInMeasure μ (icswSequence U Z s) atTop
      (fun _ => ∫ ω, m (U 0 ω).x ∂μ) := by
  have hy (z : Bool) : TendstoInMeasure μ
      (fun n ω => sampleArm (fun i : Fin (n+1) => 1/s n i ω)
        (fun i => (U i ω).outcome (Z i ω)) (fun i => Z i ω) z) atTop
      (fun _ => mArm μ (Z 0) (fun ω => 1/c (U 0 ω).x)
        (fun ω => (U 0 ω).outcome (Z 0 ω)) z) := by
    refine GP029B3b_arm_limit h z
      (fun t => if (if z then t.2.2.1 else t.2.1) then t.2.2.2.2 else t.2.2.2.1)
      (GP029B3b_response_measurable (X := X) z).1 (GP029B3b_appendix_outcome_integrable (h.iv 0) z)
      (fun i ω => (U i ω).outcome (Z i ω)) ?_
    intro i ω hω
    rw [hω]
    rfl
  have hd (z : Bool) : TendstoInMeasure μ
      (fun n ω => sampleArm (fun i : Fin (n+1) => 1/s n i ω)
        (fun i => bit ((U i ω).receipt (Z i ω))) (fun i => Z i ω) z) atTop
      (fun _ => mArm μ (Z 0) (fun ω => 1/c (U 0 ω).x)
        (fun ω => bit ((U 0 ω).receipt (Z 0 ω))) z) := by
    refine GP029B3b_arm_limit h z
      (fun t => bit (if z then t.2.2.1 else t.2.1))
      (GP029B3b_response_measurable (X := X) z).2 (GP029B3b_appendix_receipt_integrable (h.iv 0) z)
      (fun i ω => bit ((U i ω).receipt (Z i ω))) ?_
    intro i ω hω
    rw [hω]
    rfl
  have hy' := AronowAudit.P015.ConvergenceCompletion.sub_limit μ (hy true) (hy false)
  have hd' := AronowAudit.P015.ConvergenceCompletion.sub_limit μ (hd true) (hd false)
  obtain ⟨ε, he, hq⟩ := h.overlap
  have hpop := appendix_population_identities_proof μ (U 0) (Z 0) (h.iv 0)
    c m (h.score 0) ε he (hq 0)
  have hW := (GP029B3b_inverse_mean (h.iv 0) (h.score 0) ε he (hq 0)).2
  have hden : (mArm μ (Z 0) (fun ω => 1/c (U 0 ω).x)
        (fun ω => bit ((U 0 ω).receipt (Z 0 ω))) true -
      mArm μ (Z 0) (fun ω => 1/c (U 0 ω).x)
        (fun ω => bit ((U 0 ω).receipt (Z 0 ω))) false) ≠ 0 := by
    rw [hpop.2.2.2.1]
    exact one_div_ne_zero (ne_of_gt hW)
  have hlim := AronowAudit.P015.ConvergenceCompletion.div_limit μ hy' hd' hden
  change TendstoInMeasure μ (icswSequence U Z s) atTop
    (fun _ => mWald μ (U 0) (Z 0) (fun ω => 1/c (U 0 ω).x)) at hlim
  simpa only [hpop.2.2.2.2.1] using hlim

/-! Support-to-almost-everywhere transfer and the ATE substitution. -/

lemma GP029B3b_icsw_support_version_transfer {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
    (μ : Measure Ω) (V : Ω → X) (hV : Measurable V) (m a : X → ℝ)
    (heq : ∀ x ∈ (Measure.map V μ).support, m x = a x) :
    (fun ω => m (V ω)) =ᵐ[μ] (fun ω => a (V ω)) := by
  have hs : ∀ᵐ x ∂Measure.map V μ, x ∈ (Measure.map V μ).support :=
    (Measure.map V μ).support_mem_ae
  have hs' : ∀ᵐ ω ∂μ, V ω ∈ (Measure.map V μ).support :=
    ae_of_ae_map hV.aemeasurable hs
  exact hs'.mono fun ω hω => heq (V ω) hω

lemma GP029B3b_icsw_A1_integral {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X)
    (hx : Measurable (fun ω => (U ω).x)) (m a : X → ℝ)
    (haVersion : (fun ω => a (U ω).x) =ᵐ[μ]
      condExp (covariateSigma U) μ (fun ω => (U ω).tau))
    (hA1 : ∀ x ∈ (Measure.map (fun ω => (U ω).x) μ).support, m x = a x) :
    (∫ ω, m (U ω).x ∂μ) = ∫ ω, (U ω).tau ∂μ := by
  have hma := GP029B3b_icsw_support_version_transfer μ (fun ω => (U ω).x) hx m a hA1
  have hG : covariateSigma U ≤ ‹MeasurableSpace Ω› := hx.comap_le
  calc
    _ = ∫ ω, a (U ω).x ∂μ := integral_congr_ae hma
    _ = ∫ ω, condExp (covariateSigma U) μ (fun ω => (U ω).tau) ω ∂μ :=
      integral_congr_ae haVersion
    _ = _ := integral_condExp hG


theorem icsw_consistency_proof {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ℕ → Ω → PotentialUnit X)
    (Z : ℕ → Ω → Bool) (c m : X → ℝ) (s : ℕ → ℕ → Ω → ℝ)
    (h : ICSWConditions μ U Z c m s) (a : X → ℝ)
    (ha : Measurable a)
    (haVersion : ∀ i, (fun ω => a (U i ω).x) =ᵐ[μ]
      condExp (covariateSigma (U i)) μ (fun ω => (U i ω).tau))
    (hA1 : ∀ x ∈ (Measure.map (fun ω => (U 0 ω).x) μ).support, m x = a x)
    (hA3 : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ (Measure.map (fun ω => (U 0 ω).x) μ).support,
      ε < c x ∧ c x ≤ 1) :
    TendstoInMeasure μ (icswSequence U Z s) atTop (fun _ => ∫ ω, (U 0 ω).tau ∂μ) := by
  have hlimit : (∫ ω, m (U 0 ω).x ∂μ) = ∫ ω, (U 0 ω).tau ∂μ :=
    GP029B3b_icsw_A1_integral μ (U 0) (h.iv 0).1 m a (haVersion 0) hA1
  have hfull : TendstoInMeasure μ (icswSequence U Z s) atTop
      (fun _ => ∫ ω, m (U 0 ω).x ∂μ) := GP029B3b_icsw_limit h
  simpa only [hlimit] using hfull

/-! Pushforward Bayes identity, with no overlap premise. -/

section ComplierHelpers

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {U : Ω → PotentialUnit X} {Z : Ω → Bool}

lemma GP029B3b_complier_score_nonneg (hiv : IVAssumptions μ U Z)
    {c m : X → ℝ} (hv : ScoreVersions μ U c m) :
    ∀ᵐ x ∂Measure.map (fun ω => (U ω).x) μ, 0 ≤ c x := by
  have hnn : ∀ᵐ ω ∂μ, 0 ≤ c (U ω).x := by
    have hcond := condExp_nonneg (m := covariateSigma U) (μ := μ)
      (f := fun ω => if (U ω).complier then (1 : ℝ) else 0)
      (Filter.Eventually.of_forall (fun ω => by change 0 ≤ (if (U ω).complier then (1 : ℝ) else 0); split_ifs <;> norm_num))
    filter_upwards [hv.2.2.1, hcond] with ω hω hnonneg
    rw [hω]
    exact hnonneg
  exact (ae_map_iff hiv.1.aemeasurable (measurableSet_le measurable_const hv.1)).2 hnn

/-- The defining conditional-expectation identity on profile events. -/
lemma GP029B3b_complier_profile_setIntegral (hiv : IVAssumptions μ U Z)
    {c m : X → ℝ} (hv : ScoreVersions μ U c m)
    {B : Set X} (hB : MeasurableSet B) :
    (∫ x in B, c x ∂Measure.map (fun ω => (U ω).x) μ) =
      (μ ({ω | (U ω).complier} ∩ (fun ω => (U ω).x) ⁻¹' B)).toReal := by
  let A : Set Ω := (fun ω => (U ω).x) ⁻¹' B
  have hA : MeasurableSet A := hiv.1 hB
  have hAG : MeasurableSet[covariateSigma U] A := ⟨B, hB, rfl⟩
  have hG : covariateSigma U ≤ ‹MeasurableSpace Ω› := hiv.1.comap_le
  have hC := GP029B3b_appendix_complier_measurable hiv
  calc
    _ = ∫ ω in A, c (U ω).x ∂μ :=
      setIntegral_map hB hv.1.aestronglyMeasurable hiv.1.aemeasurable
    _ = ∫ ω in A, condExp (covariateSigma U) μ
        (fun ω => if (U ω).complier then (1 : ℝ) else 0) ω ∂μ := by
      apply integral_congr_ae
      exact ae_restrict_of_ae hv.2.2.1
    _ = ∫ ω in A, if (U ω).complier then (1 : ℝ) else 0 ∂μ :=
      setIntegral_condExp hG (GP029B3b_appendix_indicator_integrable hiv) hAG
    _ = _ := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, Measure.real, Measure.restrict_apply hC] using
        (integral_indicator_one (μ := μ.restrict A) hC)

/-- Unnormalized Bayes, proved as an equality of ENNReal-valued measures.
Using `ofReal` here avoids assuming an instance for finiteness of the
right-hand withDensity measure before its total mass has been identified. -/
lemma GP029B3b_complier_unnormalized_law (hiv : IVAssumptions μ U Z)
    {c m : X → ℝ} (hv : ScoreVersions μ U c m) :
    Measure.map (fun ω => (U ω).x) (μ.restrict {ω | (U ω).complier}) =
      (Measure.map (fun ω => (U ω).x) μ).withDensity (fun x => ENNReal.ofReal (c x)) := by
  have hiq := (GP029B3b_appendix_score_tower hiv hv).1
  have hiqX : Integrable c (Measure.map (fun ω => (U ω).x) μ) :=
    (integrable_map_measure hv.1.aestronglyMeasurable hiv.1.aemeasurable).2 hiq
  have hnn := GP029B3b_complier_score_nonneg hiv hv
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hiv.1 hB, withDensity_apply _ hB]
  calc
    (μ.restrict {ω | (U ω).complier}) ((fun ω => (U ω).x) ⁻¹' B) =
        ENNReal.ofReal (∫ x in B, c x ∂Measure.map (fun ω => (U ω).x) μ) := by
      rw [Measure.restrict_apply (hiv.1 hB), GP029B3b_complier_profile_setIntegral hiv hv hB,
        ENNReal.ofReal_toReal (measure_ne_top μ _)]
      simp only [Set.inter_comm]
    _ = _ := ofReal_integral_eq_lintegral_ofReal hiqX.integrableOn
      (ae_restrict_of_ae hnn)

/-- Density integration and L1 transfer, including the zero-score profiles. -/
lemma GP029B3b_complier_density_integral {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) (c m : X → ℝ) (hc : Measurable c)
    (hnn : ∀ᵐ x ∂ρ, 0 ≤ c x)
    (hcm : Integrable (fun x => c x * m x) ρ)
    (π : ℝ) (hπ : 0 < π) :
    Integrable m (ρ.withDensity (fun x => ENNReal.ofReal (c x / π))) ∧
    (∫ x, m x ∂ρ.withDensity (fun x => ENNReal.ofReal (c x / π))) =
      (∫ x, c x * m x ∂ρ) / π := by
  let d : X → ℝ≥0∞ := fun x => ENNReal.ofReal (c x / π)
  have hd : Measurable d := (hc.div_const π).ennreal_ofReal
  have hdtop : ∀ᵐ x ∂ρ, d x < ∞ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hprod : (fun x => (d x).toReal • m x) =ᵐ[ρ]
      (fun x => (c x * m x) / π) := by
    filter_upwards [hnn] with x hx
    dsimp only [d]
    rw [ENNReal.toReal_ofReal (div_nonneg hx hπ.le), smul_eq_mul]
    ring
  have hiprod : Integrable (fun x => (d x).toReal • m x) ρ :=
    (hcm.div_const π).congr hprod.symm
  refine ⟨(integrable_withDensity_iff_integrable_smul' hd hdtop).2 hiprod, ?_⟩
  calc
    _ = ∫ x, (d x).toReal • m x ∂ρ :=
      integral_withDensity_eq_integral_toReal_smul hd hdtop m
    _ = ∫ x, (c x * m x) / π ∂ρ := integral_congr_ae hprod
    _ = _ := integral_div π (fun x => c x * m x)

end ComplierHelpers


theorem complier_covariate_distribution_proof {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) (c m : X → ℝ) (hversions : ScoreVersions μ U c m)
    (hc : 0 < mP μ {ω | (U ω).complier}) :
    complierCovariateLaw μ U =
      (Measure.map (fun ω => (U ω).x) μ).withDensity
        (fun x => ENNReal.ofReal (c x / mP μ {ω | (U ω).complier})) ∧
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} =
      ∫ x, m x ∂complierCovariateLaw μ U := by
  let ρ : Measure X := Measure.map (fun ω => (U ω).x) μ
  let π : ℝ := mP μ {ω | (U ω).complier}
  have hπ : 0 < π := hc
  have hbase := GP029B3b_complier_unnormalized_law hiv hversions
  have hlaw : complierCovariateLaw μ U =
      ρ.withDensity (fun x => ENNReal.ofReal (c x / π)) := by
    unfold complierCovariateLaw
    rw [Measure.map_smul (ENNReal.ofReal ((mP μ {ω | (U ω).complier})⁻¹))
      hiv.1.aemeasurable, hbase]
    change ENNReal.ofReal (π⁻¹) • ρ.withDensity (fun x => ENNReal.ofReal (c x)) = _
    rw [← withDensity_smul (μ := ρ) (ENNReal.ofReal (π⁻¹))
      hversions.1.ennreal_ofReal]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hπ.le)]
    congr 1
    ring
  have hnn : ∀ᵐ x ∂ρ, 0 ≤ c x := GP029B3b_complier_score_nonneg hiv hversions
  obtain ⟨_, hiqm, _, hqm⟩ := GP029B3b_appendix_score_tower hiv hversions
  have hiqmX : Integrable (fun x => c x * m x) ρ :=
    (integrable_map_measure (hversions.1.mul hversions.2.1).aestronglyMeasurable
      hiv.1.aemeasurable).2 hiqm
  obtain ⟨him, hint⟩ := GP029B3b_complier_density_integral ρ c m hversions.1 hnn hiqmX π hπ
  have hmap : (∫ x, c x * m x ∂ρ) = ∫ ω, c (U ω).x * m (U ω).x ∂μ :=
    integral_map hiv.1.aemeasurable (hversions.1.mul hversions.2.1).aestronglyMeasurable
  refine ⟨hlaw, ?_⟩
  rw [hlaw, hint, hmap, hqm]
  rfl

end
end AronowAudit.P029.Wave1
