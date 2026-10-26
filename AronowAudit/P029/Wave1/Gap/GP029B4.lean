import AronowAudit.P029.P029_Audit
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
P029-T4: corrected weighted covariance identities and joint-independence alternatives.
-/
namespace AronowAudit.P029.Wave1

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/- Finite partitions, including null cells. -/

private theorem cwl_profile_mul_integrable {Ω X : Type*}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure Ω} {T : Ω → X}
    (hT : Measurable T) {v : Ω → ℝ} (hv : Integrable v μ) (w : X → ℝ) :
    Integrable (fun ω => w (T ω) * v ω) μ := by
  have hcell (x : X) : MeasurableSet {ω | T ω = x} :=
    hT (measurableSet_singleton x)
  have hid : (fun ω => w (T ω) * v ω) =
      fun ω => ∑ x : X, ({ω | T ω = x}.indicator (fun ω => w x * v ω)) ω := by
    funext ω
    simp [Set.indicator, Finset.sum_ite_eq']
  rw [hid]
  exact integrable_finsetSum _ (fun x _ => (hv.const_mul (w x)).indicator (hcell x))

private theorem cwl_profile_integral {Ω X : Type*}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure Ω} {T : Ω → X}
    (hT : Measurable T) {v : Ω → ℝ} (hv : Integrable v μ) (w : X → ℝ) :
    (∫ ω, w (T ω) * v ω ∂μ) =
      ∑ x : X, w x * (∫ ω in {ω | T ω = x}, v ω ∂μ) := by
  have hcell (x : X) : MeasurableSet {ω | T ω = x} :=
    hT (measurableSet_singleton x)
  calc
    _ = ∫ ω, ∑ x : X, ({ω | T ω = x}.indicator (fun ω => w x * v ω)) ω ∂μ := by
      congr 1; funext ω
      simp [Set.indicator, Finset.sum_ite_eq']
    _ = ∑ x : X, ∫ ω, ({ω | T ω = x}.indicator (fun ω => w x * v ω)) ω ∂μ :=
      integral_finsetSum _ (fun x _ => (hv.const_mul (w x)).indicator (hcell x))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [integral_indicator (hcell x), integral_const_mul]

private theorem cwl_profile_mean {Ω X : Type*}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → X} (hT : Measurable T) (w : X → ℝ) :
    (∫ ω, w (T ω) ∂μ) = ∑ x : X, mP μ {ω | T ω = x} * w x := by
  simpa [setIntegral_const, mP, measureReal_def, mul_comm] using
    cwl_profile_integral hT (integrable_const (1 : ℝ)) w

private theorem cwl_profile_law {Ω X : Type*}
    [MeasurableSpace Ω] [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → X} (hT : Measurable T) :
    ValidLaw (fun x => mP μ {ω | T ω = x}) := by
  refine ⟨fun _ => ENNReal.toReal_nonneg, ?_⟩
  simpa using (cwl_profile_mean (μ := μ) hT (fun _ => (1 : ℝ))).symm

private theorem cwl_null_set {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A : Set Ω} (hA : mP μ A = 0) : μ A = 0 := by
  exact ((ENNReal.toReal_eq_zero_iff _).mp hA).resolve_right (measure_ne_top μ A)

private theorem cwl_mass_mul_mean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (v : Ω → ℝ) (A : Set Ω) :
    mP μ A * mCE μ v A = ∫ ω in A, v ω ∂μ := by
  by_cases hA : mP μ A = 0
  · have hz : μ.restrict A = 0 := Measure.restrict_eq_zero.mpr (cwl_null_set hA)
    simp [mCE, hA, hz]
  · unfold mCE
    field_simp [hA]

private theorem cwl_independent_set_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {v : Ω → ℝ} {B : Ω → Bool}
    (hv : Integrable v μ) (hB : Measurable B) (hi : IndepFun v B μ) :
    (∫ ω in {ω | B ω = true}, v ω ∂μ) =
      (∫ ω, v ω ∂μ) * mP μ {ω | B ω = true} := by
  have hbit : Measurable bit := measurable_of_finite bit
  have hi' : IndepFun v (fun ω => bit (B ω)) μ := hi.comp measurable_id hbit
  have h := hi'.integral_fun_mul_eq_mul_integral
    hv.aestronglyMeasurable (hbit.comp hB).aestronglyMeasurable
  have hA : MeasurableSet {ω | B ω = true} := hB (measurableSet_singleton true)
  have hprod : (fun ω => v ω * bit (B ω)) = {ω | B ω = true}.indicator v := by
    funext ω; cases h : B ω <;> simp [bit, h, Set.indicator]
  have hone : (fun ω => bit (B ω)) =
      {ω | B ω = true}.indicator (fun _ => (1 : ℝ)) := by
    funext ω; cases h : B ω <;> simp [bit, h, Set.indicator]
  calc
    _ = ∫ ω, v ω * bit (B ω) ∂μ := by rw [hprod, integral_indicator hA]
    _ = (∫ ω, v ω ∂μ) * ∫ ω, bit (B ω) ∂μ := h
    _ = _ := by
      rw [hone, integral_indicator hA, setIntegral_const]
      simp [mP, measureReal_def]

private theorem cwl_independent_arm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {v : Ω → ℝ} {Z : Ω → Bool}
    (hv : Integrable v μ) (hZ : Measurable Z) (hi : IndepFun Z v μ)
    (z : Bool) (hz : mP μ {ω | Z ω = z} ≠ 0) :
    mCE μ v {ω | Z ω = z} = ∫ ω, v ω ∂μ := by
  let B : Ω → Bool := fun ω => decide (Z ω = z)
  have hB : Measurable B := (measurable_of_finite (fun b : Bool => decide (b = z))).comp hZ
  have hiB : IndepFun v B μ :=
    hi.symm.comp measurable_id (measurable_of_finite (fun b : Bool => decide (b = z)))
  have h := cwl_independent_set_integral hv hB hiB
  have hset : {ω | B ω = true} = {ω | Z ω = z} := by ext ω; simp [B]
  rw [hset] at h
  unfold mCE
  rw [h, mul_div_cancel_right₀ _ hz]

/- Fixed response maps on exactly the tuple used in IVAssumptions. -/
private def cwl_responseY {X : Type*} (z : Bool) (t : X × Bool × Bool × ℝ × ℝ) : ℝ :=
  if (if z then t.2.2.1 else t.2.1) then t.2.2.2.2 else t.2.2.2.1

private def cwl_responseD {X : Type*} (z : Bool) (t : X × Bool × Bool × ℝ × ℝ) : ℝ :=
  bit (if z then t.2.2.1 else t.2.1)

private theorem cwl_responseY_measurable {X : Type*} [MeasurableSpace X] (z : Bool) :
    Measurable (cwl_responseY (X := X) z) := by
  have hd0 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.1) := by fun_prop
  have hd1 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.2.1) := by fun_prop
  have hy0 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.2.2.1) := by fun_prop
  have hy1 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.2.2.2) := by fun_prop
  cases z
  · change Measurable (fun t : X × Bool × Bool × ℝ × ℝ => if t.2.1 = true then t.2.2.2.2 else t.2.2.2.1)
    exact Measurable.ite (hd0 (measurableSet_singleton true)) hy1 hy0
  · change Measurable (fun t : X × Bool × Bool × ℝ × ℝ => if t.2.2.1 = true then t.2.2.2.2 else t.2.2.2.1)
    exact Measurable.ite (hd1 (measurableSet_singleton true)) hy1 hy0

private theorem cwl_responseD_measurable {X : Type*} [MeasurableSpace X] (z : Bool) :
    Measurable (cwl_responseD (X := X) z) := by
  have hd0 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.1) := by fun_prop
  have hd1 : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => t.2.2.1) := by fun_prop
  cases z
  · change Measurable (fun t : X × Bool × Bool × ℝ × ℝ => bit t.2.1)
    exact (measurable_of_finite bit).comp hd0
  · change Measurable (fun t : X × Bool × Bool × ℝ × ℝ => bit t.2.2.1)
    exact (measurable_of_finite bit).comp hd1

/- This bridge permits any finite profile weight whose population mean is
nonzero. In particular inverse scores need not be positive on null cells. -/
private theorem cwl_weighted_bridge {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) (w : X → ℝ)
    (hW : (∫ ω, w (U ω).x ∂μ) ≠ 0) :
    mWald μ U Z (fun ω => w (U ω).x) =
      (∫ ω, w (U ω).x * (if (U ω).complier then (U ω).tau else 0) ∂μ) /
      (∫ ω, w (U ω).x * (if (U ω).complier then 1 else 0) ∂μ) := by
  rcases hiv with ⟨hx, hd0, hd1, hy0, hy1, hZ, iy0, iy1, hind, he0, he1, hmono, hrel⟩
  have hw : Measurable w := measurable_of_finite w
  have iw : Integrable (fun ω => w (U ω).x) μ := by
    simpa using cwl_profile_mul_integrable hx (integrable_const (1 : ℝ)) w
  have iY (z : Bool) : Integrable (fun ω => (U ω).outcome z) μ := by
    cases z
    · have hA : MeasurableSet {ω | (U ω).d0 = true} := hd0 (measurableSet_singleton true)
      have hid : (fun ω => (U ω).outcome false) =
          (fun ω => ({ω | (U ω).d0 = true}.indicator (fun ω => (U ω).y1)) ω +
            ({ω | (U ω).d0 = true}ᶜ.indicator (fun ω => (U ω).y0)) ω) := by
        funext ω; cases h : (U ω).d0 <;>
          simp [PotentialUnit.outcome, PotentialUnit.receipt, h, Set.indicator]
      rw [hid]; exact (iy1.indicator hA).add (iy0.indicator hA.compl)
    · have hA : MeasurableSet {ω | (U ω).d1 = true} := hd1 (measurableSet_singleton true)
      have hid : (fun ω => (U ω).outcome true) =
          (fun ω => ({ω | (U ω).d1 = true}.indicator (fun ω => (U ω).y1)) ω +
            ({ω | (U ω).d1 = true}ᶜ.indicator (fun ω => (U ω).y0)) ω) := by
        funext ω; cases h : (U ω).d1 <;>
          simp [PotentialUnit.outcome, PotentialUnit.receipt, h, Set.indicator]
      rw [hid]; exact (iy1.indicator hA).add (iy0.indicator hA.compl)
  have iD (z : Bool) : Integrable (fun ω => bit ((U ω).receipt z)) μ := by
    have hd : Measurable (fun ω => (U ω).receipt z) := by
      cases z
      · simpa only [PotentialUnit.receipt, Bool.false_eq_true, ite_false] using hd0
      · simpa only [PotentialUnit.receipt, ite_true] using hd1
    have hA : MeasurableSet {ω | (U ω).receipt z = true} := hd (measurableSet_singleton true)
    convert (integrable_const (μ := μ) (1 : ℝ)).indicator hA using 1
    funext ω; cases h : (U ω).receipt z <;> simp [bit, Set.indicator, h]
  have iWY (z : Bool) := cwl_profile_mul_integrable hx (iY z) w
  have iWD (z : Bool) := cwl_profile_mul_integrable hx (iD z) w
  have hz (z : Bool) : mP μ {ω | Z ω = z} ≠ 0 := by
    cases z
    · have hcomp : {ω | Z ω = false} = {ω | Z ω = true}ᶜ := by
        ext ω; cases Z ω <;> simp
      have hsum := measureReal_add_measureReal_compl (μ := μ)
        (hZ (measurableSet_singleton true))
      have hp : 0 < mP μ {ω | Z ω = false} := by
        rw [hcomp]
        change 0 < μ.real {ω | Z ω = true}ᶜ
        change μ.real {ω | Z ω = true} < 1 at he1
        rw [probReal_univ] at hsum
        change μ.real {ω | Z ω = true} + μ.real {ω | Z ω = true}ᶜ = 1 at hsum
        linarith
      exact ne_of_gt hp
    · exact ne_of_gt he0
  have hiw : IndepFun Z (fun ω => w (U ω).x) μ := by
    exact hind.comp measurable_id (hw.comp measurable_fst)
  have hiY (z : Bool) : IndepFun Z (fun ω => w (U ω).x * (U ω).outcome z) μ := by
    simpa [Function.comp_def, cwl_responseY, PotentialUnit.outcome, PotentialUnit.receipt] using
      hind.comp measurable_id ((hw.comp measurable_fst).mul (cwl_responseY_measurable z))
  have hiD (z : Bool) : IndepFun Z (fun ω => w (U ω).x * bit ((U ω).receipt z)) μ := by
    simpa [Function.comp_def, cwl_responseD, PotentialUnit.receipt] using
      hind.comp measurable_id ((hw.comp measurable_fst).mul (cwl_responseD_measurable z))
  have hmeanW (z : Bool) : mCE μ (fun ω => w (U ω).x) {ω | Z ω = z} =
      ∫ ω, w (U ω).x ∂μ := cwl_independent_arm iw hZ hiw z (hz z)
  have hmeanY (z : Bool) :
      mCE μ (fun ω => w (U ω).x * (U ω).outcome (Z ω)) {ω | Z ω = z} =
        ∫ ω, w (U ω).x * (U ω).outcome z ∂μ := by
    calc
      _ = mCE μ (fun ω => w (U ω).x * (U ω).outcome z) {ω | Z ω = z} := by
        unfold mCE; congr 1
        apply setIntegral_congr_fun (hZ (measurableSet_singleton z))
        intro ω hω
        dsimp only
        rw [show Z ω = z from hω]
      _ = _ := cwl_independent_arm (iWY z) hZ (hiY z) z (hz z)
  have hmeanD (z : Bool) :
      mCE μ (fun ω => w (U ω).x * bit ((U ω).receipt (Z ω))) {ω | Z ω = z} =
        ∫ ω, w (U ω).x * bit ((U ω).receipt z) ∂μ := by
    calc
      _ = mCE μ (fun ω => w (U ω).x * bit ((U ω).receipt z)) {ω | Z ω = z} := by
        unfold mCE; congr 1
        apply setIntegral_congr_fun (hZ (measurableSet_singleton z))
        intro ω hω
        dsimp only
        rw [show Z ω = z from hω]
      _ = _ := cwl_independent_arm (iWD z) hZ (hiD z) z (hz z)
  have hnd : ∀ᵐ ω ∂μ, ¬ (U ω).defier := by
    simpa only [ae_iff, not_not] using hmono
  have hY : (∫ ω, w (U ω).x * (U ω).outcome true ∂μ) -
      (∫ ω, w (U ω).x * (U ω).outcome false ∂μ) =
      ∫ ω, w (U ω).x * (if (U ω).complier then (U ω).tau else 0) ∂μ := by
    rw [← integral_sub (iWY true) (iWY false)]
    apply integral_congr_ae
    filter_upwards [hnd] with ω hω
    rw [← mul_sub, (unit_itt_identities (U ω) hω).2]
  have hD : (∫ ω, w (U ω).x * bit ((U ω).receipt true) ∂μ) -
      (∫ ω, w (U ω).x * bit ((U ω).receipt false) ∂μ) =
      ∫ ω, w (U ω).x * (if (U ω).complier then 1 else 0) ∂μ := by
    rw [← integral_sub (iWD true) (iWD false)]
    apply integral_congr_ae
    filter_upwards [hnd] with ω hω
    rw [← mul_sub, (unit_itt_identities (U ω) hω).1]
  unfold mWald mArm
  simp only [hmeanW, hmeanY, hmeanD, ← sub_div, hY, hD]
  simp only [div_div_div_cancel_right₀ hW]

private theorem cwl_complier_measurable {Ω X : Type*} [MeasurableSpace Ω]
    {U : Ω → PotentialUnit X} (hd0 : Measurable (fun ω => (U ω).d0))
    (hd1 : Measurable (fun ω => (U ω).d1)) : MeasurableSet {ω | (U ω).complier} :=
  (hd0 (measurableSet_singleton false)).inter (hd1 (measurableSet_singleton true))

private theorem cwl_event_cell_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} {T : Ω → X} (hT : Measurable T)
    {C : Set Ω} (hC : MeasurableSet C) (v : Ω → ℝ) (x : X) :
    (∫ ω in {ω | T ω = x}, (if ω ∈ C then v ω else 0) ∂μ) =
      ∫ ω in {ω | ω ∈ C ∧ T ω = x}, v ω ∂μ := by
  have hA : MeasurableSet {ω | T ω = x} := hT (measurableSet_singleton x)
  have hset : {ω | ω ∈ C ∧ T ω = x} = C ∩ {ω | T ω = x} := rfl
  rw [hset, ← integral_indicator hA, ← integral_indicator (hC.inter hA)]
  congr 1; funext ω
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs <;> simp_all

private theorem cwl_score_mass {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {μ : Measure Ω} [IsFiniteMeasure μ]
    (U : Ω → PotentialUnit X) (x : X) :
    mP μ {ω | (U ω).x = x} * scoreAt μ U x =
      mP μ {ω | (U ω).complier ∧ (U ω).x = x} := by
  have hle : mP μ {ω | (U ω).complier ∧ (U ω).x = x} ≤
      mP μ {ω | (U ω).x = x} :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (fun _ h => h.2))
  by_cases hf : mP μ {ω | (U ω).x = x} = 0
  · have hq : mP μ {ω | (U ω).complier ∧ (U ω).x = x} = 0 :=
      le_antisymm (by simpa [hf] using hle) ENNReal.toReal_nonneg
    simp [scoreAt, hf, hq]
  · unfold scoreAt; field_simp [hf]

private theorem cwl_effect_mass {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {μ : Measure Ω} [IsFiniteMeasure μ]
    (U : Ω → PotentialUnit X) (x : X) :
    mP μ {ω | (U ω).x = x} * scoreAt μ U x * complierAt μ U x =
      ∫ ω in {ω | (U ω).complier ∧ (U ω).x = x}, (U ω).tau ∂μ := by
  rw [cwl_score_mass]
  exact cwl_mass_mul_mean _ _

private theorem cwl_weighted_cells {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X)
    (hx : Measurable (fun ω => (U ω).x))
    (hC : MeasurableSet {ω | (U ω).complier})
    (it : Integrable (fun ω => (U ω).tau) μ) (w : X → ℝ) :
    (∫ ω, w (U ω).x * (if (U ω).complier then (U ω).tau else 0) ∂μ) =
      ∑ x, mP μ {ω | (U ω).x = x} * w x * scoreAt μ U x * complierAt μ U x ∧
    (∫ ω, w (U ω).x * (if (U ω).complier then 1 else 0) ∂μ) =
      ∑ x, mP μ {ω | (U ω).x = x} * w x * scoreAt μ U x := by
  have ict : Integrable (fun ω => if (U ω).complier then (U ω).tau else 0) μ :=
    it.indicator hC
  have ic : Integrable (fun ω => if (U ω).complier then (1 : ℝ) else 0) μ :=
    (integrable_const (1 : ℝ)).indicator hC
  constructor
  · rw [cwl_profile_integral hx ict w]
    apply Finset.sum_congr rfl
    intro x _
    have hcell := cwl_event_cell_integral (μ := μ) hx hC (fun ω => (U ω).tau) x
    simp only [Set.mem_setOf_eq] at hcell
    rw [hcell, ← cwl_effect_mass U x]
    ring
  · rw [cwl_profile_integral hx ic w]
    apply Finset.sum_congr rfl
    intro x _
    have hcell := cwl_event_cell_integral (μ := μ) hx hC (fun _ => (1 : ℝ)) x
    simp only [Set.mem_setOf_eq] at hcell
    rw [hcell, setIntegral_const]
    simp only [smul_eq_mul, mul_one, measureReal_def]
    change w x * mP μ {ω | (U ω).complier ∧ (U ω).x = x} = _
    rw [← cwl_score_mass U x]
    ring

private theorem cwl_positive_profile_exists {X : Type*} [Fintype X]
    (f : X → ℝ) (hf : ValidLaw f) : ∃ x, 0 < f x := by
  by_contra h
  have hz : ∀ x, f x = 0 := by
    intro x
    exact le_antisymm (le_of_not_gt (fun hx => h ⟨x, hx⟩)) (hf.1 x)
  have := hf.2
  simp only [hz, Finset.sum_const_zero] at this
  norm_num at this

private theorem cwl_positive_weight_mean {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → X}
    (hx : Measurable T) (w : X → ℝ)
    (hw : ∀ x, 0 < mP μ {ω | T ω = x} → 0 < w x) :
    0 < ∫ ω, w (T ω) ∂μ := by
  let f := fun x => mP μ {ω | T ω = x}
  have hf : ValidLaw f := cwl_profile_law hx
  obtain ⟨x, hxpos⟩ := cwl_positive_profile_exists f hf
  rw [cwl_profile_mean hx w]
  apply Finset.sum_pos'
  · intro y _
    by_cases hy : f y = 0
    · change 0 ≤ f y * w y
      rw [hy, zero_mul]
    · exact (mul_pos (lt_of_le_of_ne (hf.1 y) (Ne.symm hy))
        (hw y (lt_of_le_of_ne (hf.1 y) (Ne.symm hy)))).le
  · exact ⟨x, Finset.mem_univ x, mul_pos hxpos (hw x hxpos)⟩

private theorem cwl_inverse_cancellation {X : Type*} [Fintype X]
    (f p a : X → ℝ) (hf : ValidLaw f) (hp : ∀ x, 0 < f x → 0 < p x) :
    (∑ x, f x * (1 / p x) * p x) = 1 ∧
    (∑ x, f x * (1 / p x) * p x * a x) = ∑ x, f x * a x := by
  have hc (x : X) : f x * (1 / p x) * p x = f x := by
    by_cases h : f x = 0
    · simp [h]
    · have hp0 := ne_of_gt (hp x (lt_of_le_of_ne (hf.1 x) (Ne.symm h)))
      field_simp [hp0]
  constructor
  · simpa only [hc] using hf.2
  · simp only [hc]

/- The seven finite-profile weighted covariance identities. -/
theorem corrected_weighted_limits_proof {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z)
    (hpos : ∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x)
    (w : X → ℝ) (hw : ∀ x, 0 < w x) :
    mWald μ U Z (fun ω => w (U ω).x) =
      (∫ ω, w (U ω).x * (if (U ω).complier then (U ω).tau else 0) ∂μ) /
      (∫ ω, w (U ω).x * (if (U ω).complier then 1 else 0) ∂μ) ∧
    mWald μ U Z (fun ω => w (U ω).x) =
      (∑ x, mP μ {ω | (U ω).x = x} * w x * scoreAt μ U x * complierAt μ U x) /
      (∑ x, mP μ {ω | (U ω).x = x} * w x * scoreAt μ U x) ∧
    mWald μ U Z (fun _ => 1) = mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} ∧
    mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) =
      ∑ x, mP μ {ω | (U ω).x = x} * complierAt μ U x ∧
    mWald μ U Z (fun _ => 1) - mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) =
      mCov μ (fun ω => scoreAt μ U (U ω).x) (fun ω => complierAt μ U (U ω).x) /
      mP μ {ω | (U ω).complier} ∧
    (mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} = (∫ ω, (U ω).tau ∂μ) →
      mWald μ U Z (fun _ => 1) = (∫ ω, (U ω).tau ∂μ)) ∧
    ((∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) →
      mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) = (∫ ω, (U ω).tau ∂μ)) := by
  have hx := hiv.1
  have hd0 := hiv.2.1
  have hd1 := hiv.2.2.1
  have hC := cwl_complier_measurable hd0 hd1
  have it : Integrable (fun ω => (U ω).tau) μ :=
    hiv.2.2.2.2.2.2.2.1.sub hiv.2.2.2.2.2.2.1
  let f : X → ℝ := fun x => mP μ {ω | (U ω).x = x}
  let p : X → ℝ := scoreAt μ U
  let a : X → ℝ := complierAt μ U
  let π : ℝ := mP μ {ω | (U ω).complier}
  have hf : ValidLaw f := cwl_profile_law hx
  have hp : ∀ x, 0 < f x → 0 < p x := hpos
  have hcells := cwl_weighted_cells μ U hx hC it
  have hπsum : π = ∑ x, f x * p x := by
    have h := (hcells (fun _ => 1)).2
    have hind : (∫ ω, (if (U ω).complier then (1 : ℝ) else 0) ∂μ) = π := by
      simpa [Set.indicator, π, mP, measureReal_def] using
        (integral_indicator_one (μ := μ) hC)
    simpa only [one_mul, mul_one, hind] using h
  have hπpos : 0 < π := by
    rw [hπsum]
    have h := cwl_positive_weight_mean hx p hp
    rwa [cwl_profile_mean hx p] at h
  have hwmean : (∫ ω, w (U ω).x ∂μ) ≠ 0 :=
    ne_of_gt (cwl_positive_weight_mean hx w (fun x _ => hw x))
  have hweighted := cwl_weighted_bridge μ U Z hiv w hwmean
  have hprofile : mWald μ U Z (fun ω => w (U ω).x) =
      (∑ x, f x * w x * p x * a x) / (∑ x, f x * w x * p x) := by
    rw [hweighted, (hcells w).1, (hcells w).2]
  have hunit := cwl_weighted_bridge μ U Z hiv (fun _ => 1) (by simp)
  have hunitFinite : mWald μ U Z (fun _ => 1) =
      (∑ x, f x * p x * a x) / π := by
    rw [hunit, (hcells (fun _ => 1)).1, (hcells (fun _ => 1)).2]
    simp only [mul_one]
    change (∑ x, f x * p x * a x) / (∑ x, f x * p x) = _
    rw [← hπsum]
  have hlate : mWald μ U Z (fun _ => 1) =
      mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} := by
    rw [hunit]
    simp only [one_mul]
    have hden : (∫ ω, (if (U ω).complier then (1 : ℝ) else 0) ∂μ) = π := by
      simpa [Set.indicator, π, mP, measureReal_def] using
        (integral_indicator_one (μ := μ) hC)
    rw [hden]
    change (∫ ω, {ω | (U ω).complier}.indicator (fun ω => (U ω).tau) ω ∂μ) / π = _
    rw [integral_indicator hC]
    rfl
  have hInvMean : (∫ ω, 1 / p (U ω).x ∂μ) ≠ 0 :=
    ne_of_gt (cwl_positive_weight_mean hx (fun x => 1 / p x)
      (fun x h => one_div_pos.mpr (hp x h)))
  have hcancel := cwl_inverse_cancellation f p a hf hp
  have hinv : mWald μ U Z (fun ω => 1 / p (U ω).x) = ∑ x, f x * a x := by
    rw [cwl_weighted_bridge μ U Z hiv (fun x => 1 / p x) hInvMean,
      (hcells (fun x => 1 / p x)).1, (hcells (fun x => 1 / p x)).2,
      hcancel.1, hcancel.2, div_one]
  have hcov : mCov μ (fun ω => p (U ω).x) (fun ω => a (U ω).x) =
      (∑ x, f x * (p x * a x)) - (∑ x, f x * p x) * (∑ x, f x * a x) := by
    unfold mCov
    rw [cwl_profile_mean hx (fun x => p x * a x),
      cwl_profile_mean hx p, cwl_profile_mean hx a]
  have hgap : mWald μ U Z (fun _ => 1) -
      mWald μ U Z (fun ω => 1 / p (U ω).x) =
      mCov μ (fun ω => p (U ω).x) (fun ω => a (U ω).x) / π := by
    rw [hunitFinite, hinv, hcov]
    have hnum : (∑ x, f x * p x * a x) = ∑ x, f x * (p x * a x) := by
      apply Finset.sum_congr rfl
      intro x _; ring
    rw [hnum, ← hπsum]
    field_simp [ne_of_gt hπpos] <;> ring
  refine ⟨hweighted, hprofile, hlate, hinv, hgap, ?_, ?_⟩
  · intro hmarg
    exact hlate.trans hmarg
  · intro hlatent
    rw [hinv]
    have htotal : (∫ ω, (U ω).tau ∂μ) =
        ∑ x, f x * mCE μ (fun ω => (U ω).tau) {ω | (U ω).x = x} := by
      calc
        _ = ∑ x : X, ∫ ω in {ω | (U ω).x = x}, (U ω).tau ∂μ := by
          simpa only [one_mul] using cwl_profile_integral hx it (fun _ => 1)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          exact (cwl_mass_mul_mean _ _).symm
    rw [htotal]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hfx : f x = 0
    · simp only [hfx, zero_mul]
    · have hfxpos : 0 < f x := lt_of_le_of_ne (hf.1 x) (Ne.symm hfx)
      have h := hlatent x hfxpos
      change mCE μ (fun ω => (U ω).tau) {ω | (U ω).x = x} = a x at h
      rw [h]

/- The two joint-independence alternatives. -/

private theorem jis_complier_mass_pos {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X)
    (hx : Measurable (fun ω => (U ω).x))
    (hC : MeasurableSet {ω | (U ω).complier})
    (it : Integrable (fun ω => (U ω).tau) μ)
    (hp : ∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x) :
    0 < mP μ {ω | (U ω).complier} := by
  have h := (cwl_weighted_cells μ U hx hC it (fun _ => 1)).2
  have hmass : (∫ ω, (if (U ω).complier then (1 : ℝ) else 0) ∂μ) =
      mP μ {ω | (U ω).complier} := by
    simpa [Set.indicator, mP, measureReal_def] using
      (integral_indicator_one (μ := μ) hC)
  have hs : mP μ {ω | (U ω).complier} =
      ∑ x, mP μ {ω | (U ω).x = x} * scoreAt μ U x := by
    simpa only [one_mul, mul_one, hmass] using h
  rw [hs]
  have hpos := cwl_positive_weight_mean hx (scoreAt μ U) hp
  rwa [cwl_profile_mean hx (scoreAt μ U)] at hpos

private theorem jis_effect_joint_means {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X)
    (hx : Measurable (fun ω => (U ω).x))
    (hC : MeasurableSet {ω | (U ω).complier})
    (it : Integrable (fun ω => (U ω).tau) μ)
    (hp : ∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x)
    (hi : IndepFun (fun ω => (U ω).tau)
      (fun ω => (decide (U ω).complier, (U ω).x)) μ) :
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} = (∫ ω, (U ω).tau ∂μ) ∧
    (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) := by
  have hc : Measurable (fun ω => decide (U ω).complier) :=
    measurable_to_bool (by
      change MeasurableSet {ω | decide (U ω).complier = true}
      simpa only [decide_eq_true_eq] using hC)
  have hpair := hc.prodMk hx
  have hfactor (B : Bool × X → Bool) :
      (∫ ω in {ω | B (decide (U ω).complier, (U ω).x) = true}, (U ω).tau ∂μ) =
      (∫ ω, (U ω).tau ∂μ) *
        mP μ {ω | B (decide (U ω).complier, (U ω).x) = true} := by
    exact cwl_independent_set_integral it ((measurable_of_finite B).comp hpair)
      (hi.comp measurable_id (measurable_of_finite B))
  have hπ := jis_complier_mass_pos μ U hx hC it hp
  have hI : (∫ ω in {ω | (U ω).complier}, (U ω).tau ∂μ) =
      (∫ ω, (U ω).tau ∂μ) * mP μ {ω | (U ω).complier} := by
    simpa using hfactor Prod.fst
  constructor
  · unfold mCE
    rw [hI, mul_div_cancel_right₀ _ (ne_of_gt hπ)]
  · intro x hfx
    have hq : 0 < mP μ {ω | (U ω).complier ∧ (U ω).x = x} := by
      rw [← cwl_score_mass U x]
      exact mul_pos hfx (hp x hfx)
    have hA : (∫ ω in {ω | (U ω).x = x}, (U ω).tau ∂μ) =
        (∫ ω, (U ω).tau ∂μ) * mP μ {ω | (U ω).x = x} := by
      simpa using hfactor (fun t => decide (t.2 = x))
    have hCA : (∫ ω in {ω | (U ω).complier ∧ (U ω).x = x}, (U ω).tau ∂μ) =
        (∫ ω, (U ω).tau ∂μ) * mP μ {ω | (U ω).complier ∧ (U ω).x = x} := by
      simpa using hfactor (fun t => decide (t.1 = true ∧ t.2 = x))
    unfold latentAt mCE
    rw [hA, hCA, mul_div_cancel_right₀ _ (ne_of_gt hfx),
      mul_div_cancel_right₀ _ (ne_of_gt hq)]

private theorem jis_compliance_joint_means {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X)
    (hx : Measurable (fun ω => (U ω).x))
    (hC : MeasurableSet {ω | (U ω).complier})
    (it : Integrable (fun ω => (U ω).tau) μ)
    (hp : ∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x)
    (hi : IndepFun (fun ω => decide (U ω).complier)
      (fun ω => ((U ω).tau, (U ω).x)) μ) :
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} = (∫ ω, (U ω).tau ∂μ) ∧
    (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) := by
  have hc : Measurable (fun ω => decide (U ω).complier) :=
    measurable_to_bool (by
      change MeasurableSet {ω | decide (U ω).complier = true}
      simpa only [decide_eq_true_eq] using hC)
  have hfactor (g : ℝ × X → ℝ) (hg : Measurable g)
      (ig : Integrable (fun ω => g ((U ω).tau, (U ω).x)) μ) :
      (∫ ω in {ω | (U ω).complier}, g ((U ω).tau, (U ω).x) ∂μ) =
      (∫ ω, g ((U ω).tau, (U ω).x) ∂μ) * mP μ {ω | (U ω).complier} := by
    have h := cwl_independent_set_integral ig hc (hi.symm.comp hg measurable_id)
    simpa using h
  have hπ := jis_complier_mass_pos μ U hx hC it hp
  have hI : (∫ ω in {ω | (U ω).complier}, (U ω).tau ∂μ) =
      (∫ ω, (U ω).tau ∂μ) * mP μ {ω | (U ω).complier} := by
    exact hfactor Prod.fst measurable_fst it
  constructor
  · unfold mCE
    rw [hI, mul_div_cancel_right₀ _ (ne_of_gt hπ)]
  · intro x hfx
    let A : Set Ω := {ω | (U ω).x = x}
    let C : Set Ω := {ω | (U ω).complier}
    have hA : MeasurableSet A := hx (measurableSet_singleton x)
    have hg1 : Measurable (fun t : ℝ × X => if t.2 = x then (1 : ℝ) else 0) :=
      measurable_const.indicator (measurable_snd (measurableSet_singleton x))
    have hgt : Measurable (fun t : ℝ × X => if t.2 = x then t.1 else 0) :=
      measurable_fst.indicator (measurable_snd (measurableSet_singleton x))
    have hmass0 := hfactor (fun t => if t.2 = x then (1 : ℝ) else 0)
      hg1 ((integrable_const (1 : ℝ)).indicator hA)
    have heffect0 := hfactor (fun t => if t.2 = x then t.1 else 0)
      hgt (it.indicator hA)
    have hmass : mP μ {ω | (U ω).complier ∧ (U ω).x = x} =
        mP μ A * mP μ C := by
      have hleft : (∫ ω in C, (if (U ω).x = x then (1 : ℝ) else 0) ∂μ) =
          mP μ {ω | (U ω).complier ∧ (U ω).x = x} := by
        change (∫ ω in C, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
        rw [setIntegral_indicator hA, setIntegral_const]
        have hinter : C ∩ A = {ω | (U ω).complier ∧ (U ω).x = x} := by
          ext ω; simp only [A, C, Set.mem_inter_iff, Set.mem_setOf_eq, and_comm]
        simp only [hinter, smul_eq_mul, mul_one, mP, measureReal_def]
      have hright : (∫ ω, (if (U ω).x = x then (1 : ℝ) else 0) ∂μ) = mP μ A := by
        simpa only [A, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, mP, measureReal_def] using
          (integral_indicator_one (μ := μ) hA)
      change (∫ ω in C, (if (U ω).x = x then (1 : ℝ) else 0) ∂μ) =
        (∫ ω, (if (U ω).x = x then (1 : ℝ) else 0) ∂μ) * mP μ C at hmass0
      rwa [hleft, hright] at hmass0
    have heffect : (∫ ω in {ω | (U ω).complier ∧ (U ω).x = x}, (U ω).tau ∂μ) =
        (∫ ω in A, (U ω).tau ∂μ) * mP μ C := by
      change (∫ ω in C, A.indicator (fun ω => (U ω).tau) ω ∂μ) =
        (∫ ω, A.indicator (fun ω => (U ω).tau) ω ∂μ) * mP μ C at heffect0
      rw [setIntegral_indicator hA, integral_indicator hA] at heffect0
      have hinter : C ∩ A = {ω | (U ω).complier ∧ (U ω).x = x} := by
        ext ω; simp only [A, C, Set.mem_inter_iff, Set.mem_setOf_eq, and_comm]
      rwa [hinter] at heffect0
    unfold latentAt mCE
    rw [heffect, hmass]
    change (∫ ω in A, (U ω).tau ∂μ) / mP μ A =
      ((∫ ω in A, (U ω).tau ∂μ) * mP μ C) / (mP μ A * mP μ C)
    exact (mul_div_mul_right _ _ (ne_of_gt hπ)).symm

theorem joint_independence_suffices_proof {Ω X : Type*} [MeasurableSpace Ω]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z)
    (hpos : ∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x)
    (hind : IndepFun (fun ω => (U ω).tau)
        (fun ω => (decide (U ω).complier, (U ω).x)) μ ∨
      IndepFun (fun ω => decide (U ω).complier)
        (fun ω => ((U ω).tau, (U ω).x)) μ) :
    mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} = (∫ ω, (U ω).tau ∂μ) ∧
    (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) ∧
    mWald μ U Z (fun _ => 1) = (∫ ω, (U ω).tau ∂μ) ∧
    mWald μ U Z (fun ω => 1 / scoreAt μ U (U ω).x) = (∫ ω, (U ω).tau ∂μ) := by
  have hx := hiv.1
  have hC := cwl_complier_measurable hiv.2.1 hiv.2.2.1
  have it : Integrable (fun ω => (U ω).tau) μ :=
    hiv.2.2.2.2.2.2.2.1.sub hiv.2.2.2.2.2.2.1
  have hmeans :
      mCE μ (fun ω => (U ω).tau) {ω | (U ω).complier} = (∫ ω, (U ω).tau ∂μ) ∧
      (∀ x, 0 < mP μ {ω | (U ω).x = x} → latentAt μ U x) := by
    rcases hind with hi | hi
    · exact jis_effect_joint_means μ U hx hC it hpos hi
    · exact jis_compliance_joint_means μ U hx hC it hpos hi
  have hlimits := corrected_weighted_limits_proof μ U Z hiv hpos (fun _ => 1)
    (fun _ => zero_lt_one)
  exact ⟨hmeans.1, hmeans.2, hlimits.2.2.2.2.2.1 hmeans.1,
    hlimits.2.2.2.2.2.2 hmeans.2⟩

end
end AronowAudit.P029.Wave1
