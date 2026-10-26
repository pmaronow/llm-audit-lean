import AronowAudit.P029.P029_Audit
import AronowAudit.P029.Wave1.Gap.GP029B1
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
P029: saturated score consistency, the nested receipt model, one-sided ignorability,
and constant-effect identities.
-/
namespace AronowAudit.P029.Wave1

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-! ## Saturated score consistency -/

private theorem GP029B2b_t14_reciprocal_limit (n : ℕ → ℕ) (ht : Tendsto n atTop atTop) :
    Tendsto (fun k => ((n k : ℝ))⁻¹) atTop (𝓝 0) := by
  have hcast : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  exact tendsto_inv_atTop_zero.comp hcast

private theorem GP029B2b_t14_mass_nonneg (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (k : Fin (n+1)) : 0 ≤ binomialMass n p k := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
    (pow_nonneg (sub_nonneg.mpr hp') _)

theorem saturated_score_consistency_proof (n1 n0 : ℕ → ℕ)
    (hn1 : ∀ n, 0 < n1 n) (hn0 : ∀ n, 0 < n0 n)
    (ht1 : Tendsto n1 atTop atTop) (ht0 : Tendsto n0 atTop atTop)
    (p1 p0 : ℝ) (hp0 : 0 ≤ p0) (horder : p0 ≤ p1) (hp1 : p1 ≤ 1) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      fP (binomialArmLaw (n1 n) (n0 n) p1 p0)
        (fun k => δ < |armRateScore (n1 n) (n0 n) k - (p1-p0)|)) atTop (𝓝 0) := by
  intro δ hδ
  have h1 := (GP029B2b_t14_reciprocal_limit n1 ht1).const_mul (p1*(1-p1))
  have h0 := (GP029B2b_t14_reciprocal_limit n0 ht0).const_mul (p0*(1-p0))
  have hb : Tendsto (fun n =>
      (p1*(1-p1)/(n1 n : ℝ) + p0*(1-p0)/(n0 n : ℝ))/δ^2)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_add, zero_mul] using
      (h1.add h0).div_const (δ^2)
  apply squeeze_zero (fun n => ?_) (fun n => ?_) hb
  · unfold fP
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · exact mul_nonneg
        (GP029B2b_t14_mass_nonneg _ _ (hp0.trans horder) hp1 k.1)
        (GP029B2b_t14_mass_nonneg _ _ hp0 (horder.trans hp1) k.2)
    · exact le_rfl
  · exact (saturated_binomial_bias_bound_proof (n1 n) (n0 n) (hn1 n) (hn0 n)
      p1 p0 hp0 horder hp1).2.2.2 δ hδ

/-! ## Nested receipt model
The event factorization also applies to one-sided ignorability. -/

private theorem GP029B2b_t18_arm_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Bool) (hz : Measurable Z)
    (h0 : 0 < mP μ {ω | Z ω = true}) (h1 : mP μ {ω | Z ω = true} < 1)
    (z : Bool) : 0 < mP μ {ω | Z ω = z} := by
  cases z
  · have hcomp : {ω | Z ω = false} = {ω | Z ω = true}ᶜ := by
      ext ω; cases Z ω <;> simp
    rw [hcomp]
    have hm := measureReal_add_measureReal_compl (μ := μ) (hz (measurableSet_singleton true))
    have htotal : μ.real Set.univ = 1 := by simp
    change 0 < μ.real {ω | Z ω = true}ᶜ
    change μ.real {ω | Z ω = true} < 1 at h1
    change μ.real {ω | Z ω = true} + μ.real {ω | Z ω = true}ᶜ = μ.real Set.univ at hm
    linarith
  · exact h0

private theorem GP029B2b_t18_event_factor {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Bool) (F : Ω → E)
    (hz : Measurable Z) (hF : Measurable F) (hi : IndepFun Z F μ)
    (B : Set E) (hB : MeasurableSet B) (φ : E → ℝ) (hφ : Measurable φ)
    (z : Bool) :
    (∫ ω in {ω | F ω ∈ B ∧ Z ω = z}, φ (F ω) ∂μ) =
      mP μ {ω | Z ω = z} * ∫ ω in {ω | F ω ∈ B}, φ (F ω) ∂μ := by
  let j : Bool → ℝ := ({z} : Set Bool).indicator (fun _ => 1)
  let g : E → ℝ := B.indicator φ
  have hj : Measurable j := measurable_const.indicator (measurableSet_singleton z)
  have hg : Measurable g := hφ.indicator hB
  have hprod := (hi.comp hj hg).integral_fun_mul_eq_mul_integral
    (hj.comp hz).aestronglyMeasurable (hg.comp hF).aestronglyMeasurable
  dsimp only [Function.comp_def] at hprod
  have heq : (fun ω => j (Z ω) * g (F ω)) =
      {ω | F ω ∈ B ∧ Z ω = z}.indicator (fun ω => φ (F ω)) := by
    funext ω
    simp only [j, g, Set.indicator_apply, Set.mem_singleton_iff, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have hjint : (∫ ω, j (Z ω) ∂μ) = mP μ {ω | Z ω = z} := by
    change (∫ ω, {ω | Z ω = z}.indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
    rw [integral_indicator (show MeasurableSet {ω | Z ω = z} from hz (measurableSet_singleton z)), setIntegral_const]
    simp [mP, Measure.real]
  have hgint : (∫ ω, g (F ω) ∂μ) = ∫ ω in {ω | F ω ∈ B}, φ (F ω) ∂μ := by
    change (∫ ω, {ω | F ω ∈ B}.indicator (fun ω => φ (F ω)) ω ∂μ) = _
    exact integral_indicator (hF hB)
  rw [heq, integral_indicator (show MeasurableSet {ω | F ω ∈ B ∧ Z ω = z} from (hF hB).inter (hz (measurableSet_singleton z))),
    hjint, hgint] at hprod
  exact hprod

private theorem GP029B2b_t18_profile_arm_mean {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Bool) (F : Ω → E)
    (hz : Measurable Z) (hF : Measurable F) (hi : IndepFun Z F μ)
    (B : Set E) (hB : MeasurableSet B) (φ : E → ℝ) (hφ : Measurable φ)
    (z : Bool) (he : 0 < mP μ {ω | Z ω = z}) :
    mCE μ (fun ω => φ (F ω)) {ω | F ω ∈ B ∧ Z ω = z} =
      mCE μ (fun ω => φ (F ω)) {ω | F ω ∈ B} := by
  have hm := GP029B2b_t18_event_factor μ Z F hz hF hi B hB (fun _ => 1) measurable_const z
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hm
  change mP μ {ω | F ω ∈ B ∧ Z ω = z} =
    mP μ {ω | Z ω = z} * mP μ {ω | F ω ∈ B} at hm
  unfold mCE
  rw [GP029B2b_t18_event_factor μ Z F hz hF hi B hB φ hφ z, hm]
  exact mul_div_mul_left _ _ (ne_of_gt he)

private theorem GP029B2b_t18_bit_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : Ω → Bool) (hd : Measurable d)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, bit (d ω) ∂μ) = mP μ {ω | d ω = true ∧ ω ∈ A} := by
  have heq : A.indicator (fun ω => bit (d ω)) =
      {ω | d ω = true ∧ ω ∈ A}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    cases h : d ω <;> by_cases ha : ω ∈ A <;> simp [Set.indicator_apply, bit, h, ha]
  rw [← integral_indicator hA, heq,
    integral_indicator (show MeasurableSet {ω | d ω = true ∧ ω ∈ A} from (hd (measurableSet_singleton true)).inter hA), setIntegral_const]
  simp [mP, Measure.real]

theorem corrected_nested_receipt_model_proof {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hxmeas : Measurable (fun ω => (U ω).x))
    (hd0 : Measurable (fun ω => (U ω).d0)) (hd1 : Measurable (fun ω => (U ω).d1))
    (hz : Measurable Z)
    (hmon : μ {ω | (U ω).defier} = 0)
    (hi : IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1)) μ)
    (hz0 : 0 < mP μ {ω | Z ω = true}) (hz1 : mP μ {ω | Z ω = true} < 1)
    (x : X) (hx : 0 < mP μ {ω | (U ω).x = x})
    (hAC : 0 < mCE μ (fun ω => bit (U ω).d1) {ω | (U ω).x = x}) :
    let a := mCE μ (fun ω => bit (U ω).d1) {ω | (U ω).x = x}
    let b := alwaysAmongAC μ U x
    a*b = mCE μ (fun ω => bit (U ω).d0) {ω | (U ω).x = x} ∧
    a*(1-b) = scoreAt μ U x ∧
    (∀ z, mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | (U ω).x = x ∧ Z ω = z} =
      scoreAt μ U x * bit z + mCE μ (fun ω => bit (U ω).d0) {ω | (U ω).x = x} ∧
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | (U ω).x = x ∧ Z ω = z} =
        nestedReceipt a b z) := by
  classical
  let A : Set Ω := {ω | (U ω).x = x}
  let B : Set Ω := {ω | (U ω).d0 = true ∧ (U ω).d1 = true ∧ (U ω).x = x}
  let C : Set Ω := {ω | (U ω).complier ∧ (U ω).x = x}
  let H : Set Ω := {ω | (U ω).d1 = true ∧ (U ω).x = x}
  have hA : MeasurableSet A := hxmeas (measurableSet_singleton x)
  have hB : MeasurableSet B := (hd0 (measurableSet_singleton true)).inter
    ((hd1 (measurableSet_singleton true)).inter hA)
  have hC : MeasurableSet C := ((hd0 (measurableSet_singleton false)).inter
    (hd1 (measurableSet_singleton true))).inter hA
  have hBC : Disjoint B C := by
    apply Set.disjoint_left.mpr
    intro ω hb hc
    exact Bool.noConfusion (hb.1.symm.trans hc.1.1)
  have hH : H = B ∪ C := by
    ext ω
    cases h0 : (U ω).d0 <;> cases h1 : (U ω).d1 <;>
      simp [H, B, C, PotentialUnit.complier, h0, h1]
  have hsplit : mP μ H = mP μ B + mP μ C := by
    change μ.real H = μ.real B + μ.real C
    rw [hH, measureReal_union hBC hC]
  have hnd : ∀ᵐ ω ∂μ, ¬ (U ω).defier := by
    apply ae_iff.mpr
    simpa only [not_not] using hmon
  have hzero : {ω | (U ω).d0 = true ∧ (U ω).x = x} =ᵐ[μ] B := by
    filter_upwards [hnd] with ω hω
    cases h0 : (U ω).d0 <;> cases h1 : (U ω).d1 <;>
      simp_all [B, PotentialUnit.defier]
  have h0 : mCE μ (fun ω => bit (U ω).d0) A = mP μ B / mP μ A := by
    unfold mCE
    rw [GP029B2b_t18_bit_integral μ _ hd0 A hA]
    rw [show mP μ {ω | (U ω).d0 = true ∧ ω ∈ A} = mP μ B from
      measureReal_congr hzero]
  have h1 : mCE μ (fun ω => bit (U ω).d1) A = mP μ H / mP μ A := by
    exact congrArg (fun r => r / mP μ A) (GP029B2b_t18_bit_integral μ _ hd1 A hA)
  have hpH : 0 < mP μ H := by
    rw [h1] at hAC
    exact (div_pos_iff_of_pos_right hx).mp hAC
  have hab : (mP μ H / mP μ A) * (mP μ B / mP μ H) = mP μ B / mP μ A := by
    field_simp [ne_of_gt hpH, ne_of_gt hx] <;> ring
  have hac : (mP μ H / mP μ A) * (1 - mP μ B / mP μ H) = mP μ C / mP μ A := by
    have hspos : mP μ B + mP μ C ≠ 0 := by
      rw [← hsplit]
      exact ne_of_gt hpH
    rw [hsplit]
    field_simp [ne_of_gt hx, hspos]
    <;> ring
  refine ⟨?_, ?_, ?_⟩
  · change mCE μ (fun ω => bit (U ω).d1) A * (mP μ B / mP μ H) = _
    rw [h1, h0]
    exact hab
  · change mCE μ (fun ω => bit (U ω).d1) A * (1 - mP μ B / mP μ H) = mP μ C / mP μ A
    rw [h1]
    exact hac
  · intro z
    let F : Ω → X × Bool × Bool := fun ω => ((U ω).x, (U ω).d0, (U ω).d1)
    let φ : X × Bool × Bool → ℝ := fun t => bit (if z then t.2.2 else t.2.1)
    have hF : Measurable F := hxmeas.prodMk (hd0.prodMk hd1)
    have hφ : Measurable φ := by
      exact (measurable_of_finite bit).comp (by cases z <;> fun_prop)
    have hm := GP029B2b_t18_profile_arm_mean μ Z F hz hF hi
      {t | t.1 = x} (measurable_fst (measurableSet_singleton x)) φ hφ z
      (GP029B2b_t18_arm_pos μ Z hz hz0 hz1 z)
    have hobs : mCE μ (fun ω => bit ((U ω).receipt (Z ω)))
        {ω | (U ω).x = x ∧ Z ω = z} =
        mCE μ (fun ω => bit ((U ω).receipt z)) A := by
      calc
        _ = mCE μ (fun ω => φ (F ω)) {ω | (U ω).x = x ∧ Z ω = z} := by
          unfold mCE
          congr 1
          apply setIntegral_congr_fun (hA.inter (hz (measurableSet_singleton z)))
          intro ω hω
          have hzω : Z ω = z := hω.2
          simp only [F, φ, PotentialUnit.receipt, hzω]
        _ = _ := hm
    have hlinear : mCE μ (fun ω => bit ((U ω).receipt z)) A =
        scoreAt μ U x * bit z + mCE μ (fun ω => bit (U ω).d0) A := by
      cases z
      · simp [PotentialUnit.receipt, bit]
      · simp only [PotentialUnit.receipt, ite_true, bit, mul_one]
        change mCE μ (fun ω => bit (U ω).d1) A =
          mP μ C / mP μ A + mCE μ (fun ω => bit (U ω).d0) A
        rw [h1, h0, hsplit, add_div] <;> ring
    refine ⟨hobs.trans hlinear, ?_⟩
    rw [hobs, hlinear]
    unfold nestedReceipt
    change scoreAt μ U x * bit z + mCE μ (fun ω => bit (U ω).d0) A =
      mCE μ (fun ω => bit (U ω).d1) A * (1 - mP μ B / mP μ H) * bit z +
      mCE μ (fun ω => bit (U ω).d1) A * (mP μ B / mP μ H)
    rw [h1, hac, hab, h0]
    rfl

/-! ## One-sided ignorability -/

private theorem GP029B2b_t2_ce_congr_set {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (v : Ω → ℝ) {A B : Set Ω} (h : A =ᵐ[μ] B) :
    mCE μ v A = mCE μ v B := by
  unfold mCE
  rw [setIntegral_congr_set h, show mP μ A = mP μ B from measureReal_congr h]

private theorem GP029B2b_t2_partition_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (v : Ω → ℝ) (hv : Integrable v μ)
    (A R N : Set Ω) (hN : MeasurableSet N) (hd : Disjoint R N) (hu : A = R ∪ N)
    (hApos : 0 < mP μ A) (hRpos : 0 < mP μ R) (hNpos : 0 < mP μ N)
    (heq : mCE μ v R = mCE μ v N) : mCE μ v A = mCE μ v R := by
  have hm : mP μ A = mP μ R + mP μ N := by
    change μ.real A = μ.real R + μ.real N
    rw [hu, measureReal_union hd hN]
  have hint : (∫ ω in A, v ω ∂μ) =
      (∫ ω in R, v ω ∂μ) + (∫ ω in N, v ω ∂μ) := by
    rw [hu, setIntegral_union hd hN hv.integrableOn hv.integrableOn]
  have hr : (∫ ω in R, v ω ∂μ) = mCE μ v R * mP μ R := by
    exact (div_mul_cancel₀ _ (ne_of_gt hRpos)).symm
  have hn : (∫ ω in N, v ω ∂μ) = mCE μ v N * mP μ N := by
    exact (div_mul_cancel₀ _ (ne_of_gt hNpos)).symm
  change (∫ ω in A, v ω ∂μ) / mP μ A = mCE μ v R
  rw [hint, hr, hn, ← heq, ← mul_add, ← hm]
  exact mul_div_cancel_right₀ _ (ne_of_gt hApos)

theorem one_sided_ignorability_implication_proof {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) (hside : ∀ᵐ ω ∂μ, (U ω).d0 = false)
    (x : X) (hx : 0 < mP μ {ω | (U ω).x = x}) (hc : 0 < scoreAt μ U x)
    (hi : typicalAt μ U Z x) : latentAt μ U x := by
  classical
  obtain ⟨hxm, hd0, hd1, hy0, hy1, hz, hy0i, hy1i, hind, he0, he1, hnd, hrel⟩ := hiv
  let A : Set Ω := {ω | (U ω).x = x}
  let C : Set Ω := {ω | (U ω).complier ∧ (U ω).x = x}
  let R : Set Ω := {ω | (U ω).receipt (Z ω) = true ∧ (U ω).x = x}
  let N : Set Ω := {ω | (U ω).receipt (Z ω) = false ∧ (U ω).x = x}
  let F : Ω → X × Bool × Bool × ℝ × ℝ :=
    fun ω => ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)
  let B : Set (X × Bool × Bool × ℝ × ℝ) :=
    {t | (t.2.1 = false ∧ t.2.2.1 = true) ∧ t.1 = x}
  have hF : Measurable F := hxm.prodMk (hd0.prodMk (hd1.prodMk (hy0.prodMk hy1)))
  have hB : MeasurableSet B := by
    exact ((measurable_snd.fst (measurableSet_singleton false)).inter
      (measurable_snd.snd.fst (measurableSet_singleton true))).inter
        (measurable_fst (measurableSet_singleton x))
  have hA : MeasurableSet A := hxm (measurableSet_singleton x)
  have hreceipt : Measurable (fun ω => (U ω).receipt (Z ω)) := by
    unfold PotentialUnit.receipt
    exact Measurable.ite (hz (measurableSet_singleton true)) hd1 hd0
  have hRm : MeasurableSet R := (hreceipt (measurableSet_singleton true)).inter hA
  have hNm : MeasurableSet N := (hreceipt (measurableSet_singleton false)).inter hA
  have hRset : R =ᵐ[μ] {ω | F ω ∈ B ∧ Z ω = true} := by
    filter_upwards [hside] with ω hω
    cases h1 : (U ω).d1 <;> cases hz' : Z ω <;>
      simp [R, F, B, PotentialUnit.receipt, PotentialUnit.complier, hω, h1, hz']
  have hq : 0 < mP μ C := by
    exact (div_pos_iff_of_pos_right hx).mp hc
  have hmass : mP μ R = mP μ {ω | Z ω = true} * mP μ C := by
    have hm := GP029B2b_t18_event_factor μ Z F hz hF hind B hB (fun _ => 1) measurable_const true
    simp only [setIntegral_const, smul_eq_mul, mul_one] at hm
    calc
      mP μ R = mP μ {ω | F ω ∈ B ∧ Z ω = true} := measureReal_congr hRset
      _ = _ := hm
  have hRp : 0 < mP μ R := by rw [hmass]; exact mul_pos he0 hq
  have hdisj : Disjoint R N := by
    apply Set.disjoint_left.mpr
    intro ω hr hn
    exact Bool.noConfusion (hr.1.symm.trans hn.1)
  have hunion : A = R ∪ N := by
    ext ω
    cases hd : (U ω).receipt (Z ω) <;> simp [A, R, N, hd]
  have hm : mP μ A = mP μ R + mP μ N := by
    change μ.real A = μ.real R + μ.real N
    rw [hunion, measureReal_union hdisj hNm]
  have hqle : mP μ C ≤ mP μ A := by
    exact measureReal_mono (fun ω hω => hω.2)
  have hNp : 0 < mP μ N := by
    rw [hmass] at hm
    have hsmall : mP μ {ω | Z ω = true} * mP μ C < mP μ A := by
      have hle := mul_le_mul_of_nonneg_left hqle he0.le
      nlinarith [mul_pos (sub_pos.mpr he1) hx]
    linarith
  have hreceiver (φ : X × Bool × Bool × ℝ × ℝ → ℝ) (hφ : Measurable φ) :
      mCE μ (fun ω => φ (F ω)) R = mCE μ (fun ω => φ (F ω)) C := by
    calc
      _ = mCE μ (fun ω => φ (F ω)) {ω | F ω ∈ B ∧ Z ω = true} :=
        GP029B2b_t2_ce_congr_set μ _ hRset
      _ = _ := GP029B2b_t18_profile_arm_mean μ Z F hz hF hind B hB φ hφ true he0
  have hr0 : mCE μ (fun ω => (U ω).y0) R = mCE μ (fun ω => (U ω).y0) C :=
    hreceiver (fun t => t.2.2.2.1) measurable_snd.snd.snd.fst
  have hr1 : mCE μ (fun ω => (U ω).y1) R = mCE μ (fun ω => (U ω).y1) C :=
    hreceiver (fun t => t.2.2.2.2) measurable_snd.snd.snd.snd
  have h0 : mCE μ (fun ω => (U ω).y0) A = mCE μ (fun ω => (U ω).y0) C :=
    (GP029B2b_t2_partition_mean μ _ hy0i A R N hNm hdisj hunion hx hRp hNp hi.1).trans hr0
  have h1 : mCE μ (fun ω => (U ω).y1) A = mCE μ (fun ω => (U ω).y1) C :=
    (GP029B2b_t2_partition_mean μ _ hy1i A R N hNm hdisj hunion hx hRp hNp hi.2).trans hr1
  have hsub (E : Set Ω) :
      mCE μ (fun ω => (U ω).tau) E =
        mCE μ (fun ω => (U ω).y1) E - mCE μ (fun ω => (U ω).y0) E := by
    unfold mCE PotentialUnit.tau
    rw [integral_sub hy1i.integrableOn hy0i.integrableOn, sub_div]
  change mCE μ (fun ω => (U ω).tau) A = mCE μ (fun ω => (U ω).tau) C
  rw [hsub, hsub, h0, h1]

/-! ## Constant-effect Wald identities -/

private theorem GP029B2b_t21_constant_event_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (v : Ω → ℝ) (τ : ℝ)
    (hv : ∀ ω, v ω = τ) (A : Set Ω) (hA : 0 < mP μ A) : mCE μ v A = τ := by
  have heq : v = fun _ => τ := funext hv
  rw [heq, mCE, setIntegral_const]
  change (mP μ A * τ) / mP μ A = τ
  exact mul_div_cancel_left₀ τ (ne_of_gt hA)

private theorem GP029B2b_t21_unconditional_arm_mean {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Bool) (F : Ω → E)
    (hz : Measurable Z) (hF : Measurable F) (hi : IndepFun Z F μ)
    (φ : E → ℝ) (hφ : Measurable φ) (z : Bool)
    (he : 0 < mP μ {ω | Z ω = z}) :
    mCE μ (fun ω => φ (F ω)) {ω | Z ω = z} = ∫ ω, φ (F ω) ∂μ := by
  have h := GP029B2b_t18_profile_arm_mean μ Z F hz hF hi Set.univ MeasurableSet.univ φ hφ z he
  simpa [mCE, mP, Measure.real] using h

private theorem GP029B2b_t21_weighted_bit_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → ℝ) (hw : Integrable w μ)
    (d : Ω → Bool) (hd : Measurable d) : Integrable (fun ω => w ω * bit (d ω)) μ := by
  have heq : (fun ω => w ω * bit (d ω)) = {ω | d ω = true}.indicator w := by
    funext ω
    cases h : d ω <;> simp [bit, h, Set.indicator_apply]
  rw [heq]
  exact hw.indicator (hd (measurableSet_singleton true))

private theorem GP029B2b_t21_first_stage {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) :
    0 < mP μ {ω | (U ω).complier} := by
  obtain ⟨hxm, hd0, hd1, hy0, hy1, hz, hy0i, hy1i, hind, he0, he1, hnd, hrel⟩ := hiv
  let F : Ω → X × Bool × Bool × ℝ × ℝ :=
    fun ω => ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)
  have hF : Measurable F := hxm.prodMk (hd0.prodMk (hd1.prodMk (hy0.prodMk hy1)))
  have harm (z : Bool) :
      mCE μ (fun ω => bit ((U ω).receipt (Z ω))) {ω | Z ω = z} =
        ∫ ω, bit ((U ω).receipt z) ∂μ := by
    let φ : X × Bool × Bool × ℝ × ℝ → ℝ :=
      fun t => bit (if z then t.2.2.1 else t.2.1)
    have hφ : Measurable φ := by
      exact (measurable_of_finite bit).comp (by cases z <;> fun_prop)
    calc
      _ = mCE μ (fun ω => φ (F ω)) {ω | Z ω = z} := by
        unfold mCE
        congr 1
        apply setIntegral_congr_fun (hz (measurableSet_singleton z))
        intro ω hω
        change Z ω = z at hω
        simp [φ, F, PotentialUnit.receipt, hω]
      _ = _ := GP029B2b_t21_unconditional_arm_mean μ Z F hz hF hind φ hφ z
        (GP029B2b_t18_arm_pos μ Z hz he0 he1 z)
  have hCm : MeasurableSet {ω | (U ω).complier} :=
    (hd0 (measurableSet_singleton false)).inter (hd1 (measurableSet_singleton true))
  have hndae : ∀ᵐ ω ∂μ, ¬ (U ω).defier := by
    apply ae_iff.mpr
    simpa only [not_not] using hnd
  have hd0i : Integrable (fun ω => bit ((U ω).receipt false)) μ := by
    simpa [PotentialUnit.receipt] using
      GP029B2b_t21_weighted_bit_integrable μ (fun _ => 1) (integrable_const 1) _ hd0
  have hd1i : Integrable (fun ω => bit ((U ω).receipt true)) μ := by
    simpa [PotentialUnit.receipt] using
      GP029B2b_t21_weighted_bit_integrable μ (fun _ => 1) (integrable_const 1) _ hd1
  have hint : (∫ ω, bit ((U ω).receipt true) ∂μ) -
      (∫ ω, bit ((U ω).receipt false) ∂μ) = mP μ {ω | (U ω).complier} := by
    rw [← integral_sub hd1i hd0i]
    calc
      _ = ∫ ω, {ω | (U ω).complier}.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hndae] with ω hω
        exact (unit_itt_identities (U ω) hω).1
      _ = _ := by
        rw [integral_indicator hCm, setIntegral_const]
        simp [mP, Measure.real]
  rw [harm true, harm false, hint] at hrel
  exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hrel)

/-- Bounded positive latent weights preserve a constant treatment effect.
The lower bound one suffices for both weights used in the final theorem. -/
private theorem GP029B2b_t21_constant_weighted_wald {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hiv : IVAssumptions μ U Z) (τ : ℝ) (hτ : ∀ ω, (U ω).tau = τ)
    (ψ : X × Bool × Bool × ℝ × ℝ → ℝ) (hψ : Measurable ψ)
    (K : ℝ)
    (hb : ∀ᵐ ω ∂μ,
      1 ≤ ψ ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1) ∧
      ‖ψ ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)‖ ≤ K) :
    mWald μ U Z
      (fun ω => ψ ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)) = τ := by
  have hCp := GP029B2b_t21_first_stage μ U Z hiv
  obtain ⟨hxm, hd0, hd1, hy0, hy1, hz, hy0i, hy1i, hind, he0, he1, hnd, hrel⟩ := hiv
  let F : Ω → X × Bool × Bool × ℝ × ℝ :=
    fun ω => ((U ω).x, (U ω).d0, (U ω).d1, (U ω).y0, (U ω).y1)
  let w : Ω → ℝ := fun ω => ψ (F ω)
  let J : ℝ := ∫ ω, w ω ∂μ
  let V : ℝ := ∫ ω, w ω * (U ω).y0 ∂μ
  let H : Bool → ℝ := fun z => ∫ ω, w ω * bit ((U ω).receipt z) ∂μ
  have hF : Measurable F := hxm.prodMk (hd0.prodMk (hd1.prodMk (hy0.prodMk hy1)))
  have hwm : Measurable w := hψ.comp hF
  have hwi : Integrable w μ :=
    (integrable_const K).mono' hwm.aestronglyMeasurable (hb.mono fun _ h => h.2)
  have hwy0 : Integrable (fun ω => w ω * (U ω).y0) μ :=
    hy0i.bdd_mul hwm.aestronglyMeasurable (hb.mono fun _ h => h.2)
  have hdmi (z : Bool) : Measurable (fun ω => (U ω).receipt z) := by
    cases z
    · simpa [PotentialUnit.receipt] using hd0
    · simpa [PotentialUnit.receipt] using hd1
  have hDi (z : Bool) : Integrable (fun ω => w ω * bit ((U ω).receipt z)) μ :=
    GP029B2b_t21_weighted_bit_integrable μ w hwi _ (hdmi z)
  have hJ : 0 < J := by
    have hh := integral_mono_ae (integrable_const (1 : ℝ)) hwi (hb.mono fun _ h => h.1)
    have hone : (∫ _ : Ω, (1 : ℝ) ∂μ) = 1 := by simp
    rw [hone] at hh
    exact lt_of_lt_of_le zero_lt_one hh
  have hCm : MeasurableSet {ω | (U ω).complier} :=
    (hd0 (measurableSet_singleton false)).inter (hd1 (measurableSet_singleton true))
  have hCi : Integrable ({ω | (U ω).complier}.indicator w) μ := hwi.indicator hCm
  have hndae : ∀ᵐ ω ∂μ, ¬ (U ω).defier := by
    apply ae_iff.mpr
    simpa only [not_not] using hnd
  have hdiff : H true - H false = ∫ ω, {ω | (U ω).complier}.indicator w ω ∂μ := by
    dsimp only [H]
    rw [← integral_sub (hDi true) (hDi false)]
    apply integral_congr_ae
    filter_upwards [hndae] with ω hω
    have hu := (unit_itt_identities (U ω) hω).1
    rw [← mul_sub, hu]
    by_cases hc : (U ω).complier <;> simp [Set.indicator_apply, hc]
  have hH : 0 < H true - H false := by
    have hmono := integral_mono_ae ((integrable_const (1 : ℝ)).indicator hCm) hCi
      (hb.mono fun ω h => by
        by_cases hc : (U ω).complier
        · simpa [Set.indicator_apply, hc, w, F] using h.1
        · simp [Set.indicator_apply, hc])
    have hconst : (∫ ω, {ω | (U ω).complier}.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
        mP μ {ω | (U ω).complier} := by
      rw [integral_indicator hCm, setIntegral_const]
      simp [mP, Measure.real]
    rw [hconst] at hmono
    rw [hdiff]
    exact lt_of_lt_of_le hCp hmono
  have hweight (z : Bool) : mCE μ w {ω | Z ω = z} = J :=
    GP029B2b_t21_unconditional_arm_mean μ Z F hz hF hind ψ hψ z (GP029B2b_t18_arm_pos μ Z hz he0 he1 z)
  have hreceipt (z : Bool) :
      mCE μ (fun ω => w ω * bit ((U ω).receipt (Z ω))) {ω | Z ω = z} = H z := by
    let φ : X × Bool × Bool × ℝ × ℝ → ℝ :=
      fun t => ψ t * bit (if z then t.2.2.1 else t.2.1)
    have hφ : Measurable φ := hψ.mul (by
      exact (measurable_of_finite bit).comp (by cases z <;> fun_prop))
    calc
      _ = mCE μ (fun ω => φ (F ω)) {ω | Z ω = z} := by
        unfold mCE
        congr 1
        apply setIntegral_congr_fun (hz (measurableSet_singleton z))
        intro ω hω
        change Z ω = z at hω
        simp [φ, w, F, PotentialUnit.receipt, hω]
      _ = _ := GP029B2b_t21_unconditional_arm_mean μ Z F hz hF hind φ hφ z
        (GP029B2b_t18_arm_pos μ Z hz he0 he1 z)
  have houtcome (z : Bool) :
      mCE μ (fun ω => w ω * (U ω).outcome (Z ω)) {ω | Z ω = z} = V + τ * H z := by
    let φ : X × Bool × Bool × ℝ × ℝ → ℝ :=
      fun t => ψ t * (t.2.2.2.1 + τ * bit (if z then t.2.2.1 else t.2.1))
    have hφ : Measurable φ := hψ.mul (measurable_snd.snd.snd.fst.add
      (measurable_const.mul ((measurable_of_finite bit).comp (by cases z <;> fun_prop))))
    have hpoint (ω : Ω) :
        w ω * (U ω).outcome z = w ω * (U ω).y0 + τ * (w ω * bit ((U ω).receipt z)) := by
      have ht := hτ ω
      unfold PotentialUnit.tau at ht
      have hy : (U ω).y1 = (U ω).y0 + τ := by linarith
      unfold PotentialUnit.outcome
      cases hd : (U ω).receipt z <;> simp [bit, hd, hy] <;> ring
    calc
      _ = mCE μ (fun ω => φ (F ω)) {ω | Z ω = z} := by
        unfold mCE
        congr 1
        apply setIntegral_congr_fun (hz (measurableSet_singleton z))
        intro ω hω
        change Z ω = z at hω
        change w ω * (U ω).outcome (Z ω) = φ (F ω)
        rw [hω, hpoint]
        dsimp [φ, F, w, PotentialUnit.receipt]
        ring
      _ = ∫ ω, φ (F ω) ∂μ := GP029B2b_t21_unconditional_arm_mean μ Z F hz hF hind φ hφ z
        (GP029B2b_t18_arm_pos μ Z hz he0 he1 z)
      _ = _ := by
        have heq : (fun ω => φ (F ω)) =
            fun ω => w ω * (U ω).y0 + τ * (w ω * bit ((U ω).receipt z)) := by
          funext ω
          dsimp [φ, F, w, PotentialUnit.receipt]
          ring
        rw [heq, integral_add hwy0 ((hDi z).const_mul τ), integral_const_mul]
  change mWald μ U Z w = τ
  unfold mWald mArm
  simp only [hweight, hreceipt, houtcome]
  have hden : H true / J - H false / J ≠ 0 := by
    rw [← sub_div]
    exact div_ne_zero (ne_of_gt hH) (ne_of_gt hJ)
  apply (div_eq_iff hden).mpr
  ring

theorem constant_effect_population_limits_proof {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool) (hiv : IVAssumptions μ U Z)
    (c m : X → ℝ) (hv : ScoreVersions μ U c m)
    (ε : ℝ) (he : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε < c (U ω).x ∧ c (U ω).x ≤ 1)
    (τ : ℝ) (hτ : ∀ ω, (U ω).tau = τ) :
    (∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x →
      mCE μ (fun ω => (U ω).tau) {ω | (U ω).x = x} = τ ∧ complierAt μ U x = τ) ∧
    A1Versions μ U m ∧ mWald μ U Z (fun _ => 1) = τ ∧
      mWald μ U Z (fun ω => 1/c (U ω).x) = τ := by
  classical
  have hprofile : ∀ x, 0 < mP μ {ω | (U ω).x = x} → 0 < scoreAt μ U x →
      mCE μ (fun ω => (U ω).tau) {ω | (U ω).x = x} = τ ∧ complierAt μ U x = τ := by
    intro x hx hc
    have hC : 0 < mP μ {ω | (U ω).complier ∧ (U ω).x = x} :=
      (div_pos_iff_of_pos_right hx).mp hc
    exact ⟨GP029B2b_t21_constant_event_mean μ _ τ hτ _ hx,
      GP029B2b_t21_constant_event_mean μ _ τ hτ _ hC⟩
  have hscale : (fun ω => if (U ω).complier then (U ω).tau else 0) =
      τ • (fun ω => if (U ω).complier then (1 : ℝ) else 0) := by
    funext ω
    by_cases hc : (U ω).complier <;> simp [hc, hτ ω]
  have hcond := condExp_smul (μ := μ) τ
    (fun ω => if (U ω).complier then (1 : ℝ) else 0) (covariateSigma U)
  rw [← hscale] at hcond
  have hmconst : (fun ω => m (U ω).x) =ᵐ[μ] (fun _ => τ) := by
    filter_upwards [hv.2.2.1, hv.2.2.2, hcond, hpos] with ω hs hm ht hp
    have hc : 0 < c (U ω).x := he.trans hp.1
    have heq : c (U ω).x * m (U ω).x = c (U ω).x * τ := by
      rw [hm, ht]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hs]
      ring
    exact mul_left_cancel₀ (ne_of_gt hc) heq
  have hA1 : A1Versions μ U m := by
    have htfun : (fun ω => (U ω).tau) = (fun _ => τ) := funext hτ
    change (fun ω => m (U ω).x) =ᵐ[μ] condExp (covariateSigma U) μ (fun ω => (U ω).tau)
    rw [htfun, condExp_const (μ := μ) (show covariateSigma U ≤ ‹MeasurableSpace Ω› from hiv.1.comap_le) τ]
    exact hmconst
  refine ⟨hprofile, hA1, ?_, ?_⟩
  · exact GP029B2b_t21_constant_weighted_wald μ U Z hiv τ hτ (fun _ => 1) measurable_const 1
      (Filter.Eventually.of_forall (fun _ => by simp))
  · have hψ : Measurable (fun t : X × Bool × Bool × ℝ × ℝ => 1 / c t.1) :=
      measurable_const.div (hv.1.comp measurable_fst)
    apply GP029B2b_t21_constant_weighted_wald μ U Z hiv τ hτ
      (fun t => 1 / c t.1) hψ (1 / ε)
    filter_upwards [hpos] with ω hp
    have hc : 0 < c (U ω).x := he.trans hp.1
    constructor
    · exact (le_div_iff₀ hc).mpr (by simpa using hp.2)
    · rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hc)]
      exact (one_div_le_one_div_of_le he hp.1.le)

end

end AronowAudit.P029.Wave1
