import SAP.P018a.WH.W1.Leaves
import AronowAudit.P018.Wave1.Gap.GP0181B1
import AronowAudit.P018.Wave1.Gap.GLP0181B3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018a.WH.W1.P.T11_L5

open Finset Matrix MeasureTheory ProbabilityTheory
open AronowAudit.P018
open AronowAudit.P018.Wave1
open scoped BigOperators Matrix.Norms.Elementwise ENNReal

abbrev U := ℝ × Bool

def mono (n m : ℕ) (u : U) : ℝ := u.1^n * signValue u.2^m

local instance : IsProbabilityMeasure fairLaw := AronowAudit.P018.Wave1.printed_fair_probability
local instance : IsProbabilityMeasure uniformUnitLaw :=
  AronowAudit.P018.instIsProbabilityMeasureRealUniformUnitLaw
local instance : IsProbabilityMeasure (uniformUnitLaw.prod fairLaw) := inferInstance

lemma sign_moment_zero : (∫ b : Bool, signValue b^0 ∂fairLaw) = 1 := by
  rw [integral_fintype (printed_finite_integrable fairLaw (fun b : Bool => signValue b^0))]
  norm_num [fairLaw, Measure.real, PMF.toMeasure_uniformOfFintype_apply, signValue,
    Fintype.sum_bool, Fintype.card_bool, probReal_univ]

lemma sign_moment_one : (∫ b : Bool, signValue b ∂fairLaw) = 0 := printed_fair_integral

lemma sign_moment_two : (∫ b : Bool, signValue b^2 ∂fairLaw) = 1 := by
  rw [integral_fintype (printed_finite_integrable fairLaw (fun b : Bool => signValue b^2))]
  norm_num [fairLaw, Measure.real, PMF.toMeasure_uniformOfFintype_apply, signValue,
    Fintype.sum_bool, Fintype.card_bool, probReal_univ]

lemma unit_mono_integrable (n m : ℕ) : Integrable (mono n m) (uniformUnitLaw.prod fairLaw) := by
  exact ((uniform_unit_power_L2 n).integrable one_le_two).mul_prod
    (printed_finite_integrable fairLaw fun b : Bool => signValue b^m)

lemma unit_mono_integral (n m : ℕ) :
    (∫ u : U, mono n m u ∂uniformUnitLaw.prod fairLaw) =
      (∫ z : ℝ, z^n ∂uniformUnitLaw) * (∫ b : Bool, signValue b^m ∂fairLaw) := by
  change (∫ u : ℝ × Bool, u.1^n * signValue u.2^m ∂uniformUnitLaw.prod fairLaw) = _
  exact integral_prod_mul (fun z : ℝ => z^n) (fun b : Bool => signValue b^m)

lemma pair_mono_integrable (n m p q : ℕ) :
    Integrable (fun uv : U × U => mono n m uv.1 * mono p q uv.2)
      ((uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) :=
  (unit_mono_integrable n m).mul_prod (unit_mono_integrable p q)

lemma pair_mono_integral (n m p q : ℕ) :
    (∫ uv : U × U, mono n m uv.1 * mono p q uv.2
      ∂(uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) =
      ((∫ z : ℝ, z^n ∂uniformUnitLaw) * (∫ b : Bool, signValue b^m ∂fairLaw)) *
      ((∫ z : ℝ, z^p ∂uniformUnitLaw) * (∫ b : Bool, signValue b^q ∂fairLaw)) := by
  rw [integral_prod_mul, unit_mono_integral, unit_mono_integral]

lemma sign_moment_small (m : ℕ) (hm : m ≤ 2) :
    (∫ b : Bool, signValue b^m ∂fairLaw) =
      (if m = 0 then 1 else if m = 1 then 0 else 1) := by
  interval_cases m
  · simpa using sign_moment_zero
  · simpa using sign_moment_one
  · simpa using sign_moment_two

lemma unit_z_moment_small (n : ℕ) (hn : n ≤ 2) :
    (∫ z : ℝ, z^n ∂uniformUnitLaw) =
      (if n = 0 then 1 else if n = 1 then 0 else 1/3) := by
  interval_cases n
  · simp [integral_const, probReal_univ]
  · change (∫ z : ℝ, z^1 ∂AronowAudit.P018.uniformUnitLaw) = 0
    simpa using uniform_unit_moments.1
  · change (∫ z : ℝ, z^2 ∂AronowAudit.P018.uniformUnitLaw) = 1/3
    simpa using uniform_unit_moments.2.1

lemma mono_mean (n m : ℕ) (hn : n ≤ 2) (hm : m ≤ 2) :
    (∫ u : U, mono n m u ∂uniformUnitLaw.prod fairLaw) =
      (if n = 0 then 1 else if n = 1 then 0 else if n = 2 then 1/3 else 0) *
      (if m = 0 then 1 else if m = 1 then 0 else if m = 2 then 1 else 0) := by
  rw [unit_mono_integral, unit_z_moment_small n hn, sign_moment_small m hm]
  interval_cases n <;> interval_cases m <;> norm_num

lemma pair_mean (n m p q : ℕ) (hn : n ≤ 2) (hm : m ≤ 2)
    (hp : p ≤ 2) (hq : q ≤ 2) :
    (∫ uv : U × U, mono n m uv.1 * mono p q uv.2
      ∂(uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) =
      (if n = 0 then 1 else if n = 1 then 0 else if n = 2 then 1/3 else 0) *
      (if m = 0 then 1 else if m = 1 then 0 else if m = 2 then 1 else 0) *
      ((if p = 0 then 1 else if p = 1 then 0 else if p = 2 then 1/3 else 0) *
       (if q = 0 then 1 else if q = 1 then 0 else if q = 2 then 1 else 0)) := by
  rw [pair_mono_integral]
  have h₁ := mono_mean n m hn hm
  have h₂ := mono_mean p q hp hq
  rw [unit_mono_integral] at h₁ h₂
  rw [h₁, h₂]

lemma pair_const_integrable :
    Integrable (fun _ : U × U => (1 : ℝ))
      ((uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) :=
  (integrable_const 1)

lemma pair_sum_integral {ι : Type*} [Fintype ι] (f : ι → U × U → ℝ)
    (hf : ∀ i, Integrable (f i) ((uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw))) :
    (∫ uv, ∑ i, f i uv ∂(uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) =
      ∑ i, ∫ uv, f i uv ∂(uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw) := by
  rw [integral_finsetSum _ (fun i hi => hf i)]

lemma inner_s2 (z : ℝ) (b : Bool) :
    (∫ v : U, (signValue b + signValue v.2)^2 ∂uniformUnitLaw.prod fairLaw) = 2 := by
  let fs : Fin 3 → U → ℝ := ![fun _ => 1, fun v => 2*signValue b*mono 0 1 v, fun _ => 1]
  have he : (fun v : U => (signValue b + signValue v.2)^2) = fun v => ∑ i : Fin 3, fs i v := by
    funext v
    rcases v with ⟨w,c⟩
    cases b <;> cases c <;> norm_num [fs, Fin.sum_univ_succ, mono, signValue] <;> ring
  have hi : ∀ i : Fin 3, Integrable (fs i) (uniformUnitLaw.prod fairLaw) := by
    intro i; fin_cases i
    · exact integrable_const _
    · simpa [fs] using (unit_mono_integrable 0 1).const_mul (2*signValue b)
    · exact integrable_const _
  calc
    _ = ∫ v : U, (∑ i : Fin 3, fs i v) ∂uniformUnitLaw.prod fairLaw := by rw [he]
    _ = ∑ i : Fin 3, ∫ v : U, fs i v ∂uniformUnitLaw.prod fairLaw :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = 2 := by
      simp [fs, Fin.sum_univ_succ, integral_const, probReal_univ,
        integral_const_mul, mono_mean, sign_moment_small]
      <;> norm_num

lemma inner_s2z (z : ℝ) (b : Bool) :
    (∫ v : U, (signValue b + signValue v.2)^2 * (z+v.1)
      ∂uniformUnitLaw.prod fairLaw) = 2*z := by
  let fs : Fin 4 → U → ℝ := ![fun _ => 2*z, fun v => 2*mono 1 0 v,
    fun v => (2*signValue b*z)*mono 0 1 v,
    fun v => (2*signValue b)*mono 1 1 v]
  have he : (fun v : U => (signValue b + signValue v.2)^2 * (z+v.1)) =
      fun v => ∑ i : Fin 4, fs i v := by
    funext v
    rcases v with ⟨w,c⟩
    cases b <;> cases c <;> norm_num [fs, Fin.sum_univ_succ, mono, signValue] <;> ring
  have hi : ∀ i : Fin 4, Integrable (fs i) (uniformUnitLaw.prod fairLaw) := by
    intro i; fin_cases i
    · exact integrable_const _
    · simpa [fs, mono] using (unit_mono_integrable 1 0).const_mul (2 : ℝ)
    · simpa [fs] using (unit_mono_integrable 0 1).const_mul (2*signValue b*z)
    · simpa [fs] using (unit_mono_integrable 1 1).const_mul (2*signValue b)
  calc
    _ = ∫ v : U, (∑ i : Fin 4, fs i v) ∂uniformUnitLaw.prod fairLaw := by rw [he]
    _ = ∑ i : Fin 4, ∫ v : U, fs i v ∂uniformUnitLaw.prod fairLaw :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = 2*z := by
      simp [fs, Fin.sum_univ_succ, integral_const, probReal_univ,
        integral_const_mul, mono_mean]

lemma inner_s2z2 (z : ℝ) (b : Bool) :
    (∫ v : U, (signValue b + signValue v.2)^2 * (z+v.1)^2
      ∂uniformUnitLaw.prod fairLaw) = 2*z^2+2/3 := by
  let fs : Fin 6 → U → ℝ := ![fun _ => 2*z^2, fun v => (4*z)*mono 1 0 v,
    fun v => 2*mono 2 0 v, fun v => (2*signValue b*z^2)*mono 0 1 v,
    fun v => (4*signValue b*z)*mono 1 1 v,
    fun v => (2*signValue b)*mono 2 1 v]
  have he : (fun v : U => (signValue b + signValue v.2)^2 * (z+v.1)^2) =
      fun v => ∑ i : Fin 6, fs i v := by
    funext v
    rcases v with ⟨w,c⟩
    cases b <;> cases c <;> norm_num [fs, Fin.sum_univ_succ, mono, signValue] <;> ring
  have hi : ∀ i : Fin 6, Integrable (fs i) (uniformUnitLaw.prod fairLaw) := by
    intro i; fin_cases i
    · exact integrable_const _
    · simpa [fs, mono] using (unit_mono_integrable 1 0).const_mul (4*z)
    · simpa [fs, mono] using (unit_mono_integrable 2 0).const_mul (2 : ℝ)
    · simpa [fs, mono] using (unit_mono_integrable 0 1).const_mul (2*signValue b*z^2)
    · simpa [fs, mono] using (unit_mono_integrable 1 1).const_mul (4*signValue b*z)
    · simpa [fs, mono] using (unit_mono_integrable 2 1).const_mul (2*signValue b)
  calc
    _ = ∫ v : U, (∑ i : Fin 6, fs i v) ∂uniformUnitLaw.prod fairLaw := by rw [he]
    _ = ∑ i : Fin 6, ∫ v : U, fs i v ∂uniformUnitLaw.prod fairLaw :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = 2*z^2+2/3 := by
      simp [fs, Fin.sum_univ_succ, integral_const, probReal_univ,
        integral_const_mul, mono_mean]
      <;> norm_num

lemma projection_formula (hBeta : populationBeta W1MixedKernel = 0) (z : ℝ) (b : Bool) :
    projection W1MixedKernel (z,b) = ![signValue b, z * signValue b] := by
  have h0 : (∫ v : U, signValue b + signValue v.2 ∂uniformUnitLaw.prod fairLaw) = signValue b := by
    have hs : Integrable (fun v : U => signValue v.2) (uniformUnitLaw.prod fairLaw) := by
      convert unit_mono_integrable 0 1 using 1
      funext v
      simp [mono]
    have hm : (∫ v : U, signValue v.2 ∂uniformUnitLaw.prod fairLaw) = 0 := by
      simpa [mono] using mono_mean 0 1 (by norm_num) (by norm_num)
    rw [integral_add (integrable_const _) hs]
    simp [integral_const, probReal_univ, hm]
  have h1 : (∫ v : U, (z+v.1)*(signValue b+signValue v.2)
        ∂uniformUnitLaw.prod fairLaw) = z*signValue b := by
    have he : ∀ v : U,
        (z+v.1)*(signValue b+signValue v.2) =
          (z*signValue b) + (z*signValue v.2) + (v.1*signValue b) + (v.1*signValue v.2) := by
      intro v; ring
    have hi0 : Integrable (fun _ : U => (z*signValue b : ℝ)) (uniformUnitLaw.prod fairLaw) := integrable_const _
    have hi1 : Integrable (fun v : U => z*signValue v.2) (uniformUnitLaw.prod fairLaw) := by
      simpa [mono] using (unit_mono_integrable 0 1).const_mul z
    have hi2 : Integrable (fun v : U => v.1*signValue b) (uniformUnitLaw.prod fairLaw) := by
      convert (unit_mono_integrable 1 0).const_mul (signValue b) using 1 <;>
        funext v <;> simp [mono, mul_comm]
    have hi3 : Integrable (fun v : U => v.1*signValue v.2) (uniformUnitLaw.prod fairLaw) := by
      convert unit_mono_integrable 1 1 using 1
      funext v
      simp [mono]
    have hm01 : (∫ v : U, signValue v.2 ∂uniformUnitLaw.prod fairLaw) = 0 := by
      simpa [mono] using mono_mean 0 1 (by norm_num) (by norm_num)
    have hm10 : (∫ v : U, v.1 ∂uniformUnitLaw.prod fairLaw) = 0 := by
      simpa [mono] using mono_mean 1 0 (by norm_num) (by norm_num)
    have hm11 : (∫ v : U, v.1*signValue v.2 ∂uniformUnitLaw.prod fairLaw) = 0 := by
      simpa [mono] using mono_mean 1 1 (by norm_num) (by norm_num)
    let fs : Fin 4 → U → ℝ := ![fun _ => z*signValue b,
      fun v => z*signValue v.2, fun v => v.1*signValue b,
      fun v => v.1*signValue v.2]
    have hsum : (fun v : U => (z+v.1)*(signValue b+signValue v.2)) =
        fun v => ∑ i : Fin 4, fs i v := by
      funext v
      simp [fs, Fin.sum_univ_succ]
      ring
    have hfi : ∀ i : Fin 4, Integrable (fs i) (uniformUnitLaw.prod fairLaw) := by
      intro i
      fin_cases i
      · exact hi0
      · exact hi1
      · exact hi2
      · exact hi3
    calc
      (∫ v : U, (z+v.1)*(signValue b+signValue v.2) ∂uniformUnitLaw.prod fairLaw) =
          ∫ v : U, (∑ i : Fin 4, fs i v) ∂uniformUnitLaw.prod fairLaw := by
            rw [hsum]
      _ = ∑ i : Fin 4, ∫ v : U, fs i v ∂uniformUnitLaw.prod fairLaw :=
        integral_finsetSum _ (fun i hi => hfi i)
      _ = z*signValue b := by
        simp [fs, Fin.sum_univ_succ, integral_const, probReal_univ,
          integral_const_mul, integral_mul_const, hm01, hm10, hm11]
  have hres (u v : U) : populationResidual W1MixedKernel u v =
      signValue u.2 + signValue v.2 := by
    change W1MixedKernel.Y u v - dot (W1MixedKernel.X u v)
      (populationBeta W1MixedKernel) = _
    rw [hBeta]
    simp [W1MixedKernel, dot]
  have hs0 (v : U) : populationScore W1MixedKernel (z,b) v 0 =
      signValue b + signValue v.2 := by
    change score (W1MixedKernel.X (z,b) v)
      (populationResidual W1MixedKernel (z,b) v) 0 = _
    rw [hres]
    simp [score, W1MixedKernel]
  have hs1 (v : U) : populationScore W1MixedKernel (z,b) v 1 =
      (z+v.1)*(signValue b + signValue v.2) := by
    change score (W1MixedKernel.X (z,b) v)
      (populationResidual W1MixedKernel (z,b) v) 1 = _
    rw [hres]
    simp [score, W1MixedKernel]
    ring
  ext i
  fin_cases i
  · change (∫ v : U, populationScore W1MixedKernel (z,b) v 0
      ∂uniformUnitLaw.prod fairLaw) = signValue b
    rw [integral_congr_ae (Filter.Eventually.of_forall hs0)]
    exact h0
  · change (∫ v : U, populationScore W1MixedKernel (z,b) v 1
      ∂uniformUnitLaw.prod fairLaw) = z*signValue b
    rw [integral_congr_ae (Filter.Eventually.of_forall hs1)]
    exact h1

end SAP.P018a.WH.W1.P.T11_L5

namespace SAP.P018a.WH.W1
open SAP.P018a.WH.W1.P.T11_L5
open MeasureTheory

theorem T11_L5_proof : SAP.P018a.WH.W1.T11_L5 := by
  intro hL4
  rcases hL4 with ⟨hStanding, hBeta, _, _, _⟩
  letI : IsProbabilityMeasure W1MixedKernel.μ := hStanding.1
  letI : IsProbabilityMeasure fairLaw := AronowAudit.P018.Wave1.printed_fair_probability
  letI : IsProbabilityMeasure uniformUnitLaw :=
    AronowAudit.P018.instIsProbabilityMeasureRealUniformUnitLaw
  have hres (u v : U) : populationResidual W1MixedKernel u v =
      signValue u.2 + signValue v.2 := by
    change W1MixedKernel.Y u v - dot (W1MixedKernel.X u v)
      (populationBeta W1MixedKernel) = _
    rw [hBeta]
    simp [W1MixedKernel, dot]
  have hscore (u v : U) : populationScore W1MixedKernel u v =
      ![signValue u.2 + signValue v.2,
        (u.1+v.1)*(signValue u.2+signValue v.2)] := by
    change score (W1MixedKernel.X u v) (populationResidual W1MixedKernel u v) = _
    rw [hres]
    simp [score, W1MixedKernel] <;> ring
  have hs0 (u v : U) : populationScore W1MixedKernel u v 0 =
      signValue u.2 + signValue v.2 := by
    have h := congrFun (hscore u v) 0
    simpa using h
  have hs1 (u v : U) : populationScore W1MixedKernel u v 1 =
      (u.1+v.1)*(signValue u.2+signValue v.2) := by
    have h := congrFun (hscore u v) 1
    simpa using h
  have hScoreProd (a b : Fin 2) :
      MeasureTheory.Integrable (fun uv : U × U => populationScore W1MixedKernel uv.1 uv.2 a *
        populationScore W1MixedKernel uv.1 uv.2 b)
        ((uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) := by
    have hK : AronowAudit.P018.Standing (SAP.P018a.Bridge.toKernel W1MixedKernel) :=
      (SAP.P018a.Bridge.kernel_assumptions_agree W1MixedKernel).mp hStanding
    exact (AronowAudit.P018.Wave1.vc3_pair_score_lp
      (SAP.P018a.Bridge.toKernel W1MixedKernel) hK a 2).integrable_mul
      (AronowAudit.P018.Wave1.vc3_pair_score_lp
        (SAP.P018a.Bridge.toKernel W1MixedKernel) hK b 2)
  have hH : scoreH W1MixedKernel = !![2,0;0,4/3] := by
    ext a b
    fin_cases a <;> fin_cases b
    · change (∫ uv : U × U, populationScore W1MixedKernel uv.1 uv.2 0 *
        populationScore W1MixedKernel uv.1 uv.2 0
        ∂(uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) = 2
      have he : (fun uv : U × U => populationScore W1MixedKernel uv.1 uv.2 0 *
          populationScore W1MixedKernel uv.1 uv.2 0) =
          fun uv => (signValue uv.1.2+signValue uv.2.2)^2 := by
        funext uv; simp only [hs0]; ring
      have hi := (hScoreProd 0 0).congr
        (Filter.Eventually.of_forall fun uv => congrFun he uv)
      rw [integral_congr_ae (Filter.Eventually.of_forall fun uv => congrFun he uv), integral_prod _ hi]
      calc
        (∫ u : U, ∫ v : U, (signValue u.2+signValue v.2)^2 ∂uniformUnitLaw.prod fairLaw
          ∂uniformUnitLaw.prod fairLaw) = ∫ u : U, (2:ℝ) ∂uniformUnitLaw.prod fairLaw := by
            congr 1; funext u; exact inner_s2 u.1 u.2
        _ = 2 := by simp [integral_const, probReal_univ]
    · change (∫ uv : U × U, populationScore W1MixedKernel uv.1 uv.2 0 *
        populationScore W1MixedKernel uv.1 uv.2 1
        ∂(uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) = 0
      have he : (fun uv : U × U => populationScore W1MixedKernel uv.1 uv.2 0 *
          populationScore W1MixedKernel uv.1 uv.2 1) =
          fun uv => (signValue uv.1.2+signValue uv.2.2)^2*(uv.1.1+uv.2.1) := by
        funext uv; simp only [hs0, hs1]; ring
      have hi := (hScoreProd 0 1).congr
        (Filter.Eventually.of_forall fun uv => congrFun he uv)
      rw [integral_congr_ae (Filter.Eventually.of_forall fun uv => congrFun he uv), integral_prod _ hi]
      have hz : (∫ u : U, u.1 ∂uniformUnitLaw.prod fairLaw) = 0 := by
        simpa [mono] using mono_mean 1 0 (by norm_num) (by norm_num)
      calc
        (∫ u : U, ∫ v : U, (signValue u.2+signValue v.2)^2*(u.1+v.1)
          ∂uniformUnitLaw.prod fairLaw ∂uniformUnitLaw.prod fairLaw) =
            ∫ u : U, 2*u.1 ∂uniformUnitLaw.prod fairLaw := by
              congr 1; funext u; exact inner_s2z u.1 u.2
        _ = 0 := by rw [integral_const_mul, hz]; ring
    · change (∫ uv : U × U, populationScore W1MixedKernel uv.1 uv.2 1 *
        populationScore W1MixedKernel uv.1 uv.2 0
        ∂(uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) = 0
      have he : (fun uv : U × U => populationScore W1MixedKernel uv.1 uv.2 1 *
          populationScore W1MixedKernel uv.1 uv.2 0) =
          fun uv => (signValue uv.1.2+signValue uv.2.2)^2*(uv.1.1+uv.2.1) := by
        funext uv; simp only [hs0, hs1]; ring
      have hi := (hScoreProd 1 0).congr
        (Filter.Eventually.of_forall fun uv => congrFun he uv)
      rw [integral_congr_ae (Filter.Eventually.of_forall fun uv => congrFun he uv), integral_prod _ hi]
      have hz : (∫ u : U, u.1 ∂uniformUnitLaw.prod fairLaw) = 0 := by
        simpa [mono] using mono_mean 1 0 (by norm_num) (by norm_num)
      calc
        (∫ u : U, ∫ v : U, (signValue u.2+signValue v.2)^2*(u.1+v.1)
          ∂uniformUnitLaw.prod fairLaw ∂uniformUnitLaw.prod fairLaw) =
            ∫ u : U, 2*u.1 ∂uniformUnitLaw.prod fairLaw := by
              congr 1; funext u; exact inner_s2z u.1 u.2
        _ = 0 := by rw [integral_const_mul, hz]; ring
    · change (∫ uv : U × U, populationScore W1MixedKernel uv.1 uv.2 1 *
        populationScore W1MixedKernel uv.1 uv.2 1
        ∂(uniformUnitLaw.prod fairLaw).prod (uniformUnitLaw.prod fairLaw)) = 4/3
      have he : (fun uv : U × U => populationScore W1MixedKernel uv.1 uv.2 1 *
          populationScore W1MixedKernel uv.1 uv.2 1) =
          fun uv => (signValue uv.1.2+signValue uv.2.2)^2*(uv.1.1+uv.2.1)^2 := by
        funext uv; simp only [hs1]; ring
      have hi := (hScoreProd 1 1).congr
        (Filter.Eventually.of_forall fun uv => congrFun he uv)
      rw [integral_congr_ae (Filter.Eventually.of_forall fun uv => congrFun he uv), integral_prod _ hi]
      have hz2 : (∫ u : U, u.1^2 ∂uniformUnitLaw.prod fairLaw) = 1/3 := by
        simpa [mono] using mono_mean 2 0 (by norm_num) (by norm_num)
      calc
        (∫ u : U, ∫ v : U, (signValue u.2+signValue v.2)^2*(u.1+v.1)^2
          ∂uniformUnitLaw.prod fairLaw ∂uniformUnitLaw.prod fairLaw) =
            ∫ u : U, 2*u.1^2+2/3 ∂uniformUnitLaw.prod fairLaw := by
              congr 1; funext u; exact inner_s2z2 u.1 u.2
        _ = 4/3 := by
          have hi : MeasureTheory.Integrable (fun u : U => u.1^2)
              (uniformUnitLaw.prod fairLaw) := by
            convert unit_mono_integrable 2 0 using 1
            funext u
            simp [mono]
          have hi' : MeasureTheory.Integrable (fun u : U => 2*u.1^2)
              (uniformUnitLaw.prod fairLaw) := by
            simpa using hi.const_mul (2 : ℝ)
          rw [integral_add hi' (integrable_const _)]
          rw [integral_const_mul, hz2]
          simp [integral_const, probReal_univ]
          norm_num
  have hG : projectionGamma W1MixedKernel = !![1,0;0,1/3] := by
    ext a b
    fin_cases a <;> fin_cases b
    · change (∫ u : U, projection W1MixedKernel u 0 * projection W1MixedKernel u 0
        ∂uniformUnitLaw.prod fairLaw) = 1
      have he : (fun u : U => projection W1MixedKernel u 0 * projection W1MixedKernel u 0) =
          fun u => mono 0 2 u := by
        funext u
        rw [projection_formula hBeta u.1 u.2]
        simp [mono] <;> ring_nf
      rw [integral_congr_ae (Filter.Eventually.of_forall fun u => congrFun he u)]
      simpa [mono] using mono_mean 0 2 (by norm_num) (by norm_num)
    · change (∫ u : U, projection W1MixedKernel u 0 * projection W1MixedKernel u 1
        ∂uniformUnitLaw.prod fairLaw) = 0
      have he : (fun u : U => projection W1MixedKernel u 0 * projection W1MixedKernel u 1) =
          fun u => mono 1 2 u := by
        funext u
        rw [projection_formula hBeta u.1 u.2]
        simp [mono] <;> ring_nf
      rw [integral_congr_ae (Filter.Eventually.of_forall fun u => congrFun he u)]
      simpa [mono] using mono_mean 1 2 (by norm_num) (by norm_num)
    · change (∫ u : U, projection W1MixedKernel u 1 * projection W1MixedKernel u 0
        ∂uniformUnitLaw.prod fairLaw) = 0
      have he : (fun u : U => projection W1MixedKernel u 1 * projection W1MixedKernel u 0) =
          fun u => mono 1 2 u := by
        funext u
        rw [projection_formula hBeta u.1 u.2]
        simp [mono, mul_comm] <;> ring_nf
      rw [integral_congr_ae (Filter.Eventually.of_forall fun u => congrFun he u)]
      simpa [mono] using mono_mean 1 2 (by norm_num) (by norm_num)
    · change (∫ u : U, projection W1MixedKernel u 1 * projection W1MixedKernel u 1
        ∂uniformUnitLaw.prod fairLaw) = 1/3
      have he : (fun u : U => projection W1MixedKernel u 1 * projection W1MixedKernel u 1) =
          fun u => mono 2 2 u := by
        funext u
        rw [projection_formula hBeta u.1 u.2]
        simp [mono] <;> ring_nf
      rw [integral_congr_ae (Filter.Eventually.of_forall fun u => congrFun he u)]
      simpa [mono] using mono_mean 2 2 (by norm_num) (by norm_num)
  exact ⟨hH,hG⟩

end SAP.P018a.WH.W1
