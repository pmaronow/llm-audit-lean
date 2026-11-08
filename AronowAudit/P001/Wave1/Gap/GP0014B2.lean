import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGP0014B2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-! Record 9. The event-to-L¹ extension below is implemented by equality of
weighted pushforward measures, rather than by a simple-function limit. -/


private theorem mar_binary_bounds {Ω : Type*} (R : Ω → ℝ)
    (hbinary : ∀ ω, R ω = 0 ∨ R ω = 1) :
    (∀ ω, 0 ≤ R ω) ∧ (∀ ω, ‖R ω‖ ≤ 1) := by
  constructor <;> intro ω <;> rcases hbinary ω with h | h <;> simp [h]

/-- Restriction to respondents is multiplication by the binary response. -/
private theorem mar_response_integral {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (R f : Ω → ℝ) (hR : Measurable R)
    (hbinary : ∀ ω, R ω = 0 ∨ R ω = 1)
    (C : Set E) (hC : MeasurableSet C) :
    (∫ ω in X ⁻¹' C, f ω * R ω ∂μ) =
      ∫ ω in X ⁻¹' C, f ω ∂μ.restrict {ω | R ω = 1} := by
  have hB : MeasurableSet {ω | R ω = 1} := hR (measurableSet_singleton 1)
  have hi : (fun ω => f ω * R ω) = {ω | R ω = 1}.indicator f := by
    funext ω
    rcases hbinary ω with h | h <;> simp [Set.indicator, h]
  rw [hi, integral_indicator hB, Measure.restrict_restrict hB,
    Measure.restrict_restrict (hX hC)]
  rw [Set.inter_comm]




/-! Record 10. No MAR or population integrability of `m ∘ X` is used. -/


private theorem stable_censoring_piecewise {Ω : Type*} (Y R : Ω → ℝ)
    (hbinary : ∀ ω, R ω = 0 ∨ R ω = 1) :
    (fun ω => censored (Y ω) (R ω)) =
      {ω | R ω = 1}.piecewise Y (fun _ => -99) := by
  funext ω
  rcases hbinary ω with h | h <;> simp [censored, Set.piecewise, h]



/-! Record 11. An explicit path with the exact seven required coordinates. -/

private theorem mixture_sqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by
  exact Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)

private theorem mixture_normal_nonneg (m s y : ℝ) (hs : 0 < s) :
    0 ≤ normalDensity m s y := by
  exact div_nonneg (Real.exp_pos _).le (mul_pos hs mixture_sqrt_pos).le

private theorem mixture_lognormal_nonneg (y : ℝ) : 0 ≤ lognormalDensity 0 1 y := by
  unfold lognormalDensity
  split_ifs with hy
  · exact div_nonneg (mixture_normal_nonneg 0 1 (Real.log y) (by norm_num)) hy.le
  · exact le_rfl

private theorem mixture_exponential_nonneg (y : ℝ) : 0 ≤ exponentialDensity 1 y := by
  unfold exponentialDensity
  split_ifs <;> positivity

private theorem mixture_path_admissible (σ : ℝ) (hσ : 0 < σ) :
    MixtureAdmissible ![1/2,1/4,1,σ,0,1,1] := by
  norm_num [MixtureAdmissible, hσ]

private theorem mixture_path_exp_lower (σ y : ℝ) (hσ : 0 < σ) (hy : 0 ≤ y) :
    Real.exp (-y) / 4 ≤ mixtureDensity ![1/2,1/4,1,σ,0,1,1] y := by
  have hn := mixture_normal_nonneg 1 σ y hσ
  have hl := mixture_lognormal_nonneg y
  change Real.exp (-y) / 4 ≤
    (1/2 : ℝ) * normalDensity 1 σ y + (1/4 : ℝ) * lognormalDensity 0 1 y +
      (1-(1/2 : ℝ)-(1/4 : ℝ)) * exponentialDensity 1 y
  rw [exponentialDensity, if_pos hy]
  norm_num only [one_mul, neg_one_mul]
  linarith

private theorem mixture_path_at_one_lower (σ : ℝ) (hσ : 0 < σ) :
    1 / (2 * σ * Real.sqrt (2 * Real.pi)) ≤
      mixtureDensity ![1/2,1/4,1,σ,0,1,1] 1 := by
  have hl := mixture_lognormal_nonneg 1
  have he := mixture_exponential_nonneg 1
  have hn : normalDensity 1 σ 1 = 1 / (σ * Real.sqrt (2 * Real.pi)) := by
    simp [normalDensity]
  have hmain : 1 / (2 * σ * Real.sqrt (2 * Real.pi)) =
      (1/2 : ℝ) * normalDensity 1 σ 1 := by
    rw [hn]
    field_simp [hσ.ne', mixture_sqrt_pos.ne']
    <;> ring
  rw [hmain]
  change (1/2 : ℝ) * normalDensity 1 σ 1 ≤
    (1/2 : ℝ) * normalDensity 1 σ 1 + (1/4 : ℝ) * lognormalDensity 0 1 1 +
      (1-(1/2 : ℝ)-(1/4 : ℝ)) * exponentialDensity 1 1
  linarith

private theorem mixture_path_lower_bound (σ : ℝ) (hσ : 0 < σ) :
    (Real.exp (-5) / (32 * Real.sqrt (2 * Real.pi))) / σ ≤
      mixtureLikelihood ![1,2,3] ![1/2,1/4,1,σ,0,1,1] := by
  let θ : Fin 7 → ℝ := ![1/2,1/4,1,σ,0,1,1]
  let a : ℝ := Real.sqrt (2 * Real.pi)
  have ha : 0 < a := mixture_sqrt_pos
  have h₁ : 1 / (2 * σ * a) ≤ mixtureDensity θ 1 :=
    mixture_path_at_one_lower σ hσ
  have h₂ : Real.exp (-2) / 4 ≤ mixtureDensity θ 2 :=
    mixture_path_exp_lower σ 2 hσ (by norm_num)
  have h₃ : Real.exp (-3) / 4 ≤ mixtureDensity θ 3 :=
    mixture_path_exp_lower σ 3 hσ (by norm_num)
  have hn₁ : 0 ≤ 1 / (2 * σ * a) := by positivity
  have hn₂ : 0 ≤ Real.exp (-2) / 4 := by positivity
  have hn₃ : 0 ≤ Real.exp (-3) / 4 := by positivity
  have hd₁ : 0 ≤ mixtureDensity θ 1 := hn₁.trans h₁
  have hd₂ : 0 ≤ mixtureDensity θ 2 := hn₂.trans h₂
  have h₁₂ : (1 / (2 * σ * a)) * (Real.exp (-2) / 4) ≤
      mixtureDensity θ 1 * mixtureDensity θ 2 :=
    mul_le_mul h₁ h₂ hn₂ hd₁
  have h₁₂₃ : ((1 / (2 * σ * a)) * (Real.exp (-2) / 4)) * (Real.exp (-3) / 4) ≤
      (mixtureDensity θ 1 * mixtureDensity θ 2) * mixtureDensity θ 3 :=
    mul_le_mul h₁₂ h₃ hn₃ (mul_nonneg hd₁ hd₂)
  have hexp : Real.exp (-2) * Real.exp (-3) = Real.exp (-5) := by
    rw [← Real.exp_add]
    norm_num
  have hcoeff : ((1 / (2 * σ * a)) * (Real.exp (-2) / 4)) * (Real.exp (-3) / 4) =
      (Real.exp (-5) / (32 * a)) / σ := by
    rw [← hexp]
    field_simp [hσ.ne', ha.ne']
    <;> ring
  rw [hcoeff] at h₁₂₃
  calc
    (Real.exp (-5) / (32 * Real.sqrt (2 * Real.pi))) / σ =
        (Real.exp (-5) / (32 * a)) / σ := rfl
    _ ≤ (mixtureDensity θ 1 * mixtureDensity θ 2) * mixtureDensity θ 3 := h₁₂₃
    _ = mixtureLikelihood ![1,2,3] ![1/2,1/4,1,σ,0,1,1] := by
      simp [mixtureLikelihood, Fin.prod_univ_succ, θ, mul_assoc]

/-- Record 11, with exactly the held theorem's conclusion. -/
theorem mixture_three_point_unbounded_proof : (∀ B : ℝ, ∃ σ : ℝ, 0  <  σ ∧ MixtureAdmissible ![1/2,1/4,1,σ,0,1,1] ∧
   B  <  mixtureLikelihood ![1,2,3] ![1/2,1/4,1,σ,0,1,1]) ∧
   ¬ ∃ θ : Fin 7 → ℝ, MixtureAdmissible θ ∧ ∀ θ', MixtureAdmissible θ' →
     mixtureLikelihood ![1,2,3] θ'  ≤  mixtureLikelihood ![1,2,3] θ := by
  have hunbounded : ∀ B : ℝ, ∃ σ : ℝ, 0 < σ ∧
      MixtureAdmissible ![1/2,1/4,1,σ,0,1,1] ∧
      B < mixtureLikelihood ![1,2,3] ![1/2,1/4,1,σ,0,1,1] := by
    intro B
    let c : ℝ := Real.exp (-5) / (32 * Real.sqrt (2 * Real.pi))
    have hc : 0 < c := div_pos (Real.exp_pos _) (mul_pos (by norm_num) mixture_sqrt_pos)
    have hden : 0 < |B| + 1 := by linarith [abs_nonneg B]
    let σ : ℝ := c / (|B| + 1)
    have hσ : 0 < σ := div_pos hc hden
    have hratio : c / σ = |B| + 1 := by
      dsimp only [σ]
      field_simp [hc.ne', hden.ne']
      <;> ring
    refine ⟨σ, hσ, mixture_path_admissible σ hσ, ?_⟩
    calc
      B < |B| + 1 := by linarith [le_abs_self B]
      _ = c / σ := hratio.symm
      _ ≤ mixtureLikelihood ![1,2,3] ![1/2,1/4,1,σ,0,1,1] :=
        mixture_path_lower_bound σ hσ
  refine ⟨hunbounded, ?_⟩
  rintro ⟨θ, hθ, hmax⟩
  obtain ⟨σ, hσ, hadm, hstrict⟩ := hunbounded (mixtureLikelihood ![1,2,3] θ)
  exact (not_lt_of_ge (hmax ![1/2,1/4,1,σ,0,1,1] hadm)) hstrict

example : type_of% @AronowAudit.P001.mixture_three_point_unbounded :=
  mixture_three_point_unbounded_proof

end
end AronowAudit.P001.Wave1
