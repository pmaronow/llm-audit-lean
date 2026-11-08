import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
Drafts for dd-GP0011B1. No Lean executable was run when preparing this file.
The three original held declarations are used only in the type checks.
-/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
local instance instDecidableGP0011B1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

/-! P001-T10: a collapsing normal plus a fixed positive exponential. -/

private def t10_theta (m s : ℝ) : Fin 7 → ℝ := ![1/2,0,m,s,0,1,1]

private lemma t10_admissible (m s : ℝ) (hs : 0 < s) :
    MixtureAdmissible (t10_theta m s) := by
  norm_num [MixtureAdmissible, t10_theta, hs]

private lemma t10_sqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by
  exact Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)

private lemma t10_density_eq (m s z : ℝ) (hz : 0 < z) :
    mixtureDensity (t10_theta m s) z =
      normalDensity m s z / 2 + Real.exp (-z) / 2 := by
  norm_num [mixtureDensity, t10_theta, exponentialDensity, hz.le] <;> ring

private lemma t10_density_lower (m s z : ℝ) (hs : 0 < s) (hz : 0 < z) :
    Real.exp (-z) / 2 ≤ mixtureDensity (t10_theta m s) z := by
  have hnormal : 0 ≤ normalDensity m s z := by
    exact div_nonneg (Real.exp_pos _).le (mul_pos hs t10_sqrt_pos).le
  rw [t10_density_eq m s z hz]
  linarith

private lemma t10_center_lower (m s : ℝ) (hm : 0 < m) (hs : 0 < s) :
    1 / (2 * s * Real.sqrt (2 * Real.pi)) ≤
      mixtureDensity (t10_theta m s) m := by
  have hnormal : normalDensity m s m = 1 / (s * Real.sqrt (2 * Real.pi)) := by
    simp [normalDensity]
  rw [t10_density_eq m s m hm, hnormal]
  have he : 0 < Real.exp (-m) := Real.exp_pos _
  have heq : 1 / (2 * s * Real.sqrt (2 * Real.pi)) =
      (1 / (s * Real.sqrt (2 * Real.pi))) / 2 := by
    field_simp [ne_of_gt hs, ne_of_gt t10_sqrt_pos] <;> ring
  rw [heq]
  linarith

private lemma t10_likelihood_lower {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ i, 0 < y i) (i0 : Fin n) (s : ℝ) (hs : 0 < s) :
    ((∏ i ∈ Finset.univ.erase i0, Real.exp (-y i) / 2) /
        (2 * Real.sqrt (2 * Real.pi))) / s ≤
      mixtureLikelihood y (t10_theta (y i0) s) := by
  let b : Fin n → ℝ := fun i => Real.exp (-y i) / 2
  let g : Fin n → ℝ := fun i => mixtureDensity (t10_theta (y i0) s) (y i)
  have hb (i : Fin n) : 0 < b i := div_pos (Real.exp_pos _) (by norm_num)
  have hbg (i : Fin n) : b i ≤ g i := t10_density_lower _ _ _ hs (hy i)
  have hg (i : Fin n) : 0 ≤ g i := (hb i).le.trans (hbg i)
  have hprod : (∏ i ∈ Finset.univ.erase i0, b i) ≤
      ∏ i ∈ Finset.univ.erase i0, g i := by
    exact Finset.prod_le_prod₀ (fun i _ => (hb i).le) (fun i _ => hbg i)
  have hpnonneg : 0 ≤ ∏ i ∈ Finset.univ.erase i0, b i :=
    Finset.prod_nonneg (fun i _ => (hb i).le)
  have hcenter : 1 / (2 * s * Real.sqrt (2 * Real.pi)) ≤ g i0 :=
    t10_center_lower (y i0) s (hy i0) hs
  calc
    _ = (1 / (2 * s * Real.sqrt (2 * Real.pi))) *
        ∏ i ∈ Finset.univ.erase i0, b i := by
      dsimp only [b]
      field_simp [ne_of_gt hs, ne_of_gt t10_sqrt_pos] <;> ring
    _ ≤ g i0 * ∏ i ∈ Finset.univ.erase i0, g i :=
      mul_le_mul hcenter hprod hpnonneg (hg i0)
    _ = ∏ i, g i := Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i0)
    _ = _ := rfl

theorem mixture_unbounded_positive_sample_proof {n : ℕ} (hn : 0  <  n) (y : Fin n → ℝ) (hy : ∀ i, 0  <  y i) :
   ∀ B : ℝ, ∃ θ : Fin 7 → ℝ, MixtureAdmissible θ ∧ B  <  mixtureLikelihood y θ := by
  intro B
  let i0 : Fin n := ⟨0, hn⟩
  let C : ℝ := (∏ i ∈ Finset.univ.erase i0, Real.exp (-y i) / 2) /
    (2 * Real.sqrt (2 * Real.pi))
  have hC : 0 < C := by
    apply div_pos
    · exact Finset.prod_pos (fun i _ => div_pos (Real.exp_pos _) (by norm_num))
    · exact mul_pos (by norm_num) t10_sqrt_pos
  let M : ℝ := max B 0 + 1
  have hM : 0 < M := by dsimp only [M]; linarith [le_max_right B 0]
  have hBM : B < M := by dsimp only [M]; linarith [le_max_left B 0]
  let s : ℝ := C / M
  have hs : 0 < s := div_pos hC hM
  have hratio : C / s = M := by
    dsimp only [s]
    field_simp [ne_of_gt hC, ne_of_gt hM] <;> ring
  refine ⟨t10_theta (y i0) s, t10_admissible _ _ hs, ?_⟩
  have hlower : C / s ≤ mixtureLikelihood y (t10_theta (y i0) s) :=
    t10_likelihood_lower y hy i0 s hs
  exact (hBM.trans_eq hratio.symm).trans_le hlower

example : type_of% @AronowAudit.P001.mixture_unbounded_positive_sample :=
  mixture_unbounded_positive_sample_proof

/-! P001-T100: equality of weighted outcome laws, on arbitrary Ω. -/


private lemma t100_weighted_apply {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → ℝ) (hw : Integrable w μ)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (S : Set Ω) (hS : MeasurableSet S) :
    (μ.withDensity (fun ω => ENNReal.ofReal (w ω))) S =
      ENNReal.ofReal (∫ ω in S, w ω ∂μ) := by
  rw [withDensity_apply _ hS]
  exact (ofReal_integral_eq_lintegral_ofReal hw.integrableOn
    (ae_restrict_of_ae hw0)).symm

/-- Transport a real integral through a weighted pushforward. The theorem applies
to all measurable real test functions, and so avoids an L2 restriction. -/
private lemma t100_weighted_map_integral {Ω F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace F]
    (μ : Measure Ω) (w : Ω → ℝ) (hw : Measurable w)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (U : Ω → F) (hU : Measurable U)
    (v : F → ℝ) (hv : Measurable v) :
    (∫ z, v z ∂(μ.withDensity (fun ω => ENNReal.ofReal (w ω))).map U) =
      ∫ ω, w ω * v (U ω) ∂μ := by
  rw [integral_map_of_stronglyMeasurable hU hv.stronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    hw.ennreal_ofReal (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hw0] with ω hω
  simp only [ENNReal.toReal_ofReal hω, smul_eq_mul]




/-! P001-T12: apply the scalar residual square to each test vector a. -/

private lemma t12_linear_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {τ : ℕ} (f : Ω → Fin τ → ℝ)
    (hf : ∀ j, MemLp (fun ω => f ω j) 2 μ) (a : Fin τ → ℝ) :
    MemLp (fun ω => ∑ j, a j * f ω j) 2 μ := by
  exact memLp_finsetSum Finset.univ (fun j _ => (hf j).const_mul (a j))


private lemma t12_centered_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {τ : ℕ} (ψ : Ω → Fin τ → ℝ)
    (hψ0 : ∀ j, mean μ (fun ω => ψ ω j) = 0) (j k : Fin τ) :
    covarianceMatrix μ ψ j k = mean μ (fun ω => ψ ω j * ψ ω k) := by
  change (∫ ω, (ψ ω j - mean μ (fun ω => ψ ω j)) *
    (ψ ω k - mean μ (fun ω => ψ ω k)) ∂μ) = _
  rw [hψ0 j, hψ0 k]
  simp only [sub_zero, mean]



end
end AronowAudit.P001.Wave1
