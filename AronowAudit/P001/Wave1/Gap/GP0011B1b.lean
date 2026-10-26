import AronowAudit.P001.P001_Foundations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! P001-T12: the information lower bound for regular influence functions. -/

namespace AronowAudit.P001.Wave1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Matrix
noncomputable section
local instance GP0011B1b_instDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false




/-! P001-T12: apply the scalar residual square to each test vector a. -/

private lemma GP0011B1b_t12_linear_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {τ : ℕ} (f : Ω → Fin τ → ℝ)
    (hf : ∀ j, MemLp (fun ω => f ω j) 2 μ) (a : Fin τ → ℝ) :
    MemLp (fun ω => ∑ j, a j * f ω j) 2 μ := by
  exact memLp_finsetSum Finset.univ (fun j _ => (hf j).const_mul (a j))

/-- Expand the product of two finite L2 linear combinations under the integral.
Every summand is L1 by the L2 Holder inequality. -/
private lemma GP0011B1b_t12_mean_linear_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {τ υ : ℕ} (f : Ω → Fin τ → ℝ) (g : Ω → Fin υ → ℝ)
    (hf : ∀ j, MemLp (fun ω => f ω j) 2 μ)
    (hg : ∀ k, MemLp (fun ω => g ω k) 2 μ)
    (a : Fin τ → ℝ) (b : Fin υ → ℝ) :
    mean μ (fun ω => (∑ j, a j * f ω j) * (∑ k, b k * g ω k)) =
      ∑ j, ∑ k, a j * mean μ (fun ω => f ω j * g ω k) * b k := by
  have hterm (j : Fin τ) (k : Fin υ) :
      Integrable (fun ω => a j * (f ω j * g ω k) * b k) μ :=
    (((hf j).integrable_mul (hg k)).const_mul (a j)).mul_const (b k)
  have hrow (j : Fin τ) :
      Integrable (fun ω => ∑ k, a j * (f ω j * g ω k) * b k) μ := by
    exact integrable_finsetSum Finset.univ (fun k _ => hterm j k)
  have hexpand (ω : Ω) :
      (∑ j, a j * f ω j) * (∑ k, b k * g ω k) =
        ∑ j, ∑ k, a j * (f ω j * g ω k) * b k := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold mean
  simp_rw [hexpand]
  rw [integral_finsetSum Finset.univ (fun j _ => hrow j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum Finset.univ (fun k _ => hterm j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_mul_const, integral_const_mul]

private lemma GP0011B1b_t12_centered_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {τ : ℕ} (ψ : Ω → Fin τ → ℝ)
    (hψ0 : ∀ j, mean μ (fun ω => ψ ω j) = 0) (j k : Fin τ) :
    covarianceMatrix μ ψ j k = mean μ (fun ω => ψ ω j * ψ ω k) := by
  change (∫ ω, (ψ ω j - mean μ (fun ω => ψ ω j)) *
    (ψ ω k - mean μ (fun ω => ψ ω k)) ∂μ) = _
  rw [hψ0 j, hψ0 k]
  simp only [sub_zero, mean]

theorem regular_influence_information_lower_bound_proof {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {τ : ℕ} (s ψ : Ω → Fin τ → ℝ)
   (hs2 : ∀ j,MemLp (fun ω => s ω j) 2 μ) (hψ2 : ∀ j,MemLp (fun ω => ψ ω j) 2 μ)
   (hs0 : ∀ j,mean μ (fun ω => s ω j)=0) (hψ0 : ∀ j,mean μ (fun ω => ψ ω j)=0)
   (I : Matrix (Fin τ) (Fin τ) ℝ)
   (hI : ∀ j k,I j k=mean μ (fun ω => s ω j*s ω k)) (hpos : I.PosDef)
   (hregular : ∀ j k,mean μ (fun ω => ψ ω j*s ω k)=if j=k then 1 else 0) :
   ∀ a : Fin τ → ℝ,0 ≤ ∑ j,∑ k,a j*(covarianceMatrix μ ψ j k-I⁻¹ j k)*a k := by
  intro a
  -- b is the coefficient vector of the score projection in the direction a.
  let b : Fin τ → ℝ := I⁻¹ *ᵥ a
  have hdet : IsUnit I.det := (Matrix.isUnit_iff_isUnit_det I).mp hpos.isUnit
  have hIb : I *ᵥ b = a := by
    dsimp only [b]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv I hdet, Matrix.one_mulVec]
  have hIb_coord (j : Fin τ) : (∑ k, I j k * b k) = a j := by
    exact congrFun hIb j
  let P : Ω → ℝ := fun ω => ∑ j, a j * ψ ω j
  let S : Ω → ℝ := fun ω => ∑ j, b j * s ω j
  have hP2 : MemLp P 2 μ := GP0011B1b_t12_linear_memLp μ ψ hψ2 a
  have hS2 : MemLp S 2 μ := GP0011B1b_t12_linear_memLp μ s hs2 b
  have hPPi : Integrable (fun ω => P ω * P ω) μ := hP2.integrable_mul hP2
  have hPSi : Integrable (fun ω => P ω * S ω) μ := hP2.integrable_mul hS2
  have hSSi : Integrable (fun ω => S ω * S ω) μ := hS2.integrable_mul hS2
  have hPP : mean μ (fun ω => P ω * P ω) =
      ∑ j, ∑ k, a j * covarianceMatrix μ ψ j k * a k := by
    change mean μ (fun ω => (∑ j, a j * ψ ω j) * (∑ k, a k * ψ ω k)) = _
    rw [GP0011B1b_t12_mean_linear_mul μ ψ ψ hψ2 hψ2 a a]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [GP0011B1b_t12_centered_covariance μ ψ hψ0 j k]
  have hPS : mean μ (fun ω => P ω * S ω) = ∑ j, a j * b j := by
    change mean μ (fun ω => (∑ j, a j * ψ ω j) * (∑ k, b k * s ω k)) = _
    rw [GP0011B1b_t12_mean_linear_mul μ ψ s hψ2 hs2 a b]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [hregular]
    calc
      (∑ k, a j * (if j = k then 1 else 0) * b k) =
          ∑ k, if k = j then a j * b j else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : k = j
        · subst k
          simp
        · simp [h, Ne.symm h]
      _ = _ := by simp
  have hSS : mean μ (fun ω => S ω * S ω) = ∑ j, a j * b j := by
    change mean μ (fun ω => (∑ j, b j * s ω j) * (∑ k, b k * s ω k)) = _
    rw [GP0011B1b_t12_mean_linear_mul μ s s hs2 hs2 b b]
    calc
      (∑ j, ∑ k, b j * mean μ (fun ω => s ω j * s ω k) * b k) =
          ∑ j, b j * (∑ k, I j k * b k) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [hI j k]
        ring
      _ = ∑ j, b j * a j := by simp_rw [hIb_coord]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hJ : (∑ j, ∑ k, a j * I⁻¹ j k * a k) = ∑ j, a j * b j := by
    apply Finset.sum_congr rfl
    intro j _
    change (∑ k, a j * I⁻¹ j k * a k) = a j * (∑ k, I⁻¹ j k * a k)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hquadratic : (∑ j, ∑ k, a j * (covarianceMatrix μ ψ j k - I⁻¹ j k) * a k) =
      (∑ j, ∑ k, a j * covarianceMatrix μ ψ j k * a k) - ∑ j, a j * b j := by
    calc
      _ = (∑ j, ∑ k, a j * covarianceMatrix μ ψ j k * a k) -
          (∑ j, ∑ k, a j * I⁻¹ j k * a k) := by
        simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
      _ = _ := by rw [hJ]
  have hresidual : mean μ (fun ω => (P ω - S ω)^2) =
      mean μ (fun ω => P ω * P ω) -
        2 * mean μ (fun ω => P ω * S ω) + mean μ (fun ω => S ω * S ω) := by
    unfold mean
    calc
      _ = ∫ ω, (P ω * P ω - 2 * (P ω * S ω)) + S ω * S ω ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        ring
      _ = _ := by
        rw [integral_add (f := fun ω => P ω * P ω - 2 * (P ω * S ω))
          (hPPi.sub (hPSi.const_mul 2)) hSSi,
          integral_sub (f := fun ω => P ω * P ω) (g := fun ω => 2 * (P ω * S ω))
            hPPi (hPSi.const_mul 2), integral_const_mul]
  calc
    0 ≤ mean μ (fun ω => (P ω - S ω)^2) := integral_nonneg (fun ω => sq_nonneg _)
    _ = _ := by
      rw [hresidual, hPP, hPS, hSS, hquadratic]
      ring

end
end AronowAudit.P001.Wave1
