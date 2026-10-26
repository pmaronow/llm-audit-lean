import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Conditional finite reconstruction identities for ratios and intercept-only weighted least squares.
These identities do not identify the historical procedure,
the sampling design, or national confidence-interval coverage.
-/

namespace AronowAudit.P054

open scoped BigOperators
noncomputable section
variable {I : Type*} [Fintype I]

def groupCount (d : I → ℝ) : ℝ := ∑ i, d i
def groupWeight (d w : I → ℝ) : ℝ := ∑ i, d i * w i
def weightedProportion (d w y : I → ℝ) : ℝ :=
  (∑ i, d i * w i * y i) / groupWeight d w
def ratioResidual (d w y : I → ℝ) (i : I) : ℝ :=
  d i * w i * (y i - weightedProportion d w y)

theorem groupWeight_pos (d w : I → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hw : ∀ i, 0 < w i) (hn : 0 < groupCount d) : 0 < groupWeight d w := by
  have hd0 (i : I) : 0 ≤ d i := by rcases hd i with h | h <;> simp [h]
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hd0 i)).mp hn
  have hle : d i * w i ≤ groupWeight d w :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hd0 j) (hw j).le) (Finset.mem_univ i)
  exact lt_of_lt_of_le (mul_pos hi (hw i)) hle

/-- Finite normal equation for an intercept-only fit, also the centered
linearisation residual identity for the ratio. -/
theorem ratioResidual_sum (d w y : I → ℝ) (hW : groupWeight d w ≠ 0) :
    (∑ i, ratioResidual d w y i) = 0 := by
  simp only [ratioResidual, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold weightedProportion groupWeight at *
  rw [mul_div_cancel₀ _ hW]
  exact sub_self _

/-- Binary responses turn the weighted residual sum of squares into
W p(1-p). The weights here may be arbitrary; nonzero W is explicit. -/
theorem weighted_binary_rss (d w y : I → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hW : groupWeight d w ≠ 0) :
    (∑ i, d i * w i * (y i - weightedProportion d w y)^2) =
      groupWeight d w * weightedProportion d w y * (1 - weightedProportion d w y) := by
  let p := weightedProportion d w y
  have hm : (∑ i, d i * w i * y i) = groupWeight d w * p := by
    dsimp [p, weightedProportion]
    rw [mul_div_cancel₀ _ hW]
  have he (i : I) : d i * w i * (y i - p)^2 =
      d i * w i * y i - 2*p*(d i*w i*y i) + p^2*(d i*w i) := by
    rcases hy i with h | h <;> rw [h] <;> ring
  change (∑ i, d i * w i * (y i - p)^2) = groupWeight d w * p * (1-p)
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hm]
  change groupWeight d w * p - 2*p*(groupWeight d w*p) + p^2*groupWeight d w = _
  ring

theorem ratioResidual_sq (d w y : I → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1) :
    (∑ i, (ratioResidual d w y i)^2) =
      ∑ i, d i * (w i)^2 * (y i - weightedProportion d w y)^2 := by
  apply Finset.sum_congr rfl
  intro i _
  rcases hd i with h | h <;> simp [ratioResidual, h, mul_pow]

/-- P054-T1, finite ratio linearisation and its squared-weight term. -/
theorem ratio_linearisation {N : ℕ} (hN : 2 ≤ N)
    (d w y : Fin N → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hw : ∀ i, 0 < w i) (hn : 0 < groupCount d) :
    (∑ i, ratioResidual d w y i) = 0 ∧
    ((∑ i, (ratioResidual d w y i)^2) / ((N : ℝ)*((N : ℝ)-1))) /
        (groupWeight d w / (N : ℝ))^2 =
      (N : ℝ)/((N : ℝ)-1) *
        (∑ i, d i * (w i)^2 * (y i - weightedProportion d w y)^2) /
          (groupWeight d w)^2 := by
  have hW := ne_of_gt (groupWeight_pos d w hd hw hn)
  refine ⟨ratioResidual_sum d w y hW, ?_⟩
  rw [ratioResidual_sq d w y hd]
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ)-1 ≠ 0 := by linarith
  field_simp [hW, hN0, hN1]
  <;> ring

/-- P054-T1, equal weights recover the unweighted binary-proportion variance
inside the full-sample N/(N-1) correction. -/
theorem equal_weight_ratio (d y : I → ℝ) (c : ℝ) (hc : 0 < c)
    (hy : ∀ i, y i = 0 ∨ y i = 1) (hn : 0 < groupCount d) :
    (∑ i, d i * c^2 * (y i - weightedProportion d (fun _ => c) y)^2) /
        (groupWeight d (fun _ => c))^2 =
      weightedProportion d (fun _ => c) y *
        (1 - weightedProportion d (fun _ => c) y) / groupCount d := by
  have hW : groupWeight d (fun _ => c) = groupCount d * c := by
    simp [groupWeight, groupCount, Finset.sum_mul]
  have hW0 : groupWeight d (fun _ => c) ≠ 0 := by rw [hW]; positivity
  have hs := weighted_binary_rss d (fun _ => c) y hy hW0
  have he : (∑ i, d i * c^2 * (y i - weightedProportion d (fun _ => c) y)^2) =
      c * (∑ i, d i * c * (y i - weightedProportion d (fun _ => c) y)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hs, hW]
  field_simp [ne_of_gt hn, ne_of_gt hc]
  <;> ring

/-- Full P054-T1, including the equal-weight specialization of the same
ratio, rather than a different unweighted estimator. -/
theorem ratio_reconstruction {N : ℕ} (hN : 2 ≤ N)
    (d w y : Fin N → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hy : ∀ i, y i = 0 ∨ y i = 1) (hw : ∀ i, 0 < w i)
    (hn : 0 < groupCount d) :
    (∑ i, ratioResidual d w y i) = 0 ∧
    ((∑ i, (ratioResidual d w y i)^2) / ((N : ℝ)*((N : ℝ)-1))) /
        (groupWeight d w / (N : ℝ))^2 =
      (N : ℝ)/((N : ℝ)-1) *
        (∑ i, d i * (w i)^2 * (y i - weightedProportion d w y)^2) /
          (groupWeight d w)^2 ∧
    (∀ c : ℝ, 0 < c → w = (fun _ => c) →
      (∑ i, d i * (w i)^2 * (y i - weightedProportion d w y)^2) /
          (groupWeight d w)^2 =
        weightedProportion d w y * (1 - weightedProportion d w y) / groupCount d) := by
  have hr := ratio_linearisation hN d w y hd hw hn
  refine ⟨hr.1, hr.2, ?_⟩
  intro c hc he
  rw [he]
  exact equal_weight_ratio d y c hc hy hn


/-- P054-T2: the classical intercept-only WLS variance reduces to p(1-p)/(n-1).
This algebra establishes neither historical use nor survey-design coverage. -/
theorem classical_intercept_wls (d w y : I → ℝ)
    (hd : ∀ i, d i = 0 ∨ d i = 1) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hw : ∀ i, 0 < w i) (hn : 2 ≤ groupCount d) :
    (∑ i, d i*w i*(y i-weightedProportion d w y)^2) =
        groupWeight d w * weightedProportion d w y * (1-weightedProportion d w y) ∧
    (∑ i, d i*w i*(y i-weightedProportion d w y)^2) /
        ((groupCount d-1)*groupWeight d w) =
      weightedProportion d w y*(1-weightedProportion d w y)/(groupCount d-1) ∧
    weightedProportion d w y*(1-weightedProportion d w y)/(groupCount d-1) =
      groupCount d/(groupCount d-1) *
        (weightedProportion d w y*(1-weightedProportion d w y)/groupCount d) := by
  have hn0 : 0 < groupCount d := by linarith
  have hW := ne_of_gt (groupWeight_pos d w hd hw hn0)
  have hs := weighted_binary_rss d w y hy hW
  refine ⟨hs, ?_, ?_⟩
  · rw [hs]
    field_simp [hW]
    <;> ring
  · field_simp [ne_of_gt hn0]
    <;> ring


end
end AronowAudit.P054

