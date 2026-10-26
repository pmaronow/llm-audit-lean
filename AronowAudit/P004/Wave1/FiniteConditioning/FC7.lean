import AronowAudit.P004.Wave1.FiniteConditioningBlueprint
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt

namespace AronowAudit.P004.Wave1.FiniteConditioning

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- Finite weighted L² algebra, with all moments taken under the actual design. -/
theorem fc7_proof : FC7 := by
  classical
  intro N p hp
  have hsecond : ∀ U : Assignment N → ℝ, 0 ≤ expect p (fun z => (U z)^2) := by
    intro U
    have h := expect_mono p hp (fun _ => 0) (fun z => (U z)^2)
      (fun z => sq_nonneg (U z))
    simpa only [expect_const] using h
  have hnonneg : ∀ U : Assignment N → ℝ, 0 ≤ l2Norm p U := by
    intro U
    exact Real.sqrt_nonneg _
  have hsq : ∀ U : Assignment N → ℝ,
      (l2Norm p U)^2 = expect p (fun z => (U z)^2) := by
    intro U
    exact Real.sq_sqrt (hsecond U)
  -- Weighted Cauchy--Schwarz, using r=wUV, f=wU² and g=wV².
  -- This version avoids introducing square roots of the individual weights.
  have hcs : ∀ U V : Assignment N → ℝ,
      |expect p (fun z => U z * V z)| ≤ l2Norm p U * l2Norm p V := by
    intro U V
    have hcs_sq : (expect p (fun z => U z * V z))^2 ≤
        expect p (fun z => (U z)^2) * expect p (fun z => (V z)^2) := by
      exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        (Finset.univ : Finset (Assignment N))
        (r := fun z => designWeight p z * (U z * V z))
        (f := fun z => designWeight p z * (U z)^2)
        (g := fun z => designWeight p z * (V z)^2)
        (fun z _ => mul_nonneg (design_weight_nonneg p hp z) (sq_nonneg (U z)))
        (fun z _ => mul_nonneg (design_weight_nonneg p hp z) (sq_nonneg (V z)))
        (fun z _ => le_of_eq (by ring))
    calc
      |expect p (fun z => U z * V z)| =
          Real.sqrt ((expect p (fun z => U z * V z))^2) :=
        (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (expect p (fun z => (U z)^2) *
          expect p (fun z => (V z)^2)) := Real.sqrt_le_sqrt hcs_sq
      _ = l2Norm p U * l2Norm p V := Real.sqrt_mul (hsecond U) _
  have htriangle : ∀ U V : Assignment N → ℝ,
      l2Norm p (fun z => U z + V z) ≤ l2Norm p U + l2Norm p V := by
    intro U V
    have hexpand : expect p (fun z => (U z + V z)^2) =
        expect p (fun z => (U z)^2) +
        2 * expect p (fun z => U z * V z) + expect p (fun z => (V z)^2) := by
      have he : (fun z => (U z + V z)^2) =
          (fun z => (U z)^2 + 2 * (U z * V z) + (V z)^2) := by
        funext z
        ring
      rw [he, expect_add, expect_add, expect_mul]
    have hc : expect p (fun z => U z * V z) ≤ l2Norm p U * l2Norm p V :=
      (le_abs_self _).trans (hcs U V)
    change Real.sqrt (expect p (fun z => (U z + V z)^2)) ≤ _
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg (hnonneg U) (hnonneg V), ?_⟩
    rw [hexpand]
    nlinarith [hsq U, hsq V]
  have hscale : ∀ (c : ℝ) (U : Assignment N → ℝ),
      l2Norm p (fun z => c * U z) = |c| * l2Norm p U := by
    intro c U
    have he : (fun z => (c * U z)^2) = (fun z => c^2 * (U z)^2) := by
      funext z
      ring
    change Real.sqrt (expect p (fun z => (c * U z)^2)) =
      |c| * Real.sqrt (expect p (fun z => (U z)^2))
    rw [he, expect_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  have hdifference : ∀ U V : Assignment N → ℝ,
      l2Norm p (fun z => U z - V z) ≤ l2Norm p U + l2Norm p V := by
    intro U V
    have he : (fun z => U z - V z) = (fun z => U z + (-1 : ℝ) * V z) := by
      funext z
      ring
    rw [he]
    calc
      _ ≤ l2Norm p U + l2Norm p (fun z => (-1 : ℝ) * V z) := htriangle _ _
      _ = _ := by rw [hscale (-1 : ℝ) V]; norm_num
  have hsum : ∀ {ι : Type} (S : Finset ι) (U : ι → Assignment N → ℝ),
      l2Norm p (fun z => ∑ k ∈ S, U k z) ≤ ∑ k ∈ S, l2Norm p (U k) := by
    intro ι S U
    induction S using Finset.induction_on with
    | empty => simp [l2Norm, expect_const]
    | @insert a S ha ih =>
      simpa only [Finset.sum_insert ha] using
        (htriangle (U a) (fun z => ∑ k ∈ S, U k z)).trans
          (add_le_add (le_refl (l2Norm p (U a))) ih)
  have hsup : ∀ (U : Assignment N → ℝ) (M : ℝ),
      (∀ z, |U z| ≤ M) → l2Norm p U ≤ M := by
    intro U M hU
    have hM : 0 ≤ M := (abs_nonneg (U (fun _ => false))).trans (hU _)
    have hmom : expect p (fun z => (U z)^2) ≤ M^2 := by
      have h := expect_mono p hp (fun z => (U z)^2) (fun _ => M^2) (by
        intro z
        have hm := mul_nonneg (sub_nonneg.mpr (hU z))
          (add_nonneg hM (abs_nonneg (U z)))
        nlinarith [sq_abs (U z)])
      simpa only [expect_const] using h
    exact Real.sqrt_le_iff.mpr ⟨hM, hmom⟩
  have hmono : ∀ U V : Assignment N → ℝ,
      (∀ z, |U z| ≤ |V z|) → l2Norm p U ≤ l2Norm p V := by
    intro U V hUV
    apply Real.sqrt_le_sqrt
    apply expect_mono p hp
    intro z
    have hm := mul_nonneg (sub_nonneg.mpr (hUV z))
      (add_nonneg (abs_nonneg (V z)) (abs_nonneg (U z)))
    nlinarith [sq_abs (U z), sq_abs (V z)]
  have hcenter : ∀ U : Assignment N → ℝ,
      l2Norm p (fun z => U z - expect p U) ≤ l2Norm p U := by
    intro U
    apply Real.sqrt_le_sqrt
    have he : expect p (fun z => (U z - expect p U)^2) = variance p U := by
      simpa only [variance, pow_two] using (cov_centered p U U).symm
    rw [he]
    exact variance_le_second p U
  have hcov : ∀ U V : Assignment N → ℝ,
      |cov p U V| ≤ l2Norm p U * l2Norm p V := by
    intro U V
    rw [cov_centered]
    exact (hcs (fun z => U z - expect p U) (fun z => V z - expect p V)).trans
      (mul_le_mul (hcenter U) (hcenter V)
        (hnonneg (fun z => V z - expect p V)) (hnonneg U))
  have hvariance : ∀ U : Assignment N → ℝ,
      expect p U = 0 → variance p U = (l2Norm p U)^2 := by
    intro U hU
    rw [hsq U]
    simp only [variance, cov, hU, zero_mul, sub_zero, pow_two]
  exact ⟨hnonneg, htriangle, hdifference, hsum, hscale, hsup, hmono, hcs, hcov, hvariance⟩

end
end AronowAudit.P004.Wave1.FiniteConditioning
