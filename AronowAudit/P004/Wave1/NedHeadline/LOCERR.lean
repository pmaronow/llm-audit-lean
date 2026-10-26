import AronowAudit.P004.Wave1.NedHeadlineBlueprint
import AronowAudit.P004.Wave1.NedHeadline.DY
import AronowAudit.P004.Wave1.FiniteConditioning.FC1
import AronowAudit.P004.Wave1.FiniteConditioning.FC2
import AronowAudit.P004.Wave1.FiniteConditioning.FC3
import AronowAudit.P004.Wave1.FiniteConditioning.FC4
import AronowAudit.P004.Wave1.FiniteConditioning.FC6
import AronowAudit.P004.Wave1.FiniteConditioning.FC7
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The second moment of the sum of localization residuals.

No centering hypothesis on `X` is used: the residual `X - conditionOn X`
is centered by preservation of expectation.  At a distant pair the two
larger-ball projections of these residuals have zero product expectation.
-/

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

/-- The second-moment estimate for the localization error. -/
theorem locerr_proof : LOCERR := by
  classical
  unfold LOCERR
  intro N p X D ψ Kc Cb A e ρ hF hρ
  let pp : Fin N → ℝ := fun _ => p
  have hadm : FiniteConditioning.Admissible pp := fun _ => hF.hp
  obtain ⟨hnonneg, hadd, hsub, hsum, hscale, hsup, hmono, hCS, hcov, hvar⟩ :=
    FiniteConditioning.fc7_proof pp hadm
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hρ0 : 0 ≤ ρ := hρpos.le
  let R : Fin N → Assignment N → ℝ := fun i z =>
    X i z - conditionOn pp (ball D i ρ) (X i) z
  let b : ℝ := Kc * A * ρ ^ (-e)
  let B : ℝ := b^2
  have hb : 0 ≤ b := by
    dsimp only [b]
    exact mul_nonneg (mul_nonneg hF.hKc hF.hA) (Real.rpow_nonneg hρ0 _)
  have hB : 0 ≤ B := sq_nonneg b
  have hRmean (i : Fin N) : expect pp (R i) = 0 := by
    dsimp only [R]
    rw [expect_sub, FiniteConditioning.fc3_proof pp hadm]
    ring
  have hRnorm (i : Fin N) : l2Norm pp (R i) ≤ b := by
    calc
      l2Norm pp (R i) ≤ Kc * ψ ρ := hF.hNED i ρ hρ0
      _ ≤ Kc * (A * ρ ^ (-e)) :=
        mul_le_mul_of_nonneg_left (hF.henv ρ hρ) hF.hKc
      _ = b := by dsimp only [b]; ring
  have hnear (i j : Fin N) : |cov pp (R i) (R j)| ≤ B := by
    calc
      |cov pp (R i) (R j)| ≤ l2Norm pp (R i) * l2Norm pp (R j) := hcov _ _
      _ ≤ b * b := mul_le_mul (hRnorm i) (hRnorm j) (hnonneg _) hb
      _ = B := by dsimp only [B]; ring

  have hfar (i j : Fin N) (hij : 3 * ρ < D i j) :
      |cov pp (R i) (R j)| ≤ 2 * B * (D i j / (3 * ρ)) ^ (-e) := by
    let t : ℝ := D i j / 3
    let c : ℝ := (D i j / (3 * ρ)) ^ (-e)
    have htρ : ρ ≤ t := by dsimp only [t]; linarith
    have ht0 : 0 ≤ t := hρ0.trans htρ
    have ht1 : 1 ≤ t := hρ.trans htρ
    have hDij : 0 < D i j := lt_trans (by positivity : 0 < 3 * ρ) hij
    have hratio : 0 ≤ D i j / (3 * ρ) := by positivity
    have hc : 0 ≤ c := Real.rpow_nonneg hratio _
    have htfactor : t = ρ * (D i j / (3 * ρ)) := by
      dsimp only [t]
      field_simp [hρpos.ne'] <;> ring
    have htpow : t ^ (-e) = ρ ^ (-e) * c := by
      rw [htfactor, Real.mul_rpow hρ0 hratio]
    have hballs (k : Fin N) : ball D k ρ ⊆ ball D k t := by
      intro a ha
      have ha' : D k a ≤ ρ := by simpa only [ball, Finset.mem_filter,
        Finset.mem_univ, true_and] using ha
      simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
        using ha'.trans htρ
    let Q : Fin N → Assignment N → ℝ := fun k =>
      conditionOn pp (ball D k t) (R k)
    let E : Fin N → Assignment N → ℝ := fun k z =>
      X k z - conditionOn pp (ball D k t) (X k) z
    have hQform (k : Fin N) : Q k = fun z =>
        conditionOn pp (ball D k t) (X k) z -
          conditionOn pp (ball D k ρ) (X k) z := by
      funext z
      change conditionOn pp (ball D k t)
        (fun z => X k z - conditionOn pp (ball D k ρ) (X k) z) z = _
      rw [(FiniteConditioning.fc2_proof pp hadm (ball D k t)).2.2.1
        (X k) (conditionOn pp (ball D k ρ) (X k)) z]
      rw [congrFun ((FiniteConditioning.fc4_proof pp hadm
        (ball D k ρ) (ball D k t) (hballs k) (X k)).1) z]
    have hdecomp (k : Fin N) (z : Assignment N) : R k z = E k z + Q k z := by
      rw [hQform k]
      dsimp only [R, E]
      ring
    have hQmean (k : Fin N) : expect pp (Q k) = 0 :=
      (FiniteConditioning.fc3_proof pp hadm (ball D k t) (R k)).trans (hRmean k)
    have hQnorm (k : Fin N) : l2Norm pp (Q k) ≤ b :=
      (FiniteConditioning.fc6_proof pp hadm (ball D k t) (R k)).1.trans (hRnorm k)
    have hEnorm (k : Fin N) : l2Norm pp (E k) ≤ b * c := by
      calc
        l2Norm pp (E k) ≤ Kc * ψ t := hF.hNED k t ht0
        _ ≤ Kc * (A * t ^ (-e)) :=
          mul_le_mul_of_nonneg_left (hF.henv t ht1) hF.hKc
        _ = b * c := by rw [htpow]; dsimp only [b]; ring
    have hdisjoint : Disjoint (ball D i t : Set (Fin N))
        (ball D j t : Set (Fin N)) := by
      apply Set.disjoint_left.2
      intro k hki hkj
      have hi : D i k ≤ t := by simpa only [Finset.mem_coe, ball, Finset.mem_filter,
        Finset.mem_univ, true_and] using hki
      have hj : D j k ≤ t := by simpa only [Finset.mem_coe, ball, Finset.mem_filter,
        Finset.mem_univ, true_and] using hkj
      have ht := hF.hD.2.2.2 i k j
      rw [hF.hD.2.2.1 k j] at ht
      dsimp only [t] at hi hj
      linarith
    have hQi : DependsOn (Q i) (ball D i t : Set (Fin N)) := by
      intro z z' hz
      exact FiniteConditioning.fc1_proof pp (ball D i t) (R i) z z' hz
    have hQj : DependsOn (Q j) ((ball D i t : Set (Fin N))ᶜ) := by
      intro z z' hz
      apply FiniteConditioning.fc1_proof pp (ball D j t) (R j) z z'
      intro k hk
      apply hz k
      change k ∉ (ball D i t : Set (Fin N))
      intro hi
      exact Set.disjoint_left.mp hdisjoint hi hk
    have hQQ : expect pp (fun z => Q i z * Q j z) = 0 := by
      rw [GraphCompletion.expect_mul_of_disjoint_depends pp
        (ball D i t : Set (Fin N)) (Q i) (Q j) hQi hQj, hQmean i, zero_mul]
    have hproduct : (fun z => R i z * R j z) = fun z =>
        E i z * R j z + Q i z * E j z + Q i z * Q j z := by
      funext z
      rw [hdecomp i z, hdecomp j z]
      ring
    have hcovexpand : cov pp (R i) (R j) =
        expect pp (fun z => E i z * R j z) + expect pp (fun z => Q i z * E j z) := by
      unfold cov
      rw [hRmean i, hRmean j, zero_mul, sub_zero, hproduct,
        expect_add, expect_add, hQQ, add_zero]
    calc
      |cov pp (R i) (R j)| =
          |expect pp (fun z => E i z * R j z) + expect pp (fun z => Q i z * E j z)| :=
        congrArg abs hcovexpand
      _ ≤ |expect pp (fun z => E i z * R j z)| +
          |expect pp (fun z => Q i z * E j z)| := abs_add_le _ _
      _ ≤ l2Norm pp (E i) * l2Norm pp (R j) +
          l2Norm pp (Q i) * l2Norm pp (E j) := add_le_add (hCS _ _) (hCS _ _)
      _ ≤ (b * c) * b + b * (b * c) := add_le_add
        (mul_le_mul (hEnorm i) (hRnorm j) (hnonneg _) (mul_nonneg hb hc))
        (mul_le_mul (hQnorm i) (hEnorm j) (hnonneg _) hb)
      _ = 2 * B * (D i j / (3 * ρ)) ^ (-e) := by dsimp only [B, c]; ring

  have hpower : ρ^2 * (ρ ^ (-e))^2 = ρ ^ (2 - 2 * e) := by
    rw [← Real.rpow_two ρ, ← Real.rpow_mul_natCast hρ0 (-e) 2,
      ← Real.rpow_add hρpos]
    congr 1
    ring
  have hbase : ρ^2 * B = Kc^2 * A^2 * ρ ^ (2 - 2 * e) := by
    calc
      ρ^2 * B = Kc^2 * A^2 * (ρ^2 * (ρ ^ (-e))^2) := by
        dsimp only [B, b]
        ring
      _ = Kc^2 * A^2 * ρ ^ (2 - 2 * e) := by rw [hpower]
  have hrow (i : Fin N) : (∑ j, |cov pp (R i) (R j)|) ≤
      Cb * Kc^2 * A^2 * (10 + 74 / (1 - (2 : ℝ) ^ (2 - e))) *
        ρ ^ (2 - 2 * e) := by
    have hcard : ((ball D i (3 * ρ)).card : ℝ) ≤ 10 * Cb * ρ^2 := by
      calc
        ((ball D i (3 * ρ)).card : ℝ) ≤ Cb * (1 + (3 * ρ)^2) :=
          hF.hspacing i (3 * ρ) (by positivity)
        _ ≤ Cb * (10 * ρ^2) := by
          apply mul_le_mul_of_nonneg_left _ hF.hCb.le
          nlinarith [sq_nonneg (ρ - 1)]
        _ = 10 * Cb * ρ^2 := by ring
    have hnearSum : (∑ j ∈ ball D i (3 * ρ), |cov pp (R i) (R j)|) ≤
        10 * Cb * ρ^2 * B := by
      calc
        _ ≤ ∑ _j ∈ ball D i (3 * ρ), B :=
          Finset.sum_le_sum (fun j _ => hnear i j)
        _ = ((ball D i (3 * ρ)).card : ℝ) * B := by simp
        _ ≤ 10 * Cb * ρ^2 * B := mul_le_mul_of_nonneg_right hcard hB
    have hfarSum :
        (∑ j ∈ Finset.univ.filter (fun j => 3 * ρ < D i j), |cov pp (R i) (R j)|) ≤
          37 * Cb * ρ^2 * (2 * B) / (1 - (2 : ℝ) ^ (2 - e)) :=
      dy_proof D i Cb ρ e (2 * B) (fun j => |cov pp (R i) (R j)|)
        hF.hCb hρ hF.he (by positivity) (hF.hspacing i)
        (fun j hj => ⟨abs_nonneg _, hfar i j hj⟩)
    have hsplit : (∑ j, |cov pp (R i) (R j)|) =
        (∑ j ∈ ball D i (3 * ρ), |cov pp (R i) (R j)|) +
          ∑ j ∈ Finset.univ.filter (fun j => 3 * ρ < D i j), |cov pp (R i) (R j)| := by
      simpa only [ball, not_le] using
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun j => D i j ≤ 3 * ρ) (fun j => |cov pp (R i) (R j)|)).symm
    calc
      _ = _ := hsplit
      _ ≤ 10 * Cb * ρ^2 * B +
          37 * Cb * ρ^2 * (2 * B) / (1 - (2 : ℝ) ^ (2 - e)) :=
        add_le_add hnearSum hfarSum
      _ = Cb * (10 + 74 / (1 - (2 : ℝ) ^ (2 - e))) * (ρ^2 * B) := by ring
      _ = Cb * Kc^2 * A^2 * (10 + 74 / (1 - (2 : ℝ) ^ (2 - e))) *
          ρ ^ (2 - 2 * e) := by rw [hbase]; ring

  have hsumMean : expect pp (fun z => ∑ i, R i z) = 0 := by
    rw [expect_sum]
    simp only [hRmean, Finset.sum_const_zero]
  have hsecond : expect pp (fun z => (∑ i, R i z)^2) =
      variance pp (fun z => ∑ i, R i z) := by
    simp only [variance, cov, hsumMean, zero_mul, sub_zero, pow_two]
  change expect pp (fun z => (∑ i, R i z)^2) ≤ _
  rw [hsecond, variance_sum]
  calc
    (∑ i, ∑ j, cov pp (R i) (R j)) ≤ ∑ i, ∑ j, |cov pp (R i) (R j)| :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => le_abs_self _))
    _ ≤ ∑ _i : Fin N,
        Cb * Kc^2 * A^2 * (10 + 74 / (1 - (2 : ℝ) ^ (2 - e))) *
          ρ ^ (2 - 2 * e) := Finset.sum_le_sum (fun i _ => hrow i)
    _ = N * (Cb * Kc^2 * A^2 * (10 + 74 / (1 - (2 : ℝ) ^ (2 - e))) *
        ρ ^ (2 - 2 * e)) := by simp

end
end AronowAudit.P004.Wave1.NedHeadline
