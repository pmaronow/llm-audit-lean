import SAP.P046.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W1.P.T4_L1

open Finset
open scoped BigOperators

lemma weight_formula (w : ℝ) :
    wholeWeight w = if w ≤ 1 / 2 then 12 else 4 / 9 := by
  by_cases h : w ≤ 1 / 2
  · rw [if_pos h]
    unfold wholeWeight
    rw [RegressionExample.score, RegressionExample.scoreL, decide_eq_true h]
    norm_num
  · rw [if_neg h]
    unfold wholeWeight
    rw [RegressionExample.score, RegressionExample.scoreL,
      (decide_eq_false_iff_not).2 h]
    norm_num

lemma row_formula {n : ℕ} (w : Fin n → ℝ) (z x : Fin n → Bool)
    (i : Fin n) (theta : ℝ) :
    X (wholeRegressionSample w z x i) *
        (1 - RegressionExample.study.pi (W (wholeRegressionSample w z x i))) /
          (RegressionExample.study.pi (W (wholeRegressionSample w z x i))) ^ 2 *
        (Y (wholeRegressionSample w z x i) -
          RegressionExample.prediction theta (W (wholeRegressionSample w z x i))) ^ 2 =
      (if w i ≤ 1 / 2 then 12 * bit (x i) * (bit (z i) - 1 / 2) ^ 2 else 0) +
        (if 1 / 2 < w i ∧ x i = true then (4 / 9 : ℝ) * theta ^ 2 else 0) := by
  by_cases hw : w i ≤ 1 / 2
  · have hw' : w i ≤ (2 : ℝ)⁻¹ := by simpa only [one_div] using hw
    have hnotlt' : ¬ (2 : ℝ)⁻¹ < w i := not_lt.mpr hw'
    have hd : decide (w i ≤ (1 / 2 : ℝ)) = true := decide_eq_true hw
    cases hz : z i <;> cases hx : x i <;>
      simp [wholeRegressionSample, W, RegressionExample.study, RegressionExample.score,
        RegressionExample.scoreL, RegressionExample.prediction,
        RegressionExample.predictionL, X, Y, Y0, Y1, bit, hd, hw', hnotlt', hz, hx] <;>
        norm_num <;> ring
  · have hw' : ¬ w i ≤ (2 : ℝ)⁻¹ := by simpa only [one_div] using hw
    have hlt : (1 / 2 : ℝ) < w i := not_le.mp hw
    have hd : decide (w i ≤ (1 / 2 : ℝ)) = false :=
      (decide_eq_false_iff_not).2 hw
    have hlt' : (2 : ℝ)⁻¹ < w i := lt_of_not_ge hw'
    cases hz : z i <;> cases hx : x i <;>
      simp [wholeRegressionSample, W, RegressionExample.study, RegressionExample.score,
        RegressionExample.scoreL, RegressionExample.prediction,
        RegressionExample.predictionL, X, Y, Y0, Y1, bit, hd, hw', hlt, hlt', hz, hx] <;>
        norm_num <;> ring

lemma low_sum {n : ℕ} (T : Finset (Fin n)) (w : Fin n → ℝ) (z x : Fin n → Bool) :
    (∑ i ∈ T, if w i ≤ 1 / 2 then
      12 * bit (x i) * (bit (z i) - 1 / 2) ^ 2 else 0) =
      wholeTrainingConstant T w z x := by
  calc
    (∑ i ∈ T, if w i ≤ 1 / 2 then
        12 * bit (x i) * (bit (z i) - 1 / 2) ^ 2 else 0) =
      ∑ i ∈ T.filter (fun i => w i ≤ 1 / 2),
        12 * bit (x i) * (bit (z i) - 1 / 2) ^ 2 := by
          rw [← Finset.sum_filter]
    _ = wholeTrainingConstant T w z x := by
      simpa [wholeTrainingConstant, mul_assoc] using
        (Finset.mul_sum (T.filter (fun i => w i ≤ 1 / 2))
          (fun i => bit (x i) * (bit (z i) - 1 / 2) ^ 2) (12 : ℝ)).symm

lemma high_count {n : ℕ} (T : Finset (Fin n)) (w : Fin n → ℝ) (x : Fin n → Bool)
    (theta : ℝ) :
    (∑ i ∈ T, if 1 / 2 < w i ∧ x i = true then
      (4 / 9 : ℝ) * theta ^ 2 else 0) =
      (4 / 9 : ℝ) * wholeUpperTreated T w x * theta ^ 2 := by
  classical
  calc
    (∑ i ∈ T, if 1 / 2 < w i ∧ x i = true then
        (4 / 9 : ℝ) * theta ^ 2 else 0) =
      ∑ i ∈ T.filter (fun i => 1 / 2 < w i ∧ x i = true),
        (4 / 9 : ℝ) * theta ^ 2 := by rw [← Finset.sum_filter]
    _ = ((T.filter (fun i => 1 / 2 < w i ∧ x i = true)).card : ℝ) *
        ((4 / 9 : ℝ) * theta ^ 2) := by simp
    _ = (4 / 9 : ℝ) * wholeUpperTreated T w x * theta ^ 2 := by
      simp [wholeUpperTreated]
      ring

end SAP.P046.WH.W1.P.T4_L1

theorem SAP.P046.WH.W1.T4_L1_proof : SAP.P046.WH.W1.T4_L1 := by
  change WholeT4Training
  constructor
  · exact SAP.P046.WH.W1.P.T4_L1.weight_formula
  · intro n T w z x
    have hformula : ∀ theta : ℝ,
        empiricalRisk RegressionExample.study T (wholeRegressionSample w z x)
          (RegressionExample.prediction theta) =
        wholeTrainingConstant T w z x +
          (4 / 9 : ℝ) * wholeUpperTreated T w x * theta ^ 2 := by
      intro theta
      calc
        empiricalRisk RegressionExample.study T (wholeRegressionSample w z x)
            (RegressionExample.prediction theta) =
          ∑ i ∈ T, (
            (if w i ≤ 1 / 2 then 12 * bit (x i) * (bit (z i) - 1 / 2) ^ 2 else 0) +
              (if 1 / 2 < w i ∧ x i = true then (4 / 9 : ℝ) * theta ^ 2 else 0)) := by
                unfold empiricalRisk
                apply Finset.sum_congr rfl
                intro i hi
                exact SAP.P046.WH.W1.P.T4_L1.row_formula w z x i theta
        _ = wholeTrainingConstant T w z x +
            (4 / 9 : ℝ) * wholeUpperTreated T w x * theta ^ 2 := by
              rw [Finset.sum_add_distrib,
                SAP.P046.WH.W1.P.T4_L1.low_sum,
                SAP.P046.WH.W1.P.T4_L1.high_count]
    constructor
    · exact hformula
    · constructor
      · intro theta
        rw [hformula 0, hformula theta]
        have hN : (0 : ℝ) ≤ (wholeUpperTreated T w x : ℝ) := Nat.cast_nonneg _
        nlinarith [sq_nonneg theta, hN]
      · intro theta
        rw [hformula theta, hformula 0]
        constructor
        · intro heq
          by_cases hN : wholeUpperTreated T w x = 0
          · exact Or.inl hN
          · right
            have hNpos : (0 : ℝ) < wholeUpperTreated T w x :=
              Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
            by_contra hθ
            have hθpos : (0 : ℝ) < theta ^ 2 := sq_pos_of_ne_zero hθ
            have hprod : 0 < (4 / 9 : ℝ) * wholeUpperTreated T w x * theta ^ 2 := by
              positivity
            linarith
        · rintro (hN | hθ)
          · simp [hN]
          · simp [hθ]
