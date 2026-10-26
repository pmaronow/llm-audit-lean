import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import AronowAudit.P004.Wave1.ObservationalCoverage.O6
import AronowAudit.P004.Wave1.LinePopulation.N3

/-! Population projection and the actual augmented-variance guard. All matrix inverse
identities below require both columns to be present. -/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

/-- Information for two indicator columns, for arbitrary group probabilities. -/
theorem active_information (N : ℕ) (q r : ℝ) :
    information (fun i => if activeGroup N i then q else r) (activeO N) =
      Matrix.diagonal ![nH N * q * (1 - q) / N, nL N * r * (1 - r) / N] := by
  ext a b
  fin_cases a <;> fin_cases b
  · change (∑ i : Fin N, _) / (N : ℝ) = nH N * q * (1 - q) / N
    congr 1
    calc
      _ = ∑ i : Fin N, if activeGroup N i then q * (1 - q) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : activeGroup N i <;> simp [activeO, hi]
      _ = _ := by rw [sum_active_const]; ring
  · change (∑ i : Fin N, _) / (N : ℝ) = 0
    have hzero (i : Fin N) :
        (if activeGroup N i then q else r) *
          (1 - if activeGroup N i then q else r) * activeO N i 0 * activeO N i 1 = 0 := by
      by_cases hi : activeGroup N i <;> simp [activeO, hi]
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, hzero, Finset.sum_const_zero, zero_div]
  · change (∑ i : Fin N, _) / (N : ℝ) = 0
    have hzero (i : Fin N) :
        (if activeGroup N i then q else r) *
          (1 - if activeGroup N i then q else r) * activeO N i 1 * activeO N i 0 = 0 := by
      by_cases hi : activeGroup N i <;> simp [activeO, hi]
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, hzero, Finset.sum_const_zero, zero_div]
  · change (∑ i : Fin N, _) / (N : ℝ) = nL N * r * (1 - r) / N
    congr 1
    calc
      _ = ∑ i : Fin N, if activeGroup N i then 0 else r * (1 - r) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : activeGroup N i <;> simp [activeO, hi]
      _ = _ := by rw [sum_inactive_const]; ring

/-- Checking a left inverse explicitly avoids confusing `Ring.inverse` on a function
ring with coordinatewise inversion when a group is absent. -/
theorem active_information_inverse (N : ℕ) (hN : 3 ≤ N) (q r : ℝ)
    (hq : 0 < q ∧ q < 1) (hr : 0 < r ∧ r < 1) :
    (information (fun i => if activeGroup N i then q else r) (activeO N))⁻¹ =
      Matrix.diagonal ![(nH N * q * (1 - q) / N)⁻¹,
        (nL N * r * (1 - r) / N)⁻¹] := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hH : nH N ≠ 0 := (nH_pos (by omega : 0 < N)).ne'
  have hL : nL N ≠ 0 := (nL_pos hN).ne'
  have hq0 : q ≠ 0 := hq.1.ne'
  have hr0 : r ≠ 0 := hr.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  have hr1 : 1 - r ≠ 0 := (sub_pos.mpr hr.2).ne'
  have hdH : nH N * q * (1 - q) / (N : ℝ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero hH hq0) hq1) hNr
  have hdL : nL N * r * (1 - r) / (N : ℝ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero hL hr0) hr1) hNr
  rw [active_information]
  apply Matrix.inv_eq_left_inv
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_two, hdH, hdL] <;>
    field_simp

theorem active_population_beta (N : ℕ) (hN : 3 ≤ N) (q r : ℝ)
    (hq : 0 < q ∧ q < 1) (hr : 0 < r ∧ r < 1) (a : Bool) :
    beta (fun i => if activeGroup N i then q else r) (activeTable N) (activeO N) a =
      ![bit a * sAct N / nH N, 0] := by
  let p : Fin N → ℝ := fun i => if activeGroup N i then q else r
  have hp : ∀ i, 0 < p i ∧ p i < 1 := by
    intro i
    dsimp only [p]
    split_ifs <;> assumption
  have hvec : (fun j : Fin 2 =>
      (∑ i : Fin N, marginal p (activeTable N) i a * p i * (1 - p i) * activeO N i j) / N) =
      ![bit a * sAct N * q * (1 - q) / N, 0] := by
    funext j
    fin_cases j
    · change (∑ i : Fin N, _) / (N : ℝ) = bit a * sAct N * q * (1 - q) / N
      congr 1
      calc
        _ = ∑ i : Fin N, bit a * activeSign N i * q * (1 - q) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [active_marginal p hp i a]
          by_cases hi : activeGroup N i
          · simp only [p, if_pos hi, activeO, Fin.zero_eta, Matrix.cons_val_zero]
            ring
          · simp [p, activeO, hi, activeSign_of_not_group i hi]
        _ = bit a * sAct N * q * (1 - q) := by
          simp only [sAct, Finset.mul_sum, Finset.sum_mul]
    · change (∑ i : Fin N, _) / (N : ℝ) = 0
      have hzero (i : Fin N) :
          marginal p (activeTable N) i a * p i * (1 - p i) * activeO N i 1 = 0 := by
        rw [active_marginal p hp i a]
        by_cases hi : activeGroup N i
        · simp [activeO, hi]
        · simp [activeSign_of_not_group i hi]
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, hzero, Finset.sum_const_zero, zero_div]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hH : nH N ≠ 0 := (nH_pos (by omega : 0 < N)).ne'
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  change beta p (activeTable N) (activeO N) a = _
  unfold beta
  rw [hvec, active_information_inverse N hN q r hq hr]
  ext j
  fin_cases j <;>
    norm_num [Matrix.mulVec, dotProduct, Matrix.diagonal, Fin.sum_univ_two]
  field_simp [hNr, hH, hq0, hq1]
  <;> ring

theorem active_printedFits (N : ℕ) (hN : 3 ≤ N) (i : Fin N) (a : Bool) :
    printedFits (propensities (activeO N) activeTheta) (activeTable N) (activeO N) i a =
      if activeGroup N i then bit a * (sAct N / nH N) else 0 := by
  unfold printedFits
  rw [o4_proof N, active_population_beta N hN (1/2) (1/10) (by norm_num) (by norm_num)]
  by_cases hi : activeGroup N i <;>
    simp [activeO, hi, dot, Fin.sum_univ_two, mul_div_assoc]

/-- The centered sum of squares, including the nonzero partial-block sum `s`. -/
theorem active_residual_square_sum (N : ℕ) (hN : 0 < N) :
    (∑ i : Fin N, if activeGroup N i then (activeSign N i - sAct N / nH N)^2 else 0) =
      nH N - (sAct N)^2 / nH N := by
  let δ := sAct N / nH N
  have hrow (i : Fin N) :
      (if activeGroup N i then (activeSign N i - δ)^2 else 0) =
        (activeSign N i)^2 - 2 * δ * activeSign N i +
          (if activeGroup N i then δ^2 else 0) := by
    by_cases hi : activeGroup N i
    · simp only [if_pos hi]
      ring
    · simp [if_neg hi, activeSign_of_not_group i hi]
  change (∑ i : Fin N, if activeGroup N i then (activeSign N i - δ)^2 else 0) = _
  calc
    _ = nH N - 2 * δ * sAct N + nH N * δ^2 := by
      simp_rw [hrow]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_activeSign_sq, sum_active_const]
      rfl
    _ = _ := by
      dsimp only [δ]
      field_simp [(nH_pos hN).ne']
      <;> ring

theorem active_augmented_variance (N : ℕ) (hN : 3 ≤ N) :
    variance (propensities (activeO N) activeTheta)
      (augmented (propensities (activeO N) activeTheta) (activeTable N)
        (printedFits (propensities (activeO N) activeTheta) (activeTable N) (activeO N))) =
      (nH N - (sAct N)^2 / nH N) / (N : ℝ)^2 := by
  let δ := sAct N / nH N
  let f : Fin N → Bool → ℝ := fun i b =>
    if activeGroup N i then δ + 2 * bit b * (activeSign N i - δ) else 0
  have haug :
      augmented (propensities (activeO N) activeTheta) (activeTable N)
        (printedFits (propensities (activeO N) activeTheta) (activeTable N) (activeO N)) =
      fun z => (∑ i : Fin N, f i (z i)) / (N : ℝ) := by
    funext z
    unfold augmented
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [active_printedFits N hN i true, active_printedFits N hN i false, o4_proof N]
    by_cases hi : activeGroup N i
    · cases hz : z i <;>
        simp [f, δ, activeTable_eq_sign, hi, hz, bit] <;> ring
    · simp [f, activeTable_eq_sign, hi, activeSign_of_not_group i hi]
  rw [haug, variance_div, own_sum_variance]
  congr 1
  calc
    _ = ∑ i : Fin N, if activeGroup N i then (activeSign N i - δ)^2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [o4_proof N]
      by_cases hi : activeGroup N i
      · norm_num [f, hi, bit]
        <;> ring
      · simp [f, hi]
    _ = nH N - (sAct N)^2 / nH N := active_residual_square_sum N (by omega)

theorem o5_proof : O5 := by
  refine ⟨1/8, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 16] with N hN
  have h3 : 3 ≤ N := by omega
  have hcircle : circleAverage (activePopulation N) 0 = activeTable N := by
    exact LinePopulation.n3_proof (activeTable N)
  rw [hcircle, active_augmented_variance N h3]
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h16 : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hH : 0 < nH N := nH_pos (by omega)
  have hHlower : (N : ℝ) / 4 ≤ nH N := nH_ge_quarter N
  have hs : (sAct N)^2 ≤ 1 := sAct_sq_le_one N
  have hcorr : (sAct N)^2 / nH N ≤ 1/4 := by
    apply (div_le_iff₀ hH).mpr
    nlinarith
  have hcancel : (N : ℝ) * ((nH N - (sAct N)^2 / nH N) / (N : ℝ)^2) =
      (nH N - (sAct N)^2 / nH N) / N := by
    field_simp [hNr.ne']
    <;> ring
  rw [hcancel]
  apply (le_div_iff₀ hNr).mpr
  linarith

end
end AronowAudit.P004.Wave1.ObservationalCoverage
