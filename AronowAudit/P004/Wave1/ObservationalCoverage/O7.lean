import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import AronowAudit.P004.Wave1.ObservationalCoverage.O5
import AronowAudit.P004.Wave1.LinePopulation.N1

/-! The actual footnote-9 coefficient and doubly weighted printed SAH statistic.
The restriction to `3 ≤ N` is essential. -/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

theorem active_fitted_beta (N : ℕ) (hN : 3 ≤ N) (z : Assignment N) (a : Bool) :
    fittedBeta (propensities (activeO N) (activeMLE N z))
      (activeTable N) (activeO N) a z =
      ![if a then SAct N z / (nH N * pHatH N z) else 0, 0] := by
  let q := pHatH N z
  let r := pHatL N z
  let p : Fin N → ℝ := fun i => if activeGroup N i then q else r
  have hq : 0 < q ∧ q < 1 := pHatH_mem N z
  have hr : 0 < r ∧ r < 1 := pHatL_mem N z
  have hrow0 (i : Fin N) :
      (if z i = a then activeTable N i z * coin (p i) (!a) * activeO N i 0 else 0) =
      if a then activeSign N i * bit (z i) * (1 - q) else 0 := by
    by_cases hi : activeGroup N i
    · cases a <;> cases hz : z i <;>
        simp [p, activeO, hi, activeTable_eq_sign, coin, bit, hz]
    · cases a <;> cases hz : z i <;>
        simp [p, activeO, hi, activeTable_eq_sign, activeSign_of_not_group i hi,
          coin, bit, hz]
  have hrow1 (i : Fin N) :
      (if z i = a then activeTable N i z * coin (p i) (!a) * activeO N i 1 else 0) = 0 := by
    by_cases hi : activeGroup N i
    · cases a <;> cases hz : z i <;>
        simp [p, activeO, hi, activeTable_eq_sign, coin, bit, hz]
    · cases a <;> cases hz : z i <;>
        simp [p, activeO, hi, activeTable_eq_sign, activeSign_of_not_group i hi,
          coin, bit, hz]
  have hvec : (fun j : Fin 2 =>
      (∑ i : Fin N, if z i = a then activeTable N i z * coin (p i) (!a) * activeO N i j
        else 0) / N) = ![if a then SAct N z * (1 - q) / N else 0, 0] := by
    funext j
    fin_cases j
    · change (∑ i : Fin N, _) / (N : ℝ) = if a then SAct N z * (1 - q) / N else 0
      simp only [Fin.zero_eta, Fin.isValue]
      simp_rw [hrow0]
      cases a
      · simp
      · change (∑ i : Fin N, activeSign N i * bit (z i) * (1 - q)) / (N : ℝ) =
          SAct N z * (1 - q) / N
        rw [← Finset.sum_mul]
        rfl
    · change (∑ i : Fin N, _) / (N : ℝ) = 0
      simp only [Fin.mk_one, Fin.isValue, hrow1, Finset.sum_const_zero, zero_div]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hH : nH N ≠ 0 := (nH_pos (by omega : 0 < N)).ne'
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  rw [active_fitted_propensities hN z]
  change fittedBeta p (activeTable N) (activeO N) a z = _
  unfold fittedBeta
  rw [hvec, active_information_inverse N hN q r hq hr]
  have hq0' : pHatH N z ≠ 0 := hq0
  have hq1' : 1 - pHatH N z ≠ 0 := hq1
  ext j
  fin_cases j <;> cases a <;>
    norm_num [Matrix.mulVec, dotProduct, Matrix.diagonal, Fin.sum_univ_two]
  all_goals
    try simp only [q]
    field_simp [hNr, hH, hq0', hq1']
    try ring

theorem active_fitted_fit (N : ℕ) (hN : 3 ≤ N) (z : Assignment N) (i : Fin N) (a : Bool) :
    dot (activeO N i)
      (fittedBeta (propensities (activeO N) (activeMLE N z))
        (activeTable N) (activeO N) a z) =
      if activeGroup N i then (if a then SAct N z / (nH N * pHatH N z) else 0) else 0 := by
  rw [active_fitted_beta N hN z a]
  by_cases hi : activeGroup N i <;> simp [dot, activeO, hi, Fin.sum_univ_two]

theorem active_zero_neighborhood (N : ℕ) (i : Fin N) :
    spatialNeighborhoods activePopulation 0 N i = {i} := by
  change ball (nodeSeparation (linePopulation (activeTable N))) i 0 = {i}
  ext j
  simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [LinePopulation.n1_proof (activeTable N) i j]
  constructor
  · intro hij
    have hz : |(i : ℝ) - (j : ℝ)| = 0 := by
      nlinarith [abs_nonneg ((i : ℝ) - (j : ℝ))]
    have he : (i : ℝ) = (j : ℝ) := sub_eq_zero.mp (abs_eq_zero.mp hz)
    apply Fin.ext
    exact_mod_cast he.symm
  · intro hji
    subst j
    simp

theorem o7_proof : O7 := by
  intro N hN z
  let p : Fin N → ℝ := propensities (activeO N) (activeMLE N z)
  let g : Fin N → Bool → ℝ := fun i a =>
    dot (activeO N i) (fittedBeta p (activeTable N) (activeO N) a z)
  let q := pHatH N z
  let Q := armCount z true / (N : ℝ)
  let b := SAct N z / (nH N * pHatH N z)
  let w : Fin N → ℝ := fun i =>
    if activeGroup N i then bit (z i) * (activeSign N i - b)^2 else 0
  have hp : p = fun i => if activeGroup N i then q else pHatL N z :=
    active_fitted_propensities hN z
  have hg (i : Fin N) (a : Bool) :
      g i a = if activeGroup N i then (if a then b else 0) else 0 :=
    active_fitted_fit N hN z i a
  have hq0 : q ≠ 0 := (pHatH_mem N z).1.ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hterm (i : Fin N) :
      ((spatialNeighborhoods activePopulation 0 N i).card : ℝ) *
        (bit (z i) * (weightedEpsilon p (activeTable N) g z i)^2 / (p i)^2 +
          (1 - bit (z i)) * (weightedEpsilon p (activeTable N) g z i)^2 / (1 - p i)^2) =
      Q^2 / q^4 * w i := by
    rw [active_zero_neighborhood N i]
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    by_cases hi : activeGroup N i
    · have hpi : p i = q := by rw [hp]; simp only [if_pos hi]
      cases hz : z i <;>
        simp [weightedEpsilon, hg, hpi, activeTable_eq_sign, hi, hz, bit, Q, w]
      field_simp [hq0, hNr]
      <;> ring
    · simp [weightedEpsilon, hg, activeTable_eq_sign,
        activeSign_of_not_group i hi, hi, w]
  change printedSAH p (activeTable N) (spatialNeighborhoods activePopulation 0 N) g z =
    Q^2 * RAct N z / ((N : ℝ)^2 * q^4)
  unfold printedSAH
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hR : (∑ i : Fin N, w i) = RAct N z := rfl
  rw [hR]
  field_simp [hq0, hNr]
  <;> ring

end
end AronowAudit.P004.Wave1.ObservationalCoverage
