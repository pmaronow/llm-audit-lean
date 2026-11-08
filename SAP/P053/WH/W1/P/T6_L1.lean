import SAP.P053.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P053.WH.W1.P.T6_L1

open scoped BigOperators

private theorem sum_zero_indicator (N : ℕ) (hN : 0 < N) :
    (∑ i : Fin N, (if i.val = 0 then (1 : ℝ) else 0)) = 1 := by
  classical
  let z : Fin N := ⟨0, hN⟩
  rw [Finset.sum_eq_single z]
  · simp [z]
  · intro i hi hne
    have hiv : i.val ≠ 0 := by
      intro hv
      exact hne (Fin.ext hv)
    simp [hiv]
  · intro h
    exact (h (Finset.mem_univ z)).elim

private theorem sum_zero_indicator_sq (N : ℕ) (hN : 0 < N) :
    (∑ i : Fin N, (if i.val = 0 then (1 : ℝ) else 0)^2) = 1 := by
  calc
    _ = ∑ i : Fin N, (if i.val = 0 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> norm_num
    _ = 1 := sum_zero_indicator N hN

private theorem sum_zero_indicator_fourth (N : ℕ) (hN : 0 < N) :
    (∑ i : Fin N, (if i.val = 0 then (1 : ℝ) else 0)^4) = 1 := by
  calc
    _ = ∑ i : Fin N, (if i.val = 0 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> norm_num
    _ = 1 := sum_zero_indicator N hN

end SAP.P053.WH.W1.P.T6_L1

open SAP.P053.WH.W1.P.T6_L1
open scoped BigOperators

theorem SAP.P053.WH.W1.T6_L1_proof : SAP.P053.WH.W1.T6_L1 := by
  intro k
  let N : ℕ := (k + 2) + (k + 2)
  have hN : 0 < N := by dsimp [N]; omega
  have h1 : (∑ i ∈ (Finset.univ : Finset (Fin N)),
      (if i.val = 0 then (1 : ℝ) else 0)) = 1 := by
    simpa using sum_zero_indicator N hN
  have h2 : (∑ i ∈ (Finset.univ : Finset (Fin N)),
      (if i.val = 0 then (1 : ℝ) else 0)^2) = 1 := by
    simpa using sum_zero_indicator_sq N hN
  have h4 : (∑ i ∈ (Finset.univ : Finset (Fin N)),
      (if i.val = 0 then (1 : ℝ) else 0)^4) = 1 := by
    simpa using sum_zero_indicator_fourth N hN
  have hc : ((Finset.univ : Finset (Fin N)).card : ℝ) = (N : ℝ) := by simp
  have hNcast : (N : ℝ) = 2 * ((k : ℝ) + 2) := by
    dsimp [N]
    push_cast
    ring
  have hvar : populationVariance (sparsePopulationW1 k)
      (fun i : Fin N => if i.val = 0 then (1 : ℝ) else 0) = 1 / (N : ℝ) := by
    change sampleVariance (Finset.univ : Finset (Fin N))
      (fun i : Fin N => if i.val = 0 then (1 : ℝ) else 0) = 1 / (N : ℝ)
    unfold sampleVariance
    change AronowAudit.P053.centeredSS (Finset.univ : Finset (Fin N))
      (fun i : Fin N => if i.val = 0 then (1 : ℝ) else 0) /
      (((Finset.univ : Finset (Fin N)).card : ℝ) - 1) = 1 / (N : ℝ)
    rw [AronowAudit.P053.centeredSS_raw
      (s := (Finset.univ : Finset (Fin N)))
      (y := fun i : Fin N => if i.val = 0 then (1 : ℝ) else 0)
      (by simp [hN])]
    rw [h2, h1, hc]
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hNm1 : (N : ℝ) - 1 ≠ 0 := by
      have hgt : 1 < N := by dsimp [N]; omega
      exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hgt))
    field_simp [hNreal, hNm1]
    <;> ring
  have hfourth : (∑ i : Fin N,
      ((if i.val = 0 then (1 : ℝ) else 0)^4 +
       (if i.val = 0 then (1 : ℝ) else 0)^4)) = 2 := by
    rw [Finset.sum_add_distrib, sum_zero_indicator_fourth N hN]
    norm_num
  change populationVariance (sparsePopulationW1 k)
      (fun i : Fin N => if i.val = 0 then (1 : ℝ) else 0) =
        1 / (2 * ((k : ℝ) + 2)) ∧
    (∑ i : Fin N, ((if i.val = 0 then (1 : ℝ) else 0)^4 +
      (if i.val = 0 then (1 : ℝ) else 0)^4)) / (N : ℝ) =
        1 / ((k : ℝ) + 2)
  constructor
  · rw [hvar, hNcast]
  · rw [hfourth, hNcast]
    have hn : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp
