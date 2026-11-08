import SAP.P053.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P053.WH.W1.P.T2_L1

open SAP.P053
open scoped BigOperators
noncomputable section

def outcome (m : ℕ) : Fin (2*m + 2*m) → ℝ :=
  fun i => binaryReal (repeatY m (repeatedEquivW1 m i))

theorem sum_repeated (m : ℕ) (f : Fin 4 → ℝ) :
    (∑ i : Fin (2*m + 2*m), f (repeatedEquivW1 m i).2) =
      (m : ℝ) * ∑ j : Fin 4, f j := by
  rw [Equiv.sum_comp (repeatedEquivW1 m) (fun i : Fin m × Fin 4 => f i.2)]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_const, Fintype.card_fin]

theorem centeredSS_raw_local {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (hs : s.card ≠ 0) :
    centeredSS s f = (∑ i ∈ s, (f i)^2) - (∑ i ∈ s, f i)^2/(s.card : ℝ) := by
  have hsr : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
  calc
    centeredSS s f = ∑ i ∈ s,
        ((f i)^2 - 2 * sampleMean s f * f i + (sampleMean s f)^2) := by
      unfold centeredSS
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ s, (f i)^2) - 2 * sampleMean s f * (∑ i ∈ s, f i) +
        (s.card : ℝ) * (sampleMean s f)^2 := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by unfold sampleMean; field_simp; ring

theorem base_power_sum (q : ℕ) (hq : q ≠ 0) :
    (∑ j : Fin 4, (binaryReal (fourY j))^q) = 2 := by
  have hn : (∑ j : Fin 4, (if fourY j then 1 else 0 : ℕ)) = 2 := by decide
  have hr : (∑ j : Fin 4, (if fourY j then (1 : ℝ) else 0)) = 2 := by
    exact_mod_cast hn
  calc
    (∑ j : Fin 4, (binaryReal (fourY j))^q) =
        ∑ j : Fin 4, (if fourY j then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      cases hb : fourY j <;> simp [binaryReal, hq]
    _ = 2 := hr

theorem outcome_sum (m : ℕ) :
    (∑ i : Fin (2*m + 2*m), outcome m i) = 2 * (m : ℝ) := by
  calc
    (∑ i : Fin (2*m + 2*m), outcome m i) =
        ∑ i : Fin (2*m + 2*m), binaryReal (fourY (repeatedEquivW1 m i).2) := by
      simp [outcome, repeatY]
    _ = (m : ℝ) * ∑ j : Fin 4, binaryReal (fourY j) :=
      sum_repeated m (fun j => binaryReal (fourY j))
    _ = 2 * (m : ℝ) := by
      have hb : (∑ j : Fin 4, binaryReal (fourY j)) = 2 := by
        simpa only [pow_one] using base_power_sum 1 (by omega)
      rw [hb]
      ring

theorem outcome_sq_sum (m : ℕ) :
    (∑ i : Fin (2*m + 2*m), (outcome m i)^2) = 2 * (m : ℝ) := by
  calc
    (∑ i : Fin (2*m + 2*m), (outcome m i)^2) =
        ∑ i : Fin (2*m + 2*m), (binaryReal (fourY (repeatedEquivW1 m i).2))^2 := by
      simp [outcome, repeatY]
    _ = (m : ℝ) * ∑ j : Fin 4, (binaryReal (fourY j))^2 :=
      sum_repeated m (fun j => (binaryReal (fourY j))^2)
    _ = 2 * (m : ℝ) := by rw [base_power_sum 2 (by omega)]; ring

theorem outcome_fourth_sum (m : ℕ) :
    (∑ i : Fin (2*m + 2*m),
      ((outcome m i)^4 + (outcome m i)^4)) = 4 * (m : ℝ) := by
  calc
    (∑ i : Fin (2*m + 2*m), ((outcome m i)^4 + (outcome m i)^4)) =
        ∑ i : Fin (2*m + 2*m),
          ((binaryReal (fourY (repeatedEquivW1 m i).2))^4 +
            (binaryReal (fourY (repeatedEquivW1 m i).2))^4) := by
      simp [outcome, repeatY]
    _ = (m : ℝ) * ∑ j : Fin 4,
          ((binaryReal (fourY j))^4 + (binaryReal (fourY j))^4) :=
      sum_repeated m (fun j => (binaryReal (fourY j))^4 + (binaryReal (fourY j))^4)
    _ = 4 * (m : ℝ) := by
      rw [Finset.sum_add_distrib, base_power_sum 4 (by omega)]
      ring

end
end SAP.P053.WH.W1.P.T2_L1

theorem SAP.P053.WH.W1.T2_L1_proof : SAP.P053.WH.W1.T2_L1 := by
  intro m hm
  dsimp only
  let y := SAP.P053.WH.W1.P.T2_L1.outcome m
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hNnat : 2*m + 2*m = 4*m := by omega
  have hNreal : ((2*m + 2*m : ℕ) : ℝ) = 4 * (m : ℝ) := by
    exact_mod_cast hNnat
  have hsum : (∑ i : Fin (2*m + 2*m), y i) = 2 * (m : ℝ) := by
    simpa [y] using SAP.P053.WH.W1.P.T2_L1.outcome_sum m
  have hsq : (∑ i : Fin (2*m + 2*m), (y i)^2) = 2 * (m : ℝ) := by
    simpa [y] using SAP.P053.WH.W1.P.T2_L1.outcome_sq_sum m
  have hfourth : (∑ i : Fin (2*m + 2*m),
      ((y i)^4 + (y i)^4)) = 4 * (m : ℝ) := by
    simpa [y] using SAP.P053.WH.W1.P.T2_L1.outcome_fourth_sum m
  have hcard : (Finset.univ : Finset (Fin (2*m + 2*m))).card ≠ 0 := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hcss : centeredSS Finset.univ y = (m : ℝ) := by
    rw [SAP.P053.WH.W1.P.T2_L1.centeredSS_raw_local Finset.univ y hcard]
    have hsum' : (∑ i ∈ Finset.univ, y i) = 2 * (m : ℝ) := by simpa using hsum
    have hsq' : (∑ i ∈ Finset.univ, (y i)^2) = 2 * (m : ℝ) := by
      simpa using hsq
    rw [hsq', hsum']
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [hNreal]
    field_simp [hmR]
    ring
  constructor
  · change sampleMean Finset.univ y = 1/2
    unfold sampleMean
    rw [hsum]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [hNreal]
    field_simp [hmR]
    ring
  constructor
  · change sampleVariance Finset.univ y = (m : ℝ)/(4*(m : ℝ)-1)
    unfold sampleVariance
    rw [hcss]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [hNreal]
  · change (∑ i : Fin (2*m + 2*m), ((y i)^4 + (y i)^4)) /
        ((2*m + 2*m : ℕ) : ℝ) = 1
    rw [hfourth, hNreal]
    field_simp [hmR]

