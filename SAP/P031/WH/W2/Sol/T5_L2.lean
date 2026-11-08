import SAP.P031.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix
open Finset SAP.P031 SAP.P031.WH.W2

noncomputable section
namespace SAP.P031.WH.W2.Sol

private def posWeight (Q : Population) (i : Fin Q.N) : ℝ :=
  (if i.val < Q.M then 1 else 0) - (Q.M : ℝ) / Q.N

private def outcomeWeight (Q : Population) (j : Fin Q.N) : ℝ :=
  (Q.y1 j - groupMean univ Q.y1) / Q.M +
    (Q.y0 j - groupMean univ Q.y0) / ((Q.N : ℝ) - Q.M)

private theorem Npos (Q : Population) : (0 : ℝ) < Q.N := by
  exact_mod_cast (by have := (populationSizesW2 Q).2.2.2; omega : 0 < Q.N)

private theorem Mpos (Q : Population) : (0 : ℝ) < Q.M := by
  exact_mod_cast (by have := (populationSizesW2 Q).1; omega : 0 < Q.M)

private theorem Kpos (Q : Population) : (0 : ℝ) < (Q.N : ℝ) - Q.M := by
  have h : (0 : ℝ) < ((Q.N - Q.M : ℕ) : ℝ) := by
    exact_mod_cast (by have := (populationSizesW2 Q).2.1; omega : 0 < Q.N-Q.M)
  simpa only [Nat.cast_sub (populationSizesW2 Q).2.2.1] using h

private theorem centeredSum (Q : Population) (y : Fin Q.N → ℝ) :
    ∑ j, (y j - groupMean univ y) = 0 := by
  have hn : ((univ : Finset (Fin Q.N)).card : ℝ) ≠ 0 := by
    simpa only [card_univ, Fintype.card_fin] using (Npos Q).ne'
  simpa [groupMean, AronowAudit.P031.groupMean] using
    AronowAudit.P031.sum_centered univ y hn

private theorem outcomeWeight_sum (Q : Population) :
    ∑ j, outcomeWeight Q j = 0 := by
  simp only [outcomeWeight, sum_add_distrib, ← sum_div, centeredSum Q, zero_div, add_zero]

private theorem prefix_count (Q : Population) :
    (∑ i : Fin Q.N, if i.val < Q.M then (1 : ℝ) else 0) = Q.M := by
  have hc : ((univ : Finset (Fin Q.N)).filter (fun i => i.val < Q.M)).card = Q.M := by
    rw [Fin.card_filter_val_lt, Nat.min_eq_right (populationSizesW2 Q).2.2.1]
  rw [← Finset.sum_filter]
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
    congrArg (fun a : ℕ => (a : ℝ)) hc

private theorem posWeight_sum (Q : Population) : ∑ i, posWeight Q i = 0 := by
  have hn : ((Q.N : ℝ) ≠ 0) := (Npos Q).ne'
  simp only [posWeight, sum_sub_distrib, prefix_count Q, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn]
  ring

private theorem row_sum (Q : Population) (i : Fin Q.N) :
    ∑ j, contrastArrayW2 Q i j = 0 := by
  change ∑ j, posWeight Q i * outcomeWeight Q j / Real.sqrt (trueVariance Q) = 0
  simp only [← Finset.mul_sum, ← Finset.sum_div, outcomeWeight_sum Q, mul_zero, zero_div]

private theorem column_sum (Q : Population) (j : Fin Q.N) :
    ∑ i, contrastArrayW2 Q i j = 0 := by
  change ∑ i, posWeight Q i * outcomeWeight Q j / Real.sqrt (trueVariance Q) = 0
  simp only [← Finset.sum_mul, ← Finset.sum_div, posWeight_sum Q, zero_mul, zero_div]

private theorem posWeight_sq_sum (Q : Population) :
    (∑ i, (posWeight Q i)^2) =
      (Q.M : ℝ) * ((Q.N : ℝ) - Q.M) / Q.N := by
  have hs : ((univ : Finset (Fin Q.N)).filter (fun i => i.val < Q.M)).card = Q.M := by
    rw [Fin.card_filter_val_lt, Nat.min_eq_right (populationSizesW2 Q).2.2.1]
  have hc : (univ.filter (fun i : Fin Q.N => ¬ i.val < Q.M)).card = Q.N - Q.M := by
    have hh := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin Q.N)))
      (fun i : Fin Q.N => i.val < Q.M)
    simp only [hs, card_univ, Fintype.card_fin] at hh
    omega
  have hcalc : (∑ i, (posWeight Q i)^2) =
      (Q.M : ℝ) * (1 - (Q.M : ℝ) / Q.N)^2 +
      ((Q.N - Q.M : ℕ) : ℝ) * ((Q.M : ℝ) / Q.N)^2 := by
    simp only [posWeight]
    conv_lhs =>
      arg 2
      ext i
      rw [show ((if i.val < Q.M then (1 : ℝ) else 0) - (Q.M : ℝ) / Q.N)^2 =
          if i.val < Q.M then (1 - (Q.M : ℝ) / Q.N)^2 else
            ((Q.M : ℝ) / Q.N)^2 by split_ifs <;> ring]
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, hs, hc]
  rw [hcalc, Nat.cast_sub (populationSizesW2 Q).2.2.1]
  have hn := (Npos Q).ne'
  field_simp [hn]
  ring

private theorem centered_sq_sum (Q : Population) (y : Fin Q.N → ℝ) :
    (∑ j, (y j - groupMean univ y)^2) = (Q.N : ℝ) * popVariance y := by
  have hn : ((Q.N : ℝ) ≠ 0) := (Npos Q).ne'
  unfold popVariance
  simp only [Fintype.card_fin]
  field_simp [hn]

private theorem centered_cross_sum (Q : Population) (y z : Fin Q.N → ℝ) :
    (∑ j, (y j - groupMean univ y) * (z j - groupMean univ z)) =
      (Q.N : ℝ) * popCovariance y z := by
  have hn : ((Q.N : ℝ) ≠ 0) := (Npos Q).ne'
  unfold popCovariance
  simp only [Fintype.card_fin]
  field_simp [hn]

private theorem outcomeWeight_sq_sum (Q : Population) :
    (∑ j, (outcomeWeight Q j)^2) =
      (Q.N : ℝ) * (popVariance Q.y1 / (Q.M : ℝ)^2 +
        popVariance Q.y0 / ((Q.N : ℝ) - Q.M)^2 +
        2 * popCovariance Q.y1 Q.y0 /
          ((Q.M : ℝ) * ((Q.N : ℝ) - Q.M))) := by
  let a : Fin Q.N → ℝ := fun j => Q.y1 j - groupMean univ Q.y1
  let b : Fin Q.N → ℝ := fun j => Q.y0 j - groupMean univ Q.y0
  let m : ℝ := Q.M
  let k : ℝ := (Q.N : ℝ) - Q.M
  have hm : m ≠ 0 := (Mpos Q).ne'
  have hk : k ≠ 0 := (Kpos Q).ne'
  have hex (j : Fin Q.N) : (outcomeWeight Q j)^2 =
      (a j)^2 / m^2 + (b j)^2 / k^2 + 2 * a j * b j / (m*k) := by
    change (a j / m + b j / k)^2 = _
    field_simp [hm, hk]
    ring
  calc
    (∑ j, (outcomeWeight Q j)^2) =
        ∑ j, ((a j)^2 / m^2 + (b j)^2 / k^2 + 2 * a j * b j / (m*k)) := by
      exact Finset.sum_congr rfl (fun j _ => hex j)
    _ = (∑ j, (a j)^2) / m^2 + (∑ j, (b j)^2) / k^2 +
        2 * (∑ j, a j * b j) / (m*k) := by
      have htwo : (∑ j, 2 * a j * b j) = 2 * (∑ j, a j * b j) := by
        calc
          _ = ∑ j, 2 * (a j * b j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = _ := by rw [Finset.mul_sum]
      simp only [sum_add_distrib, ← sum_div, htwo]
    _ = (Q.N : ℝ) * (popVariance Q.y1 / m^2 +
        popVariance Q.y0 / k^2 + 2 * popCovariance Q.y1 Q.y0 / (m*k)) := by
      simp only [a, b, centered_sq_sum Q, centered_cross_sum Q]
      ring
    _ = _ := rfl

private theorem array_sq_sum (Q : Population) (hV : 0 < trueVariance Q) :
    (∑ i, ∑ j, (contrastArrayW2 Q i j)^2) = (Q.N : ℝ) - 1 := by
  have hroot : (Real.sqrt (trueVariance Q))^2 = trueVariance Q :=
    Real.sq_sqrt hV.le
  have hfactor : (∑ i, ∑ j, (contrastArrayW2 Q i j)^2) =
      (∑ i, (posWeight Q i)^2) * (∑ j, (outcomeWeight Q j)^2) /
        trueVariance Q := by
    have hinner (i : Fin Q.N) :
        (∑ j, (contrastArrayW2 Q i j)^2) =
          (posWeight Q i)^2 * (∑ j, (outcomeWeight Q j)^2) /
            trueVariance Q := by
      calc
        _ = ∑ j, (posWeight Q i)^2 * (outcomeWeight Q j)^2 /
            trueVariance Q := by
          apply Finset.sum_congr rfl
          intro j _
          change (posWeight Q i * outcomeWeight Q j /
              Real.sqrt (trueVariance Q))^2 = _
          rw [div_pow, mul_pow, hroot]
        _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]
    simp only [hinner, ← Finset.sum_mul, ← Finset.sum_div]
  have hVeq : trueVariance Q =
      1 / ((Q.N : ℝ) - 1) *
        ((((Q.N : ℝ) - Q.M) / Q.M) * popVariance Q.y1 +
          ((Q.M : ℝ) / ((Q.N : ℝ) - Q.M)) * popVariance Q.y0 +
          2 * popCovariance Q.y1 Q.y0) := by
    have hd := AronowAudit.P031.randomization_variance_alternative Q.M
      (populationSizesW2 Q).1 (by simpa only [Fintype.card_fin] using
        (populationSizesW2 Q).2.1)
      (by simpa only [Fintype.card_fin] using (populationSizesW2 Q).2.2.1)
      Q.y1 Q.y0
    have hpv1 : AronowAudit.P031.popVariance Q.y1 = popVariance Q.y1 := rfl
    have hpv0 : AronowAudit.P031.popVariance Q.y0 = popVariance Q.y0 := rfl
    have hpc : AronowAudit.P031.popCovariance Q.y1 Q.y0 =
        popCovariance Q.y1 Q.y0 := rfl
    have hrv : AronowAudit.P031.randomizationVariance Q.M Q.y1 Q.y0 =
        trueVariance Q := rfl
    simpa only [Fintype.card_fin, hpv1, hpv0, hpc, hrv] using hd
  have hnum : (∑ i, (posWeight Q i)^2) *
      (∑ j, (outcomeWeight Q j)^2) =
        ((Q.N : ℝ) - 1) * trueVariance Q := by
    rw [posWeight_sq_sum, outcomeWeight_sq_sum, hVeq]
    have hm := (Mpos Q).ne'
    have hk := (Kpos Q).ne'
    have hn := (Npos Q).ne'
    have hN4 : (4 : ℝ) ≤ Q.N := by
      exact_mod_cast (populationSizesW2 Q).2.2.2
    have hn1 : ((Q.N : ℝ) - 1) ≠ 0 := by linarith
    field_simp [hm, hk, hn, hn1] <;> ring
  rw [hfactor, hnum]
  field_simp [hV.ne']

private theorem point_linearized (Q : Population) (s : Finset (Fin Q.N))
    (hs : s.card = Q.M) :
    pointEstimate Q s - populationEffect Q = ∑ j ∈ s, outcomeWeight Q j := by
  have hkcard : sᶜ.card = Q.N - Q.M := by
    rw [card_compl, hs, Fintype.card_fin]
  have hkcast : (sᶜ.card : ℝ) = (Q.N : ℝ) - Q.M := by
    rw [hkcard, Nat.cast_sub (populationSizesW2 Q).2.2.1]
  have hm : ((Q.M : ℝ) ≠ 0) := (Mpos Q).ne'
  have hk : ((Q.N : ℝ) - Q.M) ≠ 0 := (Kpos Q).ne'
  have hn : ((Q.N : ℝ) ≠ 0) := (Npos Q).ne'
  have hlin : pointEstimate Q s =
      (∑ j ∈ s, (Q.y1 j / (s.card : ℝ) + Q.y0 j / (sᶜ.card : ℝ))) -
        (∑ j, Q.y0 j) / sᶜ.card := by
    exact AronowAudit.P031.linearized_estimate s Q.y1 Q.y0
  rw [hlin, hs, hkcast]
  unfold populationEffect averageEffect outcomeWeight groupMean
  simp only [sum_add_distrib, ← sum_div, sum_sub_distrib, sum_const,
    nsmul_eq_mul, hs, card_univ, Fintype.card_fin]
  field_simp [hm, hk, hn]
  ring

private theorem permutation_point_identity (Q : Population)
    (π : Equiv.Perm (Fin Q.N)) :
    (pointEstimate Q (permutationTreatedW2 Q π) - populationEffect Q) /
      Real.sqrt (trueVariance Q) = ∑ i, contrastArrayW2 Q i (π i) := by
  let pre : Finset (Fin Q.N) := univ.filter (fun i => i.val < Q.M)
  let s : Finset (Fin Q.N) := permutationTreatedW2 Q π
  have hprefCard : pre.card = Q.M := by
    dsimp [pre]
    rw [Fin.card_filter_val_lt, Nat.min_eq_right (populationSizesW2 Q).2.2.1]
  have hs : s.card = Q.M := by
    change (pre.image π).card = Q.M
    rw [Finset.card_image_of_injective _ π.injective, hprefCard]
  have hpermZero : (∑ i, outcomeWeight Q (π i)) = 0 := by
    rw [Equiv.sum_comp π]
    exact outcomeWeight_sum Q
  have hweighted : (∑ i, posWeight Q i * outcomeWeight Q (π i)) =
      ∑ i ∈ pre, outcomeWeight Q (π i) := by
    have hpoint (i : Fin Q.N) :
        posWeight Q i * outcomeWeight Q (π i) =
          (if i.val < Q.M then outcomeWeight Q (π i) else 0) -
            ((Q.M : ℝ) / Q.N) * outcomeWeight Q (π i) := by
      dsimp [posWeight]
      split_ifs <;> ring
    simp_rw [hpoint]
    rw [sum_sub_distrib, ← Finset.mul_sum, hpermZero, mul_zero, sub_zero]
    simp only [pre, Finset.sum_filter]
  have himage : (∑ i ∈ pre, outcomeWeight Q (π i)) =
      ∑ j ∈ s, outcomeWeight Q j := by
    change (∑ i ∈ pre, outcomeWeight Q (π i)) =
      ∑ j ∈ pre.image π, outcomeWeight Q j
    rw [Finset.sum_image (fun x _ y _ h => π.injective h)]
  have hpoint := point_linearized Q s hs
  calc
    (pointEstimate Q (permutationTreatedW2 Q π) - populationEffect Q) /
        Real.sqrt (trueVariance Q) =
          (∑ j ∈ s, outcomeWeight Q j) / Real.sqrt (trueVariance Q) := by
        rw [hpoint]
    _ = (∑ i, posWeight Q i * outcomeWeight Q (π i)) /
          Real.sqrt (trueVariance Q) := by rw [hweighted, himage]
    _ = ∑ i, contrastArrayW2 Q i (π i) := by
      rw [Finset.sum_div]
      rfl

theorem T5_L2_solution : T5_L2 := by
  intro Q hV
  exact ⟨row_sum Q, column_sum Q, array_sq_sum Q hV,
    permutation_point_identity Q⟩

#print axioms T5_L2_solution

end SAP.P031.WH.W2.Sol
end
