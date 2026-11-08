import SAP.P053.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P053.WH.W1.P.T6_L2

private theorem indicator_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) :
    (∑ i ∈ s, (if i = a then (1 : ℝ) else 0)) = if a ∈ s then 1 else 0 := by
  classical
  by_cases ha : a ∈ s
  · rw [if_pos ha]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      simp [hba]
    · simp [ha]
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hia : i = a
    · subst i
      exact (ha hi).elim
    · simp [hia]

private theorem centeredSS_raw_local {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (y : ι → ℝ) (hs : s.card ≠ 0) :
    centeredSS s y = (∑ i ∈ s, (y i)^2) - (∑ i ∈ s, y i)^2/(s.card : ℝ) := by
  have hsr : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
  calc
    centeredSS s y = ∑ i ∈ s,
        ((y i)^2 - 2 * sampleMean s y * y i + (sampleMean s y)^2) := by
      unfold centeredSS
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ s, (y i)^2) - 2 * sampleMean s y * (∑ i ∈ s, y i) +
        (s.card : ℝ) * (sampleMean s y)^2 := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by unfold sampleMean; field_simp; ring

private theorem sparse_supported (k : ℕ)
    (z : Finset (Fin (sparsePopulationW1 k).size))
    (hz : z ∈ support (ι := Fin (sparsePopulationW1 k).size)
      (sparsePopulationW1 k).n1) :
    |estimate (sparsePopulationW1 k) z| = 1/((k : ℝ)+2) ∧
    olsVariance (sparsePopulationW1 k) z = 1/((k : ℝ)+2)^2 ∧
    fisherVariance (sparsePopulationW1 k) z = 1/((k : ℝ)+2)^2 := by
  classical
  let P := sparsePopulationW1 k
  let n : ℕ := k+2
  let nr : ℝ := (k : ℝ)+2
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hnr : 0 < nr := by dsimp [nr]; positivity
  have hnr_gt1 : (1 : ℝ) < nr := by
    dsimp [nr]
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith
  have hnr1 : nr - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hnr_gt1)
  have hsize : P.size = 2*n := by
    dsimp [P, n, sparsePopulationW1, Population.size]
    omega
  have hn1 : P.n1 = n := by dsimp [P, n, sparsePopulationW1]
  have hn0 : P.n0 = n := by dsimp [P, n, sparsePopulationW1]
  have hnr_cast : (n : ℝ) = nr := by
    dsimp [n, nr]
    norm_num
  have hzPowerset : z ∈ Finset.univ.powersetCard P.n1 := by
    simpa [support] using hz
  have hzc0 : z.card = P.n1 := (Finset.mem_powersetCard.mp hzPowerset).2
  have hzc : z.card = n := hzc0.trans hn1
  have hcc0 : zᶜ.card = P.n0 := by
    rw [Finset.card_compl, hzc0]
    simp only [Fintype.card_fin]
    change P.size - P.n1 = P.n0
    rw [hsize, hn1, hn0]
    omega
  have hcc : zᶜ.card = n := hcc0.trans hn0
  let zero : Fin P.size := ⟨0, by rw [hsize]; omega⟩
  have hzero_val : zero.val = 0 := rfl
  have hObs : observed P z = fun i => if i = zero then (1 : ℝ) else 0 := by
    funext i
    have hval : observed P z i = (if i.val = 0 then (1 : ℝ) else 0) := by
      simp [observed, P, sparsePopulationW1]
    rw [hval]
    have hcond : i.val = 0 ↔ i = zero := by
      constructor
      · intro hi
        apply Fin.ext
        simpa [zero] using hi
      · intro hi
        have hv := congrArg Fin.val hi
        simpa [zero] using hv
    by_cases hi : i.val = 0
    · have heq := hcond.mp hi
      simp [hi, heq, hzero_val]
    · have hne : i ≠ zero := fun heq => hi (hcond.mpr heq)
      simp [hi, hne, hzero_val]
  have hsum (s : Finset (Fin P.size)) :
      (∑ i ∈ s, observed P z i) = if zero ∈ s then 1 else 0 := by
    rw [hObs]
    exact indicator_sum s zero
  have hsum2 (s : Finset (Fin P.size)) :
      (∑ i ∈ s, (observed P z i)^2) = if zero ∈ s then 1 else 0 := by
    rw [hObs]
    calc
      (∑ i ∈ s, (if i = zero then (1 : ℝ) else 0)^2) =
          ∑ i ∈ s, (if i = zero then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> norm_num
      _ = if zero ∈ s then 1 else 0 := indicator_sum s zero
  have hcomp : zero ∈ zᶜ ↔ zero ∉ z := by simp
  have hMeanT : sampleMean z (observed P z) =
      if zero ∈ z then 1/nr else 0 := by
    unfold sampleMean
    rw [hsum z, hzc, hnr_cast]
    by_cases hz0 : zero ∈ z <;> simp [hz0, hnr.ne']
  have hMeanC : sampleMean zᶜ (observed P z) =
      if zero ∉ z then 1/nr else 0 := by
    unfold sampleMean
    rw [hsum zᶜ, hcc, hnr_cast]
    by_cases hz0 : zero ∈ z <;> simp [hz0, hcomp, hnr.ne']
  have hEstimate : estimate P z =
      (if zero ∈ z then 1/nr else 0) - (if zero ∉ z then 1/nr else 0) := by
    simp [estimate, difference, hMeanT, hMeanC]
  have hAbs : |estimate P z| = 1/nr := by
    by_cases hz0 : zero ∈ z
    · rw [hEstimate]
      simp only [if_pos hz0, if_neg (not_not_intro hz0), sub_zero]
      exact abs_of_pos (one_div_pos.mpr hnr)
    · rw [hEstimate]
      simp only [if_neg hz0, if_pos hz0, zero_sub, abs_neg]
      exact abs_of_pos (one_div_pos.mpr hnr)
  have hzCardNe : z.card ≠ 0 := by rw [hzc]; omega
  have hcCardNe : zᶜ.card ≠ 0 := by rw [hcc]; omega
  have hssT : centeredSS z (observed P z) =
      (if zero ∈ z then 1 else 0) -
        (if zero ∈ z then 1 else 0)^2/nr := by
    rw [centeredSS_raw_local z (observed P z) hzCardNe,
      hsum2 z, hsum z, hzc, hnr_cast]
  have hssC : centeredSS zᶜ (observed P z) =
      (if zero ∉ z then 1 else 0) -
        (if zero ∉ z then 1 else 0)^2/nr := by
    rw [centeredSS_raw_local zᶜ (observed P z) hcCardNe,
      hsum2 zᶜ, hsum zᶜ, hcc, hnr_cast]
    by_cases hz0 : zero ∈ z <;> simp [hz0, hcomp]
  have hResidual : residualSS P z = (nr-1)/nr := by
    unfold residualSS
    rw [hssT, hssC]
    by_cases hz0 : zero ∈ z <;> simp [hz0] <;> field_simp <;> ring
  have hOLS : olsVariance P z = 1/nr^2 := by
    unfold olsVariance
    rw [hResidual, hsize, hn1, hn0]
    push_cast
    rw [hnr_cast]
    have hden : (2*nr-2) ≠ 0 := ne_of_gt (by nlinarith [hnr_gt1])
    field_simp [hnr.ne', hden]
    <;> ring
  have hSq : (estimate P z)^2 = 1/nr^2 := by
    have h := congrArg (fun x : ℝ => x^2) hAbs
    simpa using h
  have hSqOLS : (estimate P z)^2 = olsVariance P z := by rw [hSq, hOLS]
  have hUcardR : ((Finset.univ : Finset (Fin P.size)).card : ℝ) = 2*nr := by
    rw [Finset.card_univ, Fintype.card_fin, hsize]
    push_cast
    rw [hnr_cast]
  have hsumU : (∑ i ∈ (Finset.univ : Finset (Fin P.size)), observed P z i) = 1 := by
    rw [hsum]
    simp
  have hsum2U : (∑ i ∈ (Finset.univ : Finset (Fin P.size)),
      (observed P z i)^2) = 1 := by
    rw [hsum2]
    simp
  have hUcardNe : (Finset.univ : Finset (Fin P.size)).card ≠ 0 := by
    rw [Finset.card_univ, Fintype.card_fin, hsize]
    omega
  have hcenterU : centeredSS Finset.univ (observed P z) = 1 - 1/(2*nr) := by
    rw [centeredSS_raw_local Finset.univ (observed P z) hUcardNe,
      hsum2U, hsumU, hUcardR]
    norm_num
  have hpopVariance : populationVariance P (observed P z) = 1/(2*nr) := by
    unfold populationVariance sampleVariance
    rw [hcenterU, Finset.card_univ, Fintype.card_fin, hsize]
    push_cast
    rw [hnr_cast]
    have hden : 2*nr-1 ≠ 0 := ne_of_gt (by nlinarith [hnr_gt1])
    field_simp [hden, show 2*nr ≠ 0 by positivity]
    <;> ring
  have hFisher : fisherVariance P z = 1/nr^2 := by
    unfold fisherVariance
    rw [hpopVariance, hsize, hn1, hn0]
    push_cast
    rw [hnr_cast]
    field_simp [hnr.ne']
    <;> ring
  have hOLS' : olsVariance P z = 1/((k : ℝ)+2)^2 := by
    simpa [nr] using hOLS
  have hFisher' : fisherVariance P z = 1/((k : ℝ)+2)^2 := by
    simpa [nr] using hFisher
  have hAbs' : |estimate P z| = 1/((k : ℝ)+2) := by
    simpa [nr] using hAbs
  exact ⟨hAbs', hOLS', hFisher'⟩

end SAP.P053.WH.W1.P.T6_L2

theorem SAP.P053.WH.W1.T6_L2_proof : SAP.P053.WH.W1.T6_L2 := by
  intro k z hz
  exact SAP.P053.WH.W1.P.T6_L2.sparse_supported k z hz
