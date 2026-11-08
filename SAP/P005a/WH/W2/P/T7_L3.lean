import SAP.P005a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter SAP.P005a
open scoped BigOperators Matrix Topology

noncomputable section

theorem SAP.P005a.WH.W2.T7_L3_proof : SAP.P005a.WH.W2.T7_L3 := by
  intro n hn
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hdpos : 0 < (n : ℝ) - 2 := by linarith
  have hd : (n : ℝ) - 2 ≠ 0 := ne_of_gt hdpos
  have h1 := AronowAudit.P005.Wave1.InteractedExpansion.n1_proof
  have hq : 0 < spikeQ n :=
    AronowAudit.P005.Wave1.InteractedExpansion.spikeQ_pos_of_S1 h1 n (by omega)
  have hs : Real.sqrt (spikeQ n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  let b : ℝ := (n : ℝ)^2 / (3 * (n : ℝ)^2 * ((n : ℝ) - 2) + 1)
  have hden : 0 < 3 * (n : ℝ)^2 * ((n : ℝ) - 2) + 1 := by positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb12 : b ≤ 1/12 := by
    apply (div_le_iff₀ hden).2
    have hprod := mul_nonneg (sq_nonneg (n : ℝ)) (by linarith : 0 ≤ (n : ℝ) - 6)
    nlinarith
  have hsumV : (∑ i : Fin n, spikeV n i) = 0 := by
    simpa only [SAP.P005a.spikeV, AronowAudit.P005.spikeV] using (h1 n (by omega)).1
  have hsumV2 : (∑ i : Fin n, spikeV n i ^ 2) =
      (n : ℝ) * ((n : ℝ) - 1) / (3 * ((n : ℝ) - 2)) := by
    simpa only [SAP.P005a.spikeV, AronowAudit.P005.spikeV] using
      (h1 n (by omega)).2.1
  have hprod (i : Fin n) : spikeV n i * spikeZ n i =
      spikeV n i ^ 2 / (n : ℝ)^2 - (1 / (n : ℝ)) * spikeV n i := by
    by_cases hi : i.val = 0
    · simp [spikeV, spikeZ, spikeA, hi]
    · simp only [spikeZ, spikeA, if_neg hi]
      ring
  have hmean : popMean (fun i => spikeV n i * spikeZ n i) =
      ((n : ℝ) - 1) / (3 * ((n : ℝ) - 2) * (n : ℝ)^2) := by
    unfold popMean mean
    simp_rw [hprod]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      hsumV, hsumV2, mul_zero, sub_zero,
      Finset.card_univ, Fintype.card_fin]
    field_simp [hn0, hd]
    <;> ring
  have hqForm : spikeQ n =
      ((n : ℝ) - 1) / (n : ℝ)^2 * (1 + 1 / (3 * ((n : ℝ) - 2) * (n : ℝ)^2)) := by
    simpa only [SAP.P005a.spikeQ, SAP.P005a.popMean, SAP.P005a.mean,
      SAP.P005a.spikeZ, SAP.P005a.spikeA, SAP.P005a.spikeV,
      AronowAudit.P005.spikeQ, AronowAudit.P005.popMean, AronowAudit.P005.mean,
      AronowAudit.P005.spikeZ, AronowAudit.P005.spikeA, AronowAudit.P005.spikeV] using
        (h1 n (by omega)).2.2.2.2
  have hratio : popMean (fun i => spikeV n i * spikeZ n i) / spikeQ n = b := by
    apply (div_eq_iff (ne_of_gt hq)).2
    rw [hmean, hqForm]
    dsimp [b]
    field_simp [hn0, hd, ne_of_gt hden]
    <;> ring
  have hbEq : spikeB n = b := by
    have hpopVZ : popMean (fun i => spikeV n i * spikeZ n i) =
        (∑ i : Fin n, spikeV n i * spikeZ n i) / (n : ℝ) := by
      simp [popMean, mean, Finset.card_univ, Fintype.card_fin]
    have hqDef : spikeQ n = (∑ i : Fin n, spikeZ n i ^ 2) / (n : ℝ) := by
      simp [spikeQ, popMean, mean, Finset.card_univ, Fintype.card_fin]
    have hdenSum : (∑ i : Fin n, spikeZ n i ^ 2) ≠ 0 := by
      intro hz
      have hq0 : spikeQ n = 0 := by
        rw [hqDef, hz]
        simp [hn0]
      exact (ne_of_gt hq) hq0
    have hmeanRatio :
        ((∑ i : Fin n, spikeV n i * spikeZ n i) / (∑ i : Fin n, spikeZ n i ^ 2)) =
          popMean (fun i => spikeV n i * spikeZ n i) / spikeQ n := by
      calc
        _ = ((∑ i : Fin n, spikeV n i * spikeZ n i) / (n : ℝ)) /
            ((∑ i : Fin n, spikeZ n i ^ 2) / (n : ℝ)) := by
              field_simp [hn0, hdenSum]
              <;> ring
        _ = popMean (fun i => spikeV n i * spikeZ n i) / spikeQ n := by
              rw [← hpopVZ, ← hqDef]
    have hswap : (∑ i : Fin n, spikeZ n i * spikeV n i) =
        (∑ i : Fin n, spikeV n i * spikeZ n i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    unfold spikeB
    rw [hswap, hmeanRatio, hratio]
  have hslope : populationSlope (spikePopulation n) (spikeV n) 0 =
      popMean (fun i => spikeV n i * spikeZ n i) / Real.sqrt (spikeQ n) := by
    change popMean (fun i => spikeV n i * (spikeZ n i / Real.sqrt (spikeQ n))) = _
    have hf : (fun i => spikeV n i * (spikeZ n i / Real.sqrt (spikeQ n))) =
        (fun i => (spikeV n i * spikeZ n i) / Real.sqrt (spikeQ n)) := by
      funext i
      ring
    rw [hf]
    simp only [popMean, mean, ← Finset.sum_div]
    ring
  have hslopeB : populationSlope (spikePopulation n) (spikeV n) 0 =
      Real.sqrt (spikeQ n) * b := by
    rw [hslope]
    calc
      popMean (fun i => spikeV n i * spikeZ n i) / Real.sqrt (spikeQ n) =
          Real.sqrt (spikeQ n) *
            (popMean (fun i => spikeV n i * spikeZ n i) / (Real.sqrt (spikeQ n))^2) := by
              field_simp [hs]
              <;> ring
      _ = Real.sqrt (spikeQ n) *
          (popMean (fun i => spikeV n i * spikeZ n i) / spikeQ n) := by
            rw [Real.sq_sqrt hq.le]
      _ = Real.sqrt (spikeQ n) * b := by rw [hratio]
  have hprojection (i : Fin n) :
      dot ((spikePopulation n).x i) (populationSlope (spikePopulation n) (spikeV n)) =
        b * spikeZ n i := by
    simp only [dot, Fin.sum_univ_one]
    rw [hslope]
    change (spikeZ n i / Real.sqrt (spikeQ n)) *
      (popMean (fun j => spikeV n j * spikeZ n j) / Real.sqrt (spikeQ n)) = _
    calc
      _ = spikeZ n i * (popMean (fun j => spikeV n j * spikeZ n j) /
          (Real.sqrt (spikeQ n))^2) := by ring
      _ = b * spikeZ n i := by rw [Real.sq_sqrt hq.le, hratio]; ring
  have hvpop : popMean (spikeV n) = 0 := by
    unfold popMean mean
    simp [Finset.card_univ, Fintype.card_fin, hsumV]
  have hsmall : 1 / (n : ℝ) + 1 / (n : ℝ)^2 ≤ 1 := by
    have heq : 1 / (n : ℝ) + 1 / (n : ℝ)^2 = ((n : ℝ) + 1) / (n : ℝ)^2 := by
      field_simp [hn0]
      <;> ring
    rw [heq]
    exact (div_le_iff₀ (sq_pos_of_ne_zero hn0)).2 (by nlinarith)
  have hz (i : Fin n) : |spikeZ n i| ≤ 1 := by
    have ha0 := AronowAudit.P005.Wave1.InteractedExpansion.spikeA_bounds n (by omega) i
    have ha : -(1 / (n : ℝ)^2) ≤ spikeA n i ∧ spikeA n i ≤ 1 := by
      simpa only [SAP.P005a.spikeA, AronowAudit.P005.spikeA,
        SAP.P005a.spikeV, AronowAudit.P005.spikeV] using ha0
    have hpos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    rw [spikeZ, abs_le]
    constructor <;> linarith [ha.1, ha.2, hsmall]
  have hresVal (i : Fin n) :
      armResidual (spikePopulation n) (spikeV n) i = spikeV n i - b * spikeZ n i := by
    simp only [armResidual, centered, hvpop, sub_zero, hprojection]
  have hresBound (i : Fin n) : |spikeV n i - b * spikeZ n i| ≤ 13/12 := by
    calc
      |spikeV n i - b * spikeZ n i| ≤ |spikeV n i| + |b * spikeZ n i| := abs_sub _ _
      _ ≤ 1 + (1/12 : ℝ) * 1 := by
        rw [abs_mul, abs_of_nonneg hb0]
        exact add_le_add ((h1 n (by omega)).2.2.1 i)
          (mul_le_mul hb12 (hz i) (abs_nonneg _) (by norm_num))
      _ = 13/12 := by norm_num
  have hresFacts (i : Fin n) :
      armResidual (spikePopulation n) (spikePopulation n).yT i = spikeE n i ∧
      armResidual (spikePopulation n) (spikePopulation n).yC i = spikeE n i ∧
      |spikeE n i| ≤ (13/12 : ℝ) := by
    have hE : spikeE n i = spikeV n i - b * spikeZ n i := by
      simp [spikeE, hbEq]
    rw [hE]
    exact ⟨by simpa [spikePopulation] using hresVal i,
      by simpa [spikePopulation] using hresVal i, hresBound i⟩
  have hresTFun :
      armResidual (spikePopulation n) (spikePopulation n).yT = spikeE n := by
    funext i
    exact (hresFacts i).1
  have hresCFun :
      armResidual (spikePopulation n) (spikePopulation n).yC = spikeE n := by
    funext i
    exact (hresFacts i).2.1
  refine ⟨hbEq, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbEq]
    exact hb0
  · rw [hbEq]
    exact hb12
  · intro k
    fin_cases k
    rw [hbEq]
    exact ⟨hslopeB, hslopeB⟩
  · intro i
    exact hresFacts i
  · intro S hS
    have hc := AronowAudit.P005.Wave1.InteractedExpansion.balanced_cards n hn S hS
    have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
    have hcTarget : 2 ≤ (control S).card := by
      simpa only [SAP.P005a.control, AronowAudit.P005.control] using hc.2
    have hCn : (control S).Nonempty := Finset.card_pos.mp (by omega)
    have hlead : armLeading (spikePopulation n) S =
        mean S (spikeE n) - mean (control S) (spikeE n) := by
      unfold armLeading
      rw [hresTFun, hresCFun]
    have hmeanBound (A : Finset (Fin n)) (hA : A.Nonempty) :
        |mean A (spikeE n)| ≤ (13/12 : ℝ) := by
      exact AronowAudit.P005.Wave1.InteractedExpansion.mean_abs_le_bound A hA
        (spikeE n) (13/12) (fun i hi => (hresFacts i).2.2)
    refine ⟨hlead, ?_, by norm_num⟩
    rw [hlead]
    calc
      |mean S (spikeE n) - mean (control S) (spikeE n)| ≤
          |mean S (spikeE n)| + |mean (control S) (spikeE n)| := abs_sub _ _
      _ ≤ 13/12 + 13/12 := add_le_add (hmeanBound S hSn) (hmeanBound (control S) hCn)
      _ = 13/6 := by norm_num

end
