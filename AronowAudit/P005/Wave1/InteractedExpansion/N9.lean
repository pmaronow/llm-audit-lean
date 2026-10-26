import AronowAudit.P005.Wave1.InteractedExpansion.N6
import AronowAudit.P005.Wave1.InteractedExpansion.N8

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- A slightly coarser slope bound suffices: each residual is at most 3/2,
so the difference of its arm averages is at most 3. -/
theorem n9_proof : N9 := by
  intro h1 n hn
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hdpos : 0 < (n : ℝ) - 2 := by linarith
  have hd : (n : ℝ) - 2 ≠ 0 := ne_of_gt hdpos
  have hq := spikeQ_pos_of_S1 h1 n (by omega)
  have hs : Real.sqrt (spikeQ n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  let b : ℝ := (n : ℝ)^2 / (3 * ((n : ℝ) - 2) * (n : ℝ)^2 + 1)
  have hden : 0 < 3 * ((n : ℝ) - 2) * (n : ℝ)^2 + 1 := by positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb : b ≤ 1/2 := by
    apply (div_le_iff₀ hden).2
    have h := mul_nonneg (show 0 ≤ 3 * (n : ℝ) - 8 by linarith) (sq_nonneg (n : ℝ))
    nlinarith
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
      (h1 n (by omega)).1, (h1 n (by omega)).2.1, mul_zero, sub_zero,
      Finset.card_univ, Fintype.card_fin]
    field_simp [hn0, hd]
    <;> ring
  have hratio : popMean (fun i => spikeV n i * spikeZ n i) / spikeQ n = b := by
    apply (div_eq_iff (ne_of_gt hq)).2
    rw [hmean, (h1 n (by omega)).2.2.2.2]
    dsimp [b]
    field_simp [hn0, hd, ne_of_gt hden]
    <;> ring
  have hslope : populationSlope (spikePopulation n) (spikeV n) 0 =
      popMean (fun i => spikeV n i * spikeZ n i) / Real.sqrt (spikeQ n) := by
    change popMean (fun i => spikeV n i * (spikeZ n i / Real.sqrt (spikeQ n))) = _
    have hf : (fun i => spikeV n i * (spikeZ n i / Real.sqrt (spikeQ n))) =
        (fun i => (spikeV n i * spikeZ n i) / Real.sqrt (spikeQ n)) := by
      funext i; ring
    rw [hf]
    simp only [popMean, mean, ← Finset.sum_div]
    ring
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
  have hsmall : 1 / (n : ℝ) + 1 / (n : ℝ)^2 ≤ 1 := by
    have heq : 1 / (n : ℝ) + 1 / (n : ℝ)^2 = ((n : ℝ) + 1) / (n : ℝ)^2 := by
      field_simp [hn0]
      <;> ring
    rw [heq]
    exact (div_le_iff₀ (sq_pos_of_ne_zero hn0)).2 (by nlinarith)
  have hz (i : Fin n) : |spikeZ n i| ≤ 1 := by
    have ha := spikeA_bounds n (by omega) i
    have hpos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    rw [spikeZ, abs_le]
    constructor <;> linarith [ha.1, ha.2]
  have hvpop : popMean (spikeV n) = 0 := by
    simp [popMean, mean, (h1 n (by omega)).1]
  have hres (i : Fin n) :
      |armResidual (spikePopulation n) (spikeV n) i| ≤ 3/2 := by
    simp only [armResidual, centered, hvpop, sub_zero, hprojection]
    calc
      _ ≤ |spikeV n i| + |b * spikeZ n i| := abs_sub _ _
      _ ≤ 1 + (1/2 : ℝ) * 1 := by
        rw [abs_mul, abs_of_nonneg hb0]
        exact add_le_add ((h1 n (by omega)).2.2.1 i)
          (mul_le_mul hb (hz i) (abs_nonneg _) (by norm_num))
      _ = 3/2 := by norm_num
  refine ⟨by simp [ate, spikePopulation], ?_⟩
  intro S hS
  have hc := balanced_cards n hn S hS
  have hSn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hCn : (control S).Nonempty := Finset.card_pos.mp (by omega)
  change |mean S (armResidual (spikePopulation n) (spikeV n)) -
      mean (control S) (armResidual (spikePopulation n) (spikeV n))| ≤ 3
  calc
    _ ≤ |mean S (armResidual (spikePopulation n) (spikeV n))| +
        |mean (control S) (armResidual (spikePopulation n) (spikeV n))| := abs_sub _ _
    _ ≤ 3/2 + 3/2 := add_le_add
      (mean_abs_le_bound S hSn _ _ (fun i hi => hres i))
      (mean_abs_le_bound (control S) hCn _ _ (fun i hi => hres i))
    _ = 3 := by norm_num

end
end AronowAudit.P005.Wave1.InteractedExpansion
