import SAP.P031.WH.W2.Leaves
import AronowAudit.P053.P053_MomentConsistency

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter Finset SAP.P031 SAP.P031.WH.W2

noncomputable section
namespace SAP.P031.WH.W2.Sol

private def maxDev (Q : Population) (y : Fin Q.N → ℝ) : ℝ := by
  letI : Nonempty (Fin Q.N) := ⟨⟨0, by have := (populationSizesW2 Q).2.2.2; omega⟩⟩
  exact Causalean.Experimentation.FinitePopulationMoments.popMaxSqDev y

private theorem armMaxRate (P : ℕ → Population) (y : (n : ℕ) → Fin (P n).N → ℝ)
    (m : ℕ → ℕ) (q B : ℝ)
    (hmpos : ∀ n, 0 < m n) (hmle : ∀ n, m n ≤ (P n).N)
    (hq : q ≠ 0) (hB : 0 ≤ B)
    (hfourth : ∀ n, (∑ i, (y n i)^4) / (P n).N ≤ B)
    (hgrow : GrowingPopulations P)
    (hfrac : Tendsto (fun n => ((m n : ℕ) : ℝ) / (P n).N) atTop (𝓝 q)) :
    Tendsto (fun n => maxDev (P n) (y n) / (m n : ℝ)) atTop (𝓝 0) := by
  classical
  letI : ∀ n, Nonempty (Fin (P n).N) := fun n =>
    ⟨⟨0, by have hh := (populationSizesW2 (P n)).2.2.2; omega⟩⟩
  have hNreal : Tendsto (fun n => ((P n).N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hgrow
  have hNinv : Tendsto (fun n => 1 / ((P n).N : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hNreal
  have hf (n : ℕ) :
      (∑ i, (y n i)^4) ≤ B * (Fintype.card (Fin (P n).N) : ℝ) := by
    have hNpos : 0 < ((P n).N : ℝ) := by
      exact_mod_cast (by have hh := (populationSizesW2 (P n)).2.2.2; omega : 0 < (P n).N)
    have hh := (div_le_iff₀ hNpos).mp (hfourth n)
    simpa only [Fintype.card_fin] using hh
  simpa only [maxDev] using AronowAudit.P053.MomentCompletion.maximal_square_rate
    (y := y) (n := m) hmpos (fun n => by simpa only [Fintype.card_fin] using hmle n)
    B q hB hq hf (by simpa only [Fintype.card_fin] using hNinv)
    (by simpa only [Fintype.card_fin] using hfrac)

private theorem maxDev_nonneg (Q : Population) (y : Fin Q.N → ℝ) :
    0 ≤ maxDev Q y := by
  classical
  letI : Nonempty (Fin Q.N) := ⟨⟨0, by have := (populationSizesW2 Q).2.2.2; omega⟩⟩
  obtain ⟨j⟩ := (inferInstance : Nonempty (Fin Q.N))
  change 0 ≤ Causalean.Experimentation.FinitePopulationMoments.popMaxSqDev y
  exact (sq_nonneg (y j - Causalean.Experimentation.FinitePopulationMoments.popMean y)).trans
    (Finset.le_sup' (fun i => (y i - Causalean.Experimentation.FinitePopulationMoments.popMean y)^2)
      (Finset.mem_univ j))

private theorem centered_sq_le_maxDev (Q : Population) (y : Fin Q.N → ℝ) (j : Fin Q.N) :
    (y j - groupMean univ y)^2 ≤ maxDev Q y := by
  classical
  letI : Nonempty (Fin Q.N) := ⟨⟨0, by have := (populationSizesW2 Q).2.2.2; omega⟩⟩
  have hmean : Causalean.Experimentation.FinitePopulationMoments.popMean y =
      groupMean univ y := by
    simp [Causalean.Experimentation.FinitePopulationMoments.popMean, groupMean]
  rw [← hmean]
  change (y j - Causalean.Experimentation.FinitePopulationMoments.popMean y)^2 ≤
    Causalean.Experimentation.FinitePopulationMoments.popMaxSqDev y
  exact Finset.le_sup' (fun i =>
    (y i - Causalean.Experimentation.FinitePopulationMoments.popMean y)^2)
    (Finset.mem_univ j)

private theorem controlFractionLimit (P : ℕ → Population) (p : ℝ)
    (h : Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (𝓝 p)) :
    Tendsto (fun n => (((P n).N : ℝ) - (P n).M) / (P n).N)
      atTop (𝓝 (1 - p)) := by
  apply (tendsto_const_nhds.sub h).congr
  intro n
  have hn : ((P n).N : ℝ) ≠ 0 := by
    have hh : (4 : ℝ) ≤ (P n).N := by
      exact_mod_cast (populationSizesW2 (P n)).2.2.2
    linarith
  field_simp [hn]

private theorem controlNatFractionLimit (P : ℕ → Population) (p : ℝ)
    (h : Tendsto (fun n => ((P n).M : ℝ) / (P n).N) atTop (𝓝 p)) :
    Tendsto (fun n => (((P n).N - (P n).M : ℕ) : ℝ) / (P n).N)
      atTop (𝓝 (1 - p)) := by
  apply (controlFractionLimit P p h).congr'
  filter_upwards [] with n
  simp only [Nat.cast_sub (populationSizesW2 (P n)).2.2.1]

private theorem armRateLimits (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ)
    (h : RegularRegimeW2 P p μ1 μ0 v1 v0 c) :
    Tendsto (fun n => maxDev (P n) (P n).y1 / ((P n).M : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => maxDev (P n) (P n).y0 /
      (((P n).N - (P n).M : ℕ) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨B, hB, hfourth⟩ := h.fourthW2
  constructor
  · apply armMaxRate P (fun n => (P n).y1) (fun n => (P n).M) p B
      (fun n => by have := (populationSizesW2 (P n)).1; omega)
      (fun n => (populationSizesW2 (P n)).2.2.1)
      h.pPositiveW2.ne' hB (fun n => (hfourth n).1) h.growingW2 h.allocationW2
  · apply armMaxRate P (fun n => (P n).y0) (fun n => (P n).N - (P n).M)
      (1 - p) B
      (fun n => by have := (populationSizesW2 (P n)).2.1; omega)
      (fun n => Nat.sub_le _ _) (by linarith [h.pLessOneW2]) hB
      (fun n => (hfourth n).2) h.growingW2
      (controlNatFractionLimit P p h.allocationW2)

private theorem armScaledVarianceLimits (P : ℕ → Population) (p μ1 μ0 v1 v0 c : ℝ)
    (h : RegularRegimeW2 P p μ1 μ0 v1 v0 c) :
    Tendsto (fun n => ((P n).M : ℝ) * trueVariance (P n)) atTop
      (𝓝 (p * LeadingTrueVarianceW2 p v1 v0 c)) ∧
    Tendsto (fun n => (((P n).N - (P n).M : ℕ) : ℝ) * trueVariance (P n))
      atTop (𝓝 ((1-p) * LeadingTrueVarianceW2 p v1 v0 c)) := by
  have hV := scaledTrueLimitW2 P p μ1 μ0 v1 v0 c h
  constructor
  · apply (h.allocationW2.mul hV).congr'
    filter_upwards [] with n
    have hn : ((P n).N : ℝ) ≠ 0 := by
      have hh : (4 : ℝ) ≤ (P n).N := by
        exact_mod_cast (populationSizesW2 (P n)).2.2.2
      linarith
    field_simp [hn]
  · apply ((controlNatFractionLimit P p h.allocationW2).mul hV).congr'
    filter_upwards [] with n
    have hn : ((P n).N : ℝ) ≠ 0 := by
      have hh : (4 : ℝ) ≤ (P n).N := by
        exact_mod_cast (populationSizesW2 (P n)).2.2.2
      linarith
    field_simp [hn]

private theorem normalizedArmBound (Q : Population) (y : Fin Q.N → ℝ)
    (m : ℝ) (hm : 0 < m) (hV : 0 < trueVariance Q) (j : Fin Q.N) :
    |y j - groupMean univ y| / m / Real.sqrt (trueVariance Q) ≤
      Real.sqrt (maxDev Q y / m) / Real.sqrt (m * trueVariance Q) := by
  have hmd := maxDev_nonneg Q y
  have hr : 0 ≤ maxDev Q y / m := div_nonneg hmd hm.le
  have hmv : 0 ≤ m * trueVariance Q := (mul_pos hm hV).le
  have hrootV : 0 < Real.sqrt (trueVariance Q) := Real.sqrt_pos.2 hV
  have hrootMV : 0 < Real.sqrt (m * trueVariance Q) :=
    Real.sqrt_pos.2 (mul_pos hm hV)
  have hl : 0 ≤ |y j - groupMean univ y| / m / Real.sqrt (trueVariance Q) := by
    positivity
  have hh : 0 ≤ Real.sqrt (maxDev Q y / m) / Real.sqrt (m * trueVariance Q) := by
    positivity
  apply (sq_le_sq₀ hl hh).mp
  simp only [div_pow, sq_abs, Real.sq_sqrt hV.le, Real.sq_sqrt hr,
    Real.sq_sqrt hmv]
  calc
    (y j - groupMean univ y)^2 / m^2 / trueVariance Q =
        (y j - groupMean univ y)^2 / (m^2 * trueVariance Q) := by ring
    _ ≤ maxDev Q y / (m^2 * trueVariance Q) :=
      div_le_div_of_nonneg_right (centered_sq_le_maxDev Q y j)
        (mul_pos (sq_pos_of_pos hm) hV).le
    _ = (maxDev Q y / m) / (m * trueVariance Q) := by
      field_simp

private theorem positionWeightBound (Q : Population) (i : Fin Q.N) :
    |(if i.val < Q.M then (1 : ℝ) else 0) - (Q.M : ℝ) / Q.N| ≤ 1 := by
  have hm : (0 : ℝ) ≤ Q.M := Nat.cast_nonneg _
  have hn : (0 : ℝ) < Q.N := by
    exact_mod_cast (by have := (populationSizesW2 Q).2.2.2; omega : 0 < Q.N)
  have hle : (Q.M : ℝ) ≤ Q.N := by
    exact_mod_cast (populationSizesW2 Q).2.2.1
  have hfrac : 0 ≤ (Q.M : ℝ) / Q.N ∧ (Q.M : ℝ) / Q.N ≤ 1 := by
    constructor
    · exact div_nonneg hm hn.le
    · exact (div_le_one hn).2 hle
  split_ifs <;> apply abs_le.mpr <;> constructor <;> nlinarith [hfrac.1, hfrac.2]

private theorem arrayEntryBound (Q : Population) (hV : 0 < trueVariance Q)
    (i j : Fin Q.N) :
    |contrastArrayW2 Q i j| ≤
      Real.sqrt (maxDev Q Q.y1 / (Q.M : ℝ)) /
          Real.sqrt ((Q.M : ℝ) * trueVariance Q) +
      Real.sqrt (maxDev Q Q.y0 / (((Q.N - Q.M : ℕ) : ℝ))) /
          Real.sqrt ((((Q.N - Q.M : ℕ) : ℝ)) * trueVariance Q) := by
  let m : ℝ := Q.M
  let k : ℝ := (Q.N - Q.M : ℕ)
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (by have := (populationSizesW2 Q).1; omega : 0 < Q.M)
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast (by have := (populationSizesW2 Q).2.1; omega : 0 < Q.N - Q.M)
  have hk_eq : k = (Q.N : ℝ) - Q.M := by
    dsimp [k]
    exact Nat.cast_sub (populationSizesW2 Q).2.2.1
  let d1 : ℝ := Q.y1 j - groupMean univ Q.y1
  let d0 : ℝ := Q.y0 j - groupMean univ Q.y0
  let w : ℝ := (if i.val < Q.M then 1 else 0) - (Q.M : ℝ) / Q.N
  have hw : |w| ≤ 1 := positionWeightBound Q i
  have hsqrt : 0 ≤ Real.sqrt (trueVariance Q) := Real.sqrt_nonneg _
  have h1 : |d1| / m / Real.sqrt (trueVariance Q) ≤
      Real.sqrt (maxDev Q Q.y1 / m) /
        Real.sqrt (m * trueVariance Q) := normalizedArmBound Q Q.y1 m hm hV j
  have h0 : |d0| / k / Real.sqrt (trueVariance Q) ≤
      Real.sqrt (maxDev Q Q.y0 / k) /
        Real.sqrt (k * trueVariance Q) := normalizedArmBound Q Q.y0 k hk hV j
  change |w * (d1 / m + d0 / ((Q.N : ℝ) - Q.M)) /
      Real.sqrt (trueVariance Q)| ≤ _
  rw [← hk_eq]
  have hz : 0 ≤ |d1 / m + d0 / k| := abs_nonneg _
  calc
    |w * (d1 / m + d0 / k) / Real.sqrt (trueVariance Q)| =
        |w| * |d1 / m + d0 / k| / Real.sqrt (trueVariance Q) := by
      rw [abs_div, abs_mul, abs_of_nonneg hsqrt]
    _ ≤ |d1 / m + d0 / k| / Real.sqrt (trueVariance Q) := by
      exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hw hz]) hsqrt
    _ ≤ (|d1| / m + |d0| / k) / Real.sqrt (trueVariance Q) := by
      apply div_le_div_of_nonneg_right _ hsqrt
      simpa only [abs_div, abs_of_pos hm, abs_of_pos hk] using abs_add_le (d1 / m) (d0 / k)
    _ = |d1| / m / Real.sqrt (trueVariance Q) +
        |d0| / k / Real.sqrt (trueVariance Q) := by ring
    _ ≤ _ := add_le_add h1 h0

theorem T5_L3_solution : T5_L3 := by
  intro P p μ1 μ0 v1 v0 c h
  let mrate : ℕ → ℝ := fun n => maxDev (P n) (P n).y1 / ((P n).M : ℝ)
  let krate : ℕ → ℝ := fun n => maxDev (P n) (P n).y0 /
    (((P n).N - (P n).M : ℕ) : ℝ)
  let mscale : ℕ → ℝ := fun n => ((P n).M : ℝ) * trueVariance (P n)
  let kscale : ℕ → ℝ := fun n =>
    (((P n).N - (P n).M : ℕ) : ℝ) * trueVariance (P n)
  let β : ℕ → ℝ := fun n => Real.sqrt (mrate n) / Real.sqrt (mscale n) +
    Real.sqrt (krate n) / Real.sqrt (kscale n)
  refine ⟨β, ?_, ?_⟩
  · have hr := armRateLimits P p μ1 μ0 v1 v0 c h
    have hs := armScaledVarianceLimits P p μ1 μ0 v1 v0 c h
    have hpD : 0 < p * LeadingTrueVarianceW2 p v1 v0 c :=
      mul_pos h.pPositiveW2 h.contrastPositiveW2
    have hkD : 0 < (1-p) * LeadingTrueVarianceW2 p v1 v0 c :=
      mul_pos (by linarith [h.pLessOneW2]) h.contrastPositiveW2
    have hm := hr.1.sqrt.div hs.1.sqrt (Real.sqrt_pos.2 hpD).ne'
    have hk := hr.2.sqrt.div hs.2.sqrt (Real.sqrt_pos.2 hkD).ne'
    convert hm.add hk using 1 <;> ext n <;>
      simp only [mrate, krate, mscale, kscale, β, Function.comp_def,
        Real.sqrt_zero, zero_div, zero_add]
  · filter_upwards [trueVarianceEventuallyPositiveW2 P p μ1 μ0 v1 v0 c h] with n hn
    intro i j
    exact arrayEntryBound (P n) hn i j

#print axioms T5_L3_solution

end SAP.P031.WH.W2.Sol
end
