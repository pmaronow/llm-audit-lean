import SAP.P011c.WH.W1.Leaves
import AronowAudit.P011.P011_HomoskedasticCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P011c.WH.W1.P.T40_L1

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
open AronowAudit.P011.ProbabilityCompletion

noncomputable section

/-- The finite single-row repair underlying the stated oracle bound. -/
theorem route : SAP.P011c.WH.W1.T40_L1 := by
  intro n hn m c1 c2 hc1 hc2 hDep hs hBound hDeg ε hε
  let mp := Bridge.toModel m
  let d := 1 + c2
  let : IsProbabilityMeasure m.law := m.probability
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hd (i : Fin n) : (degree m.G i : ℝ) + 1 ≤ d := by dsimp [d]; linarith [hDeg i]
  have hL2 := weighted_memLp mp c1 hBound
  have hR := AronowAudit.P011.HomoskedasticCompletion.remainder_memLp_two hn mp c1 hBound
  have hRsecond := AronowAudit.P011.HomoskedasticCompletion.remainder_second_bound
    hn mp c1 d hc1.le hDep hBound hd
  have hAdj (i j : Fin n) : 0 ≤ adjacency m.G i j := by
    unfold adjacency
    split <;> norm_num
  have hGB : 1 ≤ gFactor m ∧ gFactor m ≤ d := by
    have hSum : (∑ i, ∑ j, adjacency m.G i j) ≤ (n : ℝ) * c2 := by
      calc
        _ ≤ ∑ _i : Fin n, c2 := Finset.sum_le_sum (fun i _ => by
          have hrow : (∑ j, adjacency m.G i j) = (degree m.G i : ℝ) :=
            (AronowAudit.P011.degree_row_sum m.G i).symm
          rw [hrow]
          exact hDeg i)
        _ = _ := by simp
    have hnon : 0 ≤ ∑ i, ∑ j, adjacency m.G i j :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hAdj i j))
    have hupper : (∑ i, ∑ j, adjacency m.G i j) / (n : ℝ) ≤ c2 :=
      (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hSum)
    have hlower := div_nonneg hnon hnR.le
    dsimp [gFactor, d]
    constructor <;> linarith
  have hCorr := AronowAudit.P011.pairwise_correlation_repair hn mp hDep hs hL2
  have hσ : 0 ≤ AronowAudit.P011.meanVariance mp :=
    AronowAudit.P011.CorrelationCompletion.meanVariance_nonneg hn mp hs hL2
  have hSum : (∑ i, ∑ j, adjacency m.G i j * AronowAudit.P011.rho mp i j) ≤
      ∑ i, ∑ j, adjacency m.G i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hCorr.2.1 i j) (hAdj i j)
  have hTrue : (n : ℝ) * var m (betaHat m) ≤ AronowAudit.P011.meanVariance mp * gFactor m := by
    have hId : (n : ℝ) * var m (betaHat m) = AronowAudit.P011.meanVariance mp *
        (1 + (∑ i, ∑ j, adjacency m.G i j * AronowAudit.P011.rho mp i j) / (n : ℝ)) := hCorr.1
    rw [hId]
    apply mul_le_mul_of_nonneg_left ?_ hσ
    unfold gFactor
    linarith [div_le_div_of_nonneg_right hSum hnR.le]
  have hScaled (y : Fin n → ℝ) :
      (n : ℝ) * V2 m.G (weighted m y) = gFactor m * sampleVariance (weighted m y) := by
    unfold V2 gFactor
    field_simp
  have hSpread : 0 ≤ AronowAudit.P011.meanSpread mp :=
    div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hnR.le
  have hPoint (y : Fin n → ℝ) :
      (n : ℝ) * (var m (betaHat m) - V2 m.G (weighted m y)) ≤
        d * |AronowAudit.P011.varianceRemainder mp y| := by
    rw [mul_sub, hScaled]
    have hRdef : sampleVariance (weighted m y) = AronowAudit.P011.meanVariance mp +
        AronowAudit.P011.meanSpread mp + AronowAudit.P011.varianceRemainder mp y := by
      unfold AronowAudit.P011.varianceRemainder
      change sampleVariance (weighted m y) = AronowAudit.P011.meanVariance mp +
        AronowAudit.P011.meanSpread mp +
          (sampleVariance (weighted m y) - AronowAudit.P011.meanVariance mp -
            AronowAudit.P011.meanSpread mp)
      ring
    rw [hRdef]
    have hg0 : 0 ≤ gFactor m := by linarith [hGB.1]
    have h1 := mul_nonneg hg0 hSpread
    have h2 := mul_le_mul_of_nonneg_left
      (neg_le_abs (AronowAudit.P011.varianceRemainder mp y)) hg0
    have h3 := mul_le_mul_of_nonneg_right hGB.2
      (abs_nonneg (AronowAudit.P011.varianceRemainder mp y))
    nlinarith [hTrue]
  have hsub : {y | (n : ℝ) * (var m (betaHat m) - V2 m.G (weighted m y)) > ε} ⊆
      {y | |AronowAudit.P011.varianceRemainder mp y| > ε / d} := by
    intro y hy
    change ε < (n : ℝ) * (var m (betaHat m) - V2 m.G (weighted m y)) at hy
    change ε / d < |AronowAudit.P011.varianceRemainder mp y|
    apply (div_lt_iff₀ hd0).mpr
    nlinarith [hPoint y]
  calc
    _ ≤ m.law.real {y | |AronowAudit.P011.varianceRemainder mp y| > ε / d} :=
      measureReal_mono (μ := m.law) hsub (measure_ne_top _ _)
    _ ≤ (∫ y, AronowAudit.P011.varianceRemainder mp y ^ 2 ∂m.law) / (ε / d)^2 :=
      AronowAudit.P011.HomoskedasticCompletion.second_moment_tail m.law _ hR _ (div_pos hε hd0)
    _ ≤ (4 * d * c1^4 / (n : ℝ)) / (ε / d)^2 :=
      div_le_div_of_nonneg_right hRsecond (sq_nonneg _)
    _ = _ := by
      have hdne : d ≠ 0 := hd0.ne'
      have hεne : ε ≠ 0 := hε.ne'
      dsimp [d] at *
      field_simp

end
end SAP.P011c.WH.W1.P.T40_L1

namespace SAP.P011c.WH.W1

theorem T40_L1_proof : T40_L1 := SAP.P011c.WH.W1.P.T40_L1.route

end SAP.P011c.WH.W1
