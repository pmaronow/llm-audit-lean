/- The auxiliary correction assumes positive marginal variance and, for
consistency, vanishing between-unit mean variance. -/
import AronowAudit.P011.P011_CorollariesCompletion
import AronowAudit.P011.P011_HomoskedasticCompletion
import AronowAudit.P011.P011_CoverageCompletion

namespace AronowAudit.P011.AuxiliaryCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Matrix Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

def factor {n : ℕ} (m : Model n) : ℝ := 1+(∑i,∑j,adjacency m.G i j*rho m i j)/(n:ℝ)

lemma auxiliary_corrected_display_completed (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hs : ∀ k, Homoskedastic (F.model k))
    (hpos : ∀ k, 0 < meanVariance (F.model k)) :
    (∀ k y, (F.size k : ℝ)*V2star (F.model k) y-scaledTrue F k =
      (1+(∑ i, ∑ j, adjacency (F.model k).G i j*rho (F.model k) i j)/(F.size k : ℝ))*
        (sampleVariance (weighted (F.model k) y)-meanVariance (F.model k))) ∧
    InProbability F (fun k y => varianceRemainder (F.model k) y) (fun _ => 0) ∧
    (Tendsto (fun k => meanSpread (F.model k)) atTop (𝓝 0) →
      InProbability F (fun k y => (F.size k : ℝ)*V2star (F.model k) y) (scaledTrue F)) := by
  classical
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  have hScaling := h
  have hSample := revised_sample_variance F c1 c2 c3 c4 h
  rcases h with ⟨hNested,hc1,hc2,hc3,hc4,hDep,hBound,hDeg,hVar,hTheta⟩
  have hL2 (k : ℕ) := ProbabilityCompletion.weighted_memLp (F.model k) c1 (hBound k)
  have hCorr (k : ℕ) := pairwise_correlation_repair (F.positive k) (F.model k) (hDep k) (hs k) (hL2 k)
  have hId (k : ℕ) (y : Fin (F.size k)→ℝ) :
      (F.size k:ℝ)*V2star (F.model k) y-scaledTrue F k=
        factor (F.model k)*(sampleVariance (weighted (F.model k) y)-meanVariance (F.model k)) := by
    have hn0 : (F.size k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (F.positive k)
    rw [scaledTrue,(hCorr k).1]
    unfold V2star factor
    field_simp <;>ring
  have hK (k : ℕ) : 0≤factor (F.model k) ∧ factor (F.model k)≤1+c2 := by
    have hnR : 0<(F.size k:ℝ) := by exact_mod_cast F.positive k
    have hv : 0≤(F.size k:ℝ)*var (F.model k) (betaHat (F.model k)) :=
      mul_nonneg hnR.le (integral_nonneg (fun y=>sq_nonneg _))
    have he : (F.size k:ℝ)*var (F.model k) (betaHat (F.model k))=
        meanVariance (F.model k)*factor (F.model k) := (hCorr k).1
    have hlo : 0≤factor (F.model k) := by rw [he] at hv;exact (mul_nonneg_iff_of_pos_left (hpos k)).mp hv
    have hAdj (i j : Fin (F.size k)) : 0≤adjacency (F.model k).G i j := by unfold adjacency;split_ifs <;>norm_num
    have hSum : (∑i,∑j,adjacency (F.model k).G i j*rho (F.model k) i j)≤
        ∑i,∑j,adjacency (F.model k).G i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ((hCorr k).2.1 i j) (hAdj i j)
    have hle : factor (F.model k)≤gFactor (F.model k) := by
      unfold factor gFactor
      linarith [div_le_div_of_nonneg_right hSum hnR.le]
    exact ⟨hlo,hle.trans (printed_auxiliary_degree_bound F c1 c2 c3 c4 hScaling k).2⟩
  have hR : InProbability F (fun k y=>varianceRemainder (F.model k) y) (fun _=>0) := by
    intro ε hε
    have hh := hSample ε hε
    have he (k : ℕ) (y : Fin (F.size k)→ℝ) : varianceRemainder (F.model k) y-0=
        sampleVariance (weighted (F.model k) y)-(meanVariance (F.model k)+meanSpread (F.model k)) := by
      unfold varianceRemainder
      ring
    simpa only [he] using hh
  refine ⟨hId,hR,?_⟩
  intro hSpread
  let μ := fun k=>(F.model k).law
  let X := fun k y=>sampleVariance (weighted (F.model k) y)-meanVariance (F.model k)
  have hRC : CoverageCompletion.RowCP μ (fun k y=>varianceRemainder (F.model k) y) 0 := hR
  have hX : CoverageCompletion.RowCP μ X 0 := by
    apply CoverageCompletion.rowCP_moving_center μ X (fun k=>meanSpread (F.model k)) 0 ?_ hSpread
    simpa only [CoverageCompletion.RowCP,X,varianceRemainder,sub_zero] using hRC
  have hd : 0<1+c2 := by linarith
  intro ε hε
  apply squeeze_zero (fun k=>measureReal_nonneg) (fun k=>?_) (hX (ε/(1+c2)) (div_pos hε hd))
  apply measureReal_mono (μ:=μ k) ?_ (measure_ne_top _ _)
  intro y hy
  change ε< |(F.size k:ℝ)*V2star (F.model k) y-scaledTrue F k| at hy
  change ε/(1+c2)< |X k y-0|
  rw [sub_zero]
  rw [hId,abs_mul,abs_of_nonneg (hK k).1] at hy
  have hb := mul_le_mul_of_nonneg_right (hK k).2 (abs_nonneg (X k y))
  apply (div_lt_iff₀ hd).mpr
  dsimp [X] at hb ⊢
  nlinarith

end
end AronowAudit.P011.AuxiliaryCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem auxiliary_corrected_display (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hs : ∀ k, Homoskedastic (F.model k))
    (hpos : ∀ k, 0 < meanVariance (F.model k)) :
    (∀ k y, (F.size k : ℝ)*V2star (F.model k) y-scaledTrue F k =
      (1+(∑ i, ∑ j, adjacency (F.model k).G i j*rho (F.model k) i j)/(F.size k : ℝ))*
        (sampleVariance (weighted (F.model k) y)-meanVariance (F.model k))) ∧
    InProbability F (fun k y => varianceRemainder (F.model k) y) (fun _ => 0) ∧
    (Tendsto (fun k => meanSpread (F.model k)) atTop (𝓝 0) →
      InProbability F (fun k y => (F.size k : ℝ)*V2star (F.model k) y) (scaledTrue F)) := by
  exact AuxiliaryCompletion.auxiliary_corrected_display_completed F c1 c2 c3 c4 h hs hpos

end AronowAudit.P011

