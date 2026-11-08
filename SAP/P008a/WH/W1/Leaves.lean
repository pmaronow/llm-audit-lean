import SAP.P008a.Defs.WholeW1
import SAP.P008a.WH.W1.Common

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

/-- T9: every squared Euclidean distance in [0,4]^2 is at most 32.
Use EuclideanSpace.dist_sq_eq, expand the two-coordinate sum, bound each
coordinate difference in [-4,4], and use nlinarith. No regression premise is needed. -/
def T9_L1 : Prop := WholeBoxBound

/-- T10: the sum of squared actual treatment-coefficient scores is positive
exactly when some actual OLS residual is nonzero, and vanishes exactly when all
residuals vanish. Both arms are present. Use binary_regression_weights_residuals;
each contrastWeight is either 1/N1 or -1/N0, hence nonzero. Apply
Finset.sum_pos_iff_of_nonneg and Finset.sum_sq_eq_zero_iff. This is a finite
algebra lemma for every N, including the empty case excluded by the arm premises. -/
def T10_L1 : Prop :=
  ∀ {N : ℕ} (z : Assignment N) (m : Fin N → ℝ),
    1 ≤ nTreated z → 1 ≤ nControl z →
    (0 < ∑ i, (wholeOLSScore z m i)^2 ↔ ∃ i, olsResidual z m i ≠ 0) ∧
    ((∑ i, (wholeOLSScore z m i)^2) = 0 ↔ ∀ i, olsResidual z m i = 0)

/-- T7: the rational parametrization has positive denominators, nonzero
1+u, unit norm, the printed inverse ratio, strictly increasing ratios and
distinct directions. Prove the rational identities by field_simp/ring using
40000^2+ell^2>0. Strict monotonicity follows from ell=2(k+1)-40001;
recover k from v/(1+u). Transfer u^2+v^2=1 with real_norm_sq_eq. -/
def T7_L1 : Prop := WholeRiskAlgebra

/-- T7: own-circle distances, centre separation and separation from other
centres. Assuming only unit directions, use norm_smul and positive radii for
the first assertion. Check the sixteen centre pairs using dist_sq_eq for
the second; dist_triangle gives 20-5/2=35/2 for the last assertion. -/
def T7_L2 : Prop :=
  (∀ k : RiskCell, ‖wholeRiskDirection k‖ = 1) → WholeRiskDistances

/-- T7: the combined centre/circle-label map is injective. The algebra and
distance certificates are explicit prerequisites. Different centre clusters
are disjoint by 35/2>5/2. Within one cluster, distances identify the radius,
then nonzero scalar cancellation and direction injectivity identify k.
Positive radii exclude centres from their own circles. -/
def T7_L3 : Prop :=
  WholeRiskAlgebra → WholeRiskDistances → Function.Injective wholeRiskEmbedding

/-- T7: the field has 640004 points and each geometric circle is precisely
the image of its 40000 cell labels. Given injectivity and the distance
certificate, use card_image_of_injective and Fintype.card_sum/card_prod.
For membership, rule out centres and other clusters by separation and
identify the radius by injectivity of ![1,3/2,2,5/2]. Do not enumerate cells. -/
def T7_L4 : Prop :=
  Function.Injective wholeRiskEmbedding → WholeRiskDistances → WholeRiskCircles

/-- T7: certify the genuine counting-circle measures and integrals, for
both schedules. Given injective coordinates and the exact circle sets,
restrict count to each finite circle, identify it with the sum of its
distinct Dirac masses, and use integrable_finsetSum_measure,
integrable_dirac and integral_finsetSum_measure. This proves finite mass
40000 and integrability for every real function before any mean is used. -/
def T7_L5 : Prop :=
  Function.Injective wholeRiskEmbedding → WholeRiskCircles → WholeRiskMeasures

/-- T7: uniform sampling of planar circle points equals independent uniform
node/radius/cell sampling. Given injectivity, use card_image_of_injective,
sum_image, and Fintype.sum_prod_type. Function.Injective.extend_apply gives
the owner of each point. Divide the finite sums by 4*4*40000. The identity
is for every test function, so it specifies the entire sampling law. -/
def T7_L6 : Prop :=
  Function.Injective wholeRiskEmbedding → WholeRiskSampling

/-- Assemble T9; only the box-distance bound is left to a writer. -/
theorem T9_assembly (h1 : T9_L1) : T9WholeStatement := by
  refine ⟨bandwidth_spatial, ols_identities, ?_, h1, ?_⟩
  · have hp : 1 ≤ nTreated wholeBandwidthAssignment := by
      norm_num [AronowAudit.P008.univ_four, wholeBandwidthAssignment, nTreated, bit]
    have hn : 1 ≤ nControl wholeBandwidthAssignment := by
      norm_num [AronowAudit.P008.univ_four, wholeBandwidthAssignment, nControl, nTreated, bit]
    rcases ols_identities wholeBandwidthAssignment wholeBandwidthMeans hp hn with
      ⟨_, _, _, hw, hr, hs, _, _, _⟩
    let X := binaryDesign wholeBandwidthAssignment
    have hg : X.transpose * X = !![(4 : ℝ), 2; 2, 2] := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [AronowAudit.P008.univ_four, X, binaryDesign, wholeBandwidthAssignment, bit,
          Matrix.mul_apply, Fin.sum_univ_succ]
    have hi : (X.transpose * X)⁻¹ = !![(1 / 2 : ℝ), -1 / 2; -1 / 2, 1] := by
      rw [hg, Matrix.inv_def]
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of, Ring.inverse_eq_inv]
    have hb : wholeOLSCoefficient wholeBandwidthAssignment wholeBandwidthMeans = ![1, 4] := by
      change ((X.transpose * X)⁻¹).mulVec (X.transpose.mulVec wholeBandwidthMeans) = _
      rw [hi]
      ext a
      fin_cases a <;> norm_num [AronowAudit.P008.univ_four, X, binaryDesign, wholeBandwidthAssignment,
        wholeBandwidthMeans, bit, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    have hres : olsResidual wholeBandwidthAssignment wholeBandwidthMeans = ![-1, 1, -1, 1] := by
      ext i
      rw [hr]
      fin_cases i <;> norm_num [AronowAudit.P008.univ_four, groupResidual, groupMean, nTreated, nControl,
        wholeBandwidthAssignment, wholeBandwidthMeans, bit, Fin.sum_univ_succ]
    have hweight : wholeOLSWeight wholeBandwidthAssignment = ![-1 / 2, -1 / 2, 1 / 2, 1 / 2] := by
      ext i
      rw [hw]
      fin_cases i <;> norm_num [AronowAudit.P008.univ_four, contrastWeight, nTreated, nControl,
        wholeBandwidthAssignment, bit, Fin.sum_univ_succ]
    have hscore : wholeOLSScore wholeBandwidthAssignment wholeBandwidthMeans = wholeBandwidthScores := by
      rw [hs]
      exact funext AronowAudit.P008.grid_position_counterexample.1
    refine ⟨hb, hres, hweight, hscore, by norm_num, by norm_num, by norm_num,
      ?_, ?_, ?_, ?_, ?_, by norm_num⟩
    · intro i l
      fin_cases i <;> fin_cases l <;> norm_num [bandwidthExampleDistance]
    · intro i l
      fin_cases i <;> fin_cases l <;> norm_num [bandwidthExampleDistance]
    · norm_num [hac, wholeBandwidthScores, bandwidthExampleDistance, Fin.sum_univ_succ]
    · norm_num [wholeBandwidthScores, Fin.sum_univ_succ]
    · norm_num [hac, wholeBandwidthScores, bandwidthExampleDistance, Fin.sum_univ_succ]
  · refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    · intro i a
      fin_cases i <;> fin_cases a <;> norm_num [toyNode]
    · intro p hp z m h₁ h₀
      have hd := h1 p hp
      have hall : ∀ i l, dist (p i) (p l) ≤ (32 / 5 : ℝ) := by
        intro i l
        nlinarith [hd i l, sq_nonneg (dist (p i) (p l) - 32 / 5)]
      have hz : (∑ i, wholeOLSScore z m i) = 0 :=
        (ols_identities z m h₁ h₀).2.2.2.2.2.2.2.1
      have hv : hac (wholeOLSScore z m) (fun i l => dist (p i) (p l)) (32 / 5) = 0 :=
        AronowAudit.P008.hac_all_pairs_zero _ _ _ hall hz
      have ha : archivedVariance (wholeOLSScore z m)
          (fun i l => dist (p i) (p l)) (2 / 5) 6 = 0 := by
        norm_num [archivedVariance]
        exact hv
      refine ⟨fun i l => ite_eq_left (hall i l), ?_, ha, ?_⟩
      · rw [hv, hz]; norm_num
      · intro h
        rw [ha]
        norm_num

/-- Assemble T10 from finite score positivity and the existing OLS/HAC identities. -/
theorem T10_assembly (h1 : T10_L1) : T10WholeStatement := by
  refine ⟨corrected_counting, ols_identities, ?_, ?_, ?_⟩
  · intro N z m D c h₁ h₀ j k
    refine ⟨rfl, rfl, ?_⟩
    intro hall
    have hz : (∑ i, wholeOLSScore z m i) = 0 :=
      (ols_identities z m h₁ h₀).2.2.2.2.2.2.2.1
    have hv : hac (wholeOLSScore z m) D c = 0 :=
      AronowAudit.P008.hac_all_pairs_zero _ D c hall hz
    exact ⟨by rw [hv, hz]; norm_num, hv⟩
  · intro i l
    by_cases hil : i = l
    · subst l; norm_num
    · have hsep : (2 / 5 : ℝ) < dist (toyNode i) (toyNode l) :=
        (AronowAudit.P008.toy_cutoff_is_hc0 (fun _ => 0)).1 i l hil
      simp only [ite_eq_right hil, ite_eq_right (not_le.mpr hsep)]
  · intro z m h₁ h₀
    have ht := AronowAudit.P008.toy_cutoff_is_hc0 (wholeOLSScore z m)
    have hh : hac (wholeOLSScore z m) (fun i l => dist (toyNode i) (toyNode l)) (2 / 5) =
        ∑ i, (wholeOLSScore z m i)^2 := ht.2
    have he : hac (wholeOLSScore z m) (fun i l => dist (toyNode i) (toyNode l)) (2 / 5) =
        hac (wholeOLSScore z m) (fun i l => dist (toyNode i) (toyNode l)) 0 := by
      apply ht.2.trans
      symm
      exact AronowAudit.P008.hac_equals_hc0 _ _ 0 le_rfl (fun _ => dist_self _)
        (fun i l hil => lt_trans (by norm_num) (ht.1 i l hil))
    have hs : wholeOLSScore z m = regressionScore z m :=
      (ols_identities z m h₁ h₀).2.2.2.2.2.1
    have ha : archivedVariance (wholeOLSScore z m)
        (fun i l => dist (toyNode i) (toyNode l)) (2 / 5) 6 = 0 := by
      rw [hs]
      exact (AronowAudit.P008.toy_archived_sixth_row_incompatible z m
        (ne_of_gt (lt_of_lt_of_le zero_lt_one h₁))
        (ne_of_gt (lt_of_lt_of_le zero_lt_one h₀))).2.1
    refine ⟨hh, he, ?_, ?_, ha⟩
    · rw [hh]; exact (h1 z m h₁ h₀).1
    · rw [hh]; exact (h1 z m h₁ h₀).2

/-- Assemble the geometric model and transfer every finite numerical clause
to its actual spatial means and its uniform planar sampling probability. -/
theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) (h3 : T7_L3)
    (h4 : T7_L4) (h5 : T7_L5) (h6 : T7_L6) : T7WholeStatement := by
  have hd : WholeRiskDistances := h2 (fun k => (h1.1 k).2.2.2.2)
  have hi : Function.Injective wholeRiskEmbedding := h3 h1 hd
  have hc : WholeRiskCircles := h4 hi hd
  have hm : WholeRiskMeasures := h5 hi hc
  have hs : WholeRiskSampling := h6 hi
  have hy (c : Bool) (l : WholeRiskLabel) (z : Assignment 4) :
      wholeRiskY c (wholeRiskEmbedding l) z = wholeRiskLabelOutcome c l z := by
    exact congrFun (hi.extend_apply (wholeRiskLabelOutcome c) (fun _ _ => 0) l) z
  have hyc (c : Bool) (i : Fin 4) (z : Assignment 4) :
      wholeRiskY c (wholeRiskCentre i) z = 0 := hy c (.inl i) z
  have hyr (i j : Fin 4) (k : RiskCell) (z : Assignment 4) :
      wholeRiskY false (wholeRiskPoint i j k) z = riskOutcome i j k z :=
    hy false (.inr (i, j, k)) z
  have hyb (i j : Fin 4) (k : RiskCell) (z : Assignment 4) :
      wholeRiskY true (wholeRiskPoint i j k) z = companionRiskOutcome i j k z :=
    hy true (.inr (i, j, k)) z
  have hMr (i j : Fin 4) (z : Assignment 4) :
      (wholeRiskModel false).M i (wholeRiskRadius j) z = riskM i j z := by
    change ((wholeRiskModel false).circleMass i (wholeRiskRadius j))⁻¹ *
      (∫ x, wholeRiskY false x z ∂(wholeRiskModel false).circleMeasure i (wholeRiskRadius j)) = _
    rw [(hm false i j).2.2.1, ((hm false i j).2.2.2.2 (fun x => wholeRiskY false x z)).2]
    simp_rw [hyr]
    simp [riskM, countMean, div_eq_mul_inv, mul_comm]
  have hMb (i j : Fin 4) (z : Assignment 4) :
      (wholeRiskModel true).M i (wholeRiskRadius j) z = companionRiskM i j z := by
    change ((wholeRiskModel true).circleMass i (wholeRiskRadius j))⁻¹ *
      (∫ x, wholeRiskY true x z ∂(wholeRiskModel true).circleMeasure i (wholeRiskRadius j)) = _
    rw [(hm true i j).2.2.1, ((hm true i j).2.2.2.2 (fun x => wholeRiskY true x z)).2]
    simp_rw [hyb]
    simp [companionRiskM, countMean, div_eq_mul_inv, mul_comm]
  have ho : WholeRiskOutcomes := by
    refine ⟨hyc, hyr, hyb, ?_, hMr, hMb⟩
    intro c x hx z
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
    rw [hy]
    cases l with
    | inl i => exact Or.inl rfl
    | inr t =>
      cases c
      · exact AronowAudit.P008.risk_circle_calculation.1 t.1 t.2.1 t.2.2 z
      · exact AronowAudit.P008.binary_companion_counterexample_bernoulli.1 t.1 t.2.1 t.2.2 z
  have hmr (i j : Fin 4) (b : Bool) :
      (wholeRiskModel false).m (uniformLaw (Assignment 4)) i b (wholeRiskRadius j) =
        ((riskBaseline i : ℝ) - 321 * bit b) / 40000 := by
    unfold SpatialModel.m marginal
    simp_rw [hMr]
    exact AronowAudit.P008.summed_risk_counterexample_bernoulli.1 i j b
  have her (i j : Fin 4) : (wholeRiskModel false).nodeEffect (uniformLaw (Assignment 4)) i
      (wholeRiskRadius j) = -321 / 40000 := by
    simp only [SpatialModel.nodeEffect, hmr]
    norm_num [bit]
    ring
  have har (j : Fin 4) : (wholeRiskModel false).amr (uniformLaw (Assignment 4))
      (wholeRiskRadius j) = -321 / 40000 := by
    simp only [SpatialModel.amr, her]
    norm_num
  have hhr (j : Fin 4) : hajek (fun i z => (wholeRiskModel false).M i (wholeRiskRadius j) z)
      ![true, true, false, false] = -321 / 40000 := by
    simp_rw [hMr]
    exact AronowAudit.P008.summed_risk_counterexample_bernoulli.2.2.1 j
  have hmb (i j : Fin 4) (b : Bool) :
      (wholeRiskModel true).m (uniformLaw (Assignment 4)) i b (wholeRiskRadius j) =
        1 - bit b := by
    unfold SpatialModel.m marginal
    simp_rw [hMb, show ∀ i j z, companionRiskM i j z = 1 - bit (z i) from
      AronowAudit.P008.binary_companion_counterexample_bernoulli.2.1]
    simp only [Function.update_self]
    exact AronowAudit.P008.expect_const (SAP.P008a.Bridge.toLaw (uniformLaw (Assignment 4))) _
  have hab (j : Fin 4) : (wholeRiskModel true).amr (uniformLaw (Assignment 4))
      (wholeRiskRadius j) = -1 := by
    simp only [SpatialModel.amr, SpatialModel.nodeEffect, hmb]
    norm_num [bit]
  have hhb (j : Fin 4) : hajek (fun i z => (wholeRiskModel true).M i (wholeRiskRadius j) z)
      ![true, true, false, false] = -1 := by
    simp_rw [hMb]
    exact AronowAudit.P008.risk_design_and_companion_estimates.2.2.1 j
  have hp (b : Bool) : wholeRiskSpatialProbability b =
      riskSamplingProbability (uniformLaw (Assignment 4)) b := by
    rw [wholeRiskSpatialProbability, hs.2.2]
    simp_rw [hs.2.1, hyr]
    unfold riskSamplingProbability
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact countMean_expect (uniformLaw (Assignment 4))
      (fun k z => riskOutcome i j k (Function.update z i b))
  have hp₀ : wholeRiskSpatialProbability false = 7 / 400 :=
    (hp false).trans AronowAudit.P008.risk_sampling_probabilities_bernoulli.1
  have hp₁ : wholeRiskSpatialProbability true = 379 / 40000 :=
    (hp true).trans AronowAudit.P008.risk_sampling_probabilities_bernoulli.2.1
  refine ⟨risk_counting, h1, hd, hi, hc, hm, ho, hs, hmr, her, har, hhr,
    ?_, ?_, hp, hp₀, hp₁, ?_, ?_, ?_, hmb, hab, ?_, hhb, ?_, ?_,
    by norm_num, by norm_num, by norm_num⟩
  · simp_rw [hhr]; norm_num
  · simp_rw [har]; norm_num
  · rw [hp₀, hp₁]; norm_num
  · intro w hw hsum
    simp_rw [har]
    rw [← Finset.sum_mul, hsum, hp₀, hp₁]
    norm_num
  · rw [hp₀]; norm_num
  · simp_rw [hab]; norm_num
  · simp_rw [hhb]; norm_num
  · intro a b ha ha' hb hb'
    constructor <;> linarith

end
end SAP.P008a.WH.W1
