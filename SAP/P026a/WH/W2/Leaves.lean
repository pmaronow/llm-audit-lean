import SAP.P026a.WH.W2.Glue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.WH.W2

open Finset
open scoped BigOperators
noncomputable section

/-- Weighted normal equations and a nonsingular rational Gram matrix identify
the unique minimizer among all real coefficient vectors. Prove the weighted
sum-of-squares decomposition. A zero excess loss forces the weighted fitted
difference to vanish; multiplying by the design gives Gram times the coefficient
difference zero. Transport the rational determinant to ℝ and use its inverse.
Zero weights are allowed, so the same lemma handles fits restricted to a block.
The empty coefficient type is harmless: it has exactly one coefficient vector. -/
def T7_L1 : Prop :=
  ∀ (k : ℕ) (A : Matrix (Fin 16) (Fin k) ℚ) (q y : Fin 16 → ℚ)
    (c : Fin k → ℚ), w2ValidFit A q y c → w2UniqueFit A q y c

/-- Every FE (Cov.) design has full column rank. Certify its rational four-by-four
Gram determinant on the ninety allocations. Use the exported treatment-mean and
cross-product certificates, or simply split the finite allocations and evaluate
the determinant. Exact enumeration gives positive determinants (minimum 5420);
only the displayed nonzero assertion is needed. -/
def T7_L2 : Prop :=
  ∀ w : W2Allocation, (w2Gram (w2FeCovDesign w) (fun _ => 1)).det ≠ 0

/-- The IPW weights are the positive inverse observed-arm marginals, both arm
weight totals are positive, and the weighted-mean coefficient vector satisfies
the nonsingular normal equations. Rewrite marginals using `table_marginal`.
Then either use the two arm-sum identities algebraically or check all ninety
allocations over ℚ. No real optimization argument belongs in this finite leaf. -/
def T7_L3 : Prop :=
  ∀ w : W2Allocation,
    (∀ i, 0 < w2IPWWeight w i ∧ w2IPWWeight w i =
      1 / inclusion paperTableUnitDesign (paperTableUnitDesign.treatment w i) i) ∧
    0 < w2IPWArmWeight w true ∧ 0 < w2IPWArmWeight w false ∧
    w2ValidFit (w2IPWDesign w) (w2IPWWeight w) paperTableY (w2IPWBeta w)

/-- The within-block treatment norm is positive and the FE coefficient vector
without X satisfies nonsingular normal equations on all ninety allocations.
Reuse the treatment-mean certificate, center within each block, and verify the
three normal equations and the three-by-three Gram determinant over ℚ. -/
def T7_L4 : Prop :=
  ∀ w : W2Allocation, 0 < (∑ i, (paperTableCenteredT w i)^2) ∧
    w2ValidFit (w2FeDesign w) (fun _ => 1) paperTableY (w2FeBeta w)

/-- The missing HT variance-estimator second moment. Unfold variance, rewrite
the marginal and joint probabilities with `table_marginal` and `table_joint`,
and evaluate the ninety rational values of equation [35]. A cached value table
can keep kernel computation small. This is a population variance, dividing by 90. -/
def T7_L5 : Prop :=
  designVariance paperTableDesign w2HTVariance = 10147/7372800

/-- The missing prior-adjusted variance-estimator second moment. Follow L5 with
the existing prior residual cluster totals. The same exact finite computation
gives population variance 20083/52428800. -/
def T7_L6 : Prop :=
  designVariance paperTableDesign w2PriorVariance = 20083/52428800

/-- IPW ATE mean/bias, SE, RMSE and variance round respectively to
-.014, .276, .277 and .076. Compute the weighted arm means exactly on the ninety
allocations, cache their rational values, and calculate E[e] and E[e²]-E[e]².
Prove the four rational rounding intervals by kernel evaluation. -/
def T7_L7 : Prop :=
  w2ATECertificate w2IPWEstimate (-14/1000) (276/1000) (277/1000) (76/1000)

/-- IPW HC1 variance-estimator mean, bias, SE and RMSE round to
.071, -.005, .017 and .018. Certify the inverse of each two-by-two Gram matrix
by multiplication, then evaluate the ten cluster scores and the factor 25/21.
Cache the ninety exact sandwich values; compute their two moments and the
ATE variance, and prove the four rational intervals. No statistical limit is used. -/
def T7_L8 : Prop :=
  w2VarianceCertificate w2IPWEstimate w2IPWVariance
    (71/1000) (-5/1000) (17/1000) (18/1000)

/-- FE ATE mean/bias, SE, RMSE and variance round respectively to
-.016, .283, .283 and .080. Substitute the certified block treatment means into
the within-block slope, cache its ninety rational values, and evaluate the
first and second population moments and their squared rounding intervals. -/
def T7_L9 : Prop :=
  w2ATECertificate w2FeEstimate (-16/1000) (283/1000) (283/1000) (80/1000)

/-- FE HC1 variance-estimator mean, bias, SE and RMSE round to
.074, -.006, .019 and .020. Certify the inverse three-by-three Gram matrices
by multiplication (or exploit within-block residualization), evaluate the
cluster scores with the factor 50/39, and cache the ninety rational values.
Then compute their population moments and prove the four rational intervals. -/
def T7_L10 : Prop :=
  w2VarianceCertificate w2FeEstimate w2FeVariance
    (74/1000) (-6/1000) (19/1000) (20/1000)

/-- Whole T7, assembled from existing exact moments, finite certificates,
and one general weighted least-squares lemma. -/
theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) (h3 : T7_L3) (h4 : T7_L4)
    (h5 : T7_L5) (h6 : T7_L6) (h7 : T7_L7) (h8 : T7_L8)
    (h9 : T7_L9) (h10 : T7_L10) : T7WholeStatement := by
  have hb := Bridge.target7
  rcases hb with ⟨hpos, hlinear, hlinearRound, hfe, hu⟩
  rcases hlinear with ⟨hlm, hls, hlev, hlz⟩
  rcases hlinearRound with ⟨hlse, hlv, hlsev⟩
  rcases hfe with ⟨hflo, hfhi, hfvlo, hfvhi, hfse, hfrm, hcomp⟩
  rcases hu with ⟨hclusters, hhm, hhs, hhev, hpm, hps, hpev, hhv, hpv⟩
  have hlcert := unbiased_certificates w2LinearEstimate w2LinearVariance
    (38307/634880) (2400328658503/15687787688755200) (246/1000) (60/1000) (12/1000)
    hlm hls hlev hlz hlse hlv hlsev
  have hhcert := unbiased_certificates w2HTEstimate w2HTVariance
    (353/1920) (10147/7372800) (429/1000) (184/1000) (37/1000)
    hhm hhs hhev h5 (by norm_num [sdRoundsToThree]) hhv (by norm_num [sdRoundsToThree])
  have hpcert := unbiased_certificates w2PriorEstimate w2PriorVariance
    (233/2560) (20083/52428800) (302/1000) (91/1000) (20/1000)
    hpm hps hpev h6 (by norm_num [sdRoundsToThree]) hpv (by norm_num [sdRoundsToThree])
  refine ⟨Bridge.target7, ?_, ?_, ?_, ?_, ?_, generalized_identifications,
    h5, h6, ?_, ?_, ?_, ?_, ?_, sqrt_rounds hfse (by norm_num),
    sqrt_rounds hfrm (by norm_num), ?_⟩
  · simp [averageEffect]
  · intro b
    exact h1 2 w2LinearDesign (w2BlockWeight b) paperTableY (w2LinearBeta b) (linear_valid b)
  · intro w
    apply h1 4 (w2FeCovDesign w) (fun _ => 1) paperTableY (w2FeCovBeta w)
    exact ⟨by norm_num, h2 w, feCov_normal w⟩
  · intro w
    obtain ⟨hw, ht, hc, hv⟩ := h3 w
    exact ⟨hw, ht, hc, hv.2.1, h1 2 _ _ _ _ hv⟩
  · intro w
    obtain ⟨hn, hv⟩ := h4 w
    exact ⟨hn, hv.2.1, h1 3 _ _ _ _ hv⟩
  · exact column_from_certificates _ _ _ _ _ _ _ _ _ _ hlcert.1 hlcert.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact column_from_certificates _ _ _ _ _ _ _ _ _ _ hhcert.1 hhcert.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact column_from_certificates _ _ _ _ _ _ _ _ _ _ hpcert.1 hpcert.2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact column_from_certificates _ _ _ _ _ _ _ _ _ _ h7 h8
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact column_from_certificates _ _ _ _ _ _ _ _ _ _ h9 h10
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · apply Real.sqrt_lt_sqrt (by norm_num)
    exact_mod_cast hcomp

end
end SAP.P026a.WH.W2
