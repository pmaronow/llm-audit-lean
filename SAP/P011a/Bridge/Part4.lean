import SAP.P011a.Bridge.Part3
import AronowAudit.P011.P011_SignCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.Bridge

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000

theorem PathOLS_proved : SAP.P011a.PathOLS :=
  AronowAudit.P011.block_ols_representations.1

theorem ScaledQuadraticExpectation_proved : SAP.P011a.ScaledQuadraticExpectation := by
  intro F c1 c2 c3 c4 h k M hM
  exact AronowAudit.P011.quadratic_expectation (F.positive k) (model (F.model k))
    (AronowAudit.P011.ProbabilityCompletion.weighted_memLp (model (F.model k)) c1
      (h.2.2.2.2.2.2.1 k)) M hM

theorem CorrectedOptimal_proved : SAP.P011a.CorrectedOptimal := by
  intro n hn R A d x hm
  have hid (B : SAP.P011a.Graph n) (hB : SAP.P011a.Compatible R d B) :
      (n : ℝ)^2 * SAP.P011a.V1plus d B x = (∑ i, SAP.P011a.centered x i^2) +
        2*SAP.P011a.correctedEdgeObjective d x B := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hId,_⟩ := CorrectedFinite_proved hn R B d hB x
    exact hId
  refine ⟨?_, hid A hm.1⟩
  intro B hB
  have hle := mul_le_mul_of_nonneg_left (hm.2 B hB) (sq_nonneg (n : ℝ))
  linarith [hid A hm.1, hid B hB]

theorem DegreeOnlyBounds_proved : SAP.P011a.DegreeOnlyBounds := by
  intro n hn d D hd x
  have hempty : SAP.P011a.Compatible (SAP.P011a.emptyGraph n) d (SAP.P011a.emptyGraph n) := by
    constructor
    · intro i j h
      exact h
    · intro i
      simp [SAP.P011a.degree, SAP.P011a.emptyGraph]
  constructor
  · intro A hm
    obtain ⟨Ap,hp⟩ := (AronowAudit.P011.oracle_sharp_bound
      (SAP.P011a.emptyGraph n) (SAP.P011a.emptyGraph n) d hempty
      (fun B => SAP.P011a.V1plus d B x)).1
    exact (DegreeOnlyFinite_proved hn d D hd x A Ap hm hp).2.1
  · intro Ap hp
    obtain ⟨A,hm⟩ := (AronowAudit.P011.oracle_sharp_bound
      (SAP.P011a.emptyGraph n) (SAP.P011a.emptyGraph n) d hempty
      (fun B => SAP.P011a.V1 B x)).1
    exact (DegreeOnlyFinite_proved hn d D hd x A Ap hm hp).2.2

theorem OracleSpecialCases_proved : SAP.P011a.OracleSpecialCases := by
  intro F c1 c2 c3 c4 h hv hspecial
  have H := OracleMeanConditions_proved F c1 c2 c3 c4 h
  have hbias : 0 ≤ Filter.liminf (fun k => SAP.P011a.meanBias (F.model k)) atTop := by
    rcases hspecial with hequal | hclique
    · have hz : ∀ k i, SAP.P011a.delta (F.model k) i = 0 := by
        intro k i
        simp only [SAP.P011a.delta, hequal k i, sub_self]
      have hlim := H.1.mp (H.2.2.1 hz)
      rw [hlim.liminf_eq]
    · have hpsd : ∀ k, SAP.P011a.PSD (SAP.P011a.oracleMatrix (F.model k).G) :=
        fun k => (CliqueCharacterization_proved (F.positive k) (F.model k).G).1.mpr (hclique k)
      exact H.2.1.mp (H.2.2.2 hpsd)
  refine ⟨RevisedCorollaries_proved F c1 c2 c3 c4 h _
    (Or.inr (Or.inr (Or.inr ⟨hv,hbias,Or.inl rfl⟩))), ?_⟩
  intro A hm
  exact RevisedCorollaries_proved F c1 c2 c3 c4 h _
    (Or.inr (Or.inr (Or.inr ⟨hv,hbias,Or.inr ⟨A,hm,rfl⟩⟩)))

theorem HomoskedasticIdentities_proved : SAP.P011a.HomoskedasticIdentities := by
  intro F c1 c2 c3 c4 h hs k
  have hn : (F.size k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (F.positive k))
  have hL2 := AronowAudit.P011.ProbabilityCompletion.weighted_memLp (model (F.model k)) c1
    (h.2.2.2.2.2.2.1 k)
  have hvar := AronowAudit.P011.QuadraticCompletion.beta_variance (model (F.model k)) hL2
  change SAP.P011a.var (F.model k) (SAP.P011a.betaHat (F.model k)) =
    (∑ i, ∑ j, SAP.P011a.covariance (F.model k) i j)/(F.size k : ℝ)^2 at hvar
  have hspread : 0 ≤ SAP.P011a.meanSpread (F.model k) :=
    div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)
  obtain ⟨_,_,_,_,_,_,hupper,hg1,hg2,hpoint,_⟩ :=
    (HomoskedasticRepair_proved F c1 c2 c3 c4 h hs).1 k
  refine ⟨?_, hspread, ?_, ?_⟩
  · intro i
    change (∑ j, SAP.P011a.covariance (F.model k) j j)/(F.size k : ℝ) = _
    rw [Finset.sum_congr rfl (fun j _ => hs k j i)]
    simp [nsmul_eq_mul, hn]
  · unfold SAP.P011a.scaledTrue
    rw [hvar]
    field_simp
  · intro y
    refine ⟨?_, ?_, ?_⟩
    · rw [(hpoint y).1]
      nlinarith [hupper]
    · unfold SAP.P011a.varianceRemainder
      ring
    · have hscalar := AronowAudit.P011.one_sided_algebra 0 0
        (SAP.P011a.meanSpread (F.model k)) (SAP.P011a.varianceRemainder (F.model k) y)
        (SAP.P011a.gFactor (F.model k)) c2 hspread (by linarith) hg2 (by simp)
      simpa only [zero_add, zero_sub, neg_mul] using hscalar

theorem RelaxationProgramValues_proved : SAP.P011a.RelaxationProgramValues := by
  obtain ⟨hf,hfval,hupper,⟨a,ha,haval,hav⟩,hibound,_⟩ := RelaxationGaps_proved.1
  obtain ⟨_,htrival,htribound,_⟩ := RelaxationGaps_proved.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [SAP.P011a.average, Fin.sum_univ_succ]
  · norm_num [SAP.P011a.sampleVariance, SAP.P011a.centered, SAP.P011a.average, Fin.sum_univ_succ]
  · linarith [hfval]
  · intro b hb
    linarith [hupper b hb]
  · exact ⟨a,ha,by linarith,hav⟩
  · intro b hb
    linarith [hibound b hb]
  · rw [hfval]
    norm_num
  · linarith [htrival]
  · intro b hb
    linarith [htribound b hb]
  · refine ⟨fun _ => 0, ?_, a, ha, ?_⟩
    · norm_num [SAP.P011a.RelaxedFeasible, SAP.P011a.toUpper, SAP.P011a.emptyGraph]
    · simp only [SAP.P011a.relaxedObjective, mul_zero, Finset.sum_const_zero]
      linarith [haval]

theorem RelaxationNamedWitness_proved : SAP.P011a.RelaxationNamedWitness :=
  AronowAudit.P011.GapCompletion.six_witness

theorem SignWitnessFacts_proved : SAP.P011a.SignWitnessFacts := by
  refine ⟨AronowAudit.P011.SignCompletion.scaling_valid.1,
    AronowAudit.P011.SignCompletion.scaling_valid.2, ?_⟩
  intro k
  exact ⟨AronowAudit.P011.SignCompletion.scaled_variance (Nat.succ_pos k),
    AronowAudit.P011.SignCompletion.beta_zero (k+1)⟩

theorem SpectralDifference_proved : SAP.P011a.SpectralDifference := by
  intro n M hM
  exact AronowAudit.P011.SpectralConfidence.positive_part_difference_representation M hM

theorem AlternatingEstimatorIdentities_proved :
    ∀ k y, SAP.P011a.V2star (SAP.P011a.alternatingFamily.model k) y =
      SAP.P011a.V2 (SAP.P011a.alternatingFamily.model k).G (SAP.P011a.weighted (SAP.P011a.alternatingFamily.model k) y) ∧
    (SAP.P011a.alternatingFamily.size k : ℝ)*SAP.P011a.V2 (SAP.P011a.alternatingFamily.model k).G
      (SAP.P011a.weighted (SAP.P011a.alternatingFamily.model k) y) = SAP.P011a.sampleVariance (SAP.P011a.weighted (SAP.P011a.alternatingFamily.model k) y) ∧
    (SAP.P011a.alternatingFamily.size k : ℝ)*SAP.P011a.V2star (SAP.P011a.alternatingFamily.model k) y - SAP.P011a.scaledTrue SAP.P011a.alternatingFamily k =
      SAP.P011a.meanSpread (SAP.P011a.alternatingFamily.model k) + SAP.P011a.varianceRemainder (SAP.P011a.alternatingFamily.model k) y := by
  intro k y
  have hn : ((k+1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have haux : SAP.P011a.V2star (SAP.P011a.alternatingFamily.model k) y =
      SAP.P011a.V2 (SAP.P011a.alternatingFamily.model k).G
        (SAP.P011a.weighted (SAP.P011a.alternatingFamily.model k) y) :=
    AronowAudit.P011.auxiliary_empty_identity (model (SAP.P011a.alternatingFamily.model k)) rfl y
  have hscale : (SAP.P011a.alternatingFamily.size k : ℝ)*SAP.P011a.V2
      (SAP.P011a.alternatingFamily.model k).G (SAP.P011a.weighted (SAP.P011a.alternatingFamily.model k) y) =
      SAP.P011a.sampleVariance (SAP.P011a.weighted (SAP.P011a.alternatingFamily.model k) y) := by
    simp [SAP.P011a.V2, SAP.P011a.adjacency, SAP.P011a.alternatingFamily,
      SAP.P011a.alternatingModel, SAP.P011a.emptyGraph]
    field_simp
  have hmarg : SAP.P011a.meanVariance (SAP.P011a.alternatingFamily.model k) =
      SAP.P011a.alternatingWeight (k+1)^2 := by
    change (∑ i : Fin (k+1), SAP.P011a.covariance (SAP.P011a.alternatingModel (k+1)) i i) /
      ((k+1 : ℕ) : ℝ) = _
    have hdiag (i : Fin (k+1)) : SAP.P011a.covariance (SAP.P011a.alternatingModel (k+1)) i i =
        SAP.P011a.alternatingWeight (k+1)^2 := (AlternatingMoments_proved k).2.2.2.1 i |>.1
    rw [Finset.sum_congr rfl (fun i _ => hdiag i)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have htrue : SAP.P011a.scaledTrue SAP.P011a.alternatingFamily k =
      SAP.P011a.alternatingWeight (k+1)^2 := (AlternatingCounterexample_proved.2.2.1 k).2.2
  refine ⟨haux, hscale, ?_⟩
  rw [haux, hscale, htrue]
  unfold SAP.P011a.varianceRemainder
  rw [hmarg]
  ring

end
end SAP.P011a.Bridge
