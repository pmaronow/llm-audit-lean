import SAP.P015b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P015b.Bridge

universe u v

open SAP.P015b Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal

theorem poolingCounterexample : PoolingCounterexample := by
  obtain ⟨hd₁, hd₂, ht₁, ht₂, hp₁, hp₂, hH, hm, hscalar, hcoord⟩ :=
    AronowAudit.P015.group_pooling_counterexample
  have hi₁ : firstGroupPrecision = (1+(firstGroupDesign.transpose*firstGroupDesign)⁻¹)⁻¹ :=
    (Matrix.inv_eq_left_inv hp₁).symm
  have hi₂ : secondGroupPrecision = (1+(secondGroupDesign.transpose*secondGroupDesign)⁻¹)⁻¹ :=
    (Matrix.inv_eq_left_inv hp₂).symm
  have hiH : (firstGroupPrecision+secondGroupPrecision)⁻¹ = poolingInverse :=
    Matrix.inv_eq_left_inv hH
  have ht₁' : sampleCoefficients firstGroupDesign ![0,0,0] = ![0,0] := ht₁
  have ht₂' : sampleCoefficients secondGroupDesign ![2,2,2] = ![2,0] := ht₂
  refine ⟨hd₁, hd₂, ht₁', ht₂', hi₁, hi₂, hiH, ?_, hscalar, ?_⟩
  · change (firstGroupPrecision+secondGroupPrecision)⁻¹.mulVec
      (firstGroupPrecision.mulVec (sampleCoefficients firstGroupDesign ![0,0,0])+
        secondGroupPrecision.mulVec (sampleCoefficients secondGroupDesign ![2,2,2])) = _
    rw [hiH, ht₁', ht₂']
    exact hm
  · intro t₁ t₂
    rw [hiH]
    exact hcoord t₁ t₂

theorem rawPoolingCounterexample : RawPoolingCounterexample := by
  exact AronowAudit.P015.group_raw_gls_counterexample

theorem matrixPooling : MatrixPooling := by
  exact AronowAudit.P015.corrected_matrix_pooling

theorem scalarPoolingCriterion : ScalarPoolingCriterion := by
  exact AronowAudit.P015.scalar_pooling_iff

theorem leverageComparison : T20Statement := by
  exact AronowAudit.P015.leverage_weight_comparison

theorem unconditionalLogisticFailure : T14Statement := by
  exact AronowAudit.P015.unconditional_logistic_misprint

theorem affinePredictor : AffinePredictorIdentity := by
  exact AronowAudit.P015.Wave1.affine_predictor

theorem fullRankLogistic : FullRankLogisticLinearization := by
  exact AronowAudit.P015.logistic_linearization

theorem causalOLS : CausalOLSConvergence.{u} := by
  intro Ω _ _ P _ K D Y₀ τ X hD hY hτ hX hiid hident hunconf ω hlinear hreg _ _ _
  exact AronowAudit.P015.ols_weighted_effect_limit P K D Y₀ τ X
    hD hY hτ hX hiid hident hunconf ω hlinear hreg

theorem zeroMoments : UnconfoundedMoments.{u} := by
  exact @AronowAudit.P015.unconfounded_zero_terms

theorem effectiveMean : T23Statement.{u} := by
  intro Ω _ P _ K D Z X hD hZ hX hiid hident ω hlinear hreg _ _ _ _ _
  exact AronowAudit.P015.effective_covariate_mean_limit P K D Z X
    hD hZ hX hiid hident ω hlinear hreg

theorem randomizedOLS : RandomizedOLSConvergence.{u} := by
  intro Ω _ _ P _ K D Y₀ τ X hD hY hτ hX hiid hident hrandom hreg _ _
  exact AronowAudit.P015.randomized_ols_limit P K D Y₀ τ X
    hD hY hτ hX hiid hident hrandom hreg

theorem randomizationCancellation : RandomizationCancellation.{u} := by
  exact @AronowAudit.P015.ProbabilityCompletion.randomization_population_weight_cancels

theorem taylorFailure : TaylorFailure := by
  exact AronowAudit.P015.TaylorCounterexample_checked

theorem taylorData : TaylorDataIdentities := by
  dsimp only [TaylorDataIdentities]
  refine ⟨?_, by norm_num, ?_⟩
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
  · intro N
    simp [residualEquation, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem logisticMLStationarity : LogisticMLStationarity := by
  exact AronowAudit.P015.PaperAssessments.nonlinear_extension_assessment.1

theorem squareLinkFailure : SquareLinkFailure := by
  exact squareLinkFailure_of_existing
    AronowAudit.P015.PaperAssessments.nonlinear_extension_assessment.2.2

theorem discretePositivity : DiscretePositivityImplications.{u,v} := by
  intro Ω B _ _ _ _ P _ X D hX hD h₂ x hx d d' hdd hp hp'
  exact ((AronowAudit.P015.PaperAssessments.positivity_passage_assessment.{u,v}.1
    P X D hX hD h₂).1 x hx).1 d d' hdd hp hp'

theorem smallWeightFamily : SmallWeightFamily := by
  exact AronowAudit.P015.PaperAssessments.positivity_passage_assessment.{0,0}.2.1.2.1

theorem smallWeightConsistency : SmallWeightConsistency := by
  have h := AronowAudit.P015.PaperAssessments.positivity_passage_assessment.{0,0}.2.1
  rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, hMean, _⟩
  exact ⟨hMean, h.2.2.2.2⟩

theorem fittedZeroFailure : FittedZeroFailure := by
  exact AronowAudit.P015.PaperAssessments.positivity_passage_assessment.{0,0}.2.2.2

theorem missingPairFailure : MissingPairFailure := by
  exact AronowAudit.P015.PositivityRefutation.printed_effective_positivity_refuted

end SAP.P015b.Bridge
