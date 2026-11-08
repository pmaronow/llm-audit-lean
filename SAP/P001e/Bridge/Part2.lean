import SAP.P001e.Bridge.Part1
import SAP.P001e.Defs
import AronowAudit.P001.P001_Foundations
import AronowAudit.P001.Wave1.Gap.WP001dB3
import AronowAudit.P001.Wave1.Gap.GLP0014B4
import AronowAudit.P001.Wave1.Gap.GP0014B2b
import AronowAudit.P001.Wave1.Gap.GP0014B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.Bridge
universe u v w z
open AronowAudit.P001

theorem ImputationNormalEquations_iff : SAP.P001e.ImputationNormalEquations ↔
  (∀ {n : ℕ} (hn : 0 < n) (Y D g : Fin n → ℝ) (β : ℝ)
   (hD : ∀ i,D i=0 ∨ D i=1)
   (he : ∑ i,(Y i-g i-β*D i)=0) (heD : ∑ i,D i*(Y i-g i-β*D i)=0),
  (∑ i,(D i*(Y i-g i)+(1-D i)*(g i+β-Y i)))/(n : ℝ)=β ∧
   (∑ i,((g i+β)-g i))/(n : ℝ)=β) := Iff.rfl

theorem post_probability_eq (A : Fin 6 → Prop) (dec : DecidablePred A) :
    finiteProbability postWeights A = @fprob 6 postTreatmentLaw A dec := by
  unfold finiteProbability fprob postWeights postTreatmentLaw
  congr 1
  funext i
  split_ifs <;> rfl

theorem post_expectation_eq (Y : Fin 6 → ℝ) :
    finiteExpectation postWeights Y = fmean postTreatmentLaw Y := rfl

theorem post_independence_iff {E F G : Type*}
    (Y : Fin 6 → E) (Z : Fin 6 → F) (X : Fin 6 → G) :
    FiniteCondIndependent postWeights Y Z X ↔ FCondIndep postTreatmentLaw Y Z X := by
  simp only [FiniteCondIndependent, FCondIndep, ← post_probability_eq]

theorem post_cellMean_eq (Y X D : Fin 6 → ℝ) (x d : ℝ) :
    finiteCellMean postWeights Y X D x d = fcond2 postTreatmentLaw Y X D x d := by
  unfold finiteCellMean fcond2
  rw [← post_probability_eq]
  congr 1

theorem standardizedDoseMean_eq {Ω E : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → E) (D Y : Ω → ℝ) (d : ℝ) :
    standardizedDoseMean μ X D Y d =
      ∑' x : E, cellMean μ (fun ω => (X ω,D ω)) Y (x,d) *
        SAP.P001e.probability μ {ω | X ω=x} := by
  unfold standardizedDoseMean
  apply tsum_congr
  intro x
  by_cases h : 0 < SAP.P001e.probability μ {ω | X ω=x}
  · simp only [h, if_pos]
  · have hz : SAP.P001e.probability μ {ω | X ω=x}=0 :=
      le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg
    simp [hz]

theorem post_latent :
  FiniteCondIndependent postWeights
     (fun i => (postOutcome i,postOutcome i,postCovariate1 i,postCovariate0 i)) postAssignment (fun _ => ()) ∧
   finiteProbability postWeights (fun i => postAssignment i=1)=1/2 ∧
   (∀ i,realizedOutcome (postCovariate0 i) (postCovariate1 i) (postAssignment i)=postCovariate i) ∧
   finiteExpectation postWeights (fun i => postOutcome i-postOutcome i)=0 ∧
   ¬ FiniteCondIndependent postWeights (fun i => (postOutcome i,postOutcome i)) postAssignment postCovariate := by
  have h := @AronowAudit.P001.post_treatment_latent_random_assignment
  simp only [← post_independence_iff,
    ← post_expectation_eq, ← post_cellMean_eq, ← postOutcome_eq, ← postCovariate_eq,
    ← postAssignment_eq, ← postCovariate0_eq, ← postCovariate1_eq, ← realizedOutcome_eq] at h
  simpa [finiteProbability, fprob, postWeights, postTreatmentLaw, postAssignment,
    postOutcome, postCovariate, Fin.sum_univ_succ] using h

theorem post_numbers :
  finiteProbability postWeights (fun i => postOutcome i=1 ∧ postCovariate i=1 ∧ postAssignment i=1)=1/3 ∧
   finiteProbability postWeights (fun i => postCovariate i=0)=1/2 ∧
   finiteCellMean postWeights postOutcome postCovariate postAssignment 0 1=0 ∧
   finiteCellMean postWeights postOutcome postCovariate postAssignment 1 1=1 ∧
   finiteCellMean postWeights postOutcome postCovariate postAssignment 0 0=1/2 ∧
   finiteCellMean postWeights postOutcome postCovariate postAssignment 1 0=1 ∧
   ((0*(1/2)+1*(1/2))-((1/2)*(1/2)+1*(1/2)) : ℝ)= -1/4 := by
  have h := @AronowAudit.P001.post_treatment_observable_mass_and_contrast
  simp only [← post_independence_iff,
    ← post_expectation_eq, ← post_cellMean_eq, ← postOutcome_eq, ← postCovariate_eq,
    ← postAssignment_eq, ← postCovariate0_eq, ← postCovariate1_eq, ← realizedOutcome_eq] at h
  simpa [finiteProbability, fprob, postWeights, postTreatmentLaw, postAssignment,
    postOutcome, postCovariate, Fin.sum_univ_succ] using h

theorem spike_witness :
  (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun d => ((0 : ℝ),d,(0 : ℝ)))=
     (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun d => (spikeResponse d,d,(0 : ℝ))) ∧
   spikeResponse (1/2)-spikeResponse 0=1 ∧ (0 : ℝ)≠1 := by
  exact @AronowAudit.P001.continuous_dose_nonidentification

theorem example_fit :
  IsUnit (exampleDesign.transpose*exampleDesign).det ∧
   leastSquaresCoef exampleDesign exampleY=exampleCoef := by
  exact @AronowAudit.P001.causal_example_ols_fit

theorem printed_numbers :
  partialImputation ![1,8,9,3,5,7]=12103/4874 ∧
   exampleCoef 1=6178/2437 ∧ (12103/4874-6178/2437 : ℝ)= -253/4874 ∧
   partialImputation ![1,8,9,3,5,7]≠exampleCoef 1 := by
  exact @AronowAudit.P001.misprinted_imputation_table_disagreement

theorem corrected_numbers :
  partialImputation exampleX1=exampleCoef 1 ∧
   (∑ i : Fin 6,(examplePrediction (exampleX1 i) (exampleX2 i) 1-
       examplePrediction (exampleX1 i) (exampleX2 i) 0))/6=exampleCoef 1 := by
  exact @AronowAudit.P001.corrected_imputation_table_agreement

theorem fitted_formula :
  ∀ {n K τ : ℕ} (g : ℝ → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (d : ℝ) (X : Fin n → Fin K → ℝ) (θ : Fin τ → ℝ),
  fittedPotentialAverage g d X θ=(∑ i,∫ y,y*g y d (X i) θ)/(n : ℝ) := by
  exact @AronowAudit.P001.ml_potential_mean_observed_covariates

end SAP.P001e.Bridge
