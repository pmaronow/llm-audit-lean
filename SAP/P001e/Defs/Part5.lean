import SAP.P001e.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v
noncomputable section

def T89Statement : Prop :=
  FiniteCondIndependent postWeights
    (fun i => (postOutcome i,postOutcome i,postCovariate1 i,postCovariate0 i))
    postAssignment (fun _ => ()) ∧
  finiteProbability postWeights (fun i => postAssignment i=1)=1/2 ∧
  (∀ i, realizedOutcome (postCovariate0 i) (postCovariate1 i) (postAssignment i)=postCovariate i) ∧
  finiteExpectation postWeights (fun i => postOutcome i-postOutcome i)=0 ∧
  ¬ FiniteCondIndependent postWeights (fun i => (postOutcome i,postOutcome i))
    postAssignment postCovariate ∧
  finiteProbability postWeights (fun i => postOutcome i=1 ∧ postCovariate i=1 ∧ postAssignment i=1)=1/3 ∧
  finiteProbability postWeights (fun i => postCovariate i=0)=1/2 ∧
  finiteProbability postWeights (fun i => postCovariate i=1)=1/2 ∧
  (∀ x ∈ ({0,1} : Finset ℝ), ∀ d ∈ ({0,1} : Finset ℝ),
    0 < finiteProbability postWeights (fun i => postCovariate i=x ∧ postAssignment i=d)) ∧
  finiteCellMean postWeights postOutcome postCovariate postAssignment 0 1=0 ∧
  finiteCellMean postWeights postOutcome postCovariate postAssignment 1 1=1 ∧
  finiteCellMean postWeights postOutcome postCovariate postAssignment 0 0=1/2 ∧
  finiteCellMean postWeights postOutcome postCovariate postAssignment 1 0=1 ∧
  postAdjustedContrast= -1/4

def T90Statement : Prop :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun d => ((0 : ℝ),d,(0 : ℝ))) =
    (volume.restrict (Set.Icc (0 : ℝ) 1)).map (fun d => (spikeResponse d,d,(0 : ℝ))) ∧
  spikeResponse (1/2)-spikeResponse 0=1 ∧
  spikeResponse (1/2)-spikeResponse (1/4)=1 ∧ (0 : ℝ)≠1

def PositiveMassDose : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
   (hX : Measurable X) (hD : Measurable D) (Y : ℝ → Ω → ℝ)
   (hY : ∀ t,Measurable (Y t)) (hi : ∀ t,Integrable (Y t) μ)
   (hobs : Measurable (fun ω => Y (D ω) ω)) (hobsI : Integrable (fun ω => Y (D ω) ω) μ)
   (hind : CondIndependent μ X hX (fun ω t => Y t ω) D) (d : ℝ)
   (hpos : ∀ x,0 < probability μ {ω | X ω=x} → 0 < probability μ {ω | X ω=x ∧ D ω=d}),
  (∀ x,0 < probability μ {ω | X ω=x} →
     cellMean μ X (Y d) x=
       cellMean μ (fun ω => (X ω,D ω)) (fun ω => Y (D ω) ω) (x,d)) ∧
   expectation μ (Y d)=∑' x : E,
     cellMean μ (fun ω => (X ω,D ω)) (fun ω => Y (D ω) ω) (x,d)*probability μ {ω | X ω=x}

def T91Statement : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (D : Ω → ℝ)
    (hX : Measurable X) (hD : Measurable D) (Y : ℝ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hi : ∀ t, Integrable (Y t) μ)
    (hobs : Measurable (fun ω => Y (D ω) ω))
    (hobsI : Integrable (fun ω => Y (D ω) ω) μ)
    (hind : CondIndependent μ X hX (fun ω t => Y t ω) D) (d d' : ℝ)
    (hpos : ∀ x, 0 < probability μ {ω | X ω=x} →
      0 < probability μ {ω | X ω=x ∧ D ω=d} ∧
      0 < probability μ {ω | X ω=x ∧ D ω=d'}),
    (∀ x, 0 < probability μ {ω | X ω=x} →
      cellMean μ X (Y d) x = cellMean μ (fun ω => (X ω,D ω)) (fun ω => Y (D ω) ω) (x,d) ∧
      cellMean μ X (Y d') x = cellMean μ (fun ω => (X ω,D ω)) (fun ω => Y (D ω) ω) (x,d')) ∧
    expectation μ (Y d)=standardizedDoseMean μ X D (fun ω => Y (D ω) ω) d ∧
    expectation μ (Y d')=standardizedDoseMean μ X D (fun ω => Y (D ω) ω) d' ∧
    expectation μ (fun ω => Y d' ω-Y d ω) =
      standardizedDoseMean μ X D (fun ω => Y (D ω) ω) d' -
      standardizedDoseMean μ X D (fun ω => Y (D ω) ω) d

def T92Statement : Prop :=
  IsUnit (exampleDesign.transpose*exampleDesign).det ∧
  leastSquaresCoef exampleDesign exampleY=exampleCoef ∧
  partialImputation ![1,8,9,3,5,7]=12103/4874 ∧
  fullImputation ![1,8,9,3,5,7]=6178/2437 ∧
  (12103/4874-6178/2437 : ℝ)= -253/4874 ∧
  partialImputation ![1,8,9,3,5,7] ≠ fullImputation ![1,8,9,3,5,7]

def ImputationNormalEquations : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (Y D g : Fin n → ℝ) (β : ℝ)
   (hD : ∀ i,D i=0 ∨ D i=1)
   (he : ∑ i,(Y i-g i-β*D i)=0) (heD : ∑ i,D i*(Y i-g i-β*D i)=0),
  (∑ i,(D i*(Y i-g i)+(1-D i)*(g i+β-Y i)))/(n : ℝ)=β ∧
   (∑ i,((g i+β)-g i))/(n : ℝ)=β

def T93Statement : Prop :=
  ImputationNormalEquations ∧
  IsUnit (exampleDesign.transpose*exampleDesign).det ∧
  leastSquaresCoef exampleDesign exampleY=exampleCoef ∧
  partialImputation exampleX1=exampleCoef 1 ∧
  fullImputation exampleX1=exampleCoef 1 ∧ exampleCoef 1=6178/2437

end
end SAP.P001e
