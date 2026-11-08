import SAP.P001e.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v
noncomputable section

def T84Core : Prop :=
  (∀ a b : ℝ,
    cellLogLikelihood cellSize cellResponses a b ≤ 
      cellLogLikelihood cellSize cellResponses (Real.log (7/5)) 0 ∧
    (cellLogLikelihood cellSize cellResponses a b=
      cellLogLikelihood cellSize cellResponses (Real.log (7/5)) 0 ↔
      a=Real.log (7/5) ∧ b=0)) ∧
   (∀ j : Fin 3,0 < cellResponses j ∧ cellResponses j < cellSize j ∧
      logisticProbability (Real.log (7/5)) 0 ((![-1,0,1] : Fin 3 → ℝ) j)=7/12) ∧
   (∑ j,cellOutcomeSum j/
      logisticProbability (Real.log (7/5)) 0 ((![-1,0,1] : Fin 3 → ℝ) j))/12=3/7 ∧
   (∑ j,cellSize j*cellOutcomeSum j/cellResponses j)/12=5/12 ∧
   (3/7 : ℝ)≠5/12

def T84Statement : Prop := T84Core ∧ (3/7-5/12 : ℝ)=1/84

def CellDifference : Prop :=
  ∀ {E : Type*} [Fintype E] (N r S q : E → ℝ) (n : ℝ) (hn : 0 < n)
   (hN : ∀ x,0 < N x) (hr : ∀ x,0 < r x) (htotal : ∑ x,N x=n) (hq : ∀ x, 0 < q x),
  (∑ x,S x/q x)/n-(∑ x,N x*S x/r x)/n=
     (∑ x,S x*(1/q x-N x/r x))/n ∧
   (∑ x,r x/(r x/N x))/n=1

def SaturatedCells : Prop :=
  ∀ {E : Type*} [Fintype E] (N r S : E → ℝ) (hN : ∀ x,0 < N x) (hr : ∀ x,0 < r x),
  (∑ x,S x/(r x/N x))=∑ x,N x*S x/r x

def SaturationCriterion : Prop :=
  ∀ {E : Type*} [Fintype E] [DecidableEq E] (N r q : E → ℝ)
   (hN : ∀ x,0 < N x) (hr : ∀ x,0 < r x) (hq : ∀ x,0 < q x),
  (∀ S : E → ℝ,(∑ x,S x/q x)=∑ x,N x*S x/r x) ↔ ∀ x,q x=r x/N x

def T85Statement : Prop :=
  ∀ {E : Type*} [Fintype E] [DecidableEq E] (N r q : E → ℝ) (n : ℝ)
    (hn : 0 < n) (hN : ∀ x, 0 < N x) (hr : ∀ x, 0 < r x)
    (hq : ∀ x, 0 < q x) (htotal : ∑ x, N x=n),
    (∀ S : E → ℝ, cellIPW S q n-cellPlugIn N r S n =
      (∑ x, S x*(1/q x-N x/r x))/n) ∧
    ((∀ S : E → ℝ, cellIPW S q n=cellPlugIn N r S n) ↔ ∀ x, q x=r x/N x) ∧
    ((∀ x, q x=r x/N x) → cellWeightMean r q n=1 ∧
      ∀ S : E → ℝ, cellIPW S q n=cellPlugIn N r S n ∧
        cellStabilized S r q n=cellPlugIn N r S n)

def T86Statement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (R : Ω → ℝ) (hR : Measurable R) (hbinary : ∀ ω,R ω=0 ∨ R ω=1)
   (p : E → ℝ) (hp : IsConditionalMean μ X R p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω) ∧ p (X ω) ≤ 1),
  IsConditionalMean μ X (fun ω => R ω/p (X ω)) (fun _ => 1) ∧
   expectation μ (fun ω => R ω/p (X ω))=1 ∧
   1 ≤ expectation μ (fun ω => 1/p (X ω)) ∧
   (expectation μ (fun ω => 1/p (X ω))=1 ↔ ∀ᵐ ω ∂μ,p (X ω)=1)

def RespondentMAR : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
   (hbinary : ∀ ω,R ω=0 ∨ R ω=1) (p m : E → ℝ) (hp : IsConditionalMean μ X R p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω)) (hmar : CondIndependent μ X hX Y R)
   (hm : IsConditionalMean (μ.restrict {ω | R ω=1}) X (fun ω => recordedOutcome (Y ω) (R ω)) m)
   (hmi : Integrable (m ∘ X) μ),
  IsConditionalMean μ X Y m

def RespondentStable : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
   (hbinary : ∀ ω,R ω=0 ∨ R ω=1) (hRpos : 0 < probability μ {ω | R ω=1} ∧ 0 < probability μ {ω | R ω=0}) (m : E → ℝ)
   (hm : IsConditionalMean (μ.restrict {ω | R ω=1}) X Y m),
  IsConditionalMean (μ.restrict {ω | R ω=1}) X (fun ω => recordedOutcome (Y ω) (R ω)) m ∧
   IsConditionalMean μ (fun ω => (R ω,X ω)) (fun ω => recordedOutcome (Y ω) (R ω))
     (fun rx => if rx.1=1 then m rx.2 else -99)

def T87Statement : Prop := RespondentStable.{u,v} ∧ RespondentMAR.{u,v}

def T88Statement : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y0 Y1 D : ℕ → Ω → ℝ)
    (h0 : ∀ i, Measurable (Y0 i)) (h1 : ∀ i, Measurable (Y1 i))
    (hD : ∀ i, Measurable (D i)) (a b : ℝ) (hab : a ≤ b)
    (hsupport : ∀ i, ∀ᵐ ω ∂μ,
      Y0 i ω ∈ Set.Icc a b ∧ Y1 i ω ∈ Set.Icc a b ∧ (D i ω = 0 ∨ D i ω = 1))
    (hpos : 0 < probability μ {ω | D 0 ω = 1} ∧ probability μ {ω | D 0 ω = 1} < 1)
    (hiid : IsIID μ (fun i ω => (realizedOutcome (Y0 i ω) (Y1 i ω) (D i ω), D i ω))),
  let Y := fun i ω => realizedOutcome (Y0 i ω) (Y1 i ω) (D i ω)
    let L := fun i ω => lowerEffect (Y i ω) (D i ω) a b
    let U := fun i ω => upperEffect (Y i ω) (D i ω) a b
    let p := probability μ {ω | D 0 ω = 1}
    let ℓ := cellMean μ (D 0) (Y 0) 1*p + a*(1-p) -
      (cellMean μ (D 0) (Y 0) 0*(1-p) + b*p)
    let u := cellMean μ (D 0) (Y 0) 1*p + b*(1-p) -
      (cellMean μ (D 0) (Y 0) 0*(1-p) + a*p)
    expectation μ (L 0) = ℓ ∧ expectation μ (U 0) = u ∧ u-ℓ = b-a ∧
    expectation μ (fun ω => Y1 0 ω - Y0 0 ω) ∈ Set.Icc ℓ u ∧
    (∀ t ∈ Set.Icc ℓ u, ∃ A0 A1 : Ω → ℝ,
      Measurable A0 ∧ Measurable A1 ∧
      (∀ᵐ ω ∂μ, A0 ω ∈ Set.Icc a b ∧ A1 ω ∈ Set.Icc a b ∧
        realizedOutcome (A0 ω) (A1 ω) (D 0 ω) = Y 0 ω) ∧
      expectation μ (fun ω => A1 ω-A0 ω) = t) ∧
    (∀ n, 0 < n → expectation μ (sampleAverage L n) = ℓ ∧ expectation μ (sampleAverage U n) = u) ∧
    ConvergesInProbability μ (sampleAverage L) ℓ ∧ ConvergesInProbability μ (sampleAverage U) u

end
end SAP.P001e
