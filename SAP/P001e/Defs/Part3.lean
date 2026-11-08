import SAP.P001e.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e
universe u v
noncomputable section

def T77Statement : Prop :=
  ∀ {Ω : Type*} {τ : ℕ} (Θ : Set (Fin τ → ℝ)) (Y : Ω → ℝ)
   {K : ℕ} (X : Ω → Fin K → ℝ) (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (hg : ∀ y x t,t∈Θ → 0 ≤ g y x t),
  ∃ L : Ω → Θ → ℝ≥0, ∀ ω t,(L ω t : ℝ)=g (Y ω) (X ω) t.val

def T78Statement : Prop :=
  ∀ {n K : ℕ} (hn : 0 < n) (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
   (bstar : Fin (K+1) → ℝ) (hmin : ∀ b,residualSS X Y bstar ≤ residualSS X Y b)
   (hQ : 0 < residualSS X Y bstar),
  0 < Real.sqrt (residualSS X Y bstar/(n : ℝ)) ∧
   (Real.sqrt (residualSS X Y bstar/(n : ℝ)))^2=residualSS X Y bstar/(n : ℝ) ∧
   ∀ b s,0 < s → gaussianLogLikelihood X Y b s  ≤ 
     gaussianLogLikelihood X Y bstar (Real.sqrt (residualSS X Y bstar/(n : ℝ)))

def T79Statement : Prop :=
  ∀ {n K : ℕ} (hn : 0 < n) (X : Fin n → Fin K → ℝ) (ν : Fin n → Measure ℝ)
   (hν : ∀ i,IsProbabilityMeasure (ν i)),
  IsProbabilityMeasure (fittedJointLaw X ν) ∧ ∀ y : ℝ, ∀ x : Fin K → ℝ,
     probability (fittedJointLaw X ν) {z | z.1 ≤ y ∧ ∀ k,z.2 k ≤ x k} =
       (∑ i,if (∀ k,X i k ≤ x k) then probability (ν i) (Set.Iic y) else 0)/(n : ℝ)

def MissingBounds : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (a b : ℝ)
   (hbound : ∀ ω,Y ω∈Set.Icc a b) (hbinary : ∀ ω,R ω=0 ∨ R ω=1),
  let L := expectation μ (fun ω => completeMissing (recordedOutcome (Y ω) (R ω)) (R ω) a)
   let U := expectation μ (fun ω => completeMissing (recordedOutcome (Y ω) (R ω)) (R ω) b)
   L ≤ expectation μ Y ∧ expectation μ Y ≤ U ∧ ∀ c : ℝ,c∈Set.Icc L U →
     ∃ Y' : Ω → ℝ, Measurable Y' ∧ (∀ ω,Y' ω∈Set.Icc a b) ∧ expectation μ Y'=c ∧
       (fun ω => recordedOutcome (Y' ω) (R ω))=(fun ω => recordedOutcome (Y ω) (R ω))

def BoundsExample : Prop :=
  (∑ i : Fin 6,completeMissing (boundsRecorded i)
       (boundsResponse i) 0)/6=1/2 ∧
   (∑ i : Fin 6,completeMissing (boundsRecorded i)
       (boundsResponse i) 1)/6=5/6

def T80Statement : Prop := MissingBounds.{u} ∧ BoundsExample

def exampleScores : Fin 6 → ℝ := ![33/100,14/100,73/100,35/100,78/100,70/100]

def respondents : Finset (Fin 6) := {0,2,3,4}

def nonrespondents : Finset (Fin 6) := {1,5}

def UniqueNearest (i j : Fin 6) (candidates : Finset (Fin 6)) : Prop :=
  j ∈ candidates ∧ ∀ k ∈ candidates, k ≠ j →
    |exampleScores j-exampleScores i| < |exampleScores k-exampleScores i|

def DonorDistances : Prop :=
  |(33/100 : ℝ)-14/100|=19/100 ∧ |(35/100 : ℝ)-14/100|=21/100 ∧
  |(73/100 : ℝ)-14/100|=59/100 ∧ |(78/100 : ℝ)-14/100|=64/100 ∧
  |(33/100 : ℝ)-70/100|=37/100 ∧ |(73/100 : ℝ)-70/100|=3/100 ∧
  |(35/100 : ℝ)-70/100|=35/100 ∧ |(78/100 : ℝ)-70/100|=8/100

def HotDeckDonors : Prop :=
  UniqueNearest 1 0 respondents ∧ UniqueNearest 5 2 respondents ∧
  (∀ k ∈ respondents, k ≠ 0 →
    |exampleScores 3-exampleScores 1| ≤ |exampleScores k-exampleScores 1|) ∧
  |exampleScores 3-exampleScores 1|-|exampleScores 0-exampleScores 1|=2/100

def hotDeckDonor : Fin 6 → Fin 6 := ![0,0,2,3,4,2]

def hotDeckData : Fin 6 → ℝ := ![2,0,3,10,12,0]

def hotDeckCompleted : Fin 6 → ℝ := fun i => hotDeckData (hotDeckDonor i)

def T81Statement : Prop :=
  DonorDistances ∧ HotDeckDonors ∧ hotDeckCompleted = ![2,2,3,10,12,3] ∧
  (∑ i, hotDeckCompleted i)/6=16/3

def T82Core : Prop :=
  ∀ {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (R : Ω → Bool)
    (hX : Measurable X) (hR : Measurable R)
    (hRpos : 0 < probability μ {ω | R ω = true} ∧ probability μ {ω | R ω = true} < 1),
  ∃ p : E → ℝ, ∃ κ : E → Measure Bool,
      Measurable p ∧ (∀ x, p x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, IsProbabilityMeasure (κ x)) ∧
      (∀ B : Set Bool, MeasurableSet B → Measurable (fun x => κ x B)) ∧
      (∀ A : Set E, MeasurableSet A → ∀ B : Set Bool, MeasurableSet B →
        μ {ω | X ω ∈ A ∧ R ω ∈ B} = ∫⁻ x in A, κ x B ∂(μ.map X)) ∧
      (∀ x, responseProbability κ x = p x ∧
        expectation (κ x) (fun r => if r then (1 : ℝ) else 0) = p x) ∧
      IsConditionalMean μ X (fun ω => if R ω then (1 : ℝ) else 0) p ∧
      (∀ m : E → ℝ, IsConditionalMean μ X (fun ω => if R ω then (1 : ℝ) else 0) m →
        (m ∘ X) =ᵐ[μ] (p ∘ X)) ∧
      (∀ q : ℝ, q ∉ Set.Icc (0 : ℝ) 1 ↔ 1 < q ∨ q < 0)

def T82Statement : Prop :=
  T82Core.{u,v} ∧ (∀ q : ℝ, 0 < q ∨ q < 1)

def T83Statement : Prop :=
  ∀ {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
   (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
   (Y R : Ω → ℝ) (hY : Measurable Y) (hR : Measurable R) (hYi : Integrable Y μ)
   (hbinary : ∀ ω,R ω=0 ∨ R ω=1) (p : E → ℝ) (hp : IsConditionalMean μ X R p)
   (hpos : ∃ ε : ℝ,0 < ε ∧ ∀ ω,ε < p (X ω)) (hmar : CondIndependent μ X hX Y R),
  expectation μ Y=expectation μ (fun ω => recordedOutcome (Y ω) (R ω)*R ω/p (X ω))

end
end SAP.P001e
