import Mathlib
import SAP.P001a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology Classical Matrix

noncomputable section

universe u1 u2 u3 u4 u5 u6 u7 u8

namespace SAP.P001a

/-- The mathematical content packaged for target P001-T11. -/
def T11Statement : Prop :=
  (UnusedMixtureWitness ∧
  ∃ T : (n : ℕ) → (Fin n → Fin 4) → Fin 3 → ℝ,
    (∀ n (y : Fin n → Fin 4),
      T n y ∈ disjointMixtureParameterSet ∧
      ∀ u ∈ disjointMixtureParameterSet,
        disjointMixtureLikelihood y u ≤ disjointMixtureLikelihood y (T n y)) ∧
    (¬ FiniteMixtureConsistent T (![1, 1/3, 1/4] : Fin 3 → ℝ) ∨
     ¬ FiniteMixtureConsistent T (![1, 1/3, 3/4] : Fin 3 → ℝ))) ∧

(IsCompact disjointMixtureParameterSet ∧
   (![1,1/3,1/4] : Fin 3 → ℝ)∈disjointMixtureParameterSet ∧
   (![1,1/3,3/4] : Fin 3 → ℝ)∈disjointMixtureParameterSet ∧
   ∀ n (y : Fin n → Fin 4),Continuous (disjointMixtureLikelihood y) ∧
     ∃ t∈disjointMixtureParameterSet,∀ u∈disjointMixtureParameterSet,
       disjointMixtureLikelihood y u ≤ disjointMixtureLikelihood y t)

/-- The mathematical content packaged for target P001-T12. -/
def T12Statement : Prop :=
  (∀ {M K τ : ℕ}
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (p : (Fin τ → ℝ) → Fin M → ℝ)
  (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (θ θ' : Fin τ → ℝ) (hθ : θ ≠ θ') (j : Fin M)
  (hp : p θ=p θ') (hpzero : p θ j=0)
  (hweight : (∀ k, 0 ≤ p θ k) ∧ (∑ k, p θ k)=1)
  (heq : ∀ k, k ≠ j → ∀ y x, g k y x θ=g k y x θ')
  (hg : ∀ t ∈ ({θ,θ'} : Set (Fin τ → ℝ)), ∀ k,
    Measurable (fun xy : (Fin K → ℝ) × ℝ => g k xy.2 xy.1 t))
  (hnonneg : ∀ t ∈ ({θ,θ'} : Set (Fin τ → ℝ)), ∀ k y x, 0 ≤ g k y x t)
  (hnorm : ∀ t ∈ ({θ,θ'} : Set (Fin τ → ℝ)), ∀ k x,
    (∫⁻ y, ENNReal.ofReal (g k y x t) ∂κ)=1)
  (hlog : Integrable (fun xy : (Fin K → ℝ) × ℝ =>
    Real.log (mixtureFamily p g xy.2 xy.1 θ))
    (conditionalModelLaw νX κ (mixtureFamily p g) θ)),
  (∀ y x, mixtureFamily p g y x θ=mixtureFamily p g y x θ') ∧
  conditionalModelLaw νX κ (mixtureFamily p g) θ=
    conditionalModelLaw νX κ (mixtureFamily p g) θ' ∧
  (∀ n, iidObservationLaw (conditionalModelLaw νX κ (mixtureFamily p g) θ) n=
    iidObservationLaw (conditionalModelLaw νX κ (mixtureFamily p g) θ') n) ∧
  mean (conditionalModelLaw νX κ (mixtureFamily p g) θ)
    (fun xy => Real.log (mixtureFamily p g xy.2 xy.1 θ)) =
  mean (conditionalModelLaw νX κ (mixtureFamily p g) θ')
    (fun xy => Real.log (mixtureFamily p g xy.2 xy.1 θ')) ∧
  (∀ T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ,
    (∀ n, Measurable (T n)) →
    ¬ (SampleCP (conditionalModelLaw νX κ (mixtureFamily p g) θ) T θ ∧
       SampleCP (conditionalModelLaw νX κ (mixtureFamily p g) θ') T θ'))) ∧

(∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ) (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (hc : IsCompact Θ) (θ : Fin τ → ℝ) (hθ : θ∈Θ)
  (commonS : Set ((Fin K → ℝ) × ℝ)) (hCommonS : MeasurableSet commonS)
  (hCommonSfull : (μ.map (fun ω => (X 0 ω, Y 0 ω))) commonS = 1)
  (hCommonPositive : ∀ xy ∈ commonS, ∀ t ∈ Θ, 0 < mixtureFamily p g xy.2 xy.1 t)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ (mixtureFamily p g) θ)
   (hlog : ∀ t∈Θ,Integrable
     (fun ω => Real.log (mixtureFamily p g (Y 0 ω) (X 0 ω) t)) μ)
   (hpositiveModel : ∀ t∈Θ,∀ᵐ ω ∂μ,0 < mixtureFamily p g (Y 0 ω) (X 0 ω) t)
   (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g)) Θ)
   (hunique : ∀ t∈Θ,expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t ≤ 
     expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ ∧
     (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t=
       expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ → t=θ))
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLogLikelihood X Y (mixtureFamily p g) n ω t ≤ 
     sampleLogLikelihood X Y (mixtureFamily p g) n ω (that n ω))
   (Δ : ℕ → Ω → ℝ) (hΔ : ∀ n ω t,t∈Θ →
     |sampleLogLikelihood X Y (mixtureFamily p g) n ω t-
       expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t| ≤ Δ n ω)
   (hlim : CP μ Δ 0),
  CP μ that θ) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {M K τ : ℕ} (X : ℕ → Ω → Fin K → ℝ) (Y : ℕ → Ω → ℝ)
   (hiid : IID μ (fun i ω => (X i ω,Y i ω)))
   (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
   (p : (Fin τ → ℝ) → Fin M → ℝ)
   (g : Fin M → ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
   (Θ : Set (Fin τ → ℝ)) (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
   (hinterior : Metric.ball θ δ⊆Θ)
   (hp : ∀ t∈Θ,(∀ m,0 ≤ p t m) ∧ (∑ m,p t m)=1)
   (hg : ∀ t∈Θ,∀ m,Measurable (fun xy : (Fin K → ℝ) × ℝ => g m xy.2 xy.1 t))
   (hnonneg : ∀ t∈Θ,∀ m y x,0 ≤ g m y x t)
   (hnorm : ∀ t∈Θ,∀ m x,(∫⁻ y,ENNReal.ofReal (g m y x t) ∂κ)=1)
   (htrue : μ.map (fun ω => (X 0 ω,Y 0 ω))=conditionalModelLaw νX κ (mixtureFamily p g) θ)
   (S : Set ((Fin K → ℝ) × ℝ)) (hS : MeasurableSet S)
   (hSfull : (μ.map (fun ω => (X 0 ω,Y 0 ω))) S = 1)
   (hpositive : ∀ xy ∈ S,∀ t∈Metric.ball θ δ,
     0 < mixtureFamily p g xy.2 xy.1 t)
   (hdiff : ∀ xy ∈ S,ContDiffOn ℝ 2
     (fun t => Real.log (mixtureFamily p g xy.2 xy.1 t)) (Metric.ball θ δ))
   (hs2 : ∀ j,MemLp (fun ω => modelScore (mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j) 2 μ)
   (hszero : ∀ j,mean μ (fun ω => modelScore (mixtureFamily p g) (Y 0 ω) (X 0 ω) θ j)=0)
   (hinfo : (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ).PosDef)
   (hHinfo : populationHessian μ (X 0) (Y 0) (mixtureFamily p g) θ=
     -informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)
   (hHcont : ContinuousAt (populationHessian μ (X 0) (Y 0) (mixtureFamily p g)) θ)
   (hHi : ∀ t∈Metric.ball θ δ,∀ j k,
     Integrable (fun ω => modelHessian (mixtureFamily p g) (Y 0 ω) (X 0 ω) t j k) μ)
   (ΔH : ℕ → Ω → ℝ) (hHbound : ∀ n ω t,t∈Metric.ball θ δ → ∀ j k,
     |sampleHessian X Y (mixtureFamily p g) n ω t j k-
       populationHessian μ (X 0) (Y 0) (mixtureFamily p g) t j k| ≤ ΔH n ω)
   (hHlim : CP μ ΔH 0)
   (that : ℕ → Ω → Fin τ → ℝ) (hmeas : ∀ n,Measurable (that n))
   (hthat : ∀ n ω,that n ω∈Θ)
   (hmax : ∀ n ω t,t∈Θ → sampleLikelihood X Y (mixtureFamily p g) n ω t ≤ 
     sampleLikelihood X Y (mixtureFamily p g) n ω (that n ω))
   
  (hcompact : IsCompact Θ) (hθ : θ ∈ Θ)
  (hlog : ∀ t ∈ Θ, Integrable (fun ω =>
    Real.log (mixtureFamily p g (Y 0 ω) (X 0 ω) t)) μ)
  (hposAll : ∀ xy ∈ S, ∀ t ∈ Θ, 0 < mixtureFamily p g xy.2 xy.1 t)
  (hM : ContinuousOn (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g)) Θ)
  (hunique : ∀ t ∈ Θ,
    expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t ≤
      expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ ∧
    (expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t =
      expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) θ → t=θ))
  (Δ : ℕ → Ω → ℝ) (hΔ : CP μ Δ 0)
  (hbound : ∀ n ω t, t ∈ Θ →
    |sampleLogLikelihood X Y (mixtureFamily p g) n ω t-
      expectedLogLikelihood μ (X 0) (Y 0) (mixtureFamily p g) t| ≤ Δ n ω)
  (hqmInt : ∃ r : ℝ, 0 < r ∧ ∀ t : Fin τ → ℝ, dist t θ < r →
    Integrable (fun xy : (Fin K → ℝ) × ℝ =>
      (Real.sqrt (mixtureFamily p g xy.2 xy.1 t) -
       Real.sqrt (mixtureFamily p g xy.2 xy.1 θ) -
       (∑ j, (t j - θ j) * modelScore (mixtureFamily p g) xy.2 xy.1 θ j) *
         Real.sqrt (mixtureFamily p g xy.2 xy.1 θ) / 2)^2) (νX.prod κ))
  (hqm : QuadraticMeanModel νX κ (mixtureFamily p g) θ),
  CP μ that θ ∧ WeakLimit μ (fun n ω => Real.sqrt n • (that n ω-θ))
     (normalVectorLaw (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)⁻¹) ∧
  (∀ T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ,
    ∀ ψ : (Fin K → ℝ) × ℝ → Fin τ → ℝ,
    RegularAL (conditionalModelLaw νX κ (mixtureFamily p g)) θ T ψ →
    ∀ a : Fin τ → ℝ, 0 ≤ ∑ j, ∑ k, a j*
      (covarianceMatrix (conditionalModelLaw νX κ (mixtureFamily p g) θ) ψ j k-
       (informationMatrix μ (X 0) (Y 0) (mixtureFamily p g) θ)⁻¹ j k)*a k))

/-- The mathematical content packaged for target P001-T13. -/
def T13Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z)
   (hlaw : μ.map (Z 0) = matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => hotDeck (firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => bootVar hotDeck (firstSample Z n ω)) 2 μ),
  MatchingFailure μ Z false) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z) (hlaw : μ.map (Z 0)=matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => hotDeck (firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => bootVar hotDeck (firstSample Z n ω)) 2 μ),
  ∃ C : ℝ,0 ≤ C ∧ ∀ n : ℕ,
     mean μ (fun ω => ((n : ℝ)*bootVar hotDeck (firstSample Z n ω))^2) ≤ C) ∧

(0 < matchS ∧ matchS < 1 ∧ matchA < 3 ∧ matchB < 3/2 ∧ matchVB < matchV)

/-- The mathematical content packaged for target P001-T14. -/
def T14Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z)
   (hlaw : μ.map (Z 0) = matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => hotDeck (firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => bootVar hotDeck (firstSample Z n ω)) 2 μ),
  MatchingFailure μ Z false) ∧

(∀ {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (r : Fin n → Bool),
  (∀ e : Fin n → Bool,hotDeck (fun j => (p j,r j,e j))-50=
     (∑ j,donorReuseWeight p r j*noise (e j))/(n : ℝ)) ∧
   IsProbabilityMeasure (signProductLaw n) ∧
   mean (signProductLaw n) (fun e => hotDeck (fun j => (p j,r j,e j)))=50 ∧
   var (signProductLaw n) (fun e => hotDeck (fun j => (p j,r j,e j)))=
     (∑ j,(donorReuseWeight p r j)^2)/(n : ℝ)^2)

/-- The mathematical content packaged for target P001-T15. -/
def T15Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z)
   (hlaw : μ.map (Z 0) = matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => causalMatch (firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => bootVar causalMatch (firstSample Z n ω)) 2 μ),
  MatchingFailure μ Z true) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z) (hlaw : μ.map (Z 0)=matchingUnitLaw),
  CP μ (fun n ω => estimatedMatchIntercept (firstSample Z n ω)) (1/4))

/-- The mathematical content packaged for target P001-T16. -/
def T16Statement : Prop :=
  (∀ {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z) (hlaw : μ.map (Z 0)=matchingUnitLaw)
   (hT2 : ∀ n, MemLp (fun ω => causalMatchEstimated (firstSample Z n ω)) 2 μ)
   (hB2 : ∀ n, MemLp (fun ω => bootVar causalMatchEstimated (firstSample Z n ω)) 2 μ),
  (∀ n,0 < n → mean μ (fun ω => causalMatchEstimated (firstSample Z n ω))=0) ∧
   Tendsto (fun (n : ℕ) => (n : ℝ)*var μ (fun ω => causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchV) ∧
   Tendsto (fun (n : ℕ) => mean μ (fun ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω))) atTop (nhds matchVB) ∧
   0 < matchVB ∧ matchVB < matchV ∧
   ¬ CP μ (fun n ω => (n : ℝ)*bootVar causalMatchEstimated (firstSample Z n ω)) matchV) ∧

(∀ {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   (Z : ℕ → Ω → ℝ × Bool × Bool) (hiid : IID μ Z) (hlaw : μ.map (Z 0)=matchingUnitLaw),
  CP μ (fun n ω => estimatedMatchIntercept (firstSample Z n ω)) (1/4)) ∧

(∀ {n : ℕ} (s : Fin n → ℝ × Bool × Bool) (r : Fin n → Bool) (i : Fin n),
  nearestDonor (estimatedMatchScore s) r i=nearestDonor (fun j => (s j).1) r i) ∧

(∀ {n : ℕ} (s : Fin n → ℝ × Bool × Bool),
  causalMatchEstimated s=causalMatch s) ∧

(∀ {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (d : Fin n → Bool),
  (∀ e : Fin n → Bool,causalMatch (fun j => (p j,d j,e j))=
     -(∑ j,donorReuseWeight p (fun i => !(d i)) j*noise (e j))/(n : ℝ)) ∧
   IsProbabilityMeasure (signProductLaw n) ∧
   mean (signProductLaw n) (fun e => causalMatch (fun j => (p j,d j,e j)))=0 ∧
   var (signProductLaw n) (fun e => causalMatch (fun j => (p j,d j,e j)))=
     (∑ j,(donorReuseWeight p (fun i => !(d i)) j)^2)/(n : ℝ)^2)


end SAP.P001a
