import SAP.P013a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def T7Statement : Prop :=
  (∀ N (hN : 1 ≤ N),
    (let F := blockPopulation N
    let P := blockDesign N
    let b := (blockBUnits N).card
    (∀ i d, pi F i d = 1/2 ∧ |F.outcome i d| ≤ 2) ∧
    (∀ i j d e, i ≠ j → jointPi F i j d e = 1/4) ∧
    GenuineDependency P F.exposure (fun i j => decide (i=j)) ∧
    RowBound (fun i j : Fin N => decide (i=j)) 1 ∧
    |causalEffect F 1 0| ≤ 2/(N : ℝ) ∧
    (∀ z, htEffect F 1 0 z-causalEffect F 1 0 =
      (2/(N : ℝ))*∑ i, rademacher (z i)) ∧
    variance P (htEffect F 1 0) = 4/(N : ℝ) ∧
    (∀ z, effectVariance F 1 0 z = 4/(N : ℝ)^2*∑ i, observed F z i ^ 2) ∧
    (∀ z, (N : ℝ)*effectVariance F 1 0 z = 4+4*(b : ℝ)/(N : ℝ) +
      8/(N : ℝ)*∑ i ∈ blockBUnits N, blockSign (i.val+1)*rademacher (z i)) ∧
    expectation P (fun z => (N : ℝ)*effectVariance F 1 0 z) = 4+4*(b : ℝ)/(N : ℝ) ∧
    variance P (fun z => (N : ℝ)*effectVariance F 1 0 z) = 64*(b : ℝ)/(N : ℝ)^2 ∧
    variance P (fun z => (N : ℝ)*effectVariance F 1 0 z) ≤ 64/(N : ℝ))) ∧
  (∀ N, 1 ≤ N → ∀ z, 0 < effectVariance (blockPopulation N) 1 0 z) ∧
  (∀ r (hr : 1 ≤ r),
    ((r % 2 = 1 →
      0 ≤ ((blockBUnits (blockEnd r)).card : ℝ)/(blockEnd r : ℝ) ∧
      ((blockBUnits (blockEnd r)).card : ℝ)/(blockEnd r : ℝ) ≤
        (blockEnd (r-1) : ℝ)/(blockEnd r : ℝ)) ∧
    (r % 2 = 0 →
      0 ≤ 1-((blockBUnits (blockEnd r)).card : ℝ)/(blockEnd r : ℝ) ∧
      1-((blockBUnits (blockEnd r)).card : ℝ)/(blockEnd r : ℝ) ≤
        (blockEnd (r-1) : ℝ)/(blockEnd r : ℝ)) ∧
    (2 ≤ r → (blockEnd (r-1) : ℝ)/(blockEnd r : ℝ) = 1/(2 : ℝ)^(2^(r-1))))) ∧
  (let P := fun n : ℕ => blockDesign (n+1)
    let F := fun n : ℕ => blockPopulation (n+1)
    let W := fun (n : ℕ) z => (n+1 : ℝ)*effectVariance (F n) 1 0 z
    let V := fun n : ℕ => variance (P n) (htEffect (F n) 1 0)
    let T := fun (n : ℕ) z => (htEffect (F n) 1 0 z-causalEffect (F n) 1 0)/
      Real.sqrt (effectVariance (F n) 1 0 z)
    (∀ n : ℕ, (n+1 : ℝ)*V n = 4 ∧ 4 ≤ expectation (P n) (W n)) ∧
    Tendsto (fun n : ℕ => variance (P n) (W n)) atTop (𝓝 0) ∧
    TendsNormal P (fun (n : ℕ) z => (htEffect (F n) 1 0 z-causalEffect (F n) 1 0)/Real.sqrt (V n)) 0 1 ∧
    ¬ (∃ s : ℝ, ConvergesInProbability P W s) ∧
    ¬ (∃ s : ℝ, ConvergesInProbability P
      (fun (n : ℕ) z => Real.sqrt (V n/effectVariance (F n) 1 0 z)) s) ∧
    ¬ (∃ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ ∧ TendsDistribution P T μ) ∧
    (let Po := fun n : ℕ => blockDesign (blockEnd (2*n+1))
     let Fo := fun n : ℕ => blockPopulation (blockEnd (2*n+1))
     let Pe := fun n : ℕ => blockDesign (blockEnd (2*n+2))
     let Fe := fun n : ℕ => blockPopulation (blockEnd (2*n+2))
     ConvergesInProbability Po (fun (n : ℕ) z => (blockEnd (2*n+1) : ℝ)*effectVariance (Fo n) 1 0 z) 4 ∧
     ConvergesInProbability Pe (fun (n : ℕ) z => (blockEnd (2*n+2) : ℝ)*effectVariance (Fe n) 1 0 z) 8 ∧
     ConvergesInProbability Po (fun (n : ℕ) z => Real.sqrt
       (variance (Po n) (htEffect (Fo n) 1 0)/effectVariance (Fo n) 1 0 z)) 1 ∧
     ConvergesInProbability Pe (fun (n : ℕ) z => Real.sqrt
       (variance (Pe n) (htEffect (Fe n) 1 0)/effectVariance (Fe n) 1 0 z)) (1/Real.sqrt 2) ∧
     TendsNormal Po (fun (n : ℕ) z => (htEffect (Fo n) 1 0 z-causalEffect (Fo n) 1 0)/
       Real.sqrt (effectVariance (Fo n) 1 0 z)) 0 1 ∧
     TendsNormal Pe (fun (n : ℕ) z => (htEffect (Fe n) 1 0 z-causalEffect (Fe n) 1 0)/
       Real.sqrt (effectVariance (Fe n) 1 0 z)) 0 (1/2)))

def T8Statement : Prop :=
  ∀ {L : ℕ → Type*} [∀ (n : ℕ), Fintype (L n)] (P : ∀ (n : ℕ), Design (L n))
    (estimate Vhat : ∀ (n : ℕ), L n → ℝ) (target V : ℕ → ℝ),
    (∀ (n : ℕ), V n=variance (P n) (estimate n) ∧ 0 < V n) →
    ∀ (c : ℝ) (hc : 0 < c),
    Tendsto (fun (n : ℕ) => (n+1 : ℝ)*V n) atTop (𝓝 c) →
    TendsNormal P (fun (n : ℕ) z => (estimate n z-target n)/Real.sqrt (V n)) 0 1 →
    (∀ (n : ℕ), (n+1 : ℝ)*V n ≤ expectation (P n) (fun z => (n+1 : ℝ)*Vhat n z)) →
    Tendsto (fun (n : ℕ) => variance (P n) (fun z => (n+1 : ℝ)*Vhat n z)) atTop (𝓝 0) →
    let W := fun (n : ℕ) z => (n+1 : ℝ)*Vhat n z
    let v := fun (n : ℕ) => (n+1 : ℝ)*V n
    ConvergesInProbability P (fun (n : ℕ) z => W n z-expectation (P n) (W n)) 0 ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      (∀ (n : ℕ), probability (P n) (fun z => W n z < (1-ε)*v n) ≤
        variance (P n) (W n)/(ε^2*(v n)^2)) ∧
      Tendsto (fun (n : ℕ) => probability (P n) (fun z => W n z < (1-ε)*v n)) atTop (𝓝 0)) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      (∀ ε : ℝ, 0 < ε → ε < 1 →
        2*normalCDF (normalCritical α*Real.sqrt (1-ε))-1 ≤
          liminf (fun (n : ℕ) => probability (P n) (fun z => 0 ≤ Vhat n z ∧
            |estimate n z-target n| ≤ normalCritical α*Real.sqrt (Vhat n z))) atTop) ∧
      1-α ≤ liminf (fun (n : ℕ) => probability (P n) (fun z => 0 ≤ Vhat n z ∧
        |estimate n z-target n| ≤ normalCritical α*Real.sqrt (Vhat n z))) atTop) ∧
    (∀ (s : ℝ) (hsc : c ≤ s),
      Tendsto (fun (n : ℕ) => expectation (P n) (W n)) atTop (𝓝 s) →
      (∀ n z, 0 < Vhat n z) →
      ConvergesInProbability P W s ∧
      ConvergesInProbability P (fun (n : ℕ) z => Real.sqrt (V n/Vhat n z)) (Real.sqrt (c/s)) ∧
      0 < Real.sqrt (c/s) ∧ Real.sqrt (c/s) ≤ 1 ∧
      TendsNormal P (fun (n : ℕ) z => (estimate n z-target n)/Real.sqrt (Vhat n z)) 0
        ⟨c/s, div_nonneg hc.le (le_trans hc.le hsc)⟩)

def T9Statement : Prop :=
  (∀ S : ExperimentSequence, NestedPopulationSetup S → StandingPositivity S →
    Condition3 S → Condition4 S →
    ConvergesInProbability (seqLaw S)
      (fun (n : ℕ) z => htMean (seqPopulation S n) (S.treated n) z-
        potentialMean (seqPopulation S n) (S.treated n)) 0) ∧
  (∀ estimate target V Vhat : ℝ, 0 < V → 0 < Vhat →
    (estimate-target)/Real.sqrt Vhat =
      ((estimate-target)/Real.sqrt V)*Real.sqrt (V/Vhat))

def T10Statement : Prop :=
  (∀ e s z : ℝ, (e-z*s)+(e+z*s)=2*e) ∧
  (∀ e L U : ℝ, ¬ (Displays3 e (295/1000) ∧ Displays3 L (50/1000) ∧
    Displays3 U (536/1000) ∧ L+U=2*e)) ∧
  (∀ e L U : ℝ, ¬ (Displays3 e (306/1000) ∧ Displays3 L (212/1000) ∧
    Displays3 U (404/1000) ∧ L+U=2*e)) ∧
  (∀ e s z : ℝ,
    ¬ (Displays3 e (295/1000) ∧ Displays3 (e-z*s) (50/1000) ∧ Displays3 (e+z*s) (536/1000)) ∧
    ¬ (Displays3 e (306/1000) ∧ Displays3 (e-z*s) (212/1000) ∧ Displays3 (e+z*s) (404/1000)))

def T11Statement : Prop :=
  ∀ (U neighbors : Finset ℕ) (i n : ℕ), i ∈ U → neighbors ⊆ U → i ∉ neighbors →
    neighbors.card=39 → 1 ≤ n → n ≤ U.card-39 →
    let p := completeProbability U n (isolatedExposure i neighbors)
    let q := completeProbability U n (noExposure i neighbors)
    p=(Nat.choose (U.card-40) (n-1) : ℝ)/Nat.choose U.card n ∧
    q=(Nat.choose (U.card-40) n : ℝ)/Nat.choose U.card n ∧
    q=((U.card : ℝ)-39-n)/n*p ∧
    (U.card ≤ 10*n+5 →
      q ≤ 9*p ∧ (p ≤ 27/40000 → q ≤ 243/40000 ∧ q < 1/100) ∧
      (1/100 ≤ q → 1/900 ≤ p ∧ 27/40000 < p))

def PrintedBiasBound : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K),
    0 < N → ∀ d : Fin K, Positivity F d → ∀ (R : ℕ) (p0 : ℝ),
    IsMinimumPi F d p0 → potentialTotal F d ≠ 0 →
    |(expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R)-
      potentialTotal F d)/potentialTotal F d| ≤ (1-p0)^(R+1)

def PrintedReplicateRule : Prop :=
  ∀ {Ω : Type} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K),
    0 < N → ∀ d : Fin K, Positivity F d → ∀ (R : ℕ) (p0 : ℝ),
    IsMinimumPi F d p0 → potentialTotal F d ≠ 0 → ∀ b : ℝ, 0 < b →
    (R : ℝ) ≥ Real.log b/Real.log (1-p0)-1 →
    |(expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R)-
      potentialTotal F d)/potentialTotal F d| ≤ b

def T12Statement : Prop := ¬ PrintedBiasBound ∧ ¬ PrintedReplicateRule

def T13Statement : Prop :=
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K),
    0 < N → ∀ d : Fin K, Positivity F d →
    expectation P (htTotal F d)=potentialTotal F d ∧
    variance P (htTotal F d)=
      (∑ i, pi F i d*(1-pi F i d)*(F.outcome i d/pi F i d)^2) +
      ∑ i, ∑ j ∈ univ.erase i, (jointPi F i j d d-pi F i d*pi F j d)*
        (F.outcome i d/pi F i d)*(F.outcome j d/pi F j d)) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K),
    0 < N → ∀ d e : Fin K, d ≠ e → Positivity F d → Positivity F e →
    expectation P (htEffect F d e)=causalEffect F d e ∧
    variance P (htEffect F d e)=
      (variance P (htTotal F d)+variance P (htTotal F e)-
        2*covariance P (htTotal F d) (htTotal F e))/(N : ℝ)^2 ∧
    covariance P (htTotal F d) (htTotal F e)=
      (∑ i, ∑ j ∈ univ.erase i, (jointPi F i j d e-pi F i d*pi F j e)*
        (F.outcome i d/pi F i d)*(F.outcome j e/pi F j e))-
      ∑ i, F.outcome i d*F.outcome i e)

def T14Statement : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K),
    0 < N → ∀ d : Fin K, Positivity F d →
    ((∀ i j, 0 < jointPi F i j d d) →
      expectation P (varianceHT F d)=variance P (htTotal F d)) ∧
    expectation P (varianceHT F d)=variance P (htTotal F d)+missingA F d ∧
    variance P (htTotal F d) ≤ expectation P (fun z => varianceHT F d z+correctionA2 F d z)


end
end SAP.P013a
