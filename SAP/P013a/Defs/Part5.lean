import SAP.P013a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P013a

open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def T1Finite (r : ℕ) (hr : 2 ≤ r) : Prop :=
  ((∀ i d, pi (pairedPopulation r hr) i d = 1/2 ∧
      |(pairedPopulation r hr).outcome i d| = 1) ∧
    (∀ i j d e, i ≠ j → jointPi (pairedPopulation r hr) i j d e =
      if pairIndex r i = pairIndex r j then
        (if d=e then pairEpsilon (2*r) else 1/2-pairEpsilon (2*r)) else 1/4) ∧
    (let h := fun i j : Fin (2*r) => decide (pairIndex r i = pairIndex r j);
      GenuineDependency (pairedDesign r hr) (pairedPopulation r hr).exposure h ∧
      PrintedDependency (pairedDesign r hr) (pairedPopulation r hr).exposure h ∧
      RowBound h 2)) ∧
  (let F := pairedPopulation r hr
    let P := pairedDesign r hr
    let N := (2*r : ℕ)
    let t := pairSplitProbability N
    causalEffect F 1 0 = 0 ∧
    (∀ z, htEffect F 1 0 z = (∑ a, pairScore (z a))/(N : ℝ) ∧
      (N : ℝ)^2*effectVariance F 1 0 z = ∑ a, pairVarianceScore N (z a) ∧
      0 < effectVariance F 1 0 z) ∧
    variance P (htEffect F 1 0) = 8*t/(N : ℝ) ∧
    expectation P (effectVariance F 1 0) = variance P (htEffect F 1 0) ∧
    probability P (allPairsSplit r) = t^r ∧
    probability P (fun z => ¬ allPairsSplit r z) ≤ 1/(N : ℝ) ∧
    (∀ z, allPairsSplit r z → (N : ℝ)*effectVariance F 1 0 z = 8-2/t) ∧
    variance P (fun z => (N : ℝ)*effectVariance F 1 0 z) =
      4*((N : ℝ)-2)^4*((N : ℝ)+2)^4 / ((N : ℝ)^5*((N : ℝ)^2-2))) ∧
  expectation (pairAtomDesign (2*r) (by omega)) (pairVarianceScore (2*r)) =
    16*pairSplitProbability (2*r)

def T1Statement : Prop :=
  (∀ r (hr : 2 ≤ r), T1Finite r hr) ∧
  ((∀ r (hr : 2 ≤ r),
      (∀ i d, pi (pairedPopulation r hr) i d = 1/2 ∧
        |(pairedPopulation r hr).outcome i d| = 1) ∧
      GenuineDependency (pairedDesign r hr) (pairedPopulation r hr).exposure
        (fun i j => decide (pairIndex r i = pairIndex r j)) ∧
      PrintedDependency (pairedDesign r hr) (pairedPopulation r hr).exposure
        (fun i j => decide (pairIndex r i = pairIndex r j)) ∧
      RowBound (fun i j : Fin (2*r) => decide (pairIndex r i = pairIndex r j)) 2) ∧
    (let P := fun n : ℕ => pairedDesign (n+2) (by omega)
     let F := fun n : ℕ => pairedPopulation (n+2) (by omega)
     let N := fun n : ℕ => (2*(n+2) : ℝ)
     let V := fun n : ℕ => variance (P n) (htEffect (F n) 1 0)
     let W := fun (n : ℕ) z => N n*effectVariance (F n) 1 0 z
     Tendsto (fun n : ℕ => N n*V n) atTop (𝓝 8) ∧
     ConvergesInProbability P W 6 ∧
     ConvergesInProbability P (fun (n : ℕ) z => effectVariance (F n) 1 0 z / V n) (3/4) ∧
     Tendsto (fun n : ℕ => variance (P n) (W n) / (4*N n)) atTop (𝓝 1) ∧
     Tendsto (fun n : ℕ => variance (P n) (W n)) atTop atTop ∧
     TendsNormal P (fun (n : ℕ) z => Real.sqrt (N n)*htEffect (F n) 1 0 z) 0 8 ∧
     (∀ α : ℝ, 0 < α → α < 1 →
       Tendsto (fun n : ℕ => probability (P n) (fun z =>
         |htEffect (F n) 1 0 z-causalEffect (F n) 1 0| ≤
           normalCritical α*Real.sqrt (effectVariance (F n) 1 0 z))) atTop
         (𝓝 (2*normalCDF (normalCritical α*Real.sqrt (3/4))-1)) ∧
       2*normalCDF (normalCritical α*Real.sqrt (3/4))-1 < 1-α)))

def ScaledVarianceConcentration (S : ExperimentSequence) : Prop :=
  ConvergesInProbability (seqLaw S) (fun (n : ℕ) z => (n+1 : ℝ) *
    (seqVarianceEstimate S n z-expectation (seqLaw S n) (seqVarianceEstimate S n))) 0

def ScaledVarianceVanishes (S : ExperimentSequence) : Prop :=
  Tendsto (fun (n : ℕ) => variance (seqLaw S n)
    (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z)) atTop (𝓝 0)

def T2Statement : Prop :=
  (∀ S : ExperimentSequence, NestedPopulationSetup S → ComparisonBounded S →
    Condition5Genuine S → Condition6 S → LowerTailCondition S →
    ∀ α : ℝ, 0 < α → α < 1 → 1-α ≤ liminf (seqCoverage S α) atTop) ∧
  (∀ S : ExperimentSequence, ScaledVarianceConcentration S → LowerTailCondition S) ∧
  (∀ S : ExperimentSequence, ScaledVarianceVanishes S → LowerTailCondition S) ∧
  (∀ S : ExperimentSequence, NestedPopulationSetup S → ComparisonBounded S →
    Condition5Genuine S → ∀ b : ℝ, 0 < b → JointLowerBound S b →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤
        C/(n+1 : ℝ)) ∧ LowerTailCondition S) ∧
  (∀ S : ExperimentSequence, NestedPopulationSetup S → ComparisonBounded S →
    Condition5Genuine S → ∀ b : ℕ → ℝ,
    (∀ (n : ℕ), PositiveJointDomain S n → IsMinimumPositiveJoint S n (b n)) →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      variance (seqLaw S n) (fun z => (n+1 : ℝ)*seqVarianceEstimate S n z) ≤
        C/((n+1 : ℝ)*b n)) ∧
    (Tendsto (fun (n : ℕ) => (n+1 : ℝ)*b n) atTop atTop → LowerTailCondition S))

def T3Statement : Prop :=
  ((∀ i d, 0 < pi (signedReplicationPopulation 2) i d ∧
      pi (signedReplicationPopulation 2) i d < 1) ∧
    pi (signedReplicationPopulation 2) 0 1 = 1/3 ∧
    pi (signedReplicationPopulation 2) 1 1 = 2/3 ∧
    potentialTotal (signedReplicationPopulation 2) 1 = 1 ∧
    expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 2) = 2/9 ∧
    |(expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 2) - 1)/1| = 7/9 ∧
    (4/9 : ℝ) < 7/9 ∧ (1/2 : ℝ) < 7/9 ∧
    ((1-1/3 : ℝ)^(1+1)) ≤ 1/2 ∧ (1/2 : ℝ) < (1-1/3)^1) ∧
  ((1 : ℝ) ≥ Real.log (1/2)/Real.log (1-1/3)-1 ∧
    (1/2 : ℝ) < |(expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 2)-potentialTotal (signedReplicationPopulation 2) 1)/
        potentialTotal (signedReplicationPopulation 2) 1|) ∧
  (potentialTotal (signedReplicationPopulation 1) 1 = 0 ∧
    expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 1) = -1/3 ∧
    |expectation (independentProduct signedReplicationDesign signedReplicationDesign)
      (signedOneReplicate 1) - potentialTotal (signedReplicationPopulation 1) 1| >
      |potentialTotal (signedReplicationPopulation 1) 1| * (1-1/3)^(1+1))

def T4Statement : Prop :=
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K),
    0 < N → ∀ d : Fin K, Positivity F d → ∀ R : ℕ, 1 ≤ R →
    ∀ p0 : ℝ, IsMinimumPi F d p0 →
    let E := expectation (independentProduct P (replicateDesign P R)) (simulatedHTTotal F d R)
    let T := potentialTotal F d
    let κ := cancellationFactor F d
    E = ∑ i, F.outcome i d * (1-(1-pi F i d)^(R+1)) ∧
    E = T - ∑ i, F.outcome i d * (1-pi F i d)^(R+1) ∧
    |E-T| ≤ (1-p0)^(R+1)*(∑ i, |F.outcome i d|) ∧
    (T ≠ 0 → 1 ≤ κ ∧ |(E-T)/T| ≤ κ*(1-p0)^(R+1) ∧
      (((∀ i, 0 ≤ F.outcome i d) ∨ (∀ i, F.outcome i d ≤ 0)) →
        κ = 1 ∧ |(E-T)/T| ≤ (1-p0)^(R+1) ∧
        (∀ b : ℝ, 0 < b → (R : ℝ) ≥ Real.log b/Real.log (1-p0)-1 →
          |(E-T)/T| ≤ b)) ∧
      (∀ b : ℝ, 0 < b → (R : ℝ) ≥ Real.log (b/κ)/Real.log (1-p0)-1 →
        |(E-T)/T| ≤ b))) ∧
  ((1999/2000 : ℚ)^(10593+1) ≤ 1/200 ∧
    1/200 < (1999/2000 : ℚ)^(10592+1))

def T5Statement : Prop :=
  (∀ {N : ℕ} (A B : Finset (Fin N)), Disjoint A B →
    (PrintedNoEdge (fun i j => decide (i=j)) A B ↔ A=∅ ∧ B=∅)) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} (P : Design Ω) (D : Ω → Fin N → Fin K),
    PrintedDependency P D (fun i j => decide (i=j)) ∧
      RowBound (fun i j : Fin N => decide (i=j)) 1 ∧
      (∀ i : Fin N, ∑ j, (if decide (i=j)=true then 1 else 0 : ℕ)=1)) ∧
  (∀ q : ℕ, let h := fun i j : Fin (3*q) => decide (i ≠ j ∧ i.val/3=j.val/3)
    (∀ i j, h i j=h j i) ∧ (∀ i, h i i=false) ∧
    (∀ A B : Finset (Fin (3*q)), Disjoint A B →
      (PrintedNoEdge h A B ↔ A=∅ ∧ B=∅)) ∧
    (∀ i, ∑ j, (if h i j=true then 1 else 0 : ℕ)=2) ∧
    (∀ {Ω : Type*} [Fintype Ω] {K : ℕ} (P : Design Ω) (D : Ω → Fin (3*q) → Fin K),
      PrintedDependency P D h)) ∧
  (∀ N : ℕ,
    PrintedDependency sharedDesign (sharedPopulation N).exposure (fun i j => decide (i=j)) ∧
    RowBound (fun i j : Fin N => decide (i=j)) 1 ∧
    (∀ i : Fin N, ∑ j, (if decide (i=j)=true then 1 else 0 : ℕ)=1) ∧
    (∀ i d, pi (sharedPopulation N) i d=1/2) ∧
    (∀ i j, jointPi (sharedPopulation N) i j 1 1=1/2 ∧
      ¬ PairIndependent (sharedPopulation N) i j)) ∧
  (∀ N : ℕ, ∀ g : Fin N → Fin N → Bool,
    (∀ i j, g i j=false → PairIndependent (sharedPopulation N) i j) →
    (∑ i, ∑ j, (if g i j=true then 1 else 0 : ℕ))=N^2) ∧
  (∃ S : ExperimentSequence, StandingPositivity S ∧ Condition3 S ∧
    Condition5Printed S ∧ ¬ Condition4 S)

def Condition5CorrectedDirected (S : ExperimentSequence) : Prop :=
  ∃ m : ℕ, ∃ h : ∀ n : ℕ, Fin (n+1) → Fin (n+1) → Bool, ∀ (n : ℕ),
    GenuineDependency (seqLaw S n) (seqPopulation S n).exposure (h n) ∧ RowBound (h n) m

def T6Statement : Prop :=
  (∀ {N : ℕ} (h : Fin N → Fin N → Bool) (A B : Finset (Fin N)),
    (CorrectedNoEdge h A B ↔ ∀ i ∈ A, ∀ j ∈ B, h i j=false ∧ h j i=false) ∧
    ((∀ i j, h i j=h j i) →
      (CorrectedNoEdge h A B ↔ ∀ i ∈ A, ∀ j ∈ B, h i j=false))) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω} (F : Population P N K)
    (h : Fin N → Fin N → Bool), GenuineDependency P F.exposure h →
    (∀ i j, graphPairIndicator h i j=0 → PairIndependent F i j) ∧
    (∀ m : ℕ, RowBound h m →
      (∑ i, ∑ j, graphPairIndicator h i j) ≤ N*(2*m+1) ∧
      ((∀ i j, h i j=h j i) → (∑ i, ∑ j, graphPairIndicator h i j) ≤ N*(m+1)))) ∧
  (∀ S : ExperimentSequence, Condition5CorrectedDirected S → Condition4 S)


end
end SAP.P013a
