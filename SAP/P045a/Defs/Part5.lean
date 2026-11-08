import SAP.P045a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a
noncomputable section

/-- Substantive conclusions retained for P045-T7; see the Challenge docstring for scope. -/
def T7Statement : Prop :=
  ((∀ i j, singleEdge4 i j = singleEdge4 j i) ∧
    (∀ i, singleEdge4 i i = 0) ∧
    faultyCopy 4 singleEdge4 0 3 = 1 ∧
    faultyCopy 4 singleEdge4 3 0 = 0 ∧
    faultyCopy 4 singleEdge4 2 1 = 1 ∧
    faultyCopy 4 singleEdge4 1 2 = 0)
  ∧
  (upperCells 4 = [(0,1),(0,2),(1,2),(0,3),(1,3),(2,3)] ∧
    lowerCells 4 = [(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)] ∧
    (∀ n : ℕ, 4 ≤ n → (upperCells n)[2]? = some (1,2) ∧ (lowerCells n)[2]? = some (3,0)) ∧
    (∀ n : ℕ, n ≤ 3 → ∀ k : ℕ, k < (upperCells n).length →
      (lowerCells n)[k]? = ((upperCells n)[k]?).map (fun x => (x.2,x.1))) ∧
    (univ.filter (fun u : Fin 6 → Bool => ∃ i j : Fin 4,
      faultyCopy 4 (upperInput4 u) i.val j.val ≠ faultyCopy 4 (upperInput4 u) j.val i.val)).card = 32 ∧
    matrixExposure singleEdge4 ![false,false,false,true] 0 = .d01 ∧
    matrixExposure (faultyCopy 4 singleEdge4) ![false,false,false,true] 0 = .d00 ∧
    matrixExposure singleEdge4 ![false,false,true,false] 1 = .d00 ∧
    matrixExposure (faultyCopy 4 singleEdge4) ![false,false,true,false] 1 = .d01 ∧
    (∀ q : ℝ, 0 ≤ q → q < 1 →
      prob (fun b : Bool => if b then q else 1-q)
        (fun b => (fun i j => if b then 0 else faultyCopy 4 singleEdge4 i j) =
          faultyCopy 4 singleEdge4) = 1-q))

/-- Substantive conclusions retained for P045-T8; see the Challenge docstring for scope. -/
def T8Statement : Prop :=
  (printedEdges.card = 20 ∧
    mean biasBaseline / 4 = 23/80 ∧
    (∀ d : ℕ, d ≤ 2 → ∀ R ∈ deletionMasks d, ∀ i,
      1 ≤ measuredDegree R i ∧ measuredDegree R i ≤ 6) ∧
    deletionBias 0 = 890121037/44498644960 ∧
    1/50 < deletionBias 0 ∧ deletionBias 0 < 1/49 ∧
    9/1000 < deletionBias 1 ∧ deletionBias 1 < 1/100 ∧
    -(1/800) < deletionBias 2 ∧ deletionBias 2 < -(1/900) ∧
    |deletionBias 2| < |deletionBias 1| ∧ |deletionBias 1| < |deletionBias 0| ∧
    deletionBias 0 ≠ 0)
  ∧
  (∀ d : Fin 3, ∀ R ∈ deletionMasks d.val,
      (∀ i : Fin 10, 1 ≤ measuredDegree R i ∧ measuredDegree R i ≤ 6) ∧
      (∀ t : Fin 10, (univ.filter (fun i => deletedAdj R t i=true)).Nonempty ∧
        (univ \ insert t (univ.filter (fun i => deletedAdj R t i=true))).Nonempty))
  ∧
  (∀ (d : Fin 3), ∀ R ∈ deletionMasks d.val,
      (∀ i : Fin 10,
        0 < (measuredDegree R i : ℝ) / 10 ∧
        0 < (9 - (measuredDegree R i : ℝ)) / 10) ∧
      (∀ t : Fin 10,
        0 < ∑ i ∈ (univ.filter (fun i => deletedAdj R t i = true)),
          1 / (measuredDegree R i : ℝ)) ∧
      (∀ t : Fin 10,
        0 < ∑ i ∈ (univ \ insert t (univ.filter (fun i => deletedAdj R t i = true))),
          1 / (9 - (measuredDegree R i : ℝ))))
  ∧
  ((deletionMasks 0).card = 1 ∧ (deletionMasks 1).card = 20 ∧
      (deletionMasks 2).card = 190)

/-- Substantive conclusions retained for P045-T9; see the Challenge docstring for scope. -/
def T9Statement : Prop :=
  (∀ (M : ℕ → ℕ → ℝ) (i j : ℕ),
    correctedCopy M i j = correctedCopy M j i)
  ∧
  (∀ (n : ℕ) (A U : ℕ → ℕ → ℝ)
    (hA : ∀ i j, A i j = A j i) (hdiag : ∀ i, A i i = 0)
    (hbin : ∀ i j, i < n → j < n → A i j = 0 ∨ A i j = 1)
    (hUdiag : ∀ i, U i i = 0)
    (hUbin : ∀ i j, i < j → j < n → U i j = 0 ∨ U i j = 1),
    ((∀ i j, i < j → j < n → U i j ≤ A i j) →
      ∀ i j, i < n → j < n → 0 ≤ correctedCopy U i j ∧ correctedCopy U i j ≤ A i j) ∧
    ((∀ i j, i < j → j < n → A i j ≤ U i j) →
      ∀ i j, i < n → j < n → i ≠ j → A i j ≤ correctedCopy U i j ∧ correctedCopy U i j ≤ 1) ∧
    ((∀ i j, i < j → j < n → U i j = A i j) →
      ∀ i j, i < n → j < n → correctedCopy U i j = A i j))
  ∧
  (∀ {n : ℕ} (T S : Network n)
    (hsub : ∀ i j, S.adj i j = true → T.adj i j = true) (z : Assignment n) (i : Fin n),
    (exposure S.adj z i = .d01 → exposure T.adj z i = .d01) ∧
    (exposure S.adj z i = .d11 → exposure T.adj z i = .d11) ∧
    (exposure S.adj z i = .d00 → exposure T.adj z i = .d00 ∨ exposure T.adj z i = .d01) ∧
    (exposure S.adj z i = .d10 → exposure T.adj z i = .d10 ∨ exposure T.adj z i = .d11))
  ∧
  (∀ {n : ℕ} (hn : 0 < n) (p : Design (Assignment n))
    (T S : Network n) (hsub : ∀ i j, S.adj i j = true → T.adj i j = true)
    (y : Fin n → Exposure → ℝ)
    (h0 : ∀ i, 0 < exposureProb p.mass (exposure S.adj) i .d00)
    (h1 : ∀ i, 0 < exposureProb p.mass (exposure S.adj) i .d01),
    let Y := fun i z => y i (exposure T.adj z i)
    let M := fun d z => htObserved p.mass (exposure S.adj) Y d z / n
    let c := fun i => condMean p.mass (fun z => exposure S.adj z i = .d00)
      (fun z => if exposure T.adj z i = .d01 then 1 else 0)
    expect p.mass (M .d00) = mean (fun i => (1-c i)*y i .d00+c i*y i .d01) ∧
    expect p.mass (M .d01) = mean (fun i => y i .d01) ∧
    expect p.mass (fun z => M .d01 z-M .d00 z)-effect y .d01 .d00 =
      -mean (fun i => c i*(y i .d01-y i .d00)) ∧
    ((∀ i, y i .d00 ≤ y i .d01) →
      expect p.mass (fun z => M .d01 z-M .d00 z) ≤ effect y .d01 .d00))
  ∧
  (deletionBias 0 ≠ 0 ∧ |deletionBias 1| < |deletionBias 0|)

/-- Substantive conclusions retained for P045-T10; see the Challenge docstring for scope. -/
def T10Statement : Prop :=
  (let d := pathDistance (n := 4);
    terminalCentres d 3 true {0,1} = 1/12 ∧
    terminalCentres d 3 true {0,2} = 1/12 ∧
    terminalCentres d 3 true {0,3} = 1/3 ∧
    terminalCentres d 3 true {1} = 1/4 ∧
    terminalCentres d 3 true {2} = 1/4 ∧
    (∑ S : Finset (Fin 4), terminalCentres d 3 true S) = 1 ∧
    prob (terminalCentres d 3 true) (fun S => ¬separated d 3 S) = 1/6 ∧
    clusteredTreatment d true (1/2) ![false,false,false,false] = 3/8 ∧
    clusteredTreatment d true (1/2) ![true,true,true,true] = 3/8 ∧
    clusteredTreatment d true (1/2) ![true,true,false,false] = 5/48 ∧
    clusteredTreatment d true (1/2) ![false,false,true,true] = 5/48 ∧
    clusteredTreatment d true (1/2) ![true,false,false,false] = 1/48 ∧
    clusteredTreatment d true (1/2) ![false,true,true,true] = 1/48 ∧
    (∀ z : Assignment 4, z ∉ ({![false,false,false,false], ![true,true,true,true],
      ![true,true,false,false], ![false,false,true,true], ![true,false,false,false], ![false,true,true,true]} : Finset (Assignment 4)) →
      clusteredTreatment d true (1/2) z = 0) ∧
    terminalCentres d 3 false {0,3} = 1/2 ∧
    terminalCentres d 3 false {1} = 1/4 ∧
    terminalCentres d 3 false {2} = 1/4 ∧
    clusteredTreatment d false (1/2) ![false,false,false,false] = 3/8 ∧
    clusteredTreatment d false (1/2) ![true,true,true,true] = 3/8 ∧
    clusteredTreatment d false (1/2) ![true,true,false,false] = 1/8 ∧
    clusteredTreatment d false (1/2) ![false,false,true,true] = 1/8 ∧
    clusteredTreatment d false (1/2) ![true,false,false,false] = 0 ∧
    clusteredTreatment d false (1/2) ![false,true,true,true] = 0)

/-- Substantive conclusions retained for P045-T11; see the Challenge docstring for scope. -/
def T11Statement : Prop :=
  (∀ {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)),
    (∀ cs : List (Fin n), greedyRun G.edist 3 cs →
      cs.Nodup ∧ cs.length ≤ n ∧ separated G.edist 3 cs.toFinset ∧
      (marked G.edist 3 cs.toFinset = univ → epsilonNet G.edist 3 cs.toFinset)) ∧
    (∀ S : Finset (Fin n), ∀ v ∉ marked G.edist 3 S,
      (univ \ marked G.edist 3 (insert v S)).card < (univ \ marked G.edist 3 S).card) ∧
    (∃ cs : List (Fin n), greedyRun G.edist 3 cs ∧ marked G.edist 3 cs.toFinset = univ))

/-- Substantive conclusions retained for P045-T12; see the Challenge docstring for scope. -/
def T12Statement : Prop :=
  (treatmentPairs.card = 45 ∧
    (∀ i, pairExposureProb cycle10 i .d11 = 2/45 ∧
      pairExposureProb cycle10 i .d10 = 7/45 ∧
      pairExposureProb cycle10 i .d01 = 1/3 ∧
      pairExposureProb cycle10 i .d00 = 7/15) ∧
    (treatmentPairs.filter (fun e => cycle10 e.1 e.2 = true)).card = 10 ∧
    (∀ e ∈ treatmentPairs, (if cycle10 e.1 e.2 then cycleL e = 2 ∧ cycleR e = 9
      else cycleL e = 1 ∧ cycleR e = 9/7)) ∧
    (∀ e ∈ treatmentPairs, cycleL e ≠ cycleR e) ∧
    average treatmentPairs cycleL = 11/9 ∧ average treatmentPairs cycleR = 3 ∧
    average treatmentPairs (fun e => mean (fun i =>
      if exposure cycle10 (pairAssignment e) i = .d11 then 2/pairExposureProb cycle10 i .d11 else 0)) = 2 ∧
    average treatmentPairs cycleL-mean (fun i : Fin 10 => cycleOut i .d11) = -7/9)

/-- Substantive conclusions retained for P045-T13; see the Challenge docstring for scope. -/
def T13Statement : Prop :=
  (∀ {n : ℕ} (hn : 0 < n) (p : Design (Assignment n))
    (A : Network n) (y : Fin n → Exposure → ℝ) (hp : ∀ i, 0 < ownProb p.mass i),
    (∀ i, ownProb p.mass i = exposureProb p.mass (exposure A.adj) i .d11 +
      exposureProb p.mass (exposure A.adj) i .d10) ∧
    expect p.mass (naiveTreated p.mass A.adj y) = mean (fun i =>
      (exposureProb p.mass (exposure A.adj) i .d11/ownProb p.mass i)*y i .d11 +
      (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*y i .d10) ∧
    expect p.mass (naiveTreated p.mass A.adj y)-mean (fun i => y i .d11) =
      -mean (fun i => (exposureProb p.mass (exposure A.adj) i .d10/ownProb p.mass i)*(y i .d11-y i .d10)) ∧
    ((∀ i, y i .d10 ≤ y i .d11) →
      expect p.mass (naiveTreated p.mass A.adj y) ≤ mean (fun i => y i .d11) ∧
      (expect p.mass (naiveTreated p.mass A.adj y) < mean (fun i => y i .d11) ↔
        ∃ i, 0 < exposureProb p.mass (exposure A.adj) i .d10 ∧ y i .d10 < y i .d11)) ∧
    ((∀ i, y i .d11 ≤ y i .d10) →
      mean (fun i => y i .d11) ≤ expect p.mass (naiveTreated p.mass A.adj y)) ∧
    ((∀ i, 0 < exposureProb p.mass (exposure A.adj) i .d11 ∧
      0 < exposureProb p.mass (exposure A.adj) i .d10) →
      expect p.mass (fun z => (htTotal p.mass (exposure A.adj) y .d11 z +
        htTotal p.mass (exposure A.adj) y .d10 z)/n) =
          mean (fun i => y i .d11)+mean (fun i => y i .d10)))
  ∧
  (∀ {n : ℕ}, 0 < n → (p : Design (Assignment n)) →
      (A : Network n) → (y : Fin n → Exposure → ℝ) →
      (∀ i, 0 < ownProb p.mass i) → ∀ z : Assignment n,
      naiveTreated p.mass A.adj y z = repairedExpansion p.mass A.adj y z)
  ∧
  ((∀ i : Fin 2, cancellingOut2 i .d11 ≠ cancellingOut2 i .d10) ∧
    naiveTreated (bernoulli (1/2)) edge2 cancellingOut2 ![false,false] = 0 ∧
    naiveTreated (bernoulli (1/2)) edge2 cancellingOut2 ![false,true] = 2 ∧
    naiveTreated (bernoulli (1/2)) edge2 cancellingOut2 ![true,false] = 1 ∧
    naiveTreated (bernoulli (1/2)) edge2 cancellingOut2 ![true,true] = 3 ∧
    expect (bernoulli (1/2)) (naiveTreated (bernoulli (1/2)) edge2 cancellingOut2) = 3/2 ∧
    mean (fun i : Fin 2 => cancellingOut2 i .d11) = 3/2)

/-- Substantive conclusions retained for P045-T14; see the Challenge docstring for scope. -/
def T14Statement : Prop :=
  (pooledMean 2 1 (9/2) 2 = some (13/6) ∧ printedPool 2 1 (9/2) 2 = some (17/4) ∧
    pooledMean 2 1 (11/4) (5/4) = some (4/3) ∧ printedPool 2 1 (11/4) (5/4) = some (21/8) ∧
    (13/6 : ℝ)-4/3 = 5/6 ∧ (17/4 : ℝ)-21/8 = 13/8 ∧
    (∀ a b : ℕ, 0 < a → 0 < b → ∀ A B : ℝ,
      A/a+B/b-(A+B)/(a+b : ℕ) =
        (b : ℝ)*A/((a : ℝ)*(a+b : ℕ)) + (a : ℝ)*B/((b : ℝ)*(a+b : ℕ))))
  ∧
  ((firstStageSets 6 3).card = 20 ∧
    ((firstStageSets 6 3).filter (fun H => sameRegimeCount H=0)).card = 8 ∧
    (∀ H ∈ firstStageSets 6 3, sameRegimeCount H=0 ∨ sameRegimeCount H=2) ∧
    (∀ B : ℝ, printedPool 0 3 0 B = none ∧ pooledMean 0 3 0 B = some (B/3)))
  ∧
  (Fintype.card (Fin 6 × Fin 75)=450 ∧
    ({0,1,2} : Finset (Fin 6)) ∈ firstStageSets 6 3 ∧
    (({0,1,2} : Finset (Fin 6)).filter (fun g => tractPartner g ∈ ({0,1,2} : Finset (Fin 6))))={0,1} ∧
    (({0,1,2} : Finset (Fin 6)).filter (fun g => tractPartner g ∉ ({0,1,2} : Finset (Fin 6))))={2} ∧
    (∀ g : Fin 6, treatedCount (tractWitnessAssignment g)=(if g.val<3 then 50 else 25) ∧
      0 < crMass 75 (if g.val<3 then 50 else 25) (tractWitnessAssignment g)) ∧
    (∀ g : Fin 6, g.val<3 → ∀ b : Bool,
      tractObservedArm tractWitnessAssignment g b =
        if g.val<2 then (if b then 9/4 else 11/8) else (if b then 2 else 5/4)) ∧
    pooledMean 2 1
      (∑ g ∈ ({0,1} : Finset (Fin 6)), tractObservedArm tractWitnessAssignment g true)
      (tractObservedArm tractWitnessAssignment 2 true)=some (13/6) ∧
    printedPool 2 1
      (∑ g ∈ ({0,1} : Finset (Fin 6)), tractObservedArm tractWitnessAssignment g true)
      (tractObservedArm tractWitnessAssignment 2 true)=some (17/4) ∧
    pooledMean 2 1
      (∑ g ∈ ({0,1} : Finset (Fin 6)), tractObservedArm tractWitnessAssignment g false)
      (tractObservedArm tractWitnessAssignment 2 false)=some (4/3) ∧
    printedPool 2 1
      (∑ g ∈ ({0,1} : Finset (Fin 6)), tractObservedArm tractWitnessAssignment g false)
      (tractObservedArm tractWitnessAssignment 2 false)=some (21/8))

end
end SAP.P045a
