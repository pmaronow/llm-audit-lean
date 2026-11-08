import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037b
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def olsMap {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) :=
  (X.transpose * X)⁻¹ * X.transpose

noncomputable def hatMatrix {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) :=
  X * olsMap X

noncomputable def olsResidual {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) :=
  y - X.mulVec ((olsMap X).mulVec y)

noncomputable def hc0Covariance {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) :=
  olsMap X * Matrix.diagonal (fun i => (olsResidual X y i)^2) *
    (olsMap X).transpose

noncomputable def vectorMean {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (v : Ω → Fin k → ℝ) : Fin k → ℝ :=
  fun j => ∫ ω, v ω j ∂μ

noncomputable def vectorCovariance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (v : Ω → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun j l => ∫ ω, (v ω j - vectorMean μ v j) *
    (v ω l - vectorMean μ v l) ∂μ

noncomputable def linearPredictionVariance {k : ℕ}
    (V : Matrix (Fin k) (Fin k) ℝ) (l : Fin k → ℝ) : ℝ :=
  dotProduct l (V.mulVec l)

def bandSizes : Fin 6 → ℝ := ![14,14,7,7,7,7]

def bandTreatments : Fin 6 → ℝ := ![0,0,1,1,1,1]

noncomputable def bandCompositions : Fin 6 → ℝ := ![0,0,0,0,1/5,1/5]

noncomputable def bandOutcomes : Fin 6 → ℝ := ![0,1/5,1/10,3/10,2/5,3/5]

noncomputable def bandDesignRow (i : Fin 6) : Fin 3 → ℝ :=
  ![1,bandTreatments i,bandTreatments i*bandCompositions i]

noncomputable def bandFit : Fin 3 → ℝ := ![1/10,1/10,3/2]

noncomputable def bandGramInverse : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/28,-1/28,0; -1/28,3/28,-5/14; 0,-5/14,25/7]

noncomputable def bandHC0 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2800,-1/2800,0; -1/2800,3/2800,-1/280; 0,-1/280,1/28]

noncomputable def bandDesignGram : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j l => ∑ i, bandSizes i*bandDesignRow i j*bandDesignRow i l

noncomputable def bandNormalRhs : Fin 3 → ℝ :=
  fun j => ∑ i, bandSizes i*bandDesignRow i j*bandOutcomes i

noncomputable def bandSandwichMeat : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j l => ∑ i, bandSizes i*(bandOutcomes i-dotProduct (bandDesignRow i) bandFit)^2*
    bandDesignRow i j*bandDesignRow i l

noncomputable def centeredBandRow (i : Fin 6) : Fin 3 → ℝ :=
  ![1,bandTreatments i,bandTreatments i*(bandCompositions i-1/10)]

noncomputable def centeredBandFit : Fin 3 → ℝ := ![1/10,1/4,3/2]

noncomputable def centeredBandGramInverse : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/28,-1/28,0;-1/28,1/14,0;0,0,25/7]

noncomputable def centeredBandGram : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j l => ∑ i, bandSizes i*centeredBandRow i j*centeredBandRow i l

noncomputable def centeredBandMeat : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j l => ∑ i, bandSizes i*(bandOutcomes i-
    dotProduct (centeredBandRow i) centeredBandFit)^2*
      centeredBandRow i j*centeredBandRow i l

structure ProbabilityDesign (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  positive : ∀ z, 0  <  mass z
  total : ∑ z, mass z=1

noncomputable def eventProbability {Ω : Type*} [Fintype Ω]
    (P : ProbabilityDesign Ω) (E : Ω → Prop) : ℝ :=
  ∑ z, P.mass z * (if E z then 1 else 0)

noncomputable def finiteExpectation {Ω : Type*} [Fintype Ω]
    (P : ProbabilityDesign Ω) (Y : Ω → ℝ) : ℝ := ∑ z, P.mass z*Y z

def passesConflictThreshold (Y : ℝ) : Prop := Y > 1/50

def treatmentPair (z : Fin 6) : Finset (Fin 4) :=
  ![{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}] z

noncomputable def potentialOutcome4 (i : Fin 4) (treated : Bool) : ℝ :=
  (3/100)*(i.val:ℝ)+(if treated then 3/100 else 0)

noncomputable def observedOutcome4 (z : Fin 6) (i : Fin 4) : ℝ :=
  potentialOutcome4 i (decide (i∈treatmentPair z))

noncomputable def keptSchools4 (z : Fin 6) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => passesConflictThreshold (observedOutcome4 z i))

noncomputable def keptTreated4 (z : Fin 6) := keptSchools4 z ∩ treatmentPair z

noncomputable def keptControl4 (z : Fin 6) := keptSchools4 z \ treatmentPair z

noncomputable def selectedContrast4 (z : Fin 6) : ℝ :=
  (∑ i ∈ keptTreated4 z, observedOutcome4 z i)/(keptTreated4 z).card -
  (∑ i ∈ keptControl4 z, observedOutcome4 z i)/(keptControl4 z).card

noncomputable def selectionWeight4 (z : Fin 6) : ℝ :=
  ((keptTreated4 z).card:ℝ)*(keptControl4 z).card /
    ((keptTreated4 z).card+(keptControl4 z).card)

noncomputable def selectedBlockEstimate (B : ℕ) (z : Fin B → Fin 6) : ℝ :=
  (∑ b, selectionWeight4 (z b)*selectedContrast4 (z b))/(∑ b, selectionWeight4 (z b))

def seedSubsets (n m : ℕ) : Finset (Finset (Fin n)) := Finset.univ.powersetCard m

def localTreatedLabel {n : ℕ} (self peers refs seeds : Finset (Fin n)) : Fin 5 :=
  if ¬Disjoint seeds self then 4 else if Disjoint seeds peers then 1
  else if Disjoint seeds refs then 2 else 3

noncomputable def localExposureProbability5 (n m : ℕ)
    (self peers refs : Finset (Fin n)) (k : Fin 5) : ℝ :=
  if k=0 then 1/2 else
    (((seedSubsets n m).filter (fun s => localTreatedLabel self peers refs s=k)).card:ℝ) /
      (2*(Nat.choose n m:ℝ))

def positiveExposurePopulation {I : Type*} (π : I → Fin 4 → ℝ) : Set I :=
  {i | ∀ k, 0 < π i k ∧ π i k < 1}

def exposureProbabilityCutoff {I : Type*} (π : I → Fin 4 → ℝ) (cutoff : ℝ) : Set I :=
  {i | ∀ k, cutoff < π i k}

def analysisPopulation {Ω I : Type*} (estimated : I → Fin 4 → ℝ)
    (seed outcomeAvailable baselineAvailable schoolPasses : Ω → I → Prop)
    (z : Ω) : Set I :=
  {i | i∈exposureProbabilityCutoff estimated (1/100) ∧ ¬seed z i ∧
    outcomeAvailable z i ∧ baselineAvailable z i ∧ schoolPasses z i}

noncomputable def blockedAvoidanceProbability {b : ℕ}
    (n t m : Fin b → ℕ) : ℝ :=
  (1/2)*∏ h, (Nat.choose (n h-m h) (t h):ℝ)/(Nat.choose (n h) (t h):ℝ)

abbrev RareSeedAssignments := Bool × ((h : Fin 4) → {s : Finset (Fin 10) // s.card=5})

def rareExposure (z : RareSeedAssignments) : Fin 4 :=
  if !z.1 then 0 else
    if Disjoint (z.2 0).val {0,1,2,3,4} ∧ Disjoint (z.2 1).val {0,1,2,3,4} then 1
    else if (0 : Fin 10)∈(z.2 0).val then 3 else 2

noncomputable def rareAssignmentMass (_ : RareSeedAssignments) : ℝ := 1/(2*252^4)

noncomputable def rareExposureProbability (k : Fin 4) : ℝ :=
  ∑ z : RareSeedAssignments, rareAssignmentMass z*(if rareExposure z=k then 1 else 0)

def blockedSchoolAssignments (B : ℕ) : Finset (Finset (Fin B × Fin 4)) :=
  Finset.univ.powerset.filter (fun s => ∀ b, (s.filter (fun i => i.1=b)).card=2)

def unblockedSchoolAssignments (n m : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powersetCard m

noncomputable def blockedAssignmentMass {B : ℕ} (s : Finset (Fin B × Fin 4)) : ℝ :=
  if s∈blockedSchoolAssignments B then (6:ℝ)^(- (B:ℤ)) else 0

noncomputable def uniformSchoolEventProbability (n m : ℕ)
    (E : Finset (Fin n) → Prop) : ℝ :=
  (((unblockedSchoolAssignments n m).filter E).card:ℝ)/(Nat.choose n m:ℝ)

def peerUnion {n : ℕ} (B : Fin n → Fin n → Bool) (i j : Fin n) : Bool :=
  B i j || B j i

def directedIndegree {n : ℕ} (B : Fin n → Fin n → Bool) (j : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => B i j=true)).card

noncomputable def indegreeQuantile90 {n : ℕ} (B : Fin n → Fin n → Bool) : ℝ :=
  let sorted := (List.ofFn (directedIndegree B)).mergeSort (· ≤ ·)
  let h := 9*(n-1)
  ((10-h%10:ℕ):ℝ)/10*(sorted.getD (h/10) 0:ℝ)+
    ((h%10:ℕ):ℝ)/10*(sorted.getD (h/10+1) 0:ℝ)

noncomputable def referentStudents {n : ℕ} (B : Fin n → Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun j => indegreeQuantile90 B < (directedIndegree B j:ℝ))

def seedPeerCount {n : ℕ} (B : Fin n → Fin n → Bool)
    (i : Fin n) (seeds : Finset (Fin n)) : ℕ :=
  (seeds.filter (fun j => B i j=true)).card

def referentSeedPeerCount {n : ℕ} (B : Fin n → Fin n → Bool)
    (γ seeds : Finset (Fin n)) (i : Fin n) : ℕ :=
  (seeds.filter (fun j => B i j=true ∧ j∈γ)).card

def nonseedExposureLabel (t r : ℕ) : Fin 3 := if t=0 then 0 else if r=0 then 1 else 2

def networkExposureLabel {n : ℕ} (B : Fin n → Fin n → Bool)
    (γ seeds : Finset (Fin n)) (i : Fin n) : Fin 3 :=
  nonseedExposureLabel (seedPeerCount B i seeds) (referentSeedPeerCount B γ seeds i)

def nominationGraph10 (i j : Fin 10) : Bool :=
  decide ((i=1 ∧ j=0) ∨ ((i=2 ∨ i=3) ∧ j=1))

def nominationGraph20 (i j : Fin 20) : Bool :=
  decide ((i=1 ∧ j=0) ∨ (i=0 ∧ (j=2 ∨ j=4)) ∨
    (8 ≤ i.val ∧ i.val ≤ 13 ∧ j=1) ∨ (14 ≤ i.val ∧ i.val ≤ 19 ∧ j=2))

def eligibleStudents20 : Fin 6 → Fin 20 := ![1,2,4,5,6,7]

noncomputable def graphExposureProbability20 (B : Fin 20 → Fin 20 → Bool) (k : Fin 4) : ℝ :=
  if k=0 then 1/2 else
    (((Finset.univ.powersetCard 3).filter (fun s : Finset (Fin 6) =>
      (networkExposureLabel B (referentStudents nominationGraph20) (s.image eligibleStudents20) 0).val+1=k.val)).card:ℝ)/40

/-- Mathematical content packaged for P037-T18. -/
def T18Statement : Prop :=
  (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) (y : Fin n → ℝ) (hX : Function.Injective X.mulVec) (v : Ω → Fin n → ℝ) (h1 : ∀ i, Integrable (fun ω => v ω i) μ) (h2 : ∀ i j, Integrable (fun ω => v ω i*v ω j) μ) (hmean : vectorMean μ v = 0) (hmom : ∀ i j, (∫ ω, v ω i*v ω j ∂μ) = if i=j then 1 else 0),
    let b := (olsMap X).mulVec y
    let bs := fun ω => (olsMap X).mulVec
      (X.mulVec b + fun i => olsResidual X y i*v ω i)
    (∀ ω, bs ω = b + (olsMap X).mulVec
      (fun i => olsResidual X y i*v ω i)) ∧
    vectorMean μ bs = b ∧ vectorCovariance μ bs = hc0Covariance X y) ∧
  (∀ {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) (hX : Function.Injective X.mulVec) (hn : 0  <  n),
    (hatMatrix X).transpose = hatMatrix X ∧
    hatMatrix X * hatMatrix X = hatMatrix X ∧
    (∀ i, 0  ≤  hatMatrix X i i ∧ hatMatrix X i i  ≤  1) ∧
    (∑ i, hatMatrix X i i) = (k:ℝ) ∧
    (∑ i, hatMatrix X i i)/(n:ℝ) = (k:ℝ)/n) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℝ) (hX : Function.Injective X.mulVec) (β : Fin k → ℝ) (σ2 : ℝ) (hσ : 0  ≤  σ2) (u : Ω → Fin n → ℝ) (h1 : ∀ i, Integrable (fun ω => u ω i) μ) (h2 : ∀ i j, Integrable (fun ω => u ω i*u ω j) μ) (hmean : vectorMean μ u = 0) (hmom : ∀ i j, (∫ ω, u ω i*u ω j ∂μ) = if i=j then σ2 else 0),
    let y := fun ω => X.mulVec β + u ω
    let A := olsMap X
    let H := hatMatrix X
    let V := vectorCovariance μ (fun ω => A.mulVec (y ω))
    let EV : Matrix (Fin k) (Fin k) ℝ := fun j l => ∫ ω, hc0Covariance X (y ω) j l ∂μ
    (∀ ω, olsResidual X (y ω) = (1-H).mulVec (u ω)) ∧
    (∀ i, (∫ ω, (olsResidual X (y ω) i)^2 ∂μ) = σ2*(1-H i i)) ∧
    V = σ2 • (A*A.transpose) ∧ V = σ2 • (X.transpose*X)⁻¹ ∧
    EV = σ2 • (A*Matrix.diagonal (fun i => 1-H i i)*A.transpose) ∧
    V-EV = σ2 • (A*Matrix.diagonal (fun i => H i i)*A.transpose) ∧
    (∀ t, 0  ≤  dotProduct t ((V-EV).mulVec t))) ∧
  (∀ {n : ℕ} (a h : Fin n → ℝ) (hh : ∀ i, 0  ≤  h i ∧ h i  ≤  1) (ha : 0  <  ∑ i, (a i)^2),
    (∑ i, (a i)^2*(1-h i))/(∑ i, (a i)^2) =
      1-(∑ i, (a i)^2*h i)/(∑ i, (a i)^2) ∧
    (∑ i, (a i)^2*(1-h i))/(∑ i, (a i)^2)  ≤  1 ∧
    ((∑ i, (a i)^2*(1-h i))/(∑ i, (a i)^2) = 1 ↔
      ∀ i, a i ≠ 0 → h i = 0))

end SAP.P037b
