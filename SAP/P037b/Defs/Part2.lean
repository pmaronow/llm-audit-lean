import Mathlib
import SAP.P037b.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037b
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Mathematical content packaged for P037-T19. -/
def T19Statement : Prop :=
  ((∀ i, potentialOutcome4 i true-potentialOutcome4 i false=3/100) ∧
    (∀ z i, i∈keptSchools4 z ↔ i≠0 ∨ 0∈treatmentPair z) ∧
    (∀ z, (keptTreated4 z).card=2 ∧
      (keptControl4 z).card=(![2,2,2,1,1,1] : Fin 6 → ℕ) z) ∧
    (∀ z, selectedContrast4 z=(![-3/100,0,3/100,-3/200,3/100,3/40] : Fin 6 → ℝ) z) ∧
    (∀ z, selectionWeight4 z=(![1,1,1,2/3,2/3,2/3] : Fin 6 → ℝ) z) ∧
    (∑ z, selectedContrast4 z)/6=3/200 ∧ (3/200:ℝ)≠3/100 ∧
    (∑ z, selectionWeight4 z)/6=5/6 ∧
    (∑ z, selectionWeight4 z*selectedContrast4 z)/6=1/100 ∧
    ((1/100:ℝ)/(5/6))=3/250 ∧ (3/250:ℝ)≠3/100) ∧
  (∀ (ε : ℝ) (hε : 0 < ε),
    Filter.Tendsto (fun B : ℕ =>
      ∑ z : Fin B → Fin 6, (1/6:ℝ)^B *
        (if |selectedBlockEstimate B z-3/250|  >  ε then 1 else 0))
      Filter.atTop (nhds 0)) ∧
  (∀ (nT nC yT yC : ℝ) (ht : 0 < nT) (hc : 0 < nC),
    nT*(1-nT/(nT+nC))^2+nC*(nT/(nT+nC))^2=nT*nC/(nT+nC) ∧
    (1-nT/(nT+nC))*yT-(nT/(nT+nC))*yC=
      (nT*nC/(nT+nC))*(yT/nT-yC/nC)) ∧
  (∀ (S : Finset (Fin 4)), S.Nonempty →
    (∑ i ∈ S, (potentialOutcome4 i true - potentialOutcome4 i false)) / (S.card : ℝ) = 3/100)

/-- Mathematical content packaged for P037-T20. -/
def T20Statement : Prop :=
  (∀ {Ω I K : Type*} [Fintype Ω] [Fintype I] [DecidableEq K] (P : ProbabilityDesign Ω) (D : Ω → I → K) (A : Ω → I → Bool) (y : I → K → ℝ) (a : I → Bool),
    (∀ d i, 0 < eventProbability P (fun z => D z i=d) →
      finiteExpectation P (fun z =>
        (if a i then 1 else 0)*(if D z i=d then 1 else 0)*y i d /
          eventProbability P (fun z => D z i=d))=(if a i then y i d else 0)) ∧
    (∀ d, (∀ i, a i=true → 0 < eventProbability P (fun z => D z i=d)) →
      0 < (Finset.univ.filter (fun i => a i=true)).card →
      finiteExpectation P (fun z =>
        (∑ i, (if a i then 1 else 0)*(if D z i=d then 1 else 0)*y i d /
          eventProbability P (fun z => D z i=d)) /
        (Finset.univ.filter (fun i => a i=true)).card)=
        (∑ i ∈ Finset.univ.filter (fun i => a i=true), y i d)/
          (Finset.univ.filter (fun i => a i=true)).card) ∧
    (∀ d i, 0 < eventProbability P (fun z => D z i=d) →
      finiteExpectation P (fun z =>
        (if A z i then 1 else 0)*(if D z i=d then 1 else 0)*y i d /
          eventProbability P (fun z => D z i=d))=
        y i d*(eventProbability P (fun z => A z i=true ∧ D z i=d) /
          eventProbability P (fun z => D z i=d)))) ∧
  (∀ {Ω I : Type*} (Y : Ω → I → ℝ) (h : ∀ i, (∀ z, 1/50 < Y z i) ∨ (∀ z, Y z i ≤ 1/50)),
    ∀ z z' i, passesConflictThreshold (Y z i) ↔ passesConflictThreshold (Y z' i))

/-- Mathematical content packaged for P037-T21. -/
def T21Statement : Prop :=
  ((seedSubsets 12 6).card=924 ∧
    (∀ k : Fin 5, localExposureProbability5 12 6 ∅ {0,1,2,3,4,5} {0} k=
      (![1/2,1/1848,461/1848,1/4,0] : Fin 5 → ℝ) k) ∧
    (∀ k : Fin 4, 0 < (![1/2,1/1848,461/1848,1/4] : Fin 4 → ℝ) k ∧
      (![1/2,1/1848,461/1848,1/4] : Fin 4 → ℝ) k < 1) ∧
    (0:ℝ) < 1/1848 ∧ (1/1848:ℝ) < 1/100 ∧
    (∀ k : Fin 5, localExposureProbability5 12 6 {2} {0,1} {0} k=
      (![1/2,1/22,3/44,3/22,1/4] : Fin 5 → ℝ) k) ∧
    (∀ k : Fin 4, (1/100:ℝ) < (![1/2,1/22,3/44,3/22] : Fin 4 → ℝ) k) ∧
    ({2,3,4,5,6,7} : Finset (Fin 12))∈seedSubsets 12 6 ∧
    ({3,4,5,6,7,8} : Finset (Fin 12))∈seedSubsets 12 6 ∧
    localTreatedLabel (n := 12) {2} {0,1} {0} {2,3,4,5,6,7}=4 ∧
    localTreatedLabel (n := 12) {2} {0,1} {0} {3,4,5,6,7,8}=1) ∧
  (∃ z : Fin 10000 → Bool × Finset (Fin 12),
      (∀ j, (z j).2∈seedSubsets 12 6) ∧
      (∀ k : Fin 4, ((Finset.univ.filter (fun j =>
        (if (z j).1 then localTreatedLabel ∅ {0,1,2,3,4,5} {0} (z j).2
          else 0)=k.castSucc)).card:ℝ)/10000=
        (![1/2,1/2000,499/2000,1/4] : Fin 4 → ℝ) k)) ∧
  ((∀ k : Fin 5, ((seedSubsets 12 6).filter
      (fun s => localTreatedLabel ∅ {0,1,2,3,4,5} {0} s = k)).card =
      (![0,1,461,462,0] : Fin 5 → ℕ) k) ∧
    (∀ k : Fin 5, ((seedSubsets 12 6).filter
      (fun s => localTreatedLabel {2} {0,1} {0} s = k)).card =
      (![0,84,126,252,462] : Fin 5 → ℕ) k) ∧
    (∑ k : Fin 4, (![1/2,1/1848,461/1848,1/4] : Fin 4 → ℝ) k) = 1 ∧
    (∑ k : Fin 5, (![1/2,1/22,3/44,3/22,1/4] : Fin 5 → ℝ) k) = 1 ∧
    (∀ k : Fin 4, 0 < (![1/2,1/2000,499/2000,1/4] : Fin 4 → ℝ) k) ∧
    (1/2000 : ℝ) < 1/100)

/-- Mathematical content packaged for P037-T22. -/
def T22Statement : Prop :=
  (∀ {Ω I : Type*} [Fintype Ω] (P : ProbabilityDesign Ω) (D : Ω → I → Fin 5) (J : ℕ) (hJ : 0 < J) (draws : Fin J → Ω) (seed outcome baseline screen : Ω → I → Prop) (z : Ω),
    let π := fun i k => eventProbability P (fun w => D w i=k.castSucc)
    let phat := fun i k => ((Finset.univ.filter
      (fun j => D (draws j) i=k.castSucc)).card:ℝ)/J
    positiveExposurePopulation π=exposureProbabilityCutoff π 0 ∧
    exposureProbabilityCutoff π (1/100)⊆positiveExposurePopulation π ∧
    exposureProbabilityCutoff phat (1/100)⊆exposureProbabilityCutoff phat 0 ∧
    exposureProbabilityCutoff phat 0⊆positiveExposurePopulation π ∧
    analysisPopulation phat seed outcome baseline screen z⊆positiveExposurePopulation π ∧
    analysisPopulation phat seed outcome baseline screen z⊆{i | ¬seed z i}) ∧
  (∀ {Ω : Type*} [Fintype Ω] (P : ProbabilityDesign Ω) (E : Ω → Prop) (hp : 0 < eventProbability P E) (hq : eventProbability P E < 1),
    let event := fun z : Fin 10000 → Ω =>
      101 ≤ (Finset.univ.filter (fun j => E (z j))).card
    0 < (∑ z, (∏ j, P.mass (z j))*(if event z then (1:ℝ) else 0)) ∧
    (∑ z, (∏ j, P.mass (z j))*(if event z then (1:ℝ) else 0)) < 1) ∧
  (∀ {Ω I : Type*} [Fintype Ω] (P : ProbabilityDesign Ω) (estimated : I → Fin 4 → ℝ) (seed outcome baseline screen : Ω → I → Prop) (i : I),
    eventProbability P (fun z => seed z i) ≤ 
      eventProbability P (fun z => i∉analysisPopulation estimated seed outcome baseline screen z)) ∧
  (∀ (r : ℕ) (hr : r ≤ 10000),
    ((r:ℝ)/10000 > 1/100 ↔ 101 ≤ r) ∧
    (101 ≤ r → 1/((r:ℝ)/10000) ≤ 10000/101 ∧ (10000/101:ℝ) < 100))

/-- Mathematical content packaged for P037-T23. -/
def T23Statement : Prop :=
  ((∑ i, bandSizes i)=56 ∧
    (∑ i, bandSizes i*bandTreatments i)=28 ∧
    bandGramInverse*bandDesignGram=1 ∧
    bandDesignGram.mulVec bandFit=bandNormalRhs ∧
    (∀ i, |bandOutcomes i-dotProduct (bandDesignRow i) bandFit|=1/10) ∧
    bandGramInverse*bandSandwichMeat*bandGramInverse.transpose=bandHC0) ∧
  (dotProduct (![1,0,0] : Fin 3 → ℝ) bandFit=1/10 ∧
    dotProduct (![1,1,1/10] : Fin 3 → ℝ) bandFit=7/20 ∧
    linearPredictionVariance bandHC0 ![1,0,0]=1/2800 ∧
    linearPredictionVariance bandHC0 ![1,1,1/10]=1/2800 ∧
    linearPredictionVariance bandHC0 ![0,1,1/10]=1/1400 ∧
    dotProduct (![1,0,0] : Fin 3 → ℝ) (bandHC0.mulVec ![0,1,1/10])=-1/2800 ∧
    ((28/100:ℝ)/27)/56=1/5400 ∧
    (1/1400:ℝ) > 1/2800 ∧ (1/5400:ℝ) < 1/2800 ∧
    (1/5400:ℝ)/(1/2800)=14/27 ∧ ((28/100:ℝ)/27)/28≠1/2800) ∧
  (centeredBandGramInverse*centeredBandGram=1 ∧
    centeredBandGram.mulVec centeredBandFit=(fun j => ∑ i,
      bandSizes i*centeredBandRow i j*bandOutcomes i) ∧
    (∀ i, dotProduct (centeredBandRow i) centeredBandFit=
      dotProduct (bandDesignRow i) bandFit) ∧
    (centeredBandGramInverse*centeredBandMeat*centeredBandGramInverse.transpose) 1 1=1/1400)

/-- Mathematical content packaged for P037-T24. -/
def T24Statement : Prop :=
  (∀ {p : ℕ} (zbar : Fin p → ℝ) (b : (Fin 3 ⊕ Fin p) → ℝ) (c : ℝ),
    dotProduct (Sum.elim (![1,0,0] : Fin 3 → ℝ) zbar) b=
      b (.inl 0)+(∑ j, zbar j*b (.inr j)) ∧
    dotProduct (Sum.elim (![1,1,c] : Fin 3 → ℝ) zbar) b=
      b (.inl 0)+b (.inl 1)+c*b (.inl 2)+(∑ j, zbar j*b (.inr j)) ∧
    dotProduct (Sum.elim (![1,1,c] : Fin 3 → ℝ) zbar) b-
      dotProduct (Sum.elim (![1,0,0] : Fin 3 → ℝ) zbar) b=
        b (.inl 1)+c*b (.inl 2)) ∧
  (∀ {k : ℕ} (V : Matrix (Fin k) (Fin k) ℝ) (hV : V.transpose=V) (l0 d : Fin k → ℝ),
    linearPredictionVariance V (l0+d) = linearPredictionVariance V l0 +
      linearPredictionVariance V d + 2*dotProduct l0 (V.mulVec d) ∧
    (linearPredictionVariance V (l0+d) = linearPredictionVariance V d ↔
      linearPredictionVariance V l0 + 2*dotProduct l0 (V.mulVec d)=0)) ∧
  (∀ {n p : ℕ} (T C : Fin n → ℝ) (z : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (c : ℝ),
    let X : Matrix (Fin n) (Fin (3+p)) ℝ := fun i j =>
      if h0 : j.val=0 then 1 else if h1 : j.val=1 then T i else if h2 : j.val=2 then T i*C i
      else z i ⟨j.val-3, by omega⟩
    let Xc : Matrix (Fin n) (Fin (3+p)) ℝ := fun i j =>
      if h0 : j.val=0 then 1 else if h1 : j.val=1 then T i else if h2 : j.val=2 then T i*(C i-c)
      else z i ⟨j.val-3, by omega⟩
    let b := (olsMap X).mulVec y
    let bc := (olsMap Xc).mulVec y
    let V := hc0Covariance X y
    Function.Injective X.mulVec →
      Xc.mulVec bc=X.mulVec b ∧ olsResidual Xc y=olsResidual X y ∧
      bc ⟨1, by omega⟩=b ⟨1, by omega⟩+c*b ⟨2, by omega⟩ ∧
      hc0Covariance Xc y ⟨1, by omega⟩ ⟨1, by omega⟩=
        V ⟨1, by omega⟩ ⟨1, by omega⟩+
        2*c*V ⟨1, by omega⟩ ⟨2, by omega⟩+
        c^2*V ⟨2, by omega⟩ ⟨2, by omega⟩)

/-- Mathematical content packaged for P037-T25. -/
def T25Statement : Prop :=
  (indegreeQuantile90 nominationGraph10=11/10 ∧ referentStudents nominationGraph10={1} ∧
    networkExposureLabel nominationGraph10 (referentStudents nominationGraph10) {1} 0=0 ∧
    networkExposureLabel (peerUnion nominationGraph10) (referentStudents nominationGraph10) {1} 0=2 ∧
    indegreeQuantile90 nominationGraph20=3/2 ∧ referentStudents nominationGraph20={1,2} ∧
    (∀ k, graphExposureProbability20 nominationGraph20 k=(![1/2,1/10,3/20,1/4] : Fin 4 → ℝ) k) ∧
    (∀ k, graphExposureProbability20 (peerUnion nominationGraph20) k=(![1/2,1/40,3/40,2/5] : Fin 4 → ℝ) k) ∧
    (∀ k, 0 < graphExposureProbability20 nominationGraph20 k ∧ graphExposureProbability20 nominationGraph20 k < 1 ∧
      0 < graphExposureProbability20 (peerUnion nominationGraph20) k ∧
      graphExposureProbability20 (peerUnion nominationGraph20) k < 1)) ∧
  (directedIndegree nominationGraph10 = (![1,2,0,0,0,0,0,0,0,0] : Fin 10 → ℕ) ∧
    directedIndegree nominationGraph20 =
      (![1,6,7,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] : Fin 20 → ℕ) ∧
    (∀ i, nominationGraph10 i i = false) ∧ (∀ i, nominationGraph20 i i = false) ∧
    (∀ i, (directedIndegree nominationGraph10 i : ℝ) ≠ indegreeQuantile90 nominationGraph10) ∧
    (∀ i, (directedIndegree nominationGraph20 i : ℝ) ≠ indegreeQuantile90 nominationGraph20) ∧
    seedPeerCount nominationGraph10 0 {1} = 0 ∧
    referentSeedPeerCount nominationGraph10 {1} {1} 0 = 0 ∧
    seedPeerCount (peerUnion nominationGraph10) 0 {1} = 1 ∧
    referentSeedPeerCount (peerUnion nominationGraph10) {1} {1} 0 = 1 ∧
    Finset.univ.filter (fun j => nominationGraph20 0 j = true) = {2,4} ∧
    Finset.univ.filter (fun j => peerUnion nominationGraph20 0 j = true) = {1,2,4} ∧
    (Finset.univ.powersetCard 3 : Finset (Finset (Fin 6))).card = 20 ∧
    (∀ k : Fin 4, (((Finset.univ.powersetCard 3).filter (fun s : Finset (Fin 6) =>
      (networkExposureLabel nominationGraph20 {1,2} (s.image eligibleStudents20) 0).val+1=k.val)).card) =
      (![0,4,6,10] : Fin 4 → ℕ) k) ∧
    (∀ k : Fin 4, (((Finset.univ.powersetCard 3).filter (fun s : Finset (Fin 6) =>
      (networkExposureLabel (peerUnion nominationGraph20) {1,2} (s.image eligibleStudents20) 0).val+1=k.val)).card) =
      (![0,1,3,16] : Fin 4 → ℕ) k) ∧
    (∀ k : Fin 3,
      graphExposureProbability20 nominationGraph20 k.succ ≠
        graphExposureProbability20 (peerUnion nominationGraph20) k.succ ∧
      1 / graphExposureProbability20 nominationGraph20 k.succ ≠
        1 / graphExposureProbability20 (peerUnion nominationGraph20) k.succ))

/-- Mathematical content packaged for P037-T26. -/
def T26Statement : Prop :=
  (∀ {n : ℕ} (B : Fin n → Fin n → Bool) (hdiag : ∀ i, B i i=false),
    (∀ i j, peerUnion B i j=peerUnion B j i) ∧
    (∀ i, peerUnion B i i=false) ∧
    (∀ i j, B i j=true → peerUnion B i j=true) ∧
    (∀ i j, peerUnion B i j=true ∧ B i j=false ↔
      B j i=true ∧ B i j=false)) ∧
  (∀ {n : ℕ} (B : Fin n → Fin n → Bool) (z γ : Fin n → Bool) (i : Fin n),
    (∑ j : Fin n, (if peerUnion B i j && z j then (1:ℕ) else 0))=
      (∑ j : Fin n, (if B i j && z j then (1:ℕ) else 0))+
      (∑ j : Fin n, (if !B i j && B j i && z j then (1:ℕ) else 0)) ∧
    (∑ j : Fin n, (if peerUnion B i j && z j && γ j then (1:ℕ) else 0))=
      (∑ j : Fin n, (if B i j && z j && γ j then (1:ℕ) else 0))+
      (∑ j : Fin n, (if !B i j && B j i && z j && γ j then (1:ℕ) else 0))) ∧
  (∀ (c b r q : ℕ) (hr : r ≤ c) (hq : q ≤ b),
    (nonseedExposureLabel c r=nonseedExposureLabel (c+b) (r+q) ↔
      (0 < c ∨ b=0) ∧ (0 < r ∨ q=0)) ∧
    (nonseedExposureLabel (c+b) (r+q)=0 → nonseedExposureLabel c r=0) ∧
    (nonseedExposureLabel c r=2 → nonseedExposureLabel (c+b) (r+q)=2)) ∧
  (∀ {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∀ z, 0 < p z) (c b r q : Ω → ℕ) (hr : ∀ z, r z ≤ c z) (hq : ∀ z, q z ≤ b z) (total : ∑ z, p z = 1),
    (∑ z, p z*(if nonseedExposureLabel (c z+b z) (r z+q z)=0 then (1:ℝ) else 0)) ≤ 
      (∑ z, p z*(if nonseedExposureLabel (c z) (r z)=0 then (1:ℝ) else 0)) ∧
    (∑ z, p z*(if nonseedExposureLabel (c z) (r z)=2 then (1:ℝ) else 0)) ≤ 
      (∑ z, p z*(if nonseedExposureLabel (c z+b z) (r z+q z)=2 then (1:ℝ) else 0)) ∧
    ((∃ z, nonseedExposureLabel (c z) (r z)=0 ∧ nonseedExposureLabel (c z+b z) (r z+q z)≠0) →
      (∑ z, p z*(if nonseedExposureLabel (c z+b z) (r z+q z)=0 then (1:ℝ) else 0)) < 
      (∑ z, p z*(if nonseedExposureLabel (c z) (r z)=0 then (1:ℝ) else 0))) ∧
    ((∃ z, nonseedExposureLabel (c z) (r z)≠2 ∧ nonseedExposureLabel (c z+b z) (r z+q z)=2) →
      (∑ z, p z*(if nonseedExposureLabel (c z) (r z)=2 then (1:ℝ) else 0)) < 
      (∑ z, p z*(if nonseedExposureLabel (c z+b z) (r z+q z)=2 then (1:ℝ) else 0))))

/-- Mathematical content packaged for P037-T29. -/
def T29Statement : Prop :=
  ((∑ z : RareSeedAssignments, rareAssignmentMass z)=1 ∧
    (∀ k, rareExposureProbability k=(![1/2,1/127008,31751/127008,1/4] : Fin 4 → ℝ) k) ∧
    (∀ k, 0 < rareExposureProbability k ∧ rareExposureProbability k < 1) ∧
    (∀ r : ℕ, rareExposureProbability 1 ≤  |(r:ℝ)/10000-rareExposureProbability 1| ∧
      rareExposureProbability 1/2 <  |(r:ℝ)/10000-rareExposureProbability 1|) ∧
    (let hits := fun draws : Fin 10000 → RareSeedAssignments =>
       (Finset.univ.filter (fun j => rareExposure (draws j)=1)).card
     let mass := fun draws : Fin 10000 → RareSeedAssignments => ∏ j, rareAssignmentMass (draws j)
     (∑ draws, mass draws*(hits draws:ℝ))=625/7938 ∧
     (∑ draws, mass draws*(if hits draws=0 then (1:ℝ) else 0))=(127007/127008:ℝ)^10000 ∧
     (∑ draws, mass draws*((hits draws:ℝ)/10000-1/127008)^2)=127007/161310320640000) ∧
    (9/10:ℝ) < (127007/127008:ℝ)^10000 ∧ (127007/127008:ℝ)^10000 < 19/20) ∧
  ((∀ r : ℕ, (1/127008:ℝ) ≤  |(r:ℝ)/10000-1/127008| ∧
      (1/254016:ℝ) <  |(r:ℝ)/10000-1/127008|) ∧
    (10000:ℝ)/127008=625/7938 ∧
    ((1/127008:ℝ)*(1-1/127008)/10000)=127007/161310320640000 ∧
    ((1/127008:ℝ)*(1-1/127008)/10000)/(1/127008)^2=127007/10000 ∧
    ((1/2:ℝ)*(1-1/2)/10000)=1/40000 ∧ (1/200:ℝ)^2=1/40000)

end SAP.P037b
