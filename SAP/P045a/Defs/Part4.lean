import SAP.P045a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical
open Finset

namespace SAP.P045a
noncomputable section

/-- Substantive conclusions retained for P045-T1; see the Challenge docstring for scope. -/
def T1Statement : Prop :=
  (Fintype.card BernoulliWitnessOutcome = 512 ∧
    (∑ w, bernoulliWitnessMass w) = 1 ∧
    (∀ p : ℝ, 0 < p → p < 1 → ∀ i : Fin 4, ∀ b : Bool,
      marginal (bernoulli p) coMembers i b = 3*p) ∧
    (∀ z : Assignment 4, ∀ i, coMembers i z = (treatedCount z : ℝ) - bit (z i)) ∧
    (∀ w high, witnessDomain true high w → witnessDomain false high w →
      witnessDirect high w = -1) ∧
    prob bernoulliWitnessMass (fun w => witnessDomain true true w ∧ witnessDomain false true w) = 7/8 ∧
    prob bernoulliWitnessMass (fun w => witnessDomain true false w ∧ witnessDomain false false w) = 87/128 ∧
    prob bernoulliWitnessMass (fun w => witnessDomain false true w ∧ witnessDomain false false w) = 3825/4096 ∧
    prob bernoulliWitnessMass (fun w => witnessDomain true true w ∧ witnessDomain false false w) = 3825/4096 ∧
    condMean bernoulliWitnessMass (fun w => witnessDomain false true w ∧ witnessDomain false false w)
      witnessIndirect = 224/255 ∧
    condMean bernoulliWitnessMass (fun w => witnessDomain true true w ∧ witnessDomain false false w)
      witnessTotal = 37/255 ∧
    prob bernoulliWitnessMass (fun w => ∀ b high, witnessDomain b high w) = 609/1024 ∧
    condMean bernoulliWitnessMass (fun w => ∀ b high, witnessDomain b high w) witnessIndirect = 16/29 ∧
    condMean bernoulliWitnessMass (fun w => ∀ b high, witnessDomain b high w) witnessTotal = -13/29 ∧
    (∀ z : Assignment 4, groupOverall coMembers z = (3/4)*(treatedCount z : ℝ)) ∧
    expect bernoulliWitnessMass witnessOverall = 3/4)
  ∧
  (condMean (bernoulli (1/2))
      (fun z : Assignment 4 => armExists true z) (armMean coMembers true) = 17/15 ∧
    condMean (bernoulli (1/2))
      (fun z : Assignment 4 => armExists false z) (armMean coMembers false) = 28/15 ∧
    condMean (bernoulli (1/4))
      (fun z : Assignment 4 => armExists true z) (armMean coMembers true) = 81/175 ∧
    condMean (bernoulli (1/4))
      (fun z : Assignment 4 => armExists false z) (armMean coMembers false) = 84/85)
  ∧
  (∀ (high : Bool),
    prob bernoulliWitnessMass (fun w => witnessDomain true high w ∧ witnessDomain false high w) =
      (if high then 7/8 else 87/128) ∧
    condMean bernoulliWitnessMass (fun w => witnessDomain true high w ∧ witnessDomain false high w)
      (witnessDirect high) = -1)
  ∧
  (∀ (p : ℝ), 0 < p → p < 1 →
      mean (fun i : Fin 4 => marginal (bernoulli p) coMembers i true) -
      mean (fun i : Fin 4 => marginal (bernoulli p) coMembers i false) = 0)
  ∧
  (∀ w, 0 ≤ bernoulliWitnessMass w)

/-- Substantive conclusions retained for P045-T2; see the Challenge docstring for scope. -/
def T2Statement : Prop :=
  (∀ {n : ℕ} (hn : 0 < n) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (y : Fin n → Assignment n → ℝ) (b : Bool),
    (∀ i, expect (bernoulli p) (fun z => if z i=b then y i z else 0) =
      (if b then p else 1-p)*marginal (bernoulli p) y i b) ∧
    expect (bernoulli p) (groupHT p y b) = mean (fun i => marginal (bernoulli p) y i b))
  ∧
  (∀ (G C : ℕ), 0 < C → C ≤ G → ∀ (n : Fin G → ℕ), (∀ g, 0 < n g) →
      ∀ (p : ℝ), 0 < p → p < 1 →
      ∀ (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ) (b : Bool),
      expect (selectedLaw n C (fun _ => bernoulli p))
        (selectedMean C (fun g => groupHT p (y g) b)) =
      mean (fun g => mean (fun i => marginal (bernoulli p) (y g) i b)))
  ∧
  (∀ {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (y : Fin n → Assignment n → ℝ) (b : Bool),
    expect (crMass n k) (armMean y b) =
      mean (fun i => marginal (crMass n k) y i b))
  ∧
  (∀ (G C : ℕ), 0 < C → C ≤ G → ∀ (n k : Fin G → ℕ),
      (∀ g, 0 < k g ∧ k g < n g) →
      ∀ (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ) (b : Bool),
      expect (selectedLaw n C (fun g => crMass (n g) (k g)))
        (selectedMean C (fun g => armMean (y g) b)) =
      mean (fun g => mean (fun i => marginal (crMass (n g) (k g)) (y g) i b)))
  ∧
  ((∀ k : Fin 4, 0 < k.val →
      (∀ i : Fin 4, marginal (crMass 4 k.val) coMembers i true = (k.val : ℝ)-1 ∧
        marginal (crMass 4 k.val) coMembers i false = (k.val : ℝ)) ∧
      mean (fun i : Fin 4 => marginal (crMass 4 k.val) coMembers i true) -
        mean (fun i : Fin 4 => marginal (crMass 4 k.val) coMembers i false) = -1 ∧
      mean (fun i : Fin 4 => marginal (bernoulli ((k.val : ℝ)/4)) coMembers i true) -
        mean (fun i : Fin 4 => marginal (bernoulli ((k.val : ℝ)/4)) coMembers i false) = 0))
  ∧
  (∀ {n : ℕ} (hn : 0 < n) (q : Design (Assignment n))
    (y : Fin n → Assignment n → ℝ),
    expect q.mass (groupOverall y) = mean (fun i => expect q.mass (y i)))
  ∧
  (∀ (G C : ℕ), 0 < C → C ≤ G → ∀ (n : Fin G → ℕ), (∀ g, 0 < n g) →
      ∀ (q : (g : Fin G) → Design (Assignment (n g)))
      (y : (g : Fin G) → Fin (n g) → Assignment (n g) → ℝ),
      expect (selectedLaw n C (fun g => (q g).mass))
        (selectedMean C (fun g => groupOverall (y g))) =
      mean (fun g => mean (fun i => expect (q g).mass (y g i))))
  ∧
  (∀ (p : ℝ), 0 < p → p < 1 → ∀ (z : Assignment 4),
    groupHT p coMembers true z =
      (treatedCount z : ℝ)*((treatedCount z : ℝ)-1)/(4*p) ∧
    groupHT p coMembers false z =
      (treatedCount z : ℝ)*(4-(treatedCount z : ℝ))/(4*(1-p)))
  ∧
  (∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1),
    expect (bernoulli p) (groupHT p (coMembers (n := 4)) true)=3*p ∧
    expect (bernoulli p) (groupHT p (coMembers (n := 4)) false)=3*p ∧
    expect (bernoulli p) (fun z : Assignment 4 =>
      groupHT p coMembers true z-groupHT p coMembers false z)=0)

/-- Substantive conclusions retained for P045-T3; see the Challenge docstring for scope. -/
def T3Statement : Prop :=
  (let n : Fin 6 → ℕ := fun _ => 3
    let law (m : ℕ) := selectedLaw n 3 (fun _ => crMass 3 m)
    let x : Fin 3 → ℝ := fun i => (i.val : ℝ)+1
    let point (a b : Fin 3 → ℝ) := selectedMean 3 (fun _ => directGroup a b)
    let vest (a b : Fin 3 → ℝ) := directVarianceEstimate 3 (fun _ => a) (fun _ => b)
    (∀ m ∈ ({1,2} : Finset ℕ),
      expect (law m) (point (fun i => x i+1) x) = 1 ∧
      variance (law m) (point (fun i => x i+1) x) = 1/2 ∧
      expect (law m) (vest (fun i => x i+1) x) = 1/3) ∧
    variance (law 2) (point (fun i => 2*x i) (fun i => (5/4)*x i)) = 9/8 ∧
    expect (law 2) (vest (fun i => 2*x i) (fun i => (5/4)*x i)) = 43/48 ∧
    variance (law 1) (point (fun i => (3/2)*x i) x) = 8/9 ∧
    expect (law 1) (vest (fun i => (3/2)*x i) x) = 19/36 ∧
    variance (law 2) (point x (fun _ => 0)) = 1/18 ∧
    expect (law 2) (vest x (fun _ => 0)) = 1/9)
  ∧
  (let x : Fin 3 → ℝ := fun i => (i.val : ℝ)+1
    ∀ m ∈ ({1,2} : Finset ℕ),
      expect (crMass 3 m) (directGroup (fun i => x i+1) x)=1 ∧
      variance (crMass 3 m) (directGroup (fun i => x i+1) x)=3/2 ∧
      expect (crMass 3 m) (droppedWithin (fun i => x i+1) x)=1/2)

/-- Substantive conclusions retained for P045-T4; see the Challenge docstring for scope. -/
def T4Statement : Prop :=
  (∀ {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (n m : Fin G → ℕ) (hm : ∀ g, 2 ≤ m g ∧ m g + 2 ≤ n g)
    (a b : (g : Fin G) → Fin (n g) → ℝ),
    let q := fun g => crMass (n g) (m g)
    let law := selectedLaw n C q
    let θ := fun g => mean (a g) - mean (b g)
    let V := fun g => popVar (a g)/(m g) + popVar (b g)/((n g-m g : ℕ) : ℝ) -
      popVar (fun i => a g i-b g i)/(n g)
    let point := selectedMean C (fun g => directGroup (a g) (b g))
    let vest := directVarianceEstimate C a b
    (∀ g, expect (q g) (directGroup (a g) (b g)) = θ g ∧
      variance (q g) (directGroup (a g) (b g)) = V g) ∧
    expect law point = mean θ ∧
    variance law point = ((1-(C : ℝ)/G)/C)*popVar θ + (∑ g, V g)/((C : ℝ)*G) ∧
    expect law vest - variance law point =
      (∑ g, popVar (fun i => a g i-b g i)/(n g))/(G : ℝ)^2 ∧
    0 ≤ expect law vest - variance law point ∧
    (expect law vest = variance law point ↔ ∀ g, ∀ i j, a g i-b g i = a g j-b g j))
  ∧
  (∀ {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (a b : Fin G → Fin 3 → ℝ),
    let n : Fin G → ℕ := fun _ => 3
    let bias := fun m : ℕ =>
      expect (selectedLaw n C (fun _ => crMass 3 m)) (directVarianceEstimate (n := n) C a b) -
      variance (selectedLaw n C (fun _ => crMass 3 m))
        (selectedMean (n := n) C (fun g : Fin G => directGroup (a g) (b g)))
    bias 2 = (Finset.sum (univ : Finset (Fin G)) (fun g =>
      popVar (fun i : Fin 3 => a g i-b g i)/3 - popVar (b g)))/(G : ℝ)^2 ∧
    bias 1 = (Finset.sum (univ : Finset (Fin G)) (fun g =>
      popVar (fun i : Fin 3 => a g i-b g i)/3 - popVar (a g)))/(G : ℝ)^2)
  ∧
  (∀ {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (x : Fin G → Fin 3 → ℝ),
    let n : Fin G → ℕ := fun _ => 3
    let bias := fun (m : ℕ) (a b : Fin G → Fin 3 → ℝ) =>
      expect (selectedLaw n C (fun _ => crMass 3 m)) (directVarianceEstimate (n := n) C a b) -
      variance (selectedLaw n C (fun _ => crMass 3 m))
        (selectedMean (n := n) C (fun g : Fin G => directGroup (a g) (b g)))
    bias 2 (fun g i => 2*x g i) (fun g i => (5/4)*x g i) =
      -(11/(8*(G : ℝ)^2))*(∑ g, popVar (x g)) ∧
    bias 1 (fun g i => (3/2)*x g i) x =
      -(13/(6*(G : ℝ)^2))*(∑ g, popVar (x g)) ∧
    ((∃ g i j, x g i ≠ x g j) →
      bias 2 (fun g i => 2*x g i) (fun g i => (5/4)*x g i) < 0 ∧
      bias 1 (fun g i => (3/2)*x g i) x < 0))
  ∧
  (∀ (m : ℕ) (hm : m ∈ ({1,2} : Finset ℕ))
    (a b : Fin 6 → Fin 3 → ℝ) (H : Finset (Fin 6)) (hH : H ∈ firstStageSets 6 3)
    (w : Fin 6 → Assignment 3) (hw : ∀ g ∈ H, w g ∈ fixedAssignments 3 m),
    requiredDirectVariance (n := fun _ => 3) 3 a b (H,w)=none)

/-- Substantive conclusions retained for P045-T5; see the Challenge docstring for scope. -/
def T5Statement : Prop :=
  ((∀ i : Fin 2, neighborhood edge2 i = univ) ∧
    (∀ i : Fin 2, badAllControl edge2 ![true,false] i ∧ ¬allControl edge2 ![true,false] i) ∧
    (∀ i : Fin 2, prob (bernoulli (1/2)) (fun z => allTreated edge2 z i) = 1/4 ∧
      prob (bernoulli (1/2)) (fun z => badAllControl edge2 z i) = 3/4 ∧
      prob (bernoulli (1/2)) (fun z => allControl edge2 z i) = 1/4) ∧
    allVsNone linear2 = 2 ∧
    fullHT (bernoulli (1/2)) edge2 linear2 false ![false,false] = -4/3 ∧
    fullHT (bernoulli (1/2)) edge2 linear2 false ![false,true] = -8/3 ∧
    fullHT (bernoulli (1/2)) edge2 linear2 false ![true,false] = -8/3 ∧
    fullHT (bernoulli (1/2)) edge2 linear2 false ![true,true] = 12 ∧
    expect (bernoulli (1/2)) (fullHT (bernoulli (1/2)) edge2 linear2 false) = 4/3 ∧
    expect (bernoulli (1/2)) (fullHT (bernoulli (1/2)) edge2 linear2 true) = 2 ∧
    allVsNone threshold2 = 2 ∧
    expect (bernoulli (1/2)) (fullHT (bernoulli (1/2)) edge2 threshold2 false) = 2 ∧
    expect (bernoulli (1/2)) (fullHT (bernoulli (1/2)) edge2 threshold2 true) = 2)

/-- Substantive conclusions retained for P045-T6; see the Challenge docstring for scope. -/
def T6Statement : Prop :=
  (∀ {n : ℕ} (A : Network n) (z : Assignment n) (i : Fin n),
    (∑ j, bit (z j) * bit (if j = i then true else A.adj j i)) = neighborhoodCount A.adj z i ∧
    (∑ j, bit (if i = j then true else A.adj i j)) = (neighborhood A.adj i).card ∧
    neighborhoodCount A.adj z i ≤ (neighborhood A.adj i).card ∧
    (allTreated A.adj z i ↔ ∀ j ∈ neighborhood A.adj i, z j = true) ∧
    (allControl A.adj z i ↔ ∀ j ∈ neighborhood A.adj i, z j = false) ∧
    (badAllControl A.adj z i ↔ ∃ j ∈ neighborhood A.adj i, z j = false) ∧
    (allControl A.adj z i → badAllControl A.adj z i) ∧
    (badAllControl A.adj z i ∧ ¬allControl A.adj z i ↔
      0 < neighborhoodCount A.adj z i ∧ neighborhoodCount A.adj z i < (neighborhood A.adj i).card) ∧
    ((∀ v : Assignment n, allControl A.adj v i ↔ badAllControl A.adj v i) ↔
      (neighborhood A.adj i).card = 1) ∧
    ¬(allTreated A.adj z i ∧ allControl A.adj z i) ∧
    (allTreated A.adj z i ↔ ¬badAllControl A.adj z i))
  ∧
  (∀ (Ω : Type) [Fintype Ω] (p : Design Ω)
      (E : Ω → Prop) [DecidablePred E] (Y : Ω → ℝ),
      0 < prob p.mass E →
      expect p.mass (fun w => if E w then Y w / prob p.mass E else 0) =
        condMean p.mass E Y)
  ∧
  (∀ {n : ℕ} (hn : 0 < n)
    (p : Design (Assignment n)) (A : Network n) (Y : Fin n → Assignment n → ℝ)
    (hT : ∀ i z, allTreated A.adj z i → Y i z = Y i (fun _ => true))
    (hC : ∀ i z, allControl A.adj z i → Y i z = Y i (fun _ => false))
    (pT : ∀ i, 0 < prob p.mass (fun z => allTreated A.adj z i))
    (pC : ∀ i, 0 < prob p.mass (fun z => allControl A.adj z i)),
    expect p.mass (fullHT p.mass A.adj Y true) = allVsNone Y ∧
    expect p.mass (fullHT p.mass A.adj Y false) =
      mean (fun i => Y i (fun _ => true) - condMean p.mass (fun z => badAllControl A.adj z i) (Y i)) ∧
    ((∀ i z, badAllControl A.adj z i → Y i z = Y i (fun _ => false)) →
      expect p.mass (fullHT p.mass A.adj Y false) = allVsNone Y))

end
end SAP.P045a
