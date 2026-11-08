import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def nominationStatistic {I : Type*} [Fintype I]
    (E : Finset I) (A : I → I → ℝ) (M z Y : I → ℝ) : ℝ :=
  (∑ i ∈ E, ∑ j, A i j*M j*z i*Y j)/(∑ i ∈ E, ∑ j, A i j*M j*z i) -
  (∑ i ∈ E, ∑ j, A i j*M j*(1-z i)*Y j)/(∑ i ∈ E, ∑ j, A i j*M j*(1-z i))

def partner (i : Fin 5 × Bool) : Fin 5 × Bool := (i.1,!i.2)

def pairedSupport : Finset (Finset (Fin 5 × Bool)) := Finset.univ.powersetCard 5

def pairedObserved : Finset (Fin 5 × Bool) := {(0,false),(1,false),(2,false),(3,false),(4,false)}

noncomputable def directOnly (z : Finset (Fin 5 × Bool)) (i : Fin 5 × Bool) : ℝ :=
  if i∈z then 1 else 0

noncomputable def pairedStatistic (z : Finset (Fin 5 × Bool)) (Y : (Fin 5 × Bool) → ℝ) : ℝ :=
  (∑ i ∈ z, Y (partner i))/5-(∑ i ∈ Finset.univ \ z, Y (partner i))/5

noncomputable def pairedPValue (z : Finset (Fin 5 × Bool)) : ℝ :=
  (((pairedSupport.filter (fun z' =>
    |pairedStatistic z' (directOnly z)| ≥ |pairedStatistic z (directOnly z)|)).card:ℝ))/252

/-- The nomination graph of the five reciprocal pairs. -/
noncomputable def pairedNomination (i j : Fin 5 × Bool) : ℝ :=
  if j=partner i then 1 else 0

/-- Exactly one student is selected from each reciprocal pair. -/
def PairSplit (z : Finset (Fin 5 × Bool)) : Prop :=
  ∀ b : Fin 5, ((b,false)∈z ↔ (b,true)∉z)

def PairedTestCertificate : Prop :=
  pairedSupport.card=252 ∧ pairedObserved∈pairedSupport ∧
    pairedStatistic pairedObserved (directOnly pairedObserved)=-1 ∧
    (∀ k : Fin 6, (pairedSupport.filter (fun z =>
      pairedStatistic z (directOnly pairedObserved)=((2*(k.val:ℝ)-5)/5))).card=
      (Nat.choose 5 k.val)^2) ∧
    pairedPValue pairedObserved=1/126 ∧ (1/126:ℝ)<1/100 ∧
    (∀ z ∈ pairedSupport,
      (∀ b : Fin 5, ((b,false)∈z ↔ (b,true)∉z)) → pairedPValue z=1/126) ∧
    (∀ z ∈ pairedSupport,
      ¬(∀ b : Fin 5, ((b,false)∈z ↔ (b,true)∉z)) → 13/63≤pairedPValue z) ∧
    ((pairedSupport.filter (fun z => pairedPValue z<1/100)).card:ℝ)/252=8/63

/-- The supported one-block counterexample, with its exact arithmetic. -/
def T35Statement : Prop :=
  PairedTestCertificate ∧
  (∀ (z z' : Finset (Fin 5 × Bool)) (i : Fin 5 × Bool),
    (i∈z ↔ i∈z') → directOnly z i=directOnly z' i) ∧
  (∀ k : Fin 6, (Nat.choose 5 k.val)^2=(![1,25,100,100,25,1] : Fin 6 → ℕ) k) ∧
  (pairedSupport.filter PairSplit).card=32 ∧
  (∀ z ∈ pairedSupport, pairedStatistic z (directOnly pairedObserved)=
    (2*((z ∩ pairedObserved.image partner).card:ℝ)-5)/5) ∧
  (∀ b : Fin 5, directOnly pairedObserved (b,false)=1 ∧
    directOnly pairedObserved (b,true)=0) ∧
  (∑ i ∈ pairedObserved, directOnly pairedObserved (partner i))/5=0 ∧
  (∑ i ∈ Finset.univ \ pairedObserved, directOnly pairedObserved (partner i))/5=1 ∧
  pairedObserved.image partner=Finset.univ \ pairedObserved ∧
  (Finset.univ \ pairedObserved).image partner=pairedObserved ∧
  pairedPValue pairedObserved=2/252 ∧ (2:ℕ)^5=32

/-- A second supported assignment, differing only in the first pair. -/
def pairedAlternative : Finset (Fin 5 × Bool) :=
  {(0,true),(1,false),(2,false),(3,false),(4,false)}

/-- The schedule has no social influence but violates the global sharp null and rejects. -/
def PairedNominationWitness : Prop :=
  (∀ z ∈ pairedSupport, ∀ Y : (Fin 5 × Bool) → ℝ,
    nominationStatistic Finset.univ pairedNomination (fun _ => 1) (directOnly z) Y=
      pairedStatistic z Y) ∧
  (∀ (z z' : Finset (Fin 5 × Bool)) (i : Fin 5 × Bool),
    (i∈z ↔ i∈z') → directOnly z i=directOnly z' i) ∧
  (¬ (∀ z ∈ pairedSupport, ∀ z' ∈ pairedSupport, ∀ i,
    directOnly z i=directOnly z' i)) ∧
  nominationStatistic Finset.univ pairedNomination (fun _ => 1)
    (directOnly pairedObserved) (directOnly pairedObserved) = -1 ∧
  pairedPValue pairedObserved=1/126 ∧
  ((pairedSupport.filter (fun z => pairedPValue z<1/100)).card:ℝ)/252=8/63

/-- Exact sharp-null validity for the nomination statistic, with nonempty recipient groups. -/
def NominationSharpNullStatement (Ω I : Type*) [Fintype Ω] [Fintype I] : Prop :=
  ∀ (E : Finset I) (A : I → I → ℝ) (M : I → ℝ) (Z : Ω → I → ℝ)
    (p : Ω → ℝ) (Y : Ω → I → ℝ) (z0 : Ω) (α : ℝ),
    (∀ i j, 0≤A i j) → (∀ i, M i=0 ∨ M i=1) →
    (∀ z i, Z z i=0 ∨ Z z i=1) → (∀ z i, i∉E → Z z i=0) →
    (∀ z, 0<∑ i ∈ E, ∑ j, A i j*M j*Z z i) →
    (∀ z, 0<∑ i ∈ E, ∑ j, A i j*M j*(1-Z z i)) →
    (∀ z, 0<p z) → (∑ z, p z=1) →
    (∀ z z' i, Y z i=Y z' i) → (0≤α ∧ α≤1) →
    let q := fun z => ∑ z', p z'*(if
      |nominationStatistic E A M (Z z') (Y z0)| ≥
      |nominationStatistic E A M (Z z) (Y z0)| then (1:ℝ) else 0)
    (∑ z, p z*(if q z≤α then (1:ℝ) else 0))≤α

def NominationDirectEffectStatement(I : Type*) [Fintype I] : Prop :=
  ∀ (E : Finset I) (A : I → I → ℝ) (M z baseline : I → ℝ) (δ : ℝ)
    (hA : ∀ i j, 0≤A i j) (hM : ∀ i, M i=0 ∨ M i=1)
    (hz : ∀ i, z i=0 ∨ z i=1) (hE : ∀ i, i∉E → z i=0)
    (hd1 : 0<∑ i ∈ E, ∑ j, A i j*M j*z i)
    (hd0 : 0<∑ i ∈ E, ∑ j, A i j*M j*(1-z i)),
    nominationStatistic E A M z (fun j => baseline j+δ*z j)=
      nominationStatistic E A M z baseline+δ*nominationStatistic E A M z z
/-- Sharp-null validity, direct-effect decomposition, and the reciprocal-pair counterexample. -/
def T36Statement (Ω I : Type*) [Fintype Ω] [Fintype I] : Prop :=
  NominationSharpNullStatement Ω I ∧ NominationDirectEffectStatement I ∧ PairedNominationWitness

end SAP.P037c
