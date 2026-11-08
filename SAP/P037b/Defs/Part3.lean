import Mathlib
import SAP.P037b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037b
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Mathematical content packaged for P037-T30. -/
def T30Statement : Prop :=
  (∀ {Ω : Type*} [Fintype Ω] (P : ProbabilityDesign Ω) (E : Ω → Prop) (J : ℕ) (hJ : 0 < J),
    let p := eventProbability P E
    let hits := fun z : Fin J → Ω => (Finset.univ.filter (fun j => E (z j))).card
    let mass := fun z : Fin J → Ω => ∏ j, P.mass (z j)
    let phat := fun z => (hits z:ℝ)/J
    (∀ r : ℕ, r ≤ J →
      (∑ z, mass z*(if hits z=r then 1 else 0))=
        (Nat.choose J r:ℝ)*p^r*(1-p)^(J-r)) ∧
    (∑ z, mass z*phat z)=p ∧
    (∑ z, mass z*(phat z-p)^2)=p*(1-p)/J ∧
    (∑ z, mass z*(if hits z=0 then 1 else 0))=(1-p)^J ∧
    (∀ ε : ℝ, 0 < ε →
      (∑ z, mass z*(if |phat z-p| ≥ ε then 1 else 0)) ≤ p*(1-p)/(J*ε^2) ∧
      p*(1-p)/(J*ε^2) ≤ 1/(4*J*ε^2)) ∧
    (∀ ε δ : ℝ, 0 < ε → 0 < δ → (J:ℝ) ≥ 1/(4*δ*ε^2) →
      (∑ z, mass z*(if |phat z-p| ≥ ε then 1 else 0)) ≤ δ) ∧
    (p=0 → ∀ z, hits z=0) ∧
    (0 < p ∧ p < 1 → 0 < (1-p)^J ∧ 0 < p*(1-p)/J)) ∧
  (∀ {Ω : Type*} [Fintype Ω] (P : ProbabilityDesign Ω) (m J : ℕ) (hJ : 0 < J) (E : Fin m → Ω → Prop) (ε : ℝ) (hε : 0 < ε),
    (∑ z : Fin J → Ω, (∏ j, P.mass (z j)) *
      (if ∃ k, |((Finset.univ.filter (fun j => E k (z j))).card:ℝ)/J-
        eventProbability P (E k)| ≥ ε then (1:ℝ) else 0)) ≤ (m:ℝ)/(4*J*ε^2)) ∧
  (∀ {b : ℕ} (n t : Fin b → ℕ) (peers : (h : Fin b) → Finset (Fin (n h))) (ht : ∀ h, t h ≤ n h),
    let Ω := (h : Fin b) → {s : Finset (Fin (n h)) // s.card=t h}
    (1/2)*(∑ z : Ω,
      (∏ h, (1:ℝ)/(Nat.choose (n h) (t h):ℝ)) *
        (if ∀ h, Disjoint (z h).val (peers h) then (1:ℝ) else 0))=
      blockedAvoidanceProbability n t (fun h => (peers h).card)) ∧
  (blockedAvoidanceProbability (fun _ : Fin 4 => 10) (fun _ => 5) ![2,2,2,2] = 8/6561 ∧
    blockedAvoidanceProbability (fun _ : Fin 4 => 10) (fun _ => 5) ![5,3,0,0] = 1/6048 ∧
    blockedAvoidanceProbability (fun _ : Fin 4 => 10) (fun _ => 5) ![6,2,0,0] = 0 ∧
    blockedAvoidanceProbability (fun _ : Fin 4 => 10) (fun _ => 5) ![5,5,0,0] = 1/127008) ∧
  ((∀ {Ω : Type*} [Fintype Ω] (P : ProbabilityDesign Ω) (E : Ω → Prop)
      (J : ℕ) (hJ : 0 < J) (draws : Fin J → Ω),
    let p := eventProbability P E
    let count := (Finset.univ.filter (fun j => E (draws j))).card
    let frequency := (count : ℝ) / J
    (∃ r : ℕ, r ≤ J ∧ frequency = (r : ℝ) / J) ∧
    (0 < p → p < 1/(2*(J:ℝ)) → p ≤ |frequency-p|) ∧
    (p = 0 → frequency = 0)) ∧
    (∀ {Ω I : Type*} [Fintype Ω] (P : ProbabilityDesign Ω)
      (D : Ω → I → Fin 5) (J : ℕ) (hJ : 0 < J) (draws : Fin J → Ω),
      exposureProbabilityCutoff (fun i k => ((Finset.univ.filter
        (fun j => D (draws j) i = k.castSucc)).card : ℝ)/J) 0 ⊆
      positiveExposurePopulation (fun i k => eventProbability P (fun w => D w i = k.castSucc))) ∧
    (∀ k, 0 < rareExposureProbability k ∧ rareExposureProbability k < 1) ∧
    (∃ draws : Fin 10000 → RareSeedAssignments,
      ¬∀ k : Fin 4, 0 < ((Finset.univ.filter (fun j => rareExposure (draws j) = k)).card : ℝ)/10000))

/-- Mathematical content packaged for P037-T31. -/
def T31Statement : Prop :=
  ((blockedSchoolAssignments 14).card=78364164096 ∧
    (unblockedSchoolAssignments 56 28).card=7648690600760440 ∧
    (unblockedSchoolAssignments 8 4).card=70 ∧ (blockedSchoolAssignments 2).card=36 ∧
    ({0,1,2,3} : Finset (Fin 8))∈unblockedSchoolAssignments 8 4 ∧
    ({(0,0),(0,1),(0,2),(0,3)} : Finset (Fin 2 × Fin 4))∉blockedSchoolAssignments 2 ∧
    uniformSchoolEventProbability 56 28 (fun s => (0 : Fin 56)∈s ∧ 1∈s)=27/110 ∧
    uniformSchoolEventProbability 4 2 (fun s => (0 : Fin 4)∈s ∧ 1∈s)=1/6 ∧
    (let varianceU := fun y : Fin 8 → ℝ =>
      (∑ s ∈ unblockedSchoolAssignments 8 4,
        ((∑ i, (if i∈s then (1:ℝ) else -1)*y i)/4)^2)/70
     let varianceB := fun y : (Fin 2 × Fin 4) → ℝ =>
      (∑ s ∈ blockedSchoolAssignments 2,
        ((∑ i, (if i∈s then (1:ℝ) else -1)*y i)/4)^2)/36
     varianceU ![1,1,1,1,0,0,0,0]=1/7 ∧
     varianceB (fun i => if i.1=0 then 1 else 0)=0 ∧
     varianceU ![2,0,1,1,1,1,1,1]=1/7 ∧
     varianceB (fun i => if i=(0,0) then 2 else if i=(0,1) then 0 else 1)=1/6)) ∧
  (∀ {Ω : Type*} [Fintype Ω] {n : ℕ} (p : Ω → ℝ) (hp : ∀ z, 0 ≤ p z) (htotal : ∑ z, p z=1) (S : Ω → Fin n → Bool) (half : ∀ i, (∑ z, p z*(if S z i then 1 else 0))=1/2) (y : Fin n → ℝ) (m : ℕ) (hm : 0 < m),
    let T := fun z => (∑ i, ((if S z i then (1:ℝ) else -1)*y i))/(m:ℝ)
    (∑ z, p z*T z)=0 ∧
    (∑ z, p z*(T z)^2)=
      (∑ i, ∑ j, y i*y j*(if i=j then 1 else
        4*(∑ z, p z*(if S z i=true ∧ S z j=true then 1 else 0))-1))/(m:ℝ)^2)

/-- Mathematical content packaged for P037-T32. -/
def T32Statement : Prop :=
  (∀ (B n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n),
    (blockedSchoolAssignments B).card=6^B ∧
    (∑ s ∈ blockedSchoolAssignments B, blockedAssignmentMass s)=1 ∧
    (unblockedSchoolAssignments n m).card=Nat.choose n m ∧
    (∀ h : Fin n, uniformSchoolEventProbability n m (fun s => h∈s)=(m:ℝ)/n) ∧
    (∀ h j : Fin n, h≠j →
      uniformSchoolEventProbability n m (fun s => h∈s ∧ j∈s)=
        ((m:ℝ)*(m-1))/(n*(n-1)))) ∧
  (∀ {Ω U K : Type*} [Fintype Ω] [Fintype U] [DecidableEq K] (p : Ω → ℝ) (q : U → ℝ) (S : Ω → Bool) (half : ∑ z, p z*(if S z then (1:ℝ) else 0)=1/2) (total : ∑ z, p z=1) (f : Bool → U → K) (k : K) (hp : ∀ z, 0  ≤  p z) (hq : ∀ u, 0  ≤  q u) (qtotal : ∑ u, q u = 1),
    (∑ z, ∑ u, p z*q u*(if f (S z) u=k then (1:ℝ) else 0))=
      (1/2)*(∑ u, q u*(if f false u=k then (1:ℝ) else 0))+
      (1/2)*(∑ u, q u*(if f true u=k then (1:ℝ) else 0)))

end SAP.P037b
