import Mathlib
import SAP.P037c.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def regression12X (i : Fin 4 × Fin 3) : ℝ := (i.1.val:ℝ)+(i.2.val:ℝ)

noncomputable def regression12Potential (i : Fin 4 × Fin 3) (k : Fin 4) : ℝ :=
  (if k=3 then 2 else 1)*regression12X i

noncomputable def regression12Y (i : Fin 4 × Fin 3) : ℝ := regression12Potential i i.1

noncomputable def regression12Pooled (weights : Fin 4 → ℝ) : Fin 5 → ℝ :=
  let beta := (weights 0+weights 1+weights 2+2*weights 3)/(∑ k, weights k)
  ![1-beta,2-2*beta,3-3*beta,8-4*beta,beta]

noncomputable def regression12Mean (b : Fin 5 → ℝ) (k : Fin 4) : ℝ :=
  b k.castSucc+(5/2)*b 4

def regression12School (i : Fin 4 × Fin 3) : Fin 6 :=
  if h : i.1=0 then ⟨i.2.val, by omega⟩ else ⟨i.1.val+2, by omega⟩

def regression12HierarchicalExposure (schools : Finset (Fin 6))
    (seeds : Fin 6 → Bool × Bool) (i : Fin 4 × Fin 3) : Fin 4 :=
  if regression12School i∉schools then 0 else
    if (seeds (regression12School i)).1 then 3 else
    if (seeds (regression12School i)).2 then 2 else 1

def regression12SchoolSize (s : Fin 6) : ℕ := if s.val<3 then 7 else 9

abbrev Regression12Student := Σ s : Fin 6, Fin (regression12SchoolSize s)

noncomputable def regression12Nomination (s : Fin 6)
    (i j : Fin (regression12SchoolSize s)) : Bool :=
  decide (((6 : ℕ) ≤ i.val ∧ (j.val=0 ∨ j.val=2)) ∨
    ((i.val=4 ∨ i.val=5) ∧ j.val=0))

noncomputable def regression12Indegree (s : Fin 6) (j : Fin (regression12SchoolSize s)) : ℕ :=
  (Finset.univ.filter (fun i => regression12Nomination s i j=true)).card

noncomputable def regression12Ninety (s : Fin 6) : ℝ :=
  let sorted := (List.ofFn (regression12Indegree s)).mergeSort (·≤·)
  let h := 9*(regression12SchoolSize s-1)
  ((10-h%10:ℕ):ℝ)/10*(sorted.getD (h/10) 0:ℝ)+
    ((h%10:ℕ):ℝ)/10*(sorted.getD (h/10+1) 0:ℝ)

def regression12SeedSet (s : Fin 6) (b : Bool × Bool)
    : Finset (Fin (regression12SchoolSize s)) :=
  {⟨if b.1 then 0 else 1, by unfold regression12SchoolSize; split_ifs <;> omega⟩,
   ⟨if b.2 then 2 else 3, by unfold regression12SchoolSize; split_ifs <;> omega⟩}

def regression12FocalStudent (i : Fin 4 × Fin 3) : Regression12Student :=
  ⟨regression12School i, ⟨6+(if i.1=0 then 0 else i.2.val), by
    unfold regression12SchoolSize regression12School
    split_ifs <;> simp_all <;> omega⟩⟩

noncomputable def regression12StudentExposure (schools : Finset (Fin 6))
    (seeds : Fin 6 → Bool × Bool) (u : Regression12Student) : Fin 5 :=
  if u.1∉schools then 0 else
  if u.2∈regression12SeedSet u.1 (seeds u.1) then 4 else
  if ∃ v ∈ regression12SeedSet u.1 (seeds u.1),
      (regression12Nomination u.1 u.2 v=true ∨ regression12Nomination u.1 v u.2=true) ∧
      regression12Ninety u.1<(regression12Indegree u.1 v:ℝ) then 3 else
  if ∃ v ∈ regression12SeedSet u.1 (seeds u.1),
      regression12Nomination u.1 u.2 v=true ∨ regression12Nomination u.1 v u.2=true
    then 2 else 1

noncomputable def regression12StudentProb (u : Regression12Student) (k : Fin 5) : ℝ :=
  ∑ schools ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
    ∑ seeds : Fin 6 → Bool × Bool,
      (1/(20*4^6):ℝ)*(if regression12StudentExposure schools seeds u=k then 1 else 0)

def Regression12DesignCertificate : Prop :=
  (∀ s j, regression12Indegree s j=
      if j.val=0 then regression12SchoolSize s-4 else
      if j.val=2 then regression12SchoolSize s-6 else 0) ∧
    (∀ s, regression12Ninety s=if s.val<3 then 9/5 else 17/5) ∧
    (∀ s j, regression12Ninety s<(regression12Indegree s j:ℝ) ↔ j.val=0) ∧
    (∀ s b, (regression12SeedSet s b).card=2 ∧
      ((regression12SeedSet s b).filter (fun j => j.val<2)).card=1 ∧
      ((regression12SeedSet s b).filter (fun j => 2≤j.val ∧ j.val<4)).card=1) ∧
    Function.Injective regression12FocalStudent ∧
    (∀ schools seeds i,
      regression12StudentExposure schools seeds (regression12FocalStudent i)=
        (regression12HierarchicalExposure schools seeds i).castSucc) ∧
    (∀ i : Fin 4 × Fin 3, ∀ k : Fin 4,
      regression12StudentProb (regression12FocalStudent i) k.castSucc=
        (![1/2,1/8,1/8,1/4] : Fin 4 → ℝ) k) ∧
    (∀ u : Regression12Student,
      (∀ k : Fin 4, 0<regression12StudentProb u k.castSucc ∧
        regression12StudentProb u k.castSucc<1) ↔
      ∃ i : Fin 4 × Fin 3, u=regression12FocalStudent i) ∧
    (∑ seeds : Fin 6 → Bool × Bool,
      (1/(20*4^6):ℝ)*(if (∀ i : Fin 4 × Fin 3,
        regression12StudentExposure {3,4,5} seeds (regression12FocalStudent i)=i.1.castSucc)
        then 1 else 0))=1/640

def Regression12NormalCertificate : Prop :=
  (∀ weights ∈ ({(![4,4,4,4] : Fin 4 → ℝ),![2,8,8,4]} : Set (Fin 4 → ℝ)),
      (∀ k : Fin 4, (∑ j : Fin 3, weights k*(regression12Y (k,j)-
        (regression12Pooled weights k.castSucc+
          regression12X (k,j)*regression12Pooled weights 4)))=0) ∧
      (∑ i : Fin 4 × Fin 3, weights i.1*regression12X i*(regression12Y i-
        (regression12Pooled weights i.1.castSucc+
          regression12X i*regression12Pooled weights 4)))=0)

def Regression12FitCertificate : Prop :=
  (∑ i : Fin 4 × Fin 3, regression12X i)/12=5/2 ∧
    (∀ weights ∈ ({(![4,4,4,4] : Fin 4 → ℝ),![2,8,8,4]} : Set (Fin 4 → ℝ)),
      (∀ k, regressionMinimum (fun i : Fin 4 × Fin 3 => if i.1=k then weights k else 0)
        (fun i => ![1,regression12X i]) regression12Y ![0,if k=3 then 2 else 1]) ∧
      (∀ b, regressionMinimum (fun i => weights i.1)
        (pooledExposureRow (fun i : Fin 4 × Fin 3 => i.1) (fun i => ![regression12X i]))
        regression12Y b ↔ b=regression12Pooled weights)) ∧
    regression12Pooled ![4,4,4,4]=![-1/4,-1/2,-3/4,3,5/4] ∧
    regression12Pooled ![2,8,8,4]=![-2/11,-4/11,-6/11,36/11,13/11] ∧
    (∀ k, regression12Mean (regression12Pooled ![4,4,4,4]) k=
      (![23/8,21/8,19/8,49/8] : Fin 4 → ℝ) k) ∧
    (∀ k, regression12Mean (regression12Pooled ![2,8,8,4]) k=
      (![61/22,57/22,53/22,137/22] : Fin 4 → ℝ) k) ∧
    (15/4:ℝ)≠5/2 ∧ (42/11:ℝ)≠5/2

/-- The separate augmented estimator on the common twelve-unit averaging set. -/
noncomputable def regression12SeparateMean (weights : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  augmentedExposureMean (fun i : Fin 4 × Fin 3 => i.1)
    (fun i => weights i.1) regression12Y
    (fun i => (if k=3 then 2 else 1)*regression12X i) k

/-- A hierarchical design and two WLS fits of the same data give distinct contrasts. -/
def T27Statement : Prop :=
  Regression12DesignCertificate ∧ Regression12FitCertificate ∧ Regression12NormalCertificate ∧
  (∀ weights ∈ ({(![4,4,4,4] : Fin 4 → ℝ),![2,8,8,4]} : Set (Fin 4 → ℝ)),
    ∀ k, regression12SeparateMean weights k=if k=3 then 5 else 5/2) ∧
  regression12Mean (regression12Pooled ![4,4,4,4]) 3-
    regression12Mean (regression12Pooled ![4,4,4,4]) 2=15/4 ∧
  regression12Mean (regression12Pooled ![2,8,8,4]) 3-
    regression12Mean (regression12Pooled ![2,8,8,4]) 2=42/11 ∧
  (15/4:ℝ)-5/2=5/4 ∧ (42/11:ℝ)-5/2=29/22 ∧
  (∀ k, (∑ i : Fin 4 × Fin 3, regression12Potential i k)/12=
    if k=3 then 5 else 5/2) ∧
  (∀ i, regression12Y i-(if i.1=3 then 2 else 1)*regression12X i=0) ∧
  (∀ weights ∈ ({(![4,4,4,4] : Fin 4 → ℝ),![2,8,8,4]} : Set (Fin 4 → ℝ)),
    regression12SeparateMean weights 3-regression12SeparateMean weights 2=5/2) ∧
  (∀ i, 1/regression12StudentProb (regression12FocalStudent i) i.1.castSucc=
    (![2,8,8,4] : Fin 4 → ℝ) i.1)

end SAP.P037c
