import SAP.P003a.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The studentized statistic fixes one real extension before testing. Uniform probability
on a finite product assignment space represents the observed randomization and independent
Monte Carlo draws. The plus-one rank includes absolute-value ties. Unit-level completion
and coupling definitions are used only with positive balanced arm sizes in T2. -/

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

abbrev Assignment (n m : ℕ) := {z : Finset (Fin n) // z.card = m}

noncomputable def varianceEstimate (o : Counts) : ℝ :=
  (o.a : ℝ)*o.b / ((o.a : ℝ)+o.b)^3 +
    (o.c : ℝ)*o.d / ((o.c : ℝ)+o.d)^3

noncomputable def standardError (o : Counts) : ℝ := Real.sqrt (varianceEstimate o)

/-- A fixed real C replaces every zero-standard-error quotient. -/
noncomputable def studentized (C : ℝ) (o v : Counts) : ℝ :=
  if standardError o = 0 then C else (estimate o-tau v)/standardError o

def canonicalPair (v : Counts) (i : ℕ) : Bool × Bool :=
  if i < v.a then (true,true)
  else if i < v.a+v.b then (true,false)
  else if i < v.a+v.b+v.c then (false,true) else (false,false)

def canonicalObserved {n : ℕ} (v : Counts) (z : Finset (Fin n)) : Counts :=
  ⟨(Finset.univ.filter fun i => i ∈ z ∧ (canonicalPair v i.val).1 = true).card,
   (Finset.univ.filter fun i => i ∈ z ∧ (canonicalPair v i.val).1 = false).card,
   (Finset.univ.filter fun i => i ∉ z ∧ (canonicalPair v i.val).2 = true).card,
   (Finset.univ.filter fun i => i ∉ z ∧ (canonicalPair v i.val).2 = false).card⟩

noncomputable def uniformProb {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ)/Fintype.card Ω

def treatedCounts {n : ℕ} (v : Counts) (z : Finset (Fin n)) : Counts :=
  ⟨(z.filter fun i => canonicalPair v i.val = (true,true)).card,
   (z.filter fun i => canonicalPair v i.val = (true,false)).card,
   (z.filter fun i => canonicalPair v i.val = (false,true)).card,
   (z.filter fun i => canonicalPair v i.val = (false,false)).card⟩

/-- The plus-one Monte Carlo rank p-value, using the same statistic throughout. -/
noncomputable def rankValue {K : ℕ} (R : Counts → Counts → ℝ) (o v : Counts)
    (samples : Fin K → Counts) : ℝ :=
  (1+∑ i, if |R (observed v (samples i)) v| ≥ |R o v| then (1 : ℝ) else 0)/(K+1)

def unitOutcomes {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ z then (w i).1 else (w i).2

def PossibleTable {n : ℕ} (y : Fin n → Bool) (z : Finset (Fin n))
    (w : PotentialTable n) : Prop := unitOutcomes w z = y

noncomputable def outcomeEstimator {n : ℕ} (y : Fin n → Bool)
    (z : Finset (Fin n)) : ℝ :=
  (∑ i, if i ∈ z then bit (y i) else 0)/z.card -
    (∑ i, if i ∈ z then 0 else bit (y i))/(n-z.card)

def unitPlus {n : ℕ} (y : Fin n → Bool) (z r : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ r then decide (i ∈ z) else y i

def coupledPlus {n : ℕ} (w : PotentialTable n) (yPlus : Fin n → Bool)
    (z : Finset (Fin n)) : PotentialTable n :=
  fun i => if i ∈ z then (yPlus i,(w i).2) else ((w i).1,yPlus i)

noncomputable def unitPValue {n : ℕ} (w : PotentialTable n) (y : Fin n → Bool)
    (z : Finset (Fin n)) : ℝ :=
  uniformProb (fun q : Assignment n z.card =>
    |tableEstimator w q.val-tableTau w| ≥ |outcomeEstimator y z-tableTau w|)

def unitObserved {n : ℕ} (y : Fin n → Bool) (z : Finset (Fin n)) : Counts :=
  ⟨(Finset.univ.filter fun i => i ∈ z ∧ y i = true).card,
   (Finset.univ.filter fun i => i ∈ z ∧ y i = false).card,
   (Finset.univ.filter fun i => i ∉ z ∧ y i = true).card,
   (Finset.univ.filter fun i => i ∉ z ∧ y i = false).card⟩

end SAP.P003a
