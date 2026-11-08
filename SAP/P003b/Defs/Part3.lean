import SAP.P003b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section

def missingMasks (o : Counts) : List Counts :=
  (List.range (o.a+1)).flatMap fun a =>
  (List.range (o.b+1)).flatMap fun b =>
  (List.range (o.c+1)).flatMap fun c =>
  (List.range (o.d+1)).map fun d => ⟨a,b,c,d⟩

def plusCompletion (o r : Counts) : Counts :=
  ⟨o.a+r.b, o.b-r.b, o.c-r.c, o.d+r.c⟩

def minusCompletion (o r : Counts) : Counts :=
  ⟨o.a-r.a, o.b+r.a, o.c+r.d, o.d-r.d⟩

noncomputable def missingInterval (α : ℝ) (o r : Counts) : Set ℝ :=
  let lo := minusCompletion o r
  let hi := plusCompletion o r
  Set.Icc (if (accepted α lo).Nonempty then min (lower α lo) (estimate lo)
           else estimate lo)
          (if (accepted α hi).Nonempty then max (upper α hi) (estimate hi)
           else estimate hi)

def IsMissingLaw (v : Counts) (m : ℕ) (μ : Counts → Counts → ℝ) : Prop :=
  (∀ q ∈ randomStates v m, ∀ r ∈ missingMasks (observed v q), 0 ≤ μ q r) ∧
  (∀ q ∈ randomStates v m,
    ((missingMasks (observed v q)).map (μ q)).sum =
      (multiplicity v q : ℝ) / v.total.choose m)

noncomputable def missingProb (v : Counts) (m : ℕ) (μ : Counts → Counts → ℝ)
    (E : Counts → Counts → Prop) : ℝ :=
  ((randomStates v m).map fun q =>
    ((missingMasks (observed v q)).map fun r => if E q r then μ q r else 0).sum).sum

def waldVarianceQ (m k : ℕ) : ℚ :=
  ((2*m : ℕ) : ℚ) / ((2*m : ℕ) - 2) *
    (2*(k : ℚ)*((m : ℚ)-k)/(m : ℚ)^3)

def waldEstimateQ (m k : ℕ) : ℚ := (2*(k : ℚ)-m)/(m : ℚ)

noncomputable def waldInterval (z : ℝ) (m k : ℕ) : Set ℝ :=
  Set.Icc ((waldEstimateQ m k : ℝ)-z*Real.sqrt (waldVarianceQ m k))
    ((waldEstimateQ m k : ℝ)+z*Real.sqrt (waldVarianceQ m k))

noncomputable def waldWidth (z : ℝ) (m k : ℕ) : ℝ := 2*z*Real.sqrt (waldVarianceQ m k)

def waldCoverageQ (m : ℕ) (lo hi : ℕ) : ℚ :=
  ((List.range (m+1)).map fun k => if lo ≤ k ∧ k ≤ hi
    then (binomial m k : ℚ)^2 else 0).sum / binomial (2*m) m

noncomputable def median (xs : List ℝ) : ℝ :=
  let ys := xs.mergeSort (fun x y => x ≤ y)
  if ys = [] then 0 else (ys[(ys.length-1)/2]! + ys[ys.length/2]!)/2

noncomputable def IsWaldMedian (L : ℕ → ℝ) (m : ℕ) (d : ℝ) : Prop :=
  ((∑ k ∈ Finset.range (m+1), if L k ≤ d then ((m.choose k : ℝ)^2) else 0) /
    ((2*m).choose m : ℝ) ≥ 1/2) ∧
  ((∑ k ∈ Finset.range (m+1), if d ≤ L k then ((m.choose k : ℝ)^2) else 0) /
    ((2*m).choose m : ℝ) ≥ 1/2)

def allCounts (n : ℕ) : Finset Counts := (randomStates ⟨n,n,n,n⟩ n).toFinset

def stratifiedCounts (N₀ N₁ : ℕ) : Finset (Counts × Counts) :=
  (allCounts N₀).product (allCounts N₁)

def treatedCounts {n : ℕ} (v : Counts) (z : Finset (Fin n)) : Counts :=
  ⟨(z.filter fun i => canonicalPair v i.val = (true,true)).card,
   (z.filter fun i => canonicalPair v i.val = (true,false)).card,
   (z.filter fun i => canonicalPair v i.val = (false,true)).card,
   (z.filter fun i => canonicalPair v i.val = (false,false)).card⟩

def updateTreated (v q : Counts) (s₀ s₁ : ℕ) : Counts :=
  let control₀ := s₀ % v.d < v.d-q.d
  let control₁ := s₁ % v.a < v.a-q.a
  ⟨if control₁ then q.a else q.a-1,
   if control₁ then q.b else q.b+1,
   if control₀ then q.c else q.c+1,
   if control₀ then q.d else q.d-1⟩

abbrev GeneralSpace (n m K : ℕ) := Assignment n m ×
  (((Fin (n+1) × Fin (n+1)) → Fin K → Assignment n m) ×
   ((Fin (n+1) × Fin (n+1)) → Fin n → Fin K →
      (Fin n.factorial × Fin n.factorial)))

def reusedSamples {n m K : ℕ} (v : Counts) (initial : Fin K → Assignment n m)
    (seeds : Fin n → Fin K → (Fin n.factorial × Fin n.factorial)) :
    ℕ → Fin K → Counts
  | 0, i => treatedCounts v (initial i).val
  | t+1, i =>
    let s := if h : t < n then seeds ⟨t,h⟩ i else
      (⟨0,Nat.factorial_pos n⟩,⟨0,Nat.factorial_pos n⟩)
    updateTreated (reuseVector v t) (reusedSamples v initial seeds t i) s.1.val s.2.val

noncomputable def rankValue {K : ℕ} (R : Counts → Counts → ℝ) (o v : Counts)
    (samples : Fin K → Counts) : ℝ :=
  (1+∑ i, if |R (observed v (samples i)) v| ≥ |R o v| then (1 : ℝ) else 0)/(K+1)

noncomputable def generalSet {n m K : ℕ} (α : ℝ)
    (θ : Counts → ℝ) (R : Counts → Counts → ℝ) (o : Counts)
    (initial : (Fin (n+1) × Fin (n+1)) → Fin K → Assignment n m)
    (seeds : (Fin (n+1) × Fin (n+1)) → Fin n → Fin K →
      (Fin n.factorial × Fin n.factorial)) : Set ℝ :=
  {t | ∃ ij : Fin (n+1) × Fin (n+1), ∃ v : Counts,
    firstOnLine o ((candidateNumerators o).reverse[ij.1.val]!) ij.2.val = some v ∧
    ∃ k ≤ n, k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k) ∧
      t = θ (reuseVector v k) ∧
      α < rankValue R o (reuseVector v k)
        (reusedSamples v (initial ij) (seeds ij) k)}

def reuseLine (o v : Counts) : List ℕ :=
  ((List.range o.total).map (fun k => k+1)).filter fun k =>
    k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k)

def generalDrawCount (o : Counts) (K : ℕ) : ℕ :=
  ((candidateNumerators o).map fun x =>
    ((List.range (o.total+1)).map fun j =>
      if (firstOnLine o x j).isSome then K else 0).sum).sum

def generalUpdateCount (o : Counts) (K : ℕ) : ℕ :=
  ((candidateNumerators o).map fun x =>
    ((List.range (o.total+1)).map fun j =>
      match firstOnLine o x j with
      | none => 0
      | some v => K*(reuseLine o v).length).sum).sum

def generalOperations (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ) : ℝ :=
  c₀*(o.total+1)^2 + 2*c₁*o.total*generalDrawCount o K +
    2*c₂*generalUpdateCount o K

def generalEnvelope (n K : ℕ) (c₀ c₁ c₂ : ℝ) : ℝ :=
  ((n : ℝ)+1)^2*(c₀+2*(c₁+c₂)*K*n)

noncomputable def recommendedK (ε : ℝ) (n : ℕ) : ℕ :=
  ⌈Real.log (4*(n : ℝ)*logTwo n/ε)/(2*ε^2)⌉₊

noncomputable def balancedEnvelope (ε c : ℝ) (n : ℕ) : ℝ :=
  4*c*recommendedK ε n*(n : ℝ)^2*logTwo n

end
end SAP.P003b
