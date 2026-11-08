import SAP.P003a.Defs.Part9

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-- Packaged content for P003-T17; see the Challenge docstring for scope. -/
def T17Statement : Prop :=
  (∀ (C : ℝ) (o v : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hv : v.total = o.total),
    0 ≤ varianceEstimate o ∧
    (standardError o = 0 ↔ o.a*o.b = 0 ∧ o.c*o.d = 0) ∧
    (standardError o = 0 → studentized C o v = C) ∧
    (0 < standardError o → studentized C o v = (estimate o-tau v)/standardError o)) ∧
  (∀ (C : ℝ),
    varianceEstimate ⟨0,2,0,3⟩ = 0 ∧ standardError ⟨0,2,0,3⟩ = 0 ∧
    estimate ⟨0,2,0,3⟩ - tau ⟨0,0,1,4⟩ = 1/5 ∧
    studentized C ⟨0,2,0,3⟩ ⟨0,0,1,4⟩ = C) ∧
  (designProb ⟨0,0,1,4⟩ 2 (fun q =>
      |studentized 0 (observed ⟨0,0,1,4⟩ q) ⟨0,0,1,4⟩| ≥
        |studentized 0 ⟨0,2,0,3⟩ ⟨0,0,1,4⟩|) = 1 ∧
    designProb ⟨0,0,1,4⟩ 2 (fun q =>
      |studentized (10^6) (observed ⟨0,0,1,4⟩ q) ⟨0,0,1,4⟩| ≥
      |studentized (10^6) ⟨0,2,0,3⟩ ⟨0,0,1,4⟩|) = 2/5) ∧
  (∀ (v : Counts) (m K : ℕ) (α : ℝ)
    (C : ℝ) (hm : 0 < m ∧ m < v.total) (hK : 0 < K)
    (hα : 0 ≤ α ∧ α ≤ 1),
    uniformProb (fun ω : Assignment v.total m × (Fin K → Assignment v.total m) =>
      rankValue (studentized C) (canonicalObserved v ω.1.val) v
        (fun i => treatedCounts v (ω.2 i).val) ≤ α) ≤ α)

/-- Packaged content for P003-T21; see the Challenge docstring for scope. -/
def T21Statement : Prop :=
  ((acceptedEffectsQ (17/18) ⟨1,6,0,2⟩).toFinset = {0,1} ∧
    intervalQ (17/18) ⟨1,6,0,2⟩ = some (0,1/9) ∧
    estimateQ ⟨1,6,0,2⟩ = 1/7 ∧
    ¬ ((0 : ℚ) ≤ 1/7 ∧ (1/7 : ℚ) ≤ 1/9) ∧
    pValue ⟨1,0,1,7⟩ ⟨1,6,0,2⟩ = 29/36 ∧ (29/36 : ℚ) < 17/18)

/-- Packaged content for P003-T22; see the Challenge docstring for scope. -/
def T22Statement : Prop :=
  (∀ (o u : Counts) (hu : Possible o u),
    u.effect ∈ candidateNumerators o ∧ u.a+u.b ≤ o.total ∧
    ∃ v, firstOnLine o u.effect (u.a+u.b) = some v ∧
      ∃ k ≤ o.total, k ≤ v.a ∧ k ≤ v.d ∧ u = reuseVector v k) ∧
  ((possibleTables ⟨0,1,0,1⟩).toFinset =
      {⟨0,0,0,2⟩,⟨0,0,1,1⟩,⟨0,1,0,1⟩,⟨0,1,1,0⟩} ∧
    firstOnLine ⟨0,1,0,1⟩ 0 0 = some ⟨0,0,0,2⟩ ∧
    firstOnLine ⟨0,1,0,1⟩ 0 1 = some ⟨0,1,1,0⟩)

/-- Packaged content for P003-T23; see the Challenge docstring for scope. -/
def T23Statement : Prop :=
  (∀ (k₁ k₂ u : ℤ) (f : ℤ → Bool) (hk : k₁ ≤ k₂),
    let s := sentinelSearch ((k₂-k₁+1).toNat+1) f (k₁-1) (k₂+1);
    (∀ c ∈ s.2, f c = true → s.1 < c) ∧
    (u ≤ s.1 → ∀ c ∈ s.2, c ≤ u → f c = false) ∧
    (∀ i j, i < j → j < s.2.length → f (s.2[i]!) = true → s.2[j]! < s.2[i]!))

end SAP.P003a
