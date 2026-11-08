import SAP.P003a.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-- Packaged content for P003-T4; see the Challenge docstring for scope. -/
def T4Statement : Prop :=
  ((0 : ℤ) < 1 ∧ (1 : ℤ) < 2 ∧
    (∀ x : ℤ, 1 ≤ x → x ≤ 2 → ((fun _ => false) x = false ↔ x ≤ 2)) ∧
    (∀ x : ℤ, 1 ≤ x → x ≤ 2 → ((fun _ => true) x = false ↔ x ≤ 0)) ∧
    printedSearch 1 1 2 (fun _ => false) 1 2 = some 1 ∧
    printedSearch 1 1 2 (fun _ => false) 1 2 ≠ some 2 ∧
    searchStep (fun _ => true) 1 2 = (1,1) ∧
    (∀ fuel, printedSearch fuel 1 2 (fun _ => true) 1 1 = none) ∧
    (∀ fuel, printedSearch fuel 1 2 (fun _ => true) 1 2 = none)) ∧
  (let o : Counts := ⟨7,1,0,8⟩;
    estimateQ o = 7/8 ∧ Possible o ⟨0,14,0,2⟩ ∧ Possible o ⟨0,15,0,1⟩ ∧
    pValue ⟨0,14,0,2⟩ o = 1 ∧ pValue ⟨0,15,0,1⟩ o = 1 ∧
    intervalQ (1/20) o = some (1/2,15/16) ∧
    (upperRun false o (exactRejectQ (1/20) o)).value = some 14)

/-- Packaged content for P003-T5; see the Challenge docstring for scope. -/
def T5Statement : Prop :=
  (∀ (k₁ k₂ r : ℤ) (f : ℤ → Bool)
    (hk : k₁ ≤ k₂) (hr : k₁-1 ≤ r ∧ r ≤ k₂)
    (hf : ∀ x, k₁ ≤ x → x ≤ k₂ → (f x = false ↔ x ≤ r)),
    let d := (k₂-k₁+1).toNat;
    let s := sentinelSearch (d+1) f (k₁-1) (k₂+1);
    s.1 = r ∧ s.2.Nodup ∧ (∀ x ∈ s.2, k₁ ≤ x ∧ x ≤ k₂) ∧
      (s.2.length : ℝ) ≤ (⌊logTwo d⌋ : ℤ) + 1) ∧
  (∀ (k₁ k₂ : ℤ) (f : ℤ → Bool) (hk : k₁ ≤ k₂),
    let d := (k₂-k₁+1).toNat;
    let s := sentinelSearch (d+1) f (k₁-1) (k₂+1);
    s.2.Nodup ∧ (∀ x ∈ s.2, k₁ ≤ x ∧ x ≤ k₂) ∧
      (s.2.length : ℝ) ≤ (⌊logTwo d⌋ : ℤ) + 1 ∧ k₁-1 ≤ s.1 ∧ s.1 ≤ k₂)

/-- Packaged content for P003-T11; see the Challenge docstring for scope. -/
def T11Statement : Prop :=
  (let q : ℝ → ℝ := fun x => if x ≤ 0 then 1 else 0;
    (∀ x, q x < 1/2 ↔ 0 < x) ∧
    (∃ x, q x < 1/2) ∧ ¬ ∃ x, q x < 1/2 ∧ ∀ u, q u < 1/2 → x ≤ u) ∧
  (∀ (x : ℝ),
    designProb ⟨0,0,0,2⟩ 1 (fun q => x ≤
      |estimate (observed ⟨0,0,0,2⟩ q)-tau ⟨0,0,0,2⟩|) =
      if x ≤ 0 then 1 else 0)

/-- Packaged content for P003-T12; see the Challenge docstring for scope. -/
def T12Statement : Prop :=
  (∀ {Ω : Type*} [Fintype Ω] (w D : Ω → ℝ)
    (hw : ∀ i, 0 < w i) (hn : ∑ i, w i = 1) (α : ℝ) (hα : 0 < α ∧ α < 1),
    ((∀ i, α ≤ finiteTail w D (D i)) ∨
      ∃ i, 0 < w i ∧ finiteTail w D (D i) < α ∧
        (∀ j, finiteTail w D (D j) < α ↔ D i ≤ D j) ∧
        (∑ j, if finiteTail w D (D j) < α then w j else 0) = finiteTail w D (D i)) ∧
    (∑ j, if finiteTail w D (D j) < α then w j else 0) < α)

/-- Packaged content for P003-T13; see the Challenge docstring for scope. -/
def T13Statement : Prop :=
  (∀ {n : ℕ} (w : PotentialTable n) (hn : 0 < n),
    (tableCounts w).total = n ∧
    (∑ i, bit (w i).1) = (tableCounts w).a + (tableCounts w).b ∧
    (∑ i, bit (w i).2) = (tableCounts w).a + (tableCounts w).c ∧
    tableTau w = tau (tableCounts w)) ∧
  (tauQ ⟨10,0,0,10⟩ = 0 ∧ ((10 : ℚ)-0)/20 = 1/2 ∧
    tauQ ⟨0,20,0,0⟩ = 1 ∧ ((0 : ℚ)-0)/20 = 0)

end SAP.P003a
