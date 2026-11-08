import SAP.P003b.Defs.Part4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section

/-- Mathematical content packaged for P003-T35. -/
def T35Statement : Prop :=
  (∀ (v : Counts) (m K : ℕ) (α : ℝ)
    (θ : Counts → ℝ) (R : Counts → Counts → ℝ)
    (hm : 0 < m ∧ m < v.total) (hK : 0 < K) (hα : 0 < α ∧ α < 1),
    uniformProb (fun ω : GeneralSpace v.total m K => θ v ∈
      generalSet α θ R (canonicalObserved v ω.1.val) ω.2.1 ω.2.2) ≥ 1-α) ∧
  (∀ (v : Counts) (m : ℕ)
    (hm : 0 < m ∧ m < v.total) (ha : 0 < v.a) (hd : 0 < v.d) (q' : Counts),
    uniformProb (fun ω : Assignment v.total m ×
        (Fin v.total.factorial × Fin v.total.factorial) =>
      updateTreated v (treatedCounts v ω.1.val) ω.2.1.val ω.2.2.val = q') =
    designProb (reuseVector v 1) m (fun q => q = q'))

/-- Mathematical content packaged for P003-T36. -/
def T36Statement : Prop :=
  (∀ (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ),
      0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂ →
      generalDrawCount o K ≤ (o.total+1)^2*K ∧
      generalUpdateCount o K ≤ (o.total+1)^2*o.total*K ∧
      (1 ≤ o.total → 1 ≤ K →
        generalOperations o K c₀ c₁ c₂ ≤ 4*(c₀+2*(c₁+c₂))*K*(o.total : ℝ)^3)) ∧
  (∀ (c₀ c₁ c₂ : ℝ) (hc : 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 ≤ c₂)
    (o : ℕ × ℕ → Counts) (ho : ∀ p, (o p).total = p.1)
    (hdesign : ∀ᶠ p in Filter.atTop,
      0 < (o p).a+(o p).b ∧ 0 < (o p).c+(o p).d),
    (fun p : ℕ × ℕ => generalOperations (o p) p.2 c₀ c₁ c₂) =O[Filter.atTop]
      (fun p : ℕ × ℕ => (p.2 : ℝ)*(p.1 : ℝ)^3))

/-- Mathematical content packaged for P003-T18. -/
def T18Statement : Prop :=
  (∀ (α ε c : ℝ)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε < α) (hc : 0 ≤ c)
    (tests : ℕ → ℕ) (operations : ℕ → ℝ) (hops : ∀ n, 0 ≤ operations n)
    (htests : ∀ᶠ n in Filter.atTop, (tests n : ℝ) ≤ 4*(n : ℝ)*logTwo n)
    (hcost : ∀ᶠ n in Filter.atTop, operations n ≤ (tests n : ℝ)*recommendedK ε n*(c*n)),
    operations =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^2*(Real.log n)^2)) ∧
  (∀ (r K : ℕ) (hr : 4 ≤ r) (hK : 0 < K),
    let n : ℕ := 2^r
    let o : Counts := ⟨0,n/2,0,n/2⟩
    0 < uniformProb (fun pool : Fin (2*testBudget n+1) → Fin K → Assignment n (n/2) =>
      (n/4+1)*K*(n-1) ≤ upperShuffleCost (1/2) (1/8) o pool) ∧
    (6 ≤ r → (K : ℝ) ≥ 32*Real.log (32*(n : ℝ)*logTwo n) →
      ((n/4+1 : ℕ) : ℝ)*K*((n-1 : ℕ) : ℝ)/2 ≤
        expectedUpperShuffleCost (1/2) (1/8) n K o)) ∧
  (∀ (c : ℝ) (hc : 0 ≤ c),
    ¬ (fun r : ℕ =>
      let n : ℕ := 2^r
      expectedUpperShuffleCost (1/2) (1/8) n (recommendedK (1/8) n) ⟨0,n/2,0,n/2⟩)
      =O[Filter.atTop] (fun r : ℕ =>
        let n : ℕ := 2^r
        (n : ℝ)*Real.rpow (Real.log n) c)) ∧
  (∀ (n : ℕ) (hn : 15 ≤ n),
    logTwo n ≤ (Real.log n)^2)

end
end SAP.P003b
