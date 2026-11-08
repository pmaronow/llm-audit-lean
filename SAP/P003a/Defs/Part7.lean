import SAP.P003a.Defs.Part6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P003a

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

/-- Packaged content for P003-T29; see the Challenge docstring for scope. -/
def T29Statement : Prop :=
  (∀ (v : Counts) (m : ℕ) (α : ℝ)
    (hm : 0 < m ∧ m < v.total) (hα : 0 < α ∧ α < 1),
    designProb v m (fun q => tau v ∈ exactInterval α (observed v q)) ≥ 1-α)

/-- Packaged content for P003-T1; see the Challenge docstring for scope. -/
def T1Statement : Prop :=
  (badPopulation.total = 20 ∧ (20 : ℕ).choose 3 = 1140 ∧ 0 < (3 : ℕ) ∧ (3 : ℕ) < 20 ∧
    (0 : ℚ) < 109/500 ∧ (109/500 : ℚ) < 1 ∧
    tauQ badPopulation = -3/20 ∧
    intervalQ (109/500) ⟨0,3,11,6⟩ = some (-7/10, -3/20) ∧
    intervalQ (109/500) ⟨0,3,10,7⟩ = some (-13/20, -1/5) ∧
    missingIntervalQ (109/500) ⟨0,3,11,6⟩ ⟨0,0,1,0⟩ = (-7/10,-1/5) ∧
    badCoverage = 297/380 ∧ badCoverage < 1 - (109/500 : ℚ) ∧
    ((randomStates badPopulation 3).map (multiplicity badPopulation)).sum = 1140 ∧
    (∀ q, badMask q ∈ missingMasks (observed badPopulation q))) ∧
  (pValue badPopulation ⟨0,3,11,6⟩ = 83/380 ∧
    pValue badPopulation ⟨0,3,10,7⟩ = 83/380 ∧
    (109/500 : ℚ) < 83/380 ∧
    Possible ⟨0,3,11,6⟩ badPopulation ∧
    ¬ Possible ⟨0,3,10,7⟩ badPopulation ∧
    estimateQ ⟨0,3,11,6⟩ = -11/17 ∧ estimateQ ⟨0,3,10,7⟩ = -10/17)

/-- Packaged content for P003-T2; see the Challenge docstring for scope. -/
def T2Statement : Prop :=
  (∀ (v : Counts) (m : ℕ) (α : ℝ)
    (hm : 0 < m) (hn : v.total = 2*m) (hα : 0 < α ∧ α < 1)
    (μ : Counts → Counts → ℝ) (hμ : IsMissingLaw v m μ),
    missingProb v m μ (fun q r => tau v ∈ missingInterval α (observed v q) r)
      ≥ 1-α) ∧
  (∀ (o r : Counts) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hr : r ∈ missingMasks o),
    completionUnion α o r ⊆ missingInterval α o r) ∧
  (∀ {n : ℕ} (m : ℕ) (hm : 0 < m) (hn : n = 2*m)
    (y y' : Fin n → Bool) (z r : Finset (Fin n)) (hz : z.card = m)
    (hy' : ∀ i, i ∉ r → y' i = y i) (w : PotentialTable n)
    (hw : PossibleTable y' z w) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (hp : α ≤ unitPValue w y' z)
    (ht : outcomeEstimator (unitPlus y z r) z < tableTau w),
    let yPlus := unitPlus y z r;
    let D := Finset.univ.filter (fun i => y' i ≠ yPlus i);
    let d := D.card;
    let wPlus := coupledPlus w yPlus z;
    PossibleTable yPlus z wPlus ∧
    tableTau wPlus = tableTau w + (d : ℝ)/n ∧
    outcomeEstimator yPlus z = outcomeEstimator y' z + 2*(d : ℝ)/n ∧
    (∀ q : Assignment n m,
      let N := (D.filter fun i => (i ∈ q.val ↔ i ∈ z)).card;
      N ≤ d ∧ tableEstimator wPlus q.val = tableEstimator w q.val + 2*(N : ℝ)/n ∧
      |(tableEstimator wPlus q.val-tableTau wPlus)-
        (tableEstimator w q.val-tableTau w)| ≤ (d : ℝ)/n) ∧
    |outcomeEstimator yPlus z-tableTau wPlus| =
      |outcomeEstimator y' z-tableTau w|-(d : ℝ)/n ∧
    unitPValue w y' z ≤ unitPValue wPlus yPlus z ∧ α ≤ unitPValue wPlus yPlus z ∧
    upper α (unitObserved yPlus z) ≥ tableTau wPlus ∧ tableTau wPlus ≥ tableTau w)

/-- Packaged content for P003-T3; see the Challenge docstring for scope. -/
def T3Statement : Prop :=
  (∀ (v : Counts) (m : ℕ) (α : ℝ)
    (hm : 0 < m ∧ m < v.total) (hα : 0 < α ∧ α < 1)
    (μ : Counts → Counts → ℝ) (hμ : IsMissingLaw v m μ),
    missingProb v m μ (fun q r => tau v ∈ completionUnion α (observed v q) r) ≥ 1-α ∧
    missingProb v m μ (fun q r => tau v ∈ completionHull α (observed v q) r) ≥ 1-α) ∧
  (∀ (α : ℝ) (o r : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hr : r ∈ missingMasks o),
    exactInterval α o ⊆ completionUnion α o r) ∧
  (∀ (α : ℝ) (o r : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hr : r ∈ missingMasks o),
    completionUnion α o r ⊆ completionHull α o r) ∧
  (∀ (o r : Counts) (hr : r ∈ missingMasks o),
    o ∈ completions o r ∧
    (completions o r).Nodup ∧
    (completions o r).length = (r.a+r.b+1)*(r.c+r.d+1)) ∧
  (∀ (v : Counts) (m : ℕ) (α : ℝ)
    (hm : 0 < m ∧ m < v.total) (hα : 0 < α ∧ α < 1),
    designProb v m (fun q => tau v ∈ exactInterval α (observed v q)) ≥ 1-α) ∧
  (completionHullQ (109/500) ⟨0,3,11,6⟩ ⟨0,0,1,0⟩ = some (-7/10,-3/20) ∧
    badHullCoverage = 892/1140 ∧ (391/500 : ℚ) ≤ badHullCoverage)

end SAP.P003a
