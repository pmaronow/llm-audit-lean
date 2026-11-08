import SAP.P003b.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
noncomputable section

def badPopulation : Counts := ⟨11,0,3,6⟩

def badMask (q : Counts) : Counts :=
  if q = ⟨0,0,3,0⟩ then ⟨0,0,1,0⟩ else ⟨0,0,0,0⟩

/-- Mathematical content packaged for P003-T24. -/
def T24Statement : Prop :=
  ∀ {n : ℕ} (w : PotentialTable n) (m : ℕ), 0 < m → n = 2*m →
    (∀ z : Finset (Fin n), z.card = m →
      zᶜ.card = m ∧
      tableEstimator w z + tableEstimator w zᶜ =
        (∑ i, (bit (w i).1-bit (w i).2))/(m : ℝ) ∧
      (∑ i, (bit (w i).1-bit (w i).2))/(m : ℝ) = 2*tableTau w) ∧
    designMean (tableCounts w) m (fun q => estimate (observed (tableCounts w) q)) = tableTau w ∧
    ∀ t : ℝ,
      designProb (tableCounts w) m (fun q => estimate (observed (tableCounts w) q) = tableTau w-t) =
      designProb (tableCounts w) m (fun q => estimate (observed (tableCounts w) q) = tableTau w+t)

/-- Mathematical content packaged for P003-T25. -/
def T25Statement : Prop :=
  (∀ (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1),
    (↑(accepted α o) : Set ℝ) = exactInterval α o ∩ candidateLattice o ∧
    (Set.Icc (estimate o) (((o.a : ℝ)-o.c+(o.a+o.b))/o.total) ∩
      (↑(accepted α o) : Set ℝ)) =
      Set.Icc (estimate o) (upper α o) ∩ candidateLattice o) ∧
  ((acceptedEffectsQ (1/2) ⟨0,2,0,2⟩).toFinset = {-1,0,1} ∧
    intervalQ (1/2) ⟨0,2,0,2⟩ = some (-1/4,1/4) ∧
    pValue ⟨1,0,2,1⟩ ⟨0,2,0,2⟩ = 2/3 ∧
    ¬ Possible ⟨0,2,0,2⟩ ⟨1,0,2,1⟩ ∧
    ((-1/4 : ℚ) ≤ 1/8 ∧ (1/8 : ℚ) ≤ 1/4) ∧
    ¬ ∃ d : ℤ, d ∈ candidateNumerators ⟨0,2,0,2⟩ ∧ (d : ℚ)/4 = 1/8)

/-- Mathematical content packaged for P003-T8. -/
def T8Statement : Prop :=
  ∀ (z : ℝ)
    (hz : 1.95996398454005 < z ∧ z < 1.95996398454006),
  ((∀ k ≤ 25, 0 ∈ waldInterval z 25 k ↔ 10 ≤ k ∧ k ≤ 15) ∧
    (∀ k ≤ 25, 0 ∈ waldInterval z 25 k → 0.55 < waldWidth z 25 k) ∧
    (∀ runs : List (Fin 26), runs ≠ [] →
      ((runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length : ℝ) /
        runs.length ≥ 0.925 →
      0.55 < median (runs.map fun k => waldWidth z 25 k.val)) ∧
    waldCoverageQ 25 10 15 = 14399081696900/15801325804719 ∧
    (waldWidth z 25 11 = 2*z*Real.sqrt (77/3750)) ∧
    ((∑ k ∈ Finset.Icc 12 13, ((25 : ℕ).choose k : ℝ)^2) /
      ((50 : ℕ).choose 25 : ℝ) < 1/2) ∧
    (1/2 < (∑ k ∈ Finset.Icc 11 14, ((25 : ℕ).choose k : ℝ)^2) /
      ((50 : ℕ).choose 25 : ℝ)) ∧
    waldCoverageQ 50 21 29 = 3816125510529753382833452/4109292299835622081085553 ∧
    waldWidth z 50 23 = 2*z*Real.sqrt (621/61250)) ∧
  ((∀ runs : List (Fin 26), runs ≠ [] →
      runs.length < 2*(runs.filter fun k => 0 ∈ waldInterval z 25 k.val).length →
      2*z*Real.sqrt (1/50) ≤ median (runs.map fun k => waldWidth z 25 k.val)) ∧
    (∀ k : ℕ, k ≤ 25 →
      let V₀ := 2*(k : ℝ)*(25-k)/15625
      let T := (waldEstimateQ 25 k : ℝ)
      (0 ∈ Set.Icc (T-z*Real.sqrt V₀) (T+z*Real.sqrt V₀) ↔ 10 ≤ k ∧ k ≤ 15) ∧
      (10 ≤ k ∧ k ≤ 15 → 0.54 < 2*z*Real.sqrt V₀)) ∧
    IsWaldMedian (waldWidth z 25) 25 (2*z*Real.sqrt (77/3750)) ∧
    (∀ k : ℕ, k ≤ 50 → (0 ∈ waldInterval z 50 k ↔ 21 ≤ k ∧ k ≤ 29)) ∧
    IsWaldMedian (waldWidth z 50) 50 (2*z*Real.sqrt (621/61250)) ∧
    (0.56170 < 2*z*Real.sqrt (77/3750) ∧ 2*z*Real.sqrt (77/3750) < 0.56171) ∧
    (0.39470 < 2*z*Real.sqrt (621/61250) ∧ 2*z*Real.sqrt (621/61250) < 0.39471))

/-- Mathematical content packaged for P003-T19. -/
def T19Statement : Prop :=
  (∀ (N₀ N₁ : ℕ),
    (∀ v ∈ stratifiedCounts N₀ N₁, v.1.total = N₀ ∧ v.2.total = N₁) ∧
    (stratifiedCounts N₀ N₁).card = (N₀+3).choose 3 * (N₁+3).choose 3 ∧
    ((stratifiedCounts N₀ N₁).card : ℝ) ≤ ((N₀+N₁+3 : ℕ) : ℝ)^6/36 ∧
    (allCounts (N₀+N₁)).card = (N₀+N₁+3).choose 3 ∧
    (∑ r ∈ Finset.range (N₀+N₁+1), (r+3).choose 3 * (N₀+N₁-r+3).choose 3) =
      (N₀+N₁+7).choose 7) ∧
  ((stratifiedCounts 2 2).card = 100 ∧ (11 : ℕ).choose 7 = 330 ∧
    (⟨3,0,0,0⟩ : Counts).total + (⟨1,0,0,0⟩ : Counts).total = 4 ∧
    (⟨3,0,0,0⟩ : Counts).total ≠ 2)

/-- Mathematical content packaged for P003-T20. -/
def T20Statement : Prop :=
  (∀ {n : ℕ} (m : ℕ)
    (hm : 0 < m ∧ m < n) (w w' : PotentialTable n)
    (hc : tableCounts w = tableCounts w'),
    ∀ t : ℝ,
    ((Finset.univ.filter fun z : Assignment n m => tableEstimator w z.val = t).card : ℝ) /
      Fintype.card (Assignment n m) =
    ((Finset.univ.filter fun z : Assignment n m => tableEstimator w' z.val = t).card : ℝ) /
      Fintype.card (Assignment n m)) ∧
  (∀ (v : Counts) (ha : 1 ≤ v.a) (hd : 1 ≤ v.d),
    ((reuseVector v 1).a : ℤ) = (v.a : ℤ)-1 ∧
    ((reuseVector v 1).b : ℤ) = (v.b : ℤ)+1 ∧
    ((reuseVector v 1).c : ℤ) = (v.c : ℤ)+1 ∧
    ((reuseVector v 1).d : ℤ) = (v.d : ℤ)-1) ∧
  (∀ (n n₁₁ n₁₀ n₀₁ j b x : ℤ)
    (u₁₁ u₁₀ u₀₁ u₀₀ : ℤ)
    (hu : u₁₁+u₁₀+u₀₁+u₀₀ = n) (hx : u₁₀-u₀₁ = x),
    ((j-b-n₀₁ ≤ j-b ↔ 0 ≤ n₀₁) ∧
     (j-b-n₀₁ ≤ n₁₁ ↔ j-n₁₁-n₀₁ ≤ b) ∧
     (j-b-n₀₁ ≤ j-x-n₀₁ ↔ x ≤ b) ∧
     (j-b-n₀₁ ≤ n-b-n₁₀-n₀₁ ↔ j+n₁₀ ≤ n)) ∧
    ((u₁₁+u₁₀-b, b, b-x, n-(u₁₁+u₁₀)-b+x) =
     (u₁₁+(u₁₀-b),u₁₀-(u₁₀-b),u₀₁-(u₁₀-b),u₀₀+(u₁₀-b))) ∧
    (∀ a d : ℤ, (a+2+d)%2 = 0 → d%2 = a%2))

/-- Mathematical content packaged for P003-T26. -/
def T26Statement : Prop :=
  badPopulation.total = 20 ∧ 0 < (3 : ℕ) ∧ 3 < badPopulation.total ∧
    (0 : ℝ) < 109/500 ∧ (109/500 : ℝ) < 1 ∧ tauQ badPopulation = -3/20 ∧
    (∀ q ∈ randomStates badPopulation 3,
      badMask q ∈ missingMasks (observed badPopulation q) ∧
      (accepted (109/500) (minusCompletion (observed badPopulation q) (badMask q))).Nonempty ∧
      (accepted (109/500) (plusCompletion (observed badPopulation q) (badMask q))).Nonempty) ∧
    designProb badPopulation 3 (fun q => tau badPopulation ∈
      missingInterval (109/500) (observed badPopulation q) (badMask q)) = 297/380 ∧
    (297/380 : ℝ) < 1-109/500

/-- Mathematical content packaged for P003-T27. -/
def T27Statement : Prop :=
  ¬ (∀ (k₁ k₂ r : ℤ) (f : ℤ → Bool),
      (0 < k₁ ∧ k₁ < k₂) → (k₁-1 ≤ r ∧ r ≤ k₂) →
      (∀ x, k₁ ≤ x → x ≤ k₂ → (f x = false ↔ x ≤ r)) →
      ∃ steps evaluations : ℕ,
        printedExecution steps k₁ k₂ f k₁ k₂ = some (r,evaluations) ∧
        (evaluations : ℝ) ≤ (⌊logTwo (k₂-k₁+1) + 2⌋ : ℤ))

/-- Mathematical content packaged for P003-T30. -/
def T30Statement : Prop :=
  ∀ (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1),
    estimate o ∈ accepted α o ∧ estimate o ∈ exactInterval α o ∧
    lower α o ≤ estimate o ∧ estimate o ≤ upper α o

/-- Mathematical content packaged for P003-T31. -/
def T31Statement : Prop :=
  ∀ (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hα : 0 < α ∧ α < 1)
    (hne : (accepted α o).Nonempty),
    upper α o-lower α o ≤ Real.sqrt
      ((4/α)*(o.total : ℝ)/(o.total-1 : ℕ)*
        ((o.total : ℝ)/((o.a+o.b : ℕ)*(o.c+o.d : ℕ))))

/-- Mathematical content packaged for P003-T33. -/
def T33Statement : Prop :=
  ∀ (o v : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hn : v.total = o.total)
    (hmin : 1 ≤ min v.b v.c) (hmax : 2 ≤ max v.b v.c),
    pValue ⟨v.a+1,v.b-1,v.c-1,v.d+1⟩ o ≥ pValue v o

/-- Mathematical content packaged for P003-T7. -/
def T7Statement : Prop :=
  (∀ (o : Counts) (reject : Counts → ℕ → Bool)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d),
    (upperRun true o reject).value.isSome ∧
    (upperRun true o reject).trace.length ≤ testBudget o.total) ∧
  (∀ (v : Counts) (m K : ℕ) (α ε : ℝ)
    (hm : 0 < m) (hn : v.total = 2*m) (hK : 0 < K)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε < α),
    uniformProb (fun ω : MonteSpace v.total m K =>
      exactInterval α (canonicalObserved v ω.1.val) ⊆
        monteInterval true α ε (canonicalObserved v ω.1.val) ω.2) ≥
          1-2*(testBudget v.total : ℝ)*Real.exp (-2*(K : ℝ)*ε^2) ∧
    (0 < α-2*ε → uniformProb (fun ω : MonteSpace v.total m K =>
      monteInterval true α ε (canonicalObserved v ω.1.val) ω.2 ⊆
        exactInterval (α-2*ε) (canonicalObserved v ω.1.val)) ≥
          1-2*(testBudget v.total : ℝ)*Real.exp (-2*(K : ℝ)*ε^2)))

/-- Mathematical content packaged for P003-T32. -/
def T32Statement : Prop :=
  ∀ (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hn : 15 ≤ o.total)
    (hα : 0 < α ∧ α < 1),
    (exactUpperRun α o).value.map (fun x => (x : ℝ)/o.total) = some (upper α o) ∧
    (exactUpperRun α (complementObserved o)).value.map
      (fun x => -(x : ℝ)/o.total) = some (lower α o) ∧
    (((exactUpperRun α o).trace.length +
      (exactUpperRun α (complementObserved o)).trace.length : ℕ) : ℝ) ≤
        4*(o.total : ℝ)*logTwo o.total

/-- Mathematical content packaged for P003-T34. -/
def T34Statement : Prop :=
  ∀ (v : Counts) (m K : ℕ) (α ε : ℝ)
    (hm : 0 < m) (hn : v.total = 2*m) (hsize : 15 ≤ v.total) (hK : 0 < K)
    (hα : 0 < α ∧ α < 1) (hε : 0 < ε ∧ ε < α),
    ((K : ℝ) ≥ Real.log (4*(v.total : ℝ)*logTwo v.total/ε)/(2*ε^2) →
      uniformProb (fun ω : MonteSpace v.total m K => tau v ∈
        monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2) ≥ 1-α) ∧
    (ε < α/3 → uniformProb (fun ω : MonteSpace v.total m K =>
      monteInterval true (α-ε) ε (canonicalObserved v ω.1.val) ω.2 ⊆
        exactInterval (α-3*ε) (canonicalObserved v ω.1.val)) ≥
          1-4*(v.total : ℝ)*logTwo v.total*Real.exp (-2*(K : ℝ)*ε^2))

/-- Mathematical content packaged for P003-T6. -/
def T6Statement : Prop :=
  (
    adaptiveData.total = 30 ∧ adaptiveData.a+adaptiveData.b = 15 ∧
    estimateQ adaptiveData = 1/15 ∧
    (0 : ℚ) < 1/200 ∧ (1/200 : ℚ) < 1/20 ∧ (1/20 : ℚ) < 1 ∧
    (((randomStates ⟨3,0,0,27⟩ 15).map fun q =>
      if observed ⟨3,0,0,27⟩ q = adaptiveData then multiplicity ⟨3,0,0,27⟩ q
      else 0).sum : ℚ)/binomial 30 15 = 45/116 ∧
    (0 : ℚ) < 45/116 ∧
    (∀ s : Bool, ((if s then (1 : ℚ) else 0)+1/200 ≥ 1/20 ↔ s = true))
  ) ∧
  (
    intervalQ (1/20) adaptiveData = some (-1/5,1/3) ∧
    intervalQ (1/25) adaptiveData = some (-1/5,1/3) ∧
    (let a := upperRun false adaptiveData (exactRejectQ (1/20) adaptiveData)
    let a' := upperRun false adaptiveData (exactRejectQ (1/25) adaptiveData)
    let bA := upperRun false adaptiveData (fun _ i => decide (i ≠ 0))
    let bB := upperRun false adaptiveData (fun _ i => decide (i = 0))
    let bD := upperRun false adaptiveData (fun _ i => decide (i < 2))
    a.value = some 10 ∧ a'.value = some 10 ∧ a.trace.length = 16 ∧
    bA.value = some 9 ∧ bA.trace[0]!.2 = false ∧ a.trace[0]!.2 = true ∧
    0 < traceProbabilityQ adaptiveData bA.trace ∧
    bB.value = some 16 ∧ bB.trace[0]!.2 = true ∧ a'.trace[0]!.2 = false ∧
    0 < traceProbabilityQ adaptiveData bB.trace ∧
    bD.value = some 16 ∧ bD.trace[0]!.2 = a.trace[0]!.2 ∧
    bD.trace[1]!.2 = true ∧ a.trace[1]!.2 = false ∧
    0 < traceProbabilityQ adaptiveData bD.trace)
  ) ∧
  (
    let a := upperRun false adaptiveData (exactRejectQ (1/20) adaptiveData)
    let a' := upperRun false adaptiveData (exactRejectQ (1/25) adaptiveData)
    let b := fun pool : Fin (2*testBudget 30+1) → Fin 1 → Assignment 30 15 =>
      upperRun false adaptiveData (approximateReject (1/20) (1/200) adaptiveData pool)
    uniformProb (fun pool => ∃ x, (b pool).value = some x ∧ x < 10) ≠
      uniformProb (fun pool =>
        let J := firstMismatch a.trace (b pool).trace
        J < a.trace.length ∧ (b pool).trace[J]!.2 = true) ∧
    uniformProb (fun pool => ∃ x, (b pool).value = some x ∧ 10 < x) ≠
      uniformProb (fun pool =>
        let J := firstMismatch a'.trace (b pool).trace
        J < a'.trace.length ∧ (b pool).trace[J]!.2 = false)
  ) ∧
  (
    let E := fun pool : Fin (2*testBudget 30+1) → Fin 5000 → Assignment 30 15 =>
      let b := upperRun false adaptiveData (approximateReject (1/20) (1/50) adaptiveData pool)
      2 ≤ b.trace.length ∧ b.trace[1]!.2 = true
    uniformProb E ≥ (4693104776190294207 : ℝ)/5012394999999664375 ∧
    (4693104776190294207 : ℝ)/5012394999999664375 > 9/10 ∧
    16*Real.exp (-4) < 48/103 ∧ (48/103 : ℝ) < 9/10
  )

end
end SAP.P003b
