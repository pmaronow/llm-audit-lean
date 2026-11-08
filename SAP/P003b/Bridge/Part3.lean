import SAP.P003b.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.Bridge
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

@[simp] theorem missingMasks_eq (o : Counts) :
    AronowAudit.P003.missingMasks (toCounts o) = (missingMasks o).map toCounts := by
  simp [AronowAudit.P003.missingMasks, missingMasks, List.map_flatMap,
    List.map_map, Function.comp_def, toCounts]
@[simp] theorem plusCompletion_eq (o r : Counts) :
    AronowAudit.P003.plusCompletion (toCounts o) (toCounts r) = toCounts (plusCompletion o r) := rfl
@[simp] theorem minusCompletion_eq (o r : Counts) :
    AronowAudit.P003.minusCompletion (toCounts o) (toCounts r) = toCounts (minusCompletion o r) := rfl
@[simp] theorem missingInterval_eq (α : ℝ) (o r : Counts) :
    AronowAudit.P003.missingInterval α (toCounts o) (toCounts r) = missingInterval α o r := by
  simp [AronowAudit.P003.missingInterval, missingInterval]
@[simp] theorem missingLaw_eq (v : Counts) (m : ℕ) (μ : AronowAudit.P003.Counts → AronowAudit.P003.Counts → ℝ) :
    AronowAudit.P003.IsMissingLaw (toCounts v) m μ ↔
      IsMissingLaw v m (fun q r => μ (toCounts q) (toCounts r)) := by
  simp [AronowAudit.P003.IsMissingLaw, IsMissingLaw, List.map_map, Function.comp_def]
@[simp] theorem missingProb_eq (v : Counts) (m : ℕ)
    (μ : AronowAudit.P003.Counts → AronowAudit.P003.Counts → ℝ)
    (E : AronowAudit.P003.Counts → AronowAudit.P003.Counts → Prop) :
    AronowAudit.P003.missingProb (toCounts v) m μ E =
      missingProb v m (fun q r => μ (toCounts q) (toCounts r)) (fun q r => E (toCounts q) (toCounts r)) := by
  simp [AronowAudit.P003.missingProb, missingProb, List.map_map, Function.comp_def]

@[simp] theorem allCounts_eq (n : ℕ) :
    AronowAudit.P003.allCounts n = (allCounts n).image toCounts := by
  unfold AronowAudit.P003.allCounts allCounts
  change (AronowAudit.P003.randomStates (toCounts ⟨n,n,n,n⟩) n).toFinset = _
  rw [randomStates_eq]
  ext v
  simp
@[simp] theorem allCounts_card_eq (n : ℕ) :
    (AronowAudit.P003.allCounts n).card = (allCounts n).card := by
  rw [allCounts_eq]
  exact Finset.card_image_of_injective _ (fun _ _ h => congrArg fromCounts h)
@[simp] theorem stratified_card_eq (n m : ℕ) :
    (AronowAudit.P003.stratifiedCounts n m).card = (stratifiedCounts n m).card := by
  simp only [AronowAudit.P003.stratifiedCounts, stratifiedCounts, Finset.product_eq_sprod, Finset.card_product, allCounts_card_eq]
@[simp] theorem stratified_mem_eq (n m : ℕ) (v w : Counts) :
    (toCounts v,toCounts w) ∈ AronowAudit.P003.stratifiedCounts n m ↔ (v,w) ∈ stratifiedCounts n m := by
  simp only [AronowAudit.P003.stratifiedCounts, stratifiedCounts, Finset.product_eq_sprod, Finset.mem_product]
  rw [allCounts_eq, allCounts_eq]
  simp only [Finset.mem_image, to_inj, exists_eq_right]

@[simp] theorem treatedCounts_eq {n : ℕ} (v : Counts) (z : Finset (Fin n)) :
    AronowAudit.P003.treatedCounts (toCounts v) z = toCounts (treatedCounts v z) := rfl
@[simp] theorem updateTreated_eq (v q : Counts) (s₀ s₁ : ℕ) :
    AronowAudit.P003.updateTreated (toCounts v) (toCounts q) s₀ s₁ = toCounts (updateTreated v q s₀ s₁) := rfl
@[simp] theorem reusedSamples_eq {n m K : ℕ} (v : Counts) (initial : Fin K → Assignment n m)
    (seeds : Fin n → Fin K → (Fin n.factorial × Fin n.factorial)) (k : ℕ) (i : Fin K) :
    AronowAudit.P003.reusedSamples (toCounts v) initial seeds k i =
      toCounts (reusedSamples v initial seeds k i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [AronowAudit.P003.reusedSamples, reusedSamples, reuseVector_eq, ih, updateTreated_eq]
@[simp] theorem reusedSamples_fn {n m K : ℕ} (v : Counts) (initial : Fin K → Assignment n m)
    (seeds : Fin n → Fin K → (Fin n.factorial × Fin n.factorial)) (k : ℕ) :
    AronowAudit.P003.reusedSamples (toCounts v) initial seeds k =
      (fun i => toCounts (reusedSamples v initial seeds k i)) := by
  funext i
  exact reusedSamples_eq v initial seeds k i
@[simp] theorem rankValue_eq {K : ℕ} (R : AronowAudit.P003.Counts → AronowAudit.P003.Counts → ℝ)
    (o v : Counts) (samples : Fin K → Counts) :
    AronowAudit.P003.rankValue R (toCounts o) (toCounts v) (fun i => toCounts (samples i)) =
      rankValue (fun o v => R (toCounts o) (toCounts v)) o v samples := by
  simp [AronowAudit.P003.rankValue, rankValue]
@[simp] theorem generalSet_eq {n m K : ℕ} (α : ℝ)
    (θ : AronowAudit.P003.Counts → ℝ) (R : AronowAudit.P003.Counts → AronowAudit.P003.Counts → ℝ) (o : Counts)
    (initial : (Fin (n+1) × Fin (n+1)) → Fin K → Assignment n m)
    (seeds : (Fin (n+1) × Fin (n+1)) → Fin n → Fin K → (Fin n.factorial × Fin n.factorial)) :
    AronowAudit.P003.generalSet α θ R (toCounts o) initial seeds =
      generalSet α (fun v => θ (toCounts v)) (fun o v => R (toCounts o) (toCounts v)) o initial seeds := by
  ext t
  simp only [AronowAudit.P003.generalSet, generalSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ij,v,hv,k,hk,ha,hd,hp,ht,hr⟩
    rw [candidateNumerators_eq,firstOnLine_eq] at hv
    obtain ⟨w,hw,rfl⟩ := Option.map_eq_some_iff.mp hv
    refine ⟨ij,w,hw,k,hk,ha,hd,?_,?_,?_⟩
    · simpa only [reuseVector_eq, possible_eq] using hp
    · simpa only [reuseVector_eq] using ht
    · simpa only [reuseVector_eq, reusedSamples_fn, rankValue_eq] using hr
  · rintro ⟨ij,v,hv,k,hk,ha,hd,hp,ht,hr⟩
    refine ⟨ij,toCounts v,?_,k,hk,ha,hd,?_,?_,?_⟩
    · simpa only [candidateNumerators_eq,firstOnLine_eq,hv,Option.map_some]
    · simpa only [reuseVector_eq, possible_eq] using hp
    · simpa only [reuseVector_eq] using ht
    · simpa only [reuseVector_eq, reusedSamples_fn, rankValue_eq] using hr
@[simp] theorem reuseLine_eq (o v : Counts) :
    AronowAudit.P003.reuseLine (toCounts o) (toCounts v) = reuseLine o v := by
  simp [AronowAudit.P003.reuseLine, reuseLine]
  all_goals rfl
@[simp] theorem drawCount_eq (o : Counts) (K : ℕ) :
    AronowAudit.P003.generalDrawCount (toCounts o) K = generalDrawCount o K := by
  simp [AronowAudit.P003.generalDrawCount, generalDrawCount]
  all_goals rfl
@[simp] theorem updateCount_eq (o : Counts) (K : ℕ) :
    AronowAudit.P003.generalUpdateCount (toCounts o) K = generalUpdateCount o K := by
  simp only [AronowAudit.P003.generalUpdateCount, generalUpdateCount, candidateNumerators_eq, total_eq]
  congr 1
  apply List.map_congr_left
  intro x hx
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [firstOnLine_eq]
  cases firstOnLine o x j <;> simp
@[simp] theorem operations_eq (o : Counts) (K : ℕ) (c₀ c₁ c₂ : ℝ) :
    AronowAudit.P003.generalOperations (toCounts o) K c₀ c₁ c₂ = generalOperations o K c₀ c₁ c₂ := by
  simp [AronowAudit.P003.generalOperations, generalOperations]

end
end SAP.P003b.Bridge
