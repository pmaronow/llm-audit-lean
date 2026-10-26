import AronowAudit.P001.Wave1.Lib.TailA.ReuseMoments
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDensity

/-! Actual multinomial void bounds and the deterministic geometry of a pinned cell. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellLocalization (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- No original label in the specified category is retained by a size-`n+1` resample.
The central pinned label is separate from these `n` independent original labels. -/
def markedNoRetained {n : ℕ} (E : Set MatchUnit) (z : Fin n → MatchUnit)
    (a : Fin (n+1) → Fin (n+1)) : Prop :=
  ∀ i, z i ∈ E → ∀ t, a t ≠ i.succ


theorem marked_exp_count_product {n : ℕ} (E : Set MatchUnit)
    (z : Fin n → MatchUnit) (c : ℝ) :
    c^(Finset.univ.filter (fun i => z i ∈ E)).card =
      ∏ i, if z i ∈ E then c else 1 := by
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]


/-- A cell is specified by the actual retained original-label sites. -/
def markedCellContains {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j i : Fin n) : Prop :=
  reuseRetained r a j ∧ ∀ l, reuseRetained r a l → |p j-p i| ≤ |p l-p i|

/-- Distinct original-site comparison distances suffice even though bootstrap copies tie. -/
theorem marked_selected_original_iff {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j : Fin n)
    (hp : ∀ i l v, l ≠ v → |p l-p i| ≠ |p v-p i|) (t : Fin n) :
    Option.map a (nearestDonor (p ∘ a) (r ∘ a) t) = some j ↔
      markedCellContains p r a j (a t) := by
  unfold nearestDonor
  split_ifs with hex
  · let k := Classical.choose hex
    have hk := Classical.choose_spec hex
    change r (a k) = true ∧ ∀ v, r (a v) = true →
      |p (a k)-p (a t)| ≤ |p (a v)-p (a t)| at hk
    simp only [Option.map_some,Option.some.injEq]
    change a k = j ↔ _
    constructor
    · intro hkj
      refine ⟨⟨by simpa only [Function.comp_apply,hkj] using hk.1,k,hkj⟩,?_⟩
      intro l hl
      obtain ⟨hr,v,hv⟩ := hl
      have h := hk.2 v (by simpa only [Function.comp_apply,hv] using hr)
      simpa only [Function.comp_apply,hkj,hv] using h
    · intro hcell
      have hkret : reuseRetained r a (a k) := ⟨hk.1,k,rfl⟩
      have hle := hcell.2 (a k) hkret
      obtain ⟨hr,v,hv⟩ := hcell.1
      have hge := hk.2 v (by simpa only [Function.comp_apply,hv] using hr)
      simp only [Function.comp_apply,hv] at hge
      by_contra hne
      exact hp (a t) (a k) j hne (le_antisymm hge hle)
  · simp only [Option.map_none,reduceCtorEq,false_iff]
    intro hcell
    obtain ⟨hr,v,hv⟩ := hcell.1
    apply hex
    refine ⟨v,by simpa only [Function.comp_apply,hv] using hr,?_⟩
    intro k hk
    have h := hcell.2 (a k) ⟨hk,k,rfl⟩
    simpa only [Function.comp_apply,hv] using h

/-- Exact aggregation by original multiplicity and retained-site cell membership. -/
theorem marked_aggregated_weight {n : ℕ} (p : Fin n → ℝ) (r : Fin n → Bool)
    (a : Fin n → Fin n) (j : Fin n)
    (hp : ∀ i l v, l ≠ v → |p l-p i| ≠ |p v-p i|) :
    bootstrapOriginalReuse p r a j =
      ∑ i, reuseOccupancy a i *
        (if r i then (if i = j then 1 else 0)
          else if markedCellContains p r a j i then 1 else 0) := by
  rw [reuse_occupancy_sum]
  unfold bootstrapOriginalReuse
  simp_rw [reuse_weight_rows]
  have hrow (k : Fin n) :
      (if a k = j then (if r (a k) then (1 : ℝ) else 0) +
        ∑ t, if r (a t) = false ∧ nearestDonor (p ∘ a) (r ∘ a) t = some k then 1 else 0
      else 0) =
      (if a k = j then (if r (a k) then 1 else 0) else 0) +
        ∑ t, if a k = j then
          (if r (a t) = false ∧ nearestDonor (p ∘ a) (r ∘ a) t = some k then 1 else 0)
          else 0 := by
    by_cases hk : a k = j <;> simp only [hk,ite_true,ite_false,Finset.sum_const_zero,add_zero]
  simp only [Function.comp_apply]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib,Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  cases hr : r (a t) with
  | true => simp [hr]
  | false =>
    simp only [hr,Bool.false_eq_true,ite_false,zero_add,true_and,ite_self]
    have hcell := marked_selected_original_iff p r a j hp t
    cases hd : nearestDonor (p ∘ a) (r ∘ a) t with
    | none =>
      simp only [hd,Option.map_none,reduceCtorEq,false_iff] at hcell
      simp [hcell]
    | some k =>
      simp only [hd,Option.map_some,Option.some.injEq] at hcell
      have heq : (fun l => if a l = j then
          if some k = some l then (1 : ℝ) else 0 else 0) =
          fun l => if l = k then (if a k = j then 1 else 0) else 0 := by
        funext l
        by_cases hl : l = k
        · subst l
          simp only [ite_true]
        · simp [hl,Ne.symm hl]
      rw [heq]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rw [← hcell]
      simp

end AronowAudit.P001.TailA
