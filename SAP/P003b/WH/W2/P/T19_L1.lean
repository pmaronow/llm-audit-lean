import SAP.P003b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W2.P.T19_L1

open SAP.P003b
open SAP.P003b.Bridge
attribute [local instance 0] Classical.propDecidable

theorem fiber_card {n : ℕ} (X : Fin n → Bool) (s : Bool) :
    Fintype.card {i : Fin n // X i = s} = wholeStratumSize X s := by
  classical
  rw [Fintype.card_subtype]
  rfl

theorem fiber_cell_card {n m : ℕ} (X : Fin n → Bool) (s : Bool)
    (e : Fin m ≃ {i : Fin n // X i = s})
    (w : PotentialTable n) (t : PotentialTable m)
    (hfit : ∀ i (hi : X i = s), w i = t (e.symm ⟨i, hi⟩))
    (a b : Bool) :
    ((Finset.univ.filter (fun i : Fin n => X i = s)).filter
      (fun i => w i = (a,b))).card =
    (Finset.univ.filter (fun j : Fin m => t j = (a,b))).card := by
  classical
  apply Finset.card_bij
    (fun i hi => e.symm ⟨i, (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2⟩)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hX : X i = s := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    calc
      t (e.symm ⟨i, hX⟩) = w i := (hfit i hX).symm
      _ = (a,b) := (Finset.mem_filter.mp hi).2
  · intro i hi j hj hmap
    have hXi : X i = s := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hXj : X j = s := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
    have hs : (⟨i, hXi⟩ : {i : Fin n // X i = s}) = ⟨j, hXj⟩ :=
      e.symm.injective hmap
    exact congrArg Subtype.val hs
  · intro j hj
    have hJ : t j = (a,b) := (Finset.mem_filter.mp hj).2
    let z : {i : Fin n // X i = s} := e j
    refine ⟨z.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact z.property
      · rw [hfit z.val z.property]
        have hz : e.symm z = j := by
          dsimp [z]
          exact e.symm_apply_apply j
        rw [hz]
        exact hJ
    · change e.symm z = j
      dsimp [z]
      exact e.symm_apply_apply j

theorem fiber_counts {n m : ℕ} (X : Fin n → Bool) (s : Bool)
    (e : Fin m ≃ {i : Fin n // X i = s})
    (w : PotentialTable n) (t : PotentialTable m)
    (hfit : ∀ i (hi : X i = s), w i = t (e.symm ⟨i, hi⟩)) :
    wholeCountsOn (Finset.univ.filter fun i => X i = s) w = tableCounts t := by
  apply Counts.ext
  · exact fiber_cell_card X s e w t hfit true true
  · exact fiber_cell_card X s e w t hfit true false
  · exact fiber_cell_card X s e w t hfit false true
  · exact fiber_cell_card X s e w t hfit false false

theorem realize_pair {n : ℕ} (X : Fin n → Bool) (v₀ v₁ : Counts)
    (h₀ : v₀.total = wholeStratumSize X false)
    (h₁ : v₁.total = wholeStratumSize X true) :
    ∃ w : PotentialTable n, wholeStratumCounts X w = (v₀,v₁) := by
  classical
  obtain ⟨u₀, hu₀⟩ := AronowAudit.P003.Wave1.neyman_exists_table (toCounts v₀)
  obtain ⟨u₁, hu₁⟩ := AronowAudit.P003.Wave1.neyman_exists_table (toCounts v₁)
  have hu₀' : tableCounts u₀ = v₀ := by
    change toCounts (tableCounts u₀) = toCounts v₀ at hu₀
    exact (to_inj _ _).mp hu₀
  have hu₁' : tableCounts u₁ = v₁ := by
    change toCounts (tableCounts u₁) = toCounts v₁ at hu₁
    exact (to_inj _ _).mp hu₁
  have hc₀ : Fintype.card {i : Fin n // X i = false} = (toCounts v₀).total := by
    calc
      _ = wholeStratumSize X false := fiber_card X false
      _ = v₀.total := h₀.symm
      _ = (toCounts v₀).total := (total_eq v₀).symm
  have hc₁ : Fintype.card {i : Fin n // X i = true} = (toCounts v₁).total := by
    calc
      _ = wholeStratumSize X true := fiber_card X true
      _ = v₁.total := h₁.symm
      _ = (toCounts v₁).total := (total_eq v₁).symm
  let e₀ : Fin (toCounts v₀).total ≃ {i : Fin n // X i = false} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin]; exact hc₀.symm)
  let e₁ : Fin (toCounts v₁).total ≃ {i : Fin n // X i = true} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin]; exact hc₁.symm)
  let w : PotentialTable n := fun i =>
    if h : X i = true then u₁ (e₁.symm ⟨i, h⟩)
    else u₀ (e₀.symm ⟨i, by
      cases hi : X i with
      | false => rfl
      | true => exact (h hi).elim
    ⟩)
  have hfit₀ : ∀ i (hi : X i = false),
      w i = u₀ (e₀.symm ⟨i, hi⟩) := by
    intro i hi
    simp [w, hi]
  have hfit₁ : ∀ i (hi : X i = true),
      w i = u₁ (e₁.symm ⟨i, hi⟩) := by
    intro i hi
    simp [w, hi]
  refine ⟨w, ?_⟩
  change (wholeCountsOn (Finset.univ.filter fun i => X i = false) w,
      wholeCountsOn (Finset.univ.filter fun i => X i = true) w) = (v₀,v₁)
  rw [fiber_counts X false e₀ w u₀ hfit₀,
    fiber_counts X true e₁ w u₁ hfit₁, hu₀', hu₁']

end SAP.P003b.WH.W2.P.T19_L1

theorem SAP.P003b.WH.W2.T19_L1_proof : SAP.P003b.WH.W2.T19_L1 := by
  intro n X
  classical
  let N₀ := wholeStratumSize X false
  let N₁ := wholeStratumSize X true
  apply Finset.ext
  intro q
  constructor
  · intro hq
    simp only [wholeStratumImage, Finset.mem_image, Finset.mem_univ, true_and] at hq
    rcases hq with ⟨w, hw⟩
    simp only [stratifiedCounts, Finset.product_eq_sprod, Finset.mem_product]
    constructor
    · apply (allCounts_mem N₀ q.1).2
      have h := countsOn_total (Finset.univ.filter fun i => X i = false) w
      change (wholeStratumCounts X w).1.total = wholeStratumSize X false at h
      rw [hw] at h
      simpa [N₀] using h
    · apply (allCounts_mem N₁ q.2).2
      have h := countsOn_total (Finset.univ.filter fun i => X i = true) w
      change (wholeStratumCounts X w).2.total = wholeStratumSize X true at h
      rw [hw] at h
      simpa [N₁] using h
  · intro hq
    simp only [stratifiedCounts, Finset.product_eq_sprod, Finset.mem_product] at hq
    have h₀ : q.1.total = N₀ := (allCounts_mem N₀ q.1).1 hq.1
    have h₁ : q.2.total = N₁ := (allCounts_mem N₁ q.2).1 hq.2
    obtain ⟨w, hw⟩ := SAP.P003b.WH.W2.P.T19_L1.realize_pair X q.1 q.2
      (by simpa [N₀] using h₀) (by simpa [N₁] using h₁)
    simp only [wholeStratumImage, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨w, hw⟩
