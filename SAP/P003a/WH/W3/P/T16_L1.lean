import SAP.P003a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W3.P.T16_L1

open Finset

theorem remaining_card (n : ℕ) (i j : Fin n) (hji : j ≠ i) :
    Fintype.card (SAP.P003a.WholeRemaining n i j) = n - 2 := by
  classical
  let r : Finset (Fin n) := (Finset.univ.erase i).erase j
  have hr : ∀ k : Fin n, k ∈ r ↔ k ≠ i ∧ k ≠ j := by
    intro k
    simp [r, Finset.mem_erase, and_comm]
  have hcard : Fintype.card (SAP.P003a.WholeRemaining n i j) = r.card := by
    change Fintype.card {k : Fin n // k ≠ i ∧ k ≠ j} = r.card
    exact Fintype.card_of_subtype r hr
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hj : j ∈ Finset.univ.erase i := by
    simp [Finset.mem_erase, hji]
  have hc1 : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem hi]
    simp
  have hc2 : r.card = n - 2 := by
    dsimp [r]
    rw [Finset.card_erase_of_mem hj, hc1]
    omega
  exact hcard.trans hc2

theorem residual_card (n m : ℕ) (i j : Fin n) (hji : j ≠ i) :
    Fintype.card (SAP.P003a.WholeResidualAssignment n m i j) = (n - 2).choose (m - 1) := by
  classical
  let r : Finset (Fin n) := (Finset.univ.erase i).erase j
  have hr : ∀ s : Finset (Fin n),
      s ∈ r.powersetCard (m - 1) ↔
        s.card = m - 1 ∧ i ∉ s ∧ j ∉ s := by
    intro s
    simp only [r, Finset.mem_powersetCard, Finset.subset_iff,
      Finset.mem_erase, Finset.mem_univ]
    constructor
    · rintro ⟨hsub, hk⟩
      refine ⟨hk, ?_, ?_⟩
      · intro hi
        exact (hsub hi).2.1 rfl
      · intro hj
        exact (hsub hj).1 rfl
    · rintro ⟨hk, hi, hj⟩
      refine ⟨?_, hk⟩
      intro x hx
      constructor
      · intro hxj
        exact hj (hxj ▸ hx)
      · constructor
        · intro hxi
          exact hi (hxi ▸ hx)
        · trivial
  have hcard : Fintype.card (SAP.P003a.WholeResidualAssignment n m i j) =
      (r.powersetCard (m - 1)).card := by
    change Fintype.card {s : Finset (Fin n) // s.card = m - 1 ∧ i ∉ s ∧ j ∉ s} = _
    exact Fintype.card_of_subtype (r.powersetCard (m - 1)) hr
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hj : j ∈ Finset.univ.erase i := by
    simp [Finset.mem_erase, hji]
  have hc1 : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem hi]
    simp
  have hc2 : r.card = n - 2 := by
    dsimp [r]
    rw [Finset.card_erase_of_mem hj, hc1]
    omega
  calc
    Fintype.card (SAP.P003a.WholeResidualAssignment n m i j) =
        (r.powersetCard (m - 1)).card := hcard
    _ = r.card.choose (m - 1) := Finset.card_powersetCard (m - 1) r
    _ = (n - 2).choose (m - 1) := by rw [hc2]

end SAP.P003a.WH.W3.P.T16_L1

theorem SAP.P003a.WH.W3.T16_L1_proof : SAP.P003a.WH.W3.T16_L1 := by
  classical
  intro n m hm hn i
  have hn2 : 2 ≤ n := by omega
  have hpartner : Nonempty (SAP.P003a.WholePartner n i) := by
    let j : Fin n := ⟨if i.val = 0 then 1 else 0, by
      by_cases h : i.val = 0
      · simp [h]
        omega
      · simp [h]
        omega⟩
    have hne : j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [j] at hv
      by_cases hzero : i.val = 0
      · simp [hzero] at hv
      · simp [hzero] at hv
        omega
    exact ⟨⟨j, hne⟩⟩
  have hchoose : m - 1 ≤ n - 2 := by omega
  have hchoosepos : 0 < (n - 2).choose (m - 1) := Nat.choose_pos hchoose
  have hremFacts : ∀ j : SAP.P003a.WholePartner n i,
      Nonempty (Fin (n-2) ≃ SAP.P003a.WholeRemaining n i j.val) ∧
      Nonempty (SAP.P003a.WholeResidualAssignment n m i j.val) ∧
      Fintype.card (SAP.P003a.WholeResidualAssignment n m i j.val) =
        (n-2).choose (m-1) := by
    intro j
    have hcard := SAP.P003a.WH.W3.P.T16_L1.remaining_card n i j.val j.property
    have heq : Fintype.card (Fin (n - 2)) =
        Fintype.card (SAP.P003a.WholeRemaining n i j.val) := by
      simp [hcard]
    have he : Fin (n - 2) ≃ SAP.P003a.WholeRemaining n i j.val :=
      Fintype.equivOfCardEq heq
    have hrescard := SAP.P003a.WH.W3.P.T16_L1.residual_card n m i j.val j.property
    refine ⟨⟨he⟩, ?_, hrescard⟩
    exact Fintype.card_pos_iff.mp (by rw [hrescard]; exact hchoosepos)
  obtain ⟨j⟩ := hpartner
  obtain ⟨r⟩ := (hremFacts j).2.1
  have hsource : Nonempty (SAP.P003a.WholePairSource n m i) :=
    ⟨Sigma.mk j (false, r)⟩
  exact ⟨hsource, hremFacts⟩
