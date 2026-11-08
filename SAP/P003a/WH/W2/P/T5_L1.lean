import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2.P.T5_L1

open SAP.P003a
open SAP.P003a.WH.W2

theorem search_inv (fuel : ℕ) (reply : ℕ → ℤ → Bool) (t : ℕ) (a b : ℤ)
    (hpos : 0 < b-a) (hle : b-a ≤ fuel) :
    let s := w2Search fuel reply t a b
    s.1.2 = s.1.1+1 ∧ a ≤ s.1.1 ∧ s.1.2 ≤ b ∧ s.2.length < fuel ∧
      (∀ p ∈ s.2, a ≤ p.1 ∧ p.2 ≤ b ∧ p.1 < w2Mid p ∧ w2Mid p < p.2) ∧
      (s.2.map w2Mid).Nodup := by
  induction fuel generalizing t a b with
  | zero => omega
  | succ fuel ih =>
    by_cases hstop : b ≤ a+1
    · have hadj : b = a+1 := by omega
      simp only [w2Search, if_pos hstop]
      simp [hadj]
    · let c : ℤ := w2Mid (a,b)
      have hac : a < c := by dsimp [c, w2Mid]; omega
      have hcb : c < b := by dsimp [c, w2Mid]; omega
      have hleft : 0 < c-a ∧ c-a ≤ fuel := by
        constructor
        · omega
        · dsimp [c, w2Mid]; omega
      have hright : 0 < b-c ∧ b-c ≤ fuel := by
        constructor
        · omega
        · dsimp [c, w2Mid]; omega
      by_cases hr : reply t c = true
      · have hn := ih (t+1) a c hleft.1 hleft.2
        dsimp only [w2Search]
        simp only [if_neg hstop, show (a+b)/2 = c from rfl, if_pos hr]
        rcases hn with ⟨hadj, hlow, hupp, hlen, hframes, hnup⟩
        refine ⟨hadj, hlow, le_trans hupp hcb.le, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨le_rfl, le_rfl, hac, hcb⟩
          · rcases hframes p hp with ⟨hp1, hp2, hpm1, hpm2⟩
            exact ⟨hp1, le_trans hp2 hcb.le, hpm1, hpm2⟩
        · apply List.nodup_cons.mpr
          refine ⟨?_, hnup⟩
          intro hc
          obtain ⟨p, hp, hpc⟩ := List.mem_map.mp hc
          rcases hframes p hp with ⟨_, hp2, _, hpm2⟩
          have hlt : w2Mid p < c := lt_of_lt_of_le hpm2 hp2
          rw [hpc] at hlt
          exact (lt_irrefl c) hlt
      · have hn := ih (t+1) c b hright.1 hright.2
        dsimp only [w2Search]
        simp only [if_neg hstop, show (a+b)/2 = c from rfl, if_neg hr]
        rcases hn with ⟨hadj, hlow, hupp, hlen, hframes, hnup⟩
        refine ⟨hadj, le_trans hac.le hlow, hupp, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨le_rfl, le_rfl, hac, hcb⟩
          · rcases hframes p hp with ⟨hp1, hp2, hpm1, hpm2⟩
            exact ⟨le_trans hac.le hp1, hp2, hpm1, hpm2⟩
        · apply List.nodup_cons.mpr
          refine ⟨?_, hnup⟩
          intro hc
          obtain ⟨p, hp, hpc⟩ := List.mem_map.mp hc
          rcases hframes p hp with ⟨hp1, _, hpm1, _⟩
          have hlt : c < w2Mid p := lt_of_le_of_lt hp1 hpm1
          rw [hpc] at hlt
          exact (lt_irrefl c) hlt

end SAP.P003a.WH.W2.P.T5_L1

theorem SAP.P003a.WH.W2.T5_L1_proof : SAP.P003a.WH.W2.T5_L1 := by
  intro k₁ k₂ hk reply
  let d : ℕ := (k₂-k₁+1).toNat
  let a : ℤ := k₁-1
  let b : ℤ := k₂+1
  let fuel : ℕ := d+1
  have hd : 0 ≤ k₂-k₁+1 := by omega
  have hcast : (d : ℤ) = k₂-k₁+1 := by
    dsimp [d]
    exact Int.toNat_of_nonneg hd
  have hwidth : 0 < b-a ∧ b-a ≤ fuel := by
    dsimp [a, b, fuel]
    rw [hcast]
    omega
  have h := SAP.P003a.WH.W2.P.T5_L1.search_inv fuel reply 0 a b hwidth.1 hwidth.2
  dsimp [W2SearchGeometry, w2Run]
  dsimp only [a, b, fuel, d] at h ⊢
  rcases h with ⟨hadj, hlow, hupp, hlen, hframes, hnup⟩
  refine ⟨hadj, ?_, hlow, hupp, ?_, ?_, ?_⟩
  · simpa using hlen
  · intro p hp
    rcases hframes p hp with ⟨hp1, hp2, hpm1, hpm2⟩
    refine ⟨hp1, hp2, hpm1, hpm2⟩
  · simpa only [w2Queries, w2Run] using hnup
  · intro c hc
    have hmem : c ∈ (w2Search ((k₂-k₁+1).toNat+1) reply 0 (k₁-1) (k₂+1)).2.map w2Mid := by
      simpa only [w2Queries, w2Run] using hc
    obtain ⟨p, hp, hpc⟩ := List.mem_map.mp hmem
    rcases hframes p hp with ⟨hp1, hp2, hpm1, hpm2⟩
    have hlower : k₁-1 < c := by
      have hh : k₁-1 < w2Mid p := lt_of_le_of_lt hp1 hpm1
      simpa only [hpc] using hh
    have hupper : c < k₂+1 := by
      have hh : w2Mid p < k₂+1 := lt_of_lt_of_le hpm2 hp2
      simpa only [hpc] using hh
    omega
