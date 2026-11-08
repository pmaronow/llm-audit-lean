import SAP.P003a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W1.P.T22_L1

open SAP.P003a

theorem slot_of_candidate (o : Counts) (x : ℤ)
    (hx : x ∈ candidateNumerators o) :
    ∃ i : Fin (o.total+1), (candidateNumerators o).reverse[i.val]! = x := by
  classical
  obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hx
  have hlen : (candidateNumerators o).length = o.total+1 := by
    simp [candidateNumerators]
  have hr' : r < o.total+1 := by
    rw [← hlen]
    exact hr
  let i : Fin (o.total+1) := ⟨o.total-r, by omega⟩
  have hir : i.val < (candidateNumerators o).reverse.length := by
    rw [List.length_reverse, hlen]
    exact i.isLt
  have hrev : (candidateNumerators o).reverse[i.val] = x := by
    rw [List.getElem_reverse hir]
    have heq : (candidateNumerators o).length - 1 - i.val = r := by
      dsimp [i]
      omega
    simpa only [heq] using hget
  refine ⟨i, ?_⟩
  simpa only [getElem!_pos (candidateNumerators o).reverse i.val hir] using hrev

theorem possible_of_mem_reuseLine (o v : Counts) (k : ℕ)
    (hk : k ∈ w1ReuseLine o v) : Possible o (reuseVector v k) := by
  have hf := (List.mem_filter.mp hk).2
  have hf' : k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k) := of_decide_eq_true hf
  exact hf'.2.2

end SAP.P003a.WH.W1.P.T22_L1

theorem SAP.P003a.WH.W1.T22_L1_proof : SAP.P003a.WH.W1.T22_L1 := by
  classical
  intro o u
  constructor
  · rintro ⟨s, hs, hsu⟩
    subst u
    rcases s with ⟨slot, base, k⟩
    change (⟨slot, base, k⟩ : SAP.P003a.W1Visit o.total) ∈
      (List.finRange (o.total+1)).flatMap (fun i =>
        (List.finRange (o.total+1)).flatMap (SAP.P003a.w1LineVisits o i)) at hs
    rw [List.mem_flatMap] at hs
    obtain ⟨i, hi, hs⟩ := hs
    rw [List.mem_flatMap] at hs
    obtain ⟨j, hj, hline⟩ := hs
    have hir : i.val < (SAP.P003a.candidateNumerators o).reverse.length := by
      simpa [List.length_reverse, SAP.P003a.candidateNumerators] using i.isLt
    cases hbase : SAP.P003a.firstOnLine o
        ((SAP.P003a.candidateNumerators o).reverse[i.val]) j.val with
    | none =>
        simp only [SAP.P003a.w1LineVisits,
          getElem!_pos (SAP.P003a.candidateNumerators o).reverse i.val hir,
          hbase] at hline
        simp at hline
    | some v =>
        simp only [SAP.P003a.w1LineVisits,
          getElem!_pos (SAP.P003a.candidateNumerators o).reverse i.val hir, hbase,
          List.mem_cons, List.mem_map] at hline
        rcases hline with hhead | ⟨k', hk', heq⟩
        ·
          have hp := (SAP.P003a.WH.W1.first_line_spec o
            ((SAP.P003a.candidateNumerators o).reverse[i.val]) j.val v hbase).1
          have hb : base = v := congrArg SAP.P003a.W1Visit.base hhead
          have hkEq : k = 0 := congrArg SAP.P003a.W1Visit.k hhead
          rw [hb, hkEq]
          simpa [SAP.P003a.reuseVector] using hp
        ·
          have hp := SAP.P003a.WH.W1.P.T22_L1.possible_of_mem_reuseLine o v k' hk'
          have hb : v = base := congrArg SAP.P003a.W1Visit.base heq
          have hkEq : k' = k := congrArg SAP.P003a.W1Visit.k heq
          rw [← hb, ← hkEq]
          exact hp
  · intro hu
    have hloop := (SAP.P003a.WH.W1.retained_T22.1 o u hu)
    obtain ⟨hx, hjbound, v, hbase, k, hk, hka, hkd, hreuse⟩ := hloop
    obtain ⟨i, hi⟩ := SAP.P003a.WH.W1.P.T22_L1.slot_of_candidate o u.effect hx
    let j : Fin (o.total+1) := ⟨u.a+u.b, by omega⟩
    have hbase' : SAP.P003a.firstOnLine o
        ((SAP.P003a.candidateNumerators o).reverse[i.val]!) j.val = some v := by
      rw [hi]
      simpa [j] using hbase
    have hir : i.val < (SAP.P003a.candidateNumerators o).reverse.length := by
      simpa [List.length_reverse, SAP.P003a.candidateNumerators] using i.isLt
    have hbaseIdx : SAP.P003a.firstOnLine o
        ((SAP.P003a.candidateNumerators o).reverse[i.val]) j.val = some v := by
      simpa only [getElem!_pos (SAP.P003a.candidateNumerators o).reverse i.val hir]
        using hbase'
    have hline : (⟨(i,j),v,k⟩ : SAP.P003a.W1Visit o.total) ∈
        SAP.P003a.w1LineVisits o i j := by
      by_cases hk0 : k = 0
      · subst k
        simp only [SAP.P003a.w1LineVisits,
          getElem!_pos (SAP.P003a.candidateNumerators o).reverse i.val hir,
          hbaseIdx, List.mem_cons]
        left
        trivial
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hkin : k ∈ (List.range o.total).map (fun t => t+1) := by
          apply List.mem_map.mpr
          refine ⟨k-1, List.mem_range.mpr ?_, ?_⟩
          · omega
          · omega
        have hposs : Possible o (SAP.P003a.reuseVector v k) := by
          rw [← hreuse]
          exact hu
        have hreuseLine : k ∈ SAP.P003a.w1ReuseLine o v := by
          unfold SAP.P003a.w1ReuseLine
          apply List.mem_filter.mpr
          refine ⟨hkin, ?_⟩
          simpa only [decide_eq_true_eq] using And.intro hka (And.intro hkd hposs)
        simp only [SAP.P003a.w1LineVisits,
          getElem!_pos (SAP.P003a.candidateNumerators o).reverse i.val hir,
          hbaseIdx, List.mem_cons,
          List.mem_map]
        right
        exact ⟨k, hreuseLine, rfl⟩
    have hout : (⟨(i,j),v,k⟩ : SAP.P003a.W1Visit o.total) ∈
        SAP.P003a.w1Traversal true o := by
      change (⟨(i,j),v,k⟩ : SAP.P003a.W1Visit o.total) ∈
        (List.finRange (o.total+1)).flatMap (fun i =>
          (List.finRange (o.total+1)).flatMap (SAP.P003a.w1LineVisits o i))
      rw [List.mem_flatMap]
      refine ⟨i, List.mem_finRange i, ?_⟩
      rw [List.mem_flatMap]
      exact ⟨j, List.mem_finRange j, hline⟩
    refine ⟨⟨(i,j),v,k⟩, hout, ?_⟩
    exact hreuse.symm
