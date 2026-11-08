import SAP.P003a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W1.P.T22_L2

open SAP.P003a.Bridge

lemma reuseLine_mem_iff (o v : Counts) (k : ℕ) :
    k ∈ w1ReuseLine o v ↔
      0 < k ∧ k ≤ o.total ∧ k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k) := by
  unfold w1ReuseLine
  simp only [List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨j, hj, hjk⟩, ha, hd, hp⟩
    exact ⟨by omega, by omega, ha, hd, hp⟩
  · rintro ⟨hk, hkn, ha, hd, hp⟩
    refine ⟨⟨k-1, by omega, ?_⟩, ha, hd, hp⟩
    omega

lemma lineVisits_mem_iff (o : Counts) (i j : Fin (o.total+1))
    (s : W1Visit o.total) :
    s ∈ w1LineVisits o i j ↔
      ∃ v, firstOnLine o ((candidateNumerators o).reverse[i.val]!) j.val = some v ∧
        s.slot = (i,j) ∧ s.base = v ∧ (s.k = 0 ∨ s.k ∈ w1ReuseLine o v) := by
  cases h : firstOnLine o ((candidateNumerators o).reverse[i.val]!) j.val with
  | none =>
      rw [w1LineVisits, h]
      simp
  | some v =>
      rw [w1LineVisits, h]
      rcases s with ⟨slot, base, k⟩
      simp [List.mem_map, eq_comm, and_comm, and_left_comm, and_assoc]
      constructor
      · intro hs
        rcases hs with ⟨hvb, hk, hslot⟩ | ⟨hvb, hk, hslot⟩
        · subst base
          exact ⟨rfl, Or.inl hk, hslot⟩
        · subst base
          exact ⟨rfl, Or.inr hk, hslot⟩
      · rintro ⟨hvb, hk | hk, hslot⟩
        · subst base
          exact Or.inl ⟨rfl, hk, hslot⟩
        · subst base
          exact Or.inr ⟨rfl, hk, hslot⟩

lemma traversalVisit_mem_iff (o : Counts) (ij : Fin (o.total+1) × Fin (o.total+1))
    (v : Counts) (k : ℕ) :
    (∃ s ∈ w1Traversal true o, s.slot = ij ∧ s.base = v ∧ s.k = k) ↔
      firstOnLine o ((candidateNumerators o).reverse[ij.1.val]!) ij.2.val = some v ∧
        (k = 0 ∨ k ∈ w1ReuseLine o v) := by
  classical
  constructor
  · rintro ⟨s, hs, hsij, hsv, hsk⟩
    unfold w1Traversal at hs
    simp only [if_true] at hs
    rcases List.mem_flatMap.mp hs with ⟨i, hi, hs⟩
    rcases List.mem_flatMap.mp hs with ⟨j, hj, hline⟩
    have hspec := (lineVisits_mem_iff o i j s).mp hline
    rcases hspec with ⟨w, hfirst, hslot, hw, hk⟩
    have hwv : w = v := hw.symm.trans hsv
    rw [hwv] at hfirst hk
    rw [hsk] at hk
    have hij : (i,j) = ij := hslot.symm.trans hsij
    have hi' : i = ij.1 := congrArg Prod.fst hij
    have hj' : j = ij.2 := congrArg Prod.snd hij
    subst i
    subst j
    exact ⟨hfirst, hk⟩
  · rintro ⟨hfirst, hk⟩
    refine ⟨⟨ij,v,k⟩, ?_, rfl, rfl, rfl⟩
    unfold w1Traversal
    simp only [if_true]
    apply List.mem_flatMap.mpr
    refine ⟨ij.1, ?_, ?_⟩
    · simp
    apply List.mem_flatMap.mpr
    refine ⟨ij.2, ?_, ?_⟩
    · simp
    apply (lineVisits_mem_iff o ij.1 ij.2 ⟨ij,v,k⟩).2
    exact ⟨v, hfirst, rfl, rfl, hk⟩

lemma visitIndex_iff (o : Counts) (ij : Fin (o.total+1) × Fin (o.total+1))
    (v : Counts) (k : ℕ) :
    (∃ s ∈ w1Traversal true o, s.slot = ij ∧ s.base = v ∧ s.k = k) ↔
      firstOnLine o ((candidateNumerators o).reverse[ij.1.val]!) ij.2.val = some v ∧
      k ≤ o.total ∧ k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k) := by
  rw [traversalVisit_mem_iff]
  constructor
  · rintro ⟨hfirst, hk | hk⟩
    · subst k
      have hbase := (first_line_spec o _ _ v hfirst).1
      exact ⟨by omega, by omega, by omega, by omega, by simpa [reuseVector] using hbase⟩
    · obtain ⟨hkpos, hkn, ha, hd, hp⟩ := (reuseLine_mem_iff o v k).mp hk
      exact ⟨hfirst, hkn, ha, hd, hp⟩
  · rintro ⟨hfirst, hkn, ha, hd, hp⟩
    by_cases hk : k = 0
    · exact ⟨hfirst, Or.inl hk⟩
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hm : k ∈ w1ReuseLine o v :=
        (reuseLine_mem_iff o v k).2 ⟨hkpos, hkn, ha, hd, hp⟩
      exact ⟨hfirst, Or.inr hm⟩

end SAP.P003a.WH.W1.P.T22_L2

theorem SAP.P003a.WH.W1.T22_L2_proof : SAP.P003a.WH.W1.T22_L2 := by
  classical
  intro m K α θ R o initial seeds
  ext t
  constructor
  · intro ht
    change ∃ s ∈ w1Traversal true o,
      t = θ (reuseVector s.base s.k) ∧
        α < rankValue R o (reuseVector s.base s.k)
          (w1ReusedSamples s.base (initial s.slot) (seeds s.slot) s.k) at ht
    rcases ht with ⟨s, hs, rfl, hrank⟩
    have hv := (SAP.P003a.WH.W1.P.T22_L2.visitIndex_iff o s.slot s.base s.k).mp
      ⟨s, hs, rfl, rfl, rfl⟩
    rcases hv with ⟨hfirst, hkn, ha, hd, hp⟩
    refine ⟨s.slot, s.base, hfirst, s.k, hkn, ha, hd, hp, rfl, hrank⟩
  · intro ht
    change ∃ ij : Fin (o.total+1) × Fin (o.total+1), ∃ v,
      firstOnLine o ((candidateNumerators o).reverse[ij.1.val]!) ij.2.val = some v ∧
      ∃ k ≤ o.total, k ≤ v.a ∧ k ≤ v.d ∧ Possible o (reuseVector v k) ∧
        t = θ (reuseVector v k) ∧
        α < rankValue R o (reuseVector v k)
          (w1ReusedSamples v (initial ij) (seeds ij) k) at ht
    rcases ht with ⟨ij, v, hfirst, k, hkn, ha, hd, hp, rfl, hrank⟩
    have hm := (SAP.P003a.WH.W1.P.T22_L2.visitIndex_iff o ij v k).mpr
      ⟨hfirst, hkn, ha, hd, hp⟩
    rcases hm with ⟨s, hs, hsij, hsv, hsk⟩
    refine ⟨s, hs, ?_⟩
    constructor
    · simp [hsv, hsk]
    · simpa [hsij, hsv, hsk] using hrank

