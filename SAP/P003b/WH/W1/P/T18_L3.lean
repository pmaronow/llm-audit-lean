import SAP.P003b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W1.P.T18_L3

open SAP.P003b
open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

lemma literalBase_entry (o : Counts) (x : ℤ) {j : ℕ} {v : Counts}
    (h : w1LiteralBase o x = some (j, v)) :
    j ∈ List.range (o.total + 1) ∧ firstOnLine o x j = some v := by
  unfold w1LiteralBase at h
  have hhead := List.head?_eq_some_iff.mp h
  obtain ⟨ys, hys⟩ := hhead
  have hmem : (j, v) ∈
      (List.range (o.total + 1)).filterMap
        (fun j => (firstOnLine o x j).map (fun v => (j, v))) := by
    rw [hys]
    simp
  obtain ⟨j', hj', hm⟩ := List.mem_filterMap.mp hmem
  cases hline : firstOnLine o x j' with
  | none => simp [hline] at hm
  | some v' =>
      simp only [hline, Option.map_some] at hm
      rcases Prod.mk.inj (Option.some.inj hm) with ⟨rfl, rfl⟩
      exact ⟨hj', hline⟩

lemma literalDrawTerm_le (o : Counts) (K : ℕ) (x : ℤ) :
    (if (w1LiteralBase o x).isSome then K else 0) ≤
      ((List.range (o.total + 1)).map fun j =>
        if (firstOnLine o x j).isSome then K else 0).sum := by
  classical
  cases hb : w1LiteralBase o x with
  | none => simp
  | some p =>
      rcases p with ⟨j, v⟩
      obtain ⟨hj, hline⟩ := literalBase_entry o x hb
      simp only [Option.isSome_some, ↓reduceIte]
      have hmem : K ∈ List.map (fun j =>
          if (firstOnLine o x j).isSome then K else 0)
          (List.range (o.total + 1)) := by
        apply List.mem_map.mpr
        exact ⟨j, hj, by simp [hline]⟩
      exact List.single_le_sum (fun z hz => Nat.zero_le z) K hmem

lemma literalUpdateTerm_le (o : Counts) (K : ℕ) (x : ℤ) :
    (match w1LiteralBase o x with
      | none => 0
      | some (_, v) => K * (reuseLine o v).length) ≤
      ((List.range (o.total + 1)).map fun j =>
        match firstOnLine o x j with
        | none => 0
        | some v => K * (reuseLine o v).length).sum := by
  classical
  cases hb : w1LiteralBase o x with
  | none => simp
  | some p =>
      rcases p with ⟨j, v⟩
      obtain ⟨hj, hline⟩ := literalBase_entry o x hb
      simp only
      have hterm : K * (reuseLine o v).length ∈ List.map (fun j =>
          match firstOnLine o x j with
          | none => 0
          | some v => K * (reuseLine o v).length)
          (List.range (o.total + 1)) := by
        apply List.mem_map.mpr
        exact ⟨j, hj, by simp [hline]⟩
      exact List.single_le_sum (fun z hz => Nat.zero_le z)
        (K * (reuseLine o v).length) hterm

lemma literalDrawCount_le (o : Counts) (K : ℕ) :
    w1LiteralDrawCount o K ≤ generalDrawCount o K := by
  unfold w1LiteralDrawCount generalDrawCount
  apply List.sum_le_sum
  intro x hx
  exact literalDrawTerm_le o K x

lemma literalUpdateCount_le (o : Counts) (K : ℕ) :
    w1LiteralUpdateCount o K ≤ generalUpdateCount o K := by
  unfold w1LiteralUpdateCount generalUpdateCount
  apply List.sum_le_sum
  intro x hx
  exact literalUpdateTerm_le o K x

end SAP.P003b.WH.W1.P.T18_L3

theorem SAP.P003b.WH.W1.T18_L3_proof : SAP.P003b.WH.W1.T18_L3 := by
  intro o K
  exact ⟨SAP.P003b.WH.W1.P.T18_L3.literalDrawCount_le o K,
    SAP.P003b.WH.W1.P.T18_L3.literalUpdateCount_le o K⟩
