import SAP.P045a.WH.W2.Leaves
import AronowAudit.P045.Wave1.ClusterSampler.N3
import AronowAudit.P045.Wave1.ClusterSampler.N4
import AronowAudit.P045.Wave1.ClusterSampler.N5
import AronowAudit.P045.Wave1.ClusterSampler.N6
import AronowAudit.P045.Wave1.ClusterSampler.N7
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace SAP.P045a.WH.W2.P.T10_L2

open AronowAudit.P045
open AronowAudit.P045.Wave1.ClusterSampler

noncomputable section

theorem coded_classification : TraceClassification :=
  n5_proof n3_proof

theorem coded_off (S : Finset (Fin 4))
    (hS : S ∉ ({{0,1},{0,2},{0,3},{1},{2}} : Finset (Finset (Fin 4)))) :
    SAP.P045a.fourPathLengthMass true S = 0 := by
  classical
  funext t
  unfold SAP.P045a.fourPathLengthMass
  apply Finset.sum_eq_zero
  intro z _
  by_cases hs : (List.ofFn z).toFinset = S
  · rw [if_pos hs]
    by_contra hm
    apply hS
    rcases coded_classification (List.ofFn z) hm with h | h | h | ⟨r,j,hj,h⟩
    · simp [← hs,h]
    · simp [← hs,h]
    · have : S = ({0,3} : Finset (Fin 4)) := by
        simpa [h, Finset.pair_comm] using hs.symm
      simp [this]
    · have : S = ({0,j} : Finset (Fin 4)) := by
        simpa [h, List.toFinset_append,
          List.toFinset_replicate_of_ne_zero (by omega : r+1 ≠ 0)] using hs.symm
      fin_cases j <;> simp_all
  · exact if_neg hs

theorem coded_pair_inner (a : Fin 4) (ha : a ≠ 0) (ha3 : a ≠ 3) (t : ℕ) :
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({0,a} : Finset (Fin 4)) then
      traceMass AronowAudit.P045.pathDistance 3 true (List.ofFn z) else 0) =
      if 2 ≤ t then (1/4 : ℝ)^t else 0 := by
  classical
  have hsupp : ∀ cs : List (Fin 4), cs.toFinset = {0,a} →
      traceMass AronowAudit.P045.pathDistance 3 true cs ≠ 0 →
      ∃ r : ℕ, cs = List.replicate (r+1) 0 ++ [a] := by
    intro cs hs hm
    have h0 : (0 : Fin 4) ∈ cs.toFinset := by rw [hs]; simp
    rcases coded_classification cs hm with h | h | h | ⟨r,j,hj,h⟩
    · norm_num [h] at h0
    · norm_num [h] at h0
    · have h3 : (3 : Fin 4) ∈ cs.toFinset := by simp [h]
      simpa [hs, Ne.symm ha3] using h3
    · have hjmem : j = 0 ∨ j = a := by
        have : j ∈ cs.toFinset := by simp [h]
        simpa [hs] using this
      have hja := hjmem.resolve_left hj
      exact ⟨r, by simpa only [hja] using h⟩
  by_cases ht : 2 ≤ t
  · obtain ⟨r,rfl⟩ : ∃ r : ℕ, t = r+2 := ⟨t-2, by omega⟩
    let retry : Fin (r+2) → Fin 4 :=
      Fin.append (m := r+1) (n := 1) (fun _ => 0) (fun _ => a)
    have hretry : List.ofFn retry = List.replicate (r+1) 0 ++ [a] := by
      simpa only [retry, List.ofFn_const, List.replicate_one] using
        List.ofFn_fin_append (fun _ : Fin (r+1) => (0 : Fin 4)) (fun _ : Fin 1 => a)
    have hset : (List.replicate (r+1) (0 : Fin 4) ++ [a]).toFinset = {0,a} := by
      simp [List.toFinset_append, List.toFinset_replicate_of_ne_zero (by omega : r+1 ≠ 0)]
    rw [Fintype.sum_eq_single retry]
    · rw [hretry, if_pos hset]
      change traceMass (AronowAudit.P045.pathDistance (n := 4)) 3 true
        (List.replicate (r+1) (0 : Fin 4) ++ [a]) = _
      rw [if_pos (show 2 ≤ r+2 by omega)]
      exact AronowAudit.P045.four_path_repeat_trace_mass r a ha
    · intro z hz
      by_cases hs : (List.ofFn z).toFinset = ({0,a} : Finset (Fin 4))
      · rw [if_pos hs]
        by_contra hm
        obtain ⟨s,heq⟩ := hsupp (List.ofFn z) hs hm
        have hlen : r+2 = s+2 := by simpa using congrArg List.length heq
        have hsr : s = r := by omega
        subst s
        exact hz (List.ofFn_injective (heq.trans hretry.symm))
      · exact if_neg hs
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hs : (List.ofFn z).toFinset = ({0,a} : Finset (Fin 4))
    · rw [if_pos hs]
      by_contra hm
      obtain ⟨r,heq⟩ := hsupp (List.ofFn z) hs hm
      have hlen : t = r+2 := by simpa using congrArg List.length heq
      omega
    · exact if_neg hs

theorem repaired_nonzero_data {cs : List (Fin 4)}
    (hm : traceMass AronowAudit.P045.pathDistance 3 false cs ≠ 0) :
    (∀ k : Fin cs.length,
      marked AronowAudit.P045.pathDistance 3 (cs.take k.val).toFinset ≠ univ) ∧
      marked AronowAudit.P045.pathDistance 3 cs.toFinset = univ := by
  by_contra ht
  exact hm (by simp only [traceMass, if_neg ht])

theorem repaired_nonzero_draw {cs : List (Fin 4)}
    (hm : traceMass AronowAudit.P045.pathDistance 3 false cs ≠ 0) (k : Fin cs.length) :
    centreDraw AronowAudit.P045.pathDistance 3 false (cs.take k.val).toFinset (cs.get k) ≠ 0 := by
  classical
  have ht := repaired_nonzero_data hm
  have hp : (∏ i : Fin cs.length,
      centreDraw AronowAudit.P045.pathDistance 3 false (cs.take i.val).toFinset (cs.get i)) ≠ 0 := by
    simpa only [traceMass, if_pos ht] using hm
  intro hk
  exact hp (Finset.prod_eq_zero (Finset.mem_univ k) hk)

theorem repaired_kernel_support (S : Finset (Fin 4)) (v : Fin 4)
    (hf : centreDraw AronowAudit.P045.pathDistance 3 false S v ≠ 0) :
    centreDraw AronowAudit.P045.pathDistance 3 true S v ≠ 0 := by
  classical
  let R := (univ : Finset (Fin 4)) \ marked AronowAudit.P045.pathDistance 3 S
  simp only [centreDraw, Bool.false_eq_true, false_and, ↓reduceIte] at hf
  change (if v ∈ R then 1/(R.card : ℝ) else 0) ≠ 0 at hf
  change (if true = true ∧ R.card = 1 then
      let u := R.toList.head?.getD v
      if v.val ≤ u.val then (1 : ℝ)/(u.val+1 : ℕ) else 0
    else if v ∈ R then 1/(R.card : ℝ) else 0) ≠ 0
  by_cases hc : R.card = 1
  · obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hc
    have hv : v = u := by
      by_contra hv
      simp [hu,hv] at hf
    subst v
    simp [hu, Nat.cast_add, Nat.cast_one]
    positivity
  · simpa [hc] using hf

theorem repaired_classification (cs : List (Fin 4))
    (hm : traceMass AronowAudit.P045.pathDistance 3 false cs ≠ 0) :
    cs = [1] ∨ cs = [2] ∨ cs = [3,0] ∨ cs = [0,3] := by
  classical
  have ht := repaired_nonzero_data hm
  have hcode : traceMass AronowAudit.P045.pathDistance 3 true cs ≠ 0 := by
    rw [traceMass, if_pos ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact repaired_kernel_support _ _ (repaired_nonzero_draw hm k)
  rcases coded_classification cs hcode with h | h | h | ⟨r,j,hj,h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · subst cs
    have hR : (univ : Finset (Fin 4)) \ marked AronowAudit.P045.pathDistance 3 {0} = {3} := by decide
    cases r with
    | zero =>
      have hd := repaired_nonzero_draw hm
        (⟨1, by simp⟩ : Fin (List.replicate (0+1) (0 : Fin 4) ++ [j]).length)
      have hd' : centreDraw AronowAudit.P045.pathDistance 3 false {0} j ≠ 0 := by
        simpa [List.replicate_succ, List.get_eq_getElem] using hd
      have hj3 : j = 3 := by
        by_contra hj3
        simp [centreDraw,hR,hj3] at hd'
      simp [hj3, List.replicate_succ]
    | succ r =>
      have hd := repaired_nonzero_draw hm
        (⟨1, by simp⟩ : Fin (List.replicate (r + 1 + 1) (0 : Fin 4) ++ [j]).length)
      have hd' : centreDraw (AronowAudit.P045.pathDistance (n := 4)) 3 false {0} 0 ≠ 0 := by
        simpa [List.replicate_succ, List.get_eq_getElem] using hd
      norm_num [centreDraw,hR] at hd'

theorem repaired_trace_masses :
    traceMass (AronowAudit.P045.pathDistance (n := 4)) 3 false [1] = 1/4 ∧
    traceMass (AronowAudit.P045.pathDistance (n := 4)) 3 false [2] = 1/4 ∧
    traceMass (AronowAudit.P045.pathDistance (n := 4)) 3 false [3,0] = 1/4 ∧
    traceMass (AronowAudit.P045.pathDistance (n := 4)) 3 false [0,3] = 1/4 := by
  have hRe : (univ : Finset (Fin 4)) \ marked (AronowAudit.P045.pathDistance (n := 4)) 3 ∅ = univ := by decide
  have hR0 : (univ : Finset (Fin 4)) \ marked (AronowAudit.P045.pathDistance (n := 4)) 3 {0} = {3} := by decide
  have hR3 : (univ : Finset (Fin 4)) \ marked (AronowAudit.P045.pathDistance (n := 4)) 3 {3} = {0} := by decide
  have hdE (v : Fin 4) : centreDraw (AronowAudit.P045.pathDistance (n := 4)) 3 false ∅ v = 1/4 := by
    norm_num [centreDraw, hRe]
  have hd3 : centreDraw (AronowAudit.P045.pathDistance (n := 4)) 3 false {3} 0 = 1 := by
    norm_num [centreDraw, hR3]
  have hd0 : centreDraw (AronowAudit.P045.pathDistance (n := 4)) 3 false {0} 3 = 1 := by
    norm_num [centreDraw, hR0]
  have ht1 : (∀ k : Fin ([1] : List (Fin 4)).length,
      marked (AronowAudit.P045.pathDistance (n := 4)) 3 ([1].take k.val).toFinset ≠ univ) ∧
      marked (AronowAudit.P045.pathDistance (n := 4)) 3 [1].toFinset = univ := by decide
  have ht2 : (∀ k : Fin ([2] : List (Fin 4)).length,
      marked (AronowAudit.P045.pathDistance (n := 4)) 3 ([2].take k.val).toFinset ≠ univ) ∧
      marked (AronowAudit.P045.pathDistance (n := 4)) 3 [2].toFinset = univ := by decide
  have ht30 : (∀ k : Fin ([3,0] : List (Fin 4)).length,
      marked (AronowAudit.P045.pathDistance (n := 4)) 3 ([3,0].take k.val).toFinset ≠ univ) ∧
      marked (AronowAudit.P045.pathDistance (n := 4)) 3 [3,0].toFinset = univ := by decide
  have ht03 : (∀ k : Fin ([0,3] : List (Fin 4)).length,
      marked (AronowAudit.P045.pathDistance (n := 4)) 3 ([0,3].take k.val).toFinset ≠ univ) ∧
      marked (AronowAudit.P045.pathDistance (n := 4)) 3 [0,3].toFinset = univ := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold traceMass
    rw [if_pos ht1]
    norm_num [Fin.prod_univ_succ, hdE]
  · unfold traceMass
    rw [if_pos ht2]
    norm_num [Fin.prod_univ_succ, hdE]
  · unfold traceMass
    rw [if_pos ht30]
    simp only [List.length_cons, List.length_nil]
    norm_num [Fin.prod_univ_succ, hdE, hd3]
  · unfold traceMass
    rw [if_pos ht03]
    simp only [List.length_cons, List.length_nil]
    norm_num [Fin.prod_univ_succ, hdE, hd0]

theorem repaired_trace_formula (cs : List (Fin 4)) :
    traceMass AronowAudit.P045.pathDistance 3 false cs =
      (if cs = [1] then 1/4 else 0) + (if cs = [2] then 1/4 else 0) +
      (if cs = [3,0] then 1/4 else 0) + (if cs = [0,3] then 1/4 else 0) := by
  classical
  by_cases h1 : cs = [1]
  · subst cs; norm_num [repaired_trace_masses.1]
  by_cases h2 : cs = [2]
  · subst cs; norm_num [repaired_trace_masses.2.1]
  by_cases h30 : cs = [3,0]
  · subst cs; norm_num [repaired_trace_masses.2.2.1]
  by_cases h03 : cs = [0,3]
  · subst cs; norm_num [repaired_trace_masses.2.2.2]
  have hm : traceMass AronowAudit.P045.pathDistance 3 false cs = 0 := by
    by_contra hm
    rcases repaired_classification cs hm with h | h | h | h <;> contradiction
  simp only [hm, if_neg h1, if_neg h2, if_neg h30, if_neg h03, add_zero]

theorem fibre_inner (cs : List (Fin 4)) (S : Finset (Fin 4)) (t : ℕ) :
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = S then
      (if List.ofFn z = cs then (1/4 : ℝ) else 0) else 0) =
      if t = cs.length then (if cs.toFinset = S then 1/4 else 0) else 0 := by
  classical
  by_cases ht : t = cs.length
  · subst t
    let zcs : Fin cs.length → Fin 4 := cs.get
    have hcs : List.ofFn zcs = cs := List.ofFn_get cs
    rw [Fintype.sum_eq_single zcs]
    · simp [hcs]
    · intro z hz
      have hl : List.ofFn z ≠ cs := fun h => hz (List.ofFn_injective (h.trans hcs.symm))
      simp [hl]
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro z _
    have hl : List.ofFn z ≠ cs := by
      intro h
      exact ht (by simpa only [List.length_ofFn] using congrArg List.length h)
    simp [hl]

theorem repaired_inner (S : Finset (Fin 4)) (t : ℕ) :
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = S then
      traceMass AronowAudit.P045.pathDistance 3 false (List.ofFn z) else 0) =
      (if t = 1 then (if ({1} : Finset (Fin 4)) = S then 1/4 else 0) +
        (if ({2} : Finset (Fin 4)) = S then 1/4 else 0) else 0) +
      (if t = 2 then (if ({0,3} : Finset (Fin 4)) = S then 1/2 else 0) else 0) := by
  classical
  have hsplit (P : Prop) [Decidable P] (x y : ℝ) :
      (if P then x + y else 0) = (if P then x else 0) + (if P then y else 0) := by
    split_ifs <;> simp
  simp_rw [repaired_trace_formula, hsplit]
  simp only [Finset.sum_add_distrib, fibre_inner]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  have h30 : ({3,0} : Finset (Fin 4)) = {0,3} := by decide
  rw [h30]
  split_ifs <;> norm_num

theorem summable_geometric_tail :
    Summable (fun t : ℕ => if 2 ≤ t then (1/4 : ℝ)^t else 0) := by
  apply Summable.of_nonneg_of_le (f := fun t : ℕ => (1/4 : ℝ)^t) _ _
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  · intro t
    by_cases h : 2 ≤ t
    · simp [h] <;> positivity
    · simp [h] <;> positivity
  · intro t
    by_cases h : 2 ≤ t
    · simp [h] <;> positivity
    · simp [h] <;> positivity

theorem finite_at (n : ℕ) (c : ℝ) :
    Summable (fun t : ℕ => if t = n then c else 0) :=
  (hasSum_ite_eq n c).summable

end
end SAP.P045a.WH.W2.P.T10_L2

open SAP.P045a.WH.W2.P.T10_L2
open AronowAudit.P045.Wave1.ClusterSampler

theorem SAP.P045a.WH.W2.T10_L2_proof : SAP.P045a.WH.W2.T10_L2 := by
  classical
  intro coded S
  cases coded with
  | false =>
    have hinner (t : ℕ) := repaired_inner S t
    have hs1 : Summable (fun t : ℕ =>
        if t = 1 then (if ({1} : Finset (Fin 4)) = S then (1/4 : ℝ) else 0) else 0) :=
      finite_at 1 _
    have hs2 : Summable (fun t : ℕ =>
        if t = 1 then (if ({2} : Finset (Fin 4)) = S then (1/4 : ℝ) else 0) else 0) :=
      finite_at 1 _
    have hs3 : Summable (fun t : ℕ =>
        if t = 2 then (if ({0,3} : Finset (Fin 4)) = S then (1/2 : ℝ) else 0) else 0) :=
      finite_at 2 _
    have hsplit (P : Prop) [Decidable P] (x y : ℝ) :
        (if P then x + y else 0) = (if P then x else 0) + (if P then y else 0) := by
      split_ifs <;> simp
    have heq : SAP.P045a.fourPathLengthMass false S = fun t : ℕ =>
        (if t = 1 then (if ({1} : Finset (Fin 4)) = S then 1/4 else 0) else 0) +
        (if t = 1 then (if ({2} : Finset (Fin 4)) = S then 1/4 else 0) else 0) +
        (if t = 2 then (if ({0,3} : Finset (Fin 4)) = S then 1/2 else 0) else 0) := by
      funext t
      unfold SAP.P045a.fourPathLengthMass
      change (∑ z : Fin t → Fin 4,
        if (List.ofFn z).toFinset = S then
          traceMass AronowAudit.P045.pathDistance 3 false (List.ofFn z) else 0) = _
      rw [hinner t]
      rw [hsplit]
    rw [heq]
    exact (hs1.add hs2).add hs3
  | true =>
    let hc : TraceClassification := coded_classification
    let h6 : SingletonNetSums := n6_proof n4_proof hc
    let h7 : PairNetSums := n7_proof n4_proof hc
    by_cases hS : S ∈ ({{0,1},{0,2},{0,3},{1},{2}} : Finset (Finset (Fin 4)))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hS
      rcases hS with hS | hS | hS | hS | hS
      · subst S
        have hlength : SAP.P045a.fourPathLengthMass true {0,1} =
            fun t => if 2 ≤ t then (1/4 : ℝ)^t else 0 := by
          funext t
          exact coded_pair_inner 1 (by decide) (by decide) t
        rw [hlength]
        exact summable_geometric_tail
      · subst S
        have hlength : SAP.P045a.fourPathLengthMass true {0,2} =
            fun t => if 2 ≤ t then (1/4 : ℝ)^t else 0 := by
          funext t
          exact coded_pair_inner 2 (by decide) (by decide) t
        rw [hlength]
        exact summable_geometric_tail
      · subst S
        have hlength : (fun t : ℕ => SAP.P045a.fourPathLengthMass true {0,3} t) =
            fun t => (if t = 2 then (1/4 : ℝ) else 0) +
              (if 2 ≤ t then (1/4 : ℝ)^t else 0) := by
          funext t
          exact h7 t
        change Summable (fun t : ℕ => SAP.P045a.fourPathLengthMass true {0,3} t)
        rw [hlength]
        exact (finite_at 2 _).add summable_geometric_tail
      · subst S
        have hlength : (fun t : ℕ => SAP.P045a.fourPathLengthMass true {1} t) =
            fun t => if t = 1 then (1/4 : ℝ) else 0 := by
          funext t
          exact (h6 t).1
        change Summable (fun t : ℕ => SAP.P045a.fourPathLengthMass true {1} t)
        rw [hlength]
        exact finite_at 1 _
      · subst S
        have hlength : (fun t : ℕ => SAP.P045a.fourPathLengthMass true {2} t) =
            fun t => if t = 1 then (1/4 : ℝ) else 0 := by
          funext t
          exact (h6 t).2
        change Summable (fun t : ℕ => SAP.P045a.fourPathLengthMass true {2} t)
        rw [hlength]
        exact finite_at 1 _
    · exact (coded_off S hS).symm ▸ summable_zero
