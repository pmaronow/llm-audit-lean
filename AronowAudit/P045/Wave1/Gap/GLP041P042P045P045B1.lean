import AronowAudit.P045.Wave1.ClusterSampler.N3
import AronowAudit.P045.Wave1.ClusterSampler.N4
import AronowAudit.P045.Wave1.ClusterSampler.N5
import AronowAudit.P045.Wave1.ClusterSampler.N6
import AronowAudit.P045.Wave1.ClusterSampler.N7
import AronowAudit.P045.Wave1.ClusterSampler.N8

/-!
Exact four-path terminal and treatment laws for P045-T10.
-/

set_option autoImplicit false

namespace AronowAudit.P045.Wave1

open AronowAudit.P045 Finset
open scoped BigOperators

noncomputable section

private theorem p045t10_classify : ClusterSampler.TraceClassification :=
  ClusterSampler.n5_proof ClusterSampler.n3_proof

private theorem p045t10_net_masses :
    terminalCentres (pathDistance (n := 4)) 3 true {1} = 1/4 ∧
    terminalCentres (pathDistance (n := 4)) 3 true {2} = 1/4 ∧
    terminalCentres (pathDistance (n := 4)) 3 true {0,3} = 1/3 :=
  ClusterSampler.n8_proof
    (ClusterSampler.n6_proof ClusterSampler.n4_proof p045t10_classify)
    (ClusterSampler.n7_proof ClusterSampler.n4_proof p045t10_classify)

/-- The other two pairs have just one retry trace at each length at least two. -/
private theorem p045t10_pair_inner (a : Fin 4) (ha : a ≠ 0) (ha3 : a ≠ 3) (t : ℕ) :
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = ({0,a} : Finset (Fin 4)) then
      traceMass pathDistance 3 true (List.ofFn z) else 0) =
      if 2 ≤ t then (1/4 : ℝ)^t else 0 := by
  classical
  have hsupp : ∀ cs : List (Fin 4), cs.toFinset = {0,a} →
      traceMass pathDistance 3 true cs ≠ 0 →
      ∃ r : ℕ, cs = List.replicate (r+1) 0 ++ [a] := by
    intro cs hs hm
    have h0 : (0 : Fin 4) ∈ cs.toFinset := by rw [hs]; simp
    rcases p045t10_classify cs hm with h | h | h | ⟨r,j,hj,h⟩
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
    · rw [hretry, if_pos hset, four_path_repeat_trace_mass r a ha, if_pos (by omega)]
    · intro z hz
      by_cases hs : (List.ofFn z).toFinset = ({0,a} : Finset (Fin 4))
      · rw [if_pos hs]
        by_contra hm
        obtain ⟨s,heq⟩ := hsupp (List.ofFn z) hs hm
        have hlen : r+2 = s+2 := by
          simpa using congrArg List.length heq
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

private theorem p045t10_tail_sum :
    (∑' t : ℕ, if 2 ≤ t then (1/4 : ℝ)^t else 0) = 1/12 := by
  let g : ℕ → ℝ := fun t => if 2 ≤ t then (1/4 : ℝ)^t else 0
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le (f := fun t : ℕ => (1/4 : ℝ)^t) _ _
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    · intro t; dsimp [g]; split_ifs <;> positivity
    · intro t
      dsimp only [g]
      split_ifs
      · exact le_rfl
      · positivity
  have hshift : (∑' t : ℕ, g (t+2)) = 1/12 := by
    calc
      _ = ∑' t : ℕ, (1/4 : ℝ)^t * (1/4 : ℝ)^2 := by
        apply tsum_congr
        intro t
        simp only [g, if_pos (show 2 ≤ t+2 by omega), pow_add]
      _ = (∑' t : ℕ, (1/4 : ℝ)^t) * (1/4 : ℝ)^2 := tsum_mul_right
      _ = 1/12 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
  have hsplit := hg.sum_add_tsum_nat_add 2
  have hhead : (∑ t ∈ range 2, g t) = 0 := by norm_num [g, sum_range_succ]
  rw [hhead, hshift, zero_add] at hsplit
  exact hsplit.symm

private theorem p045t10_pair_mass (a : Fin 4) (ha : a ≠ 0) (ha3 : a ≠ 3) :
    terminalCentres pathDistance 3 true {0,a} = 1/12 := by
  unfold terminalCentres
  simp_rw [p045t10_pair_inner a ha ha3]
  exact p045t10_tail_sum

private theorem p045t10_coded_off (S : Finset (Fin 4))
    (hS : S ∉ ({{0,1},{0,2},{0,3},{1},{2}} : Finset (Finset (Fin 4)))) :
    terminalCentres pathDistance 3 true S = 0 := by
  classical
  unfold terminalCentres
  apply (tsum_congr _).trans (tsum_zero)
  intro t
  apply Finset.sum_eq_zero
  intro z _
  by_cases hs : (List.ofFn z).toFinset = S
  · rw [if_pos hs]
    by_contra hm
    apply hS
    rcases p045t10_classify (List.ofFn z) hm with h | h | h | ⟨r,j,hj,h⟩
    · simp [← hs,h]
    · simp [← hs,h]
    · have : S = ({0,3} : Finset (Fin 4)) := by simpa [h, Finset.pair_comm] using hs.symm
      simp [this]
    · have : S = ({0,j} : Finset (Fin 4)) := by
        simpa [h, List.toFinset_append,
          List.toFinset_replicate_of_ne_zero (by omega : r+1 ≠ 0)] using hs.symm
      fin_cases j <;> simp_all
  · exact if_neg hs

private theorem p045t10_coded_weighted (F : Finset (Fin 4) → ℝ) :
    (∑ S : Finset (Fin 4), terminalCentres pathDistance 3 true S * F S) =
      1/12 * F {0,1} + 1/12 * F {0,2} + 1/3 * F {0,3} +
      1/4 * F {1} + 1/4 * F {2} := by
  classical
  have hs : (∑ S : Finset (Fin 4), terminalCentres pathDistance 3 true S * F S) =
      ∑ S ∈ ({{0,1},{0,2},{0,3},{1},{2}} : Finset (Finset (Fin 4))),
        terminalCentres pathDistance 3 true S * F S := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro S _ hS
    rw [p045t10_coded_off S hS, zero_mul]
  rw [hs]
  rw [Finset.sum_insert (by decide : ({0,1} : Finset (Fin 4)) ∉
      ({{0,2},{0,3},{1},{2}} : Finset (Finset (Fin 4)))),
    Finset.sum_insert (by decide : ({0,2} : Finset (Fin 4)) ∉
      ({{0,3},{1},{2}} : Finset (Finset (Fin 4)))),
    Finset.sum_insert (by decide : ({0,3} : Finset (Fin 4)) ∉
      ({{1},{2}} : Finset (Finset (Fin 4)))),
    Finset.sum_insert (by decide : ({1} : Finset (Fin 4)) ∉
      ({{2}} : Finset (Finset (Fin 4)))),
    Finset.sum_singleton]
  norm_num [p045t10_pair_mass 1 (by decide) (by decide),
    p045t10_pair_mass 2 (by decide) (by decide), p045t10_net_masses.1,
    p045t10_net_masses.2.1, p045t10_net_masses.2.2]
  ring

/-- Every supported repaired transition is also supported by the coded kernel. -/
private theorem p045t10_kernel_support (S : Finset (Fin 4)) (v : Fin 4)
    (hf : centreDraw pathDistance 3 false S v ≠ 0) :
    centreDraw pathDistance 3 true S v ≠ 0 := by
  classical
  let R := (univ : Finset (Fin 4)) \ marked pathDistance 3 S
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

private theorem p045t10_nonzero_data (coded : Bool) {cs : List (Fin 4)}
    (hm : traceMass pathDistance 3 coded cs ≠ 0) :
    (∀ k : Fin cs.length, marked pathDistance 3 (cs.take k.val).toFinset ≠ univ) ∧
      marked pathDistance 3 cs.toFinset = univ := by
  by_contra ht
  exact hm (by simp only [traceMass, if_neg ht])

private theorem p045t10_nonzero_draw (coded : Bool) {cs : List (Fin 4)}
    (hm : traceMass pathDistance 3 coded cs ≠ 0) (k : Fin cs.length) :
    centreDraw pathDistance 3 coded (cs.take k.val).toFinset (cs.get k) ≠ 0 := by
  classical
  have ht := p045t10_nonzero_data coded hm
  have hp : (∏ i : Fin cs.length,
      centreDraw pathDistance 3 coded (cs.take i.val).toFinset (cs.get i)) ≠ 0 := by
    simpa only [traceMass, if_pos ht] using hm
  intro hk
  exact hp (Finset.prod_eq_zero (Finset.mem_univ k) hk)

private theorem p045t10_repaired_classify (cs : List (Fin 4))
    (hm : traceMass pathDistance 3 false cs ≠ 0) :
    cs = [1] ∨ cs = [2] ∨ cs = [3,0] ∨ cs = [0,3] := by
  classical
  have ht := p045t10_nonzero_data false hm
  have hcode : traceMass pathDistance 3 true cs ≠ 0 := by
    rw [traceMass, if_pos ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact p045t10_kernel_support _ _ (p045t10_nonzero_draw false hm k)
  rcases p045t10_classify cs hcode with h | h | h | ⟨r,j,hj,h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · subst cs
    have hR : (univ : Finset (Fin 4)) \ marked pathDistance 3 {0} = {3} := by decide
    cases r with
    | zero =>
      have hd := p045t10_nonzero_draw false hm (⟨1, by simp⟩ : Fin 2)
      have hd' : centreDraw pathDistance 3 false {0} j ≠ 0 := by
        simpa [List.replicate_succ, List.get_eq_getElem] using hd
      have hj3 : j = 3 := by
        by_contra hj3
        simp [centreDraw,hR,hj3] at hd'
      simp [hj3, List.replicate_succ]
    | succ r =>
      have hd := p045t10_nonzero_draw false hm
        (⟨1, by simp⟩ : Fin (List.replicate (r + 1 + 1) (0 : Fin 4) ++ [j]).length)
      have hd' : centreDraw (pathDistance (n := 4)) 3 false {0} 0 ≠ 0 := by
        simpa [List.replicate_succ, List.get_eq_getElem] using hd
      norm_num [centreDraw,hR] at hd'


private theorem p045t10_repaired_trace_masses :
    traceMass (pathDistance (n := 4)) 3 false [1] = 1/4 ∧
    traceMass (pathDistance (n := 4)) 3 false [2] = 1/4 ∧
    traceMass (pathDistance (n := 4)) 3 false [3,0] = 1/4 ∧
    traceMass (pathDistance (n := 4)) 3 false [0,3] = 1/4 := by
  have hRe : (univ : Finset (Fin 4)) \ marked pathDistance 3 ∅ = univ := by decide
  have hR0 : (univ : Finset (Fin 4)) \ marked pathDistance 3 {0} = {3} := by decide
  have hR3 : (univ : Finset (Fin 4)) \ marked pathDistance 3 {3} = {0} := by decide
  have hm3 : marked (pathDistance (n := 4)) 3 {3} = {1,2,3} := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    unfold traceMass
    rw [if_pos (by decide)]
    simp only [List.length_cons, List.length_nil]
    norm_num [Fin.prod_univ_succ, centreDraw, hRe, hR0, hR3,
      four_path_marking_certificate.1, four_path_marking_certificate.2.1, hm3] <;> decide

private theorem p045t10_repaired_trace_formula (cs : List (Fin 4)) :
    traceMass pathDistance 3 false cs =
      (if cs = [1] then 1/4 else 0) + (if cs = [2] then 1/4 else 0) +
      (if cs = [3,0] then 1/4 else 0) + (if cs = [0,3] then 1/4 else 0) := by
  classical
  by_cases h1 : cs = [1]
  · subst cs; norm_num [p045t10_repaired_trace_masses.1]
  by_cases h2 : cs = [2]
  · subst cs; norm_num [p045t10_repaired_trace_masses.2.1]
  by_cases h30 : cs = [3,0]
  · subst cs; norm_num [p045t10_repaired_trace_masses.2.2.1]
  by_cases h03 : cs = [0,3]
  · subst cs; norm_num [p045t10_repaired_trace_masses.2.2.2]
  have hm : traceMass pathDistance 3 false cs = 0 := by
    by_contra hm
    rcases p045t10_repaired_classify cs hm with h | h | h | h <;> contradiction
  simp only [hm, if_neg h1, if_neg h2, if_neg h30, if_neg h03, add_zero]

/-- A specified list has exactly one array representation at its own length. -/
private theorem p045t10_fibre_inner (cs : List (Fin 4)) (S : Finset (Fin 4)) (t : ℕ) :
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

private theorem p045t10_repaired_inner (S : Finset (Fin 4)) (t : ℕ) :
    (∑ z : Fin t → Fin 4, if (List.ofFn z).toFinset = S then
      traceMass pathDistance 3 false (List.ofFn z) else 0) =
      (if t = 1 then (if ({1} : Finset (Fin 4)) = S then 1/4 else 0) +
        (if ({2} : Finset (Fin 4)) = S then 1/4 else 0) else 0) +
      (if t = 2 then (if ({0,3} : Finset (Fin 4)) = S then 1/2 else 0) else 0) := by
  classical
  have hsplit (P : Prop) [Decidable P] (x y : ℝ) :
      (if P then x + y else 0) = (if P then x else 0) + (if P then y else 0) := by
    split_ifs <;> simp
  simp_rw [p045t10_repaired_trace_formula, hsplit]
  simp only [Finset.sum_add_distrib, p045t10_fibre_inner]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  have h30 : ({3,0} : Finset (Fin 4)) = {0,3} := by decide
  rw [h30]
  split_ifs <;> norm_num

private theorem p045t10_repaired_table (S : Finset (Fin 4)) :
    terminalCentres pathDistance 3 false S =
      (if S = {1} then 1/4 else 0) + (if S = {2} then 1/4 else 0) +
      (if S = {0,3} then 1/2 else 0) := by
  classical
  unfold terminalCentres
  simp_rw [p045t10_repaired_inner S]
  rw [((hasSum_ite_eq 1 _).summable).tsum_add (hasSum_ite_eq 2 _).summable,
    (hasSum_ite_eq 1 _).tsum_eq, (hasSum_ite_eq 2 _).tsum_eq]
  simp only [eq_comm]

private theorem p045t10_repaired_weighted (F : Finset (Fin 4) → ℝ) :
    (∑ S : Finset (Fin 4), terminalCentres pathDistance 3 false S * F S) =
      1/4 * F {1} + 1/4 * F {2} + 1/2 * F {0,3} := by
  classical
  simp_rw [p045t10_repaired_table, add_mul, ite_mul, zero_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The list representation of `{0, a}` is `[0, a]` or `[a, 0]` when `a ≠ 0`. -/
private theorem p045t10_pair_toList (a : Fin 4) (ha : a ≠ 0) :
    ({0,a} : Finset (Fin 4)).toList = [0,a] ∨
    ({0,a} : Finset (Fin 4)).toList = [a,0] := by
  apply List.perm_pair.mp
  simpa only [Finset.toList_singleton] using
    (Finset.toList_insert (s := ({a} : Finset (Fin 4))) (by simpa using Ne.symm ha))

private theorem p045t10_nearest_pairs (v : Fin 4) :
    nearestCentre pathDistance {0,1} v = some (if v = 0 then 0 else 1) ∧
    nearestCentre pathDistance {0,2} v = some (if v.val < 2 then 0 else 2) ∧
    nearestCentre pathDistance {0,3} v = some (if v.val < 2 then 0 else 3) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases p045t10_pair_toList 1 (by decide) with h | h <;>
      rw [nearestCentre, h] <;> fin_cases v <;>
      simp +decide [List.mergeSort, List.MergeSort.Internal.splitInTwo]
  · rcases p045t10_pair_toList 2 (by decide) with h | h <;>
      rw [nearestCentre, h] <;> fin_cases v <;>
      simp +decide [List.mergeSort, List.MergeSort.Internal.splitInTwo]
  · rcases p045t10_pair_toList 3 (by decide) with h | h <;>
      rw [nearestCentre, h] <;> fin_cases v <;>
      simp +decide [List.mergeSort, List.MergeSort.Internal.splitInTwo]

private theorem p045t10_nearest_single (a v : Fin 4) :
    nearestCentre pathDistance {a} v = some a := by
  simp [nearestCentre]


/-- Independence of the two distinct centre coins, with unused coins integrated out. -/
private theorem p045t10_two_coins (i j : Fin 4) (hij : i ≠ j) (A B : Bool → Prop)
    [DecidablePred A] [DecidablePred B] :
    prob (bernoulli (1/2)) (fun c : Assignment 4 => A (c i) ∧ B (c j)) =
      ((if A true then (1/2 : ℝ) else 0) + (if A false then 1/2 else 0)) *
      ((if B true then (1/2 : ℝ) else 0) + (if B false then 1/2 else 0)) := by
  classical
  let q : Bool → ℝ := fun b => if b then 1/2 else 1 - 1/2
  let X : Bool → ℝ := fun b => if A b then 1 else 0
  let Y : Bool → ℝ := fun b => if B b then 1 else 0
  have hq : ∑ b, q b = 1 := by norm_num [q, Fintype.univ_bool]
  have hXY : prob (bernoulli (1/2)) (fun c : Assignment 4 => A (c i) ∧ B (c j)) =
      expect (bernoulli (1/2)) (fun c => X (c i) * Y (c j)) := by
    unfold prob
    congr 1
    funext c
    by_cases hA : A (c i) <;> by_cases hB : B (c j) <;> simp [X, Y, hA, hB]
  rw [hXY]
  change expect (fun c : Fin 4 → Bool => ∏ g, q (c g)) (fun c => X (c i) * Y (c j)) = _
  rw [independent_pair_expect q hq i j hij X Y]
  norm_num [expect, q, X, Y, Fintype.univ_bool, mul_ite]

private theorem p045t10_coin_single (a : Fin 4) (z : Assignment 4) :
    clusterProb pathDistance {a} (1/2) z =
      if z 0 = z 1 ∧ z 1 = z 2 ∧ z 2 = z 3 then 1/2 else 0 := by
  classical
  let F : Bool → ℝ := fun b => if ∀ v : Fin 4, z v = b then 1 else 0
  have h : clusterProb pathDistance {a} (1/2) z =
      expect (bernoulli (1/2)) (fun c : Assignment 4 => F (c a)) := by
    unfold clusterProb prob
    congr 1
    funext c
    simp [F, p045t10_nearest_single]
  rw [h, bernoulli_coordinate_expect]
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> cases h3 : z 3 <;>
    norm_num [F, Fin.forall_fin_succ, h0, h1, h2, h3]

private theorem p045t10_coin_01 (z : Assignment 4) :
    clusterProb pathDistance {0,1} (1/2) z =
      if z 1 = z 2 ∧ z 2 = z 3 then 1/4 else 0 := by
  classical
  have he : (fun c : Assignment 4 => ∀ v, ∃ s,
      nearestCentre pathDistance {0,1} v = some s ∧ z v = c s) =
      (fun c => z 0 = c 0 ∧ (z 1 = c 1 ∧ z 2 = c 1 ∧ z 3 = c 1)) := by
    funext c
    simp_rw [(p045t10_nearest_pairs _).1]
    simp [Fin.forall_fin_succ]
  unfold clusterProb
  rw [he, p045t10_two_coins 0 1 (by decide)
    (fun b => z 0 = b) (fun b => z 1 = b ∧ z 2 = b ∧ z 3 = b)]
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> cases h3 : z 3 <;>
    norm_num [h0, h1, h2, h3]

private theorem p045t10_coin_02 (z : Assignment 4) :
    clusterProb pathDistance {0,2} (1/2) z =
      if z 0 = z 1 ∧ z 2 = z 3 then 1/4 else 0 := by
  classical
  have he : (fun c : Assignment 4 => ∀ v, ∃ s,
      nearestCentre pathDistance {0,2} v = some s ∧ z v = c s) =
      (fun c => (z 0 = c 0 ∧ z 1 = c 0) ∧ (z 2 = c 2 ∧ z 3 = c 2)) := by
    funext c
    simp_rw [(p045t10_nearest_pairs _).2.1]
    simp [Fin.forall_fin_succ, and_assoc]
  unfold clusterProb
  rw [he, p045t10_two_coins 0 2 (by decide)
    (fun b => z 0 = b ∧ z 1 = b) (fun b => z 2 = b ∧ z 3 = b)]
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> cases h3 : z 3 <;>
    norm_num [h0, h1, h2, h3]

private theorem p045t10_coin_03 (z : Assignment 4) :
    clusterProb pathDistance {0,3} (1/2) z =
      if z 0 = z 1 ∧ z 2 = z 3 then 1/4 else 0 := by
  classical
  have he : (fun c : Assignment 4 => ∀ v, ∃ s,
      nearestCentre pathDistance {0,3} v = some s ∧ z v = c s) =
      (fun c => (z 0 = c 0 ∧ z 1 = c 0) ∧ (z 2 = c 3 ∧ z 3 = c 3)) := by
    funext c
    simp_rw [(p045t10_nearest_pairs _).2.2]
    simp [Fin.forall_fin_succ, and_assoc]
  unfold clusterProb
  rw [he, p045t10_two_coins 0 3 (by decide)
    (fun b => z 0 = b ∧ z 1 = b) (fun b => z 2 = b ∧ z 3 = b)]
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> cases h3 : z 3 <;>
    norm_num [h0, h1, h2, h3]

private theorem p045t10_coded_treatment (z : Assignment 4) :
    clusteredTreatment pathDistance true (1/2) z =
      (if z 0 = z 1 ∧ z 1 = z 2 ∧ z 2 = z 3 then 1/4 else 0) +
      (if z 1 = z 2 ∧ z 2 = z 3 then 1/48 else 0) +
      (if z 0 = z 1 ∧ z 2 = z 3 then 5/48 else 0) := by
  classical
  unfold clusteredTreatment
  rw [p045t10_coded_weighted, p045t10_coin_01, p045t10_coin_02,
    p045t10_coin_03, p045t10_coin_single, p045t10_coin_single]
  split_ifs <;> norm_num

private theorem p045t10_repaired_treatment (z : Assignment 4) :
    clusteredTreatment pathDistance false (1/2) z =
      (if z 0 = z 1 ∧ z 1 = z 2 ∧ z 2 = z 3 then 1/4 else 0) +
      (if z 0 = z 1 ∧ z 2 = z 3 then 1/8 else 0) := by
  classical
  unfold clusteredTreatment
  rw [p045t10_repaired_weighted, p045t10_coin_03,
    p045t10_coin_single, p045t10_coin_single]
  split_ifs <;> norm_num


private theorem p045t10_coded_total :
    (∑ S : Finset (Fin 4), terminalCentres pathDistance 3 true S) = 1 := by
  have h := p045t10_coded_weighted (fun _ => 1)
  norm_num at h
  exact h

private theorem p045t10_failure_probability :
    prob (terminalCentres (pathDistance (n := 4)) 3 true)
      (fun S => ¬separated pathDistance 3 S) = 1/6 := by
  classical
  have h01 : ¬separated (pathDistance (n := 4)) 3 {0,1} := by decide
  have h02 : ¬separated (pathDistance (n := 4)) 3 {0,2} := by decide
  have h03 : separated (pathDistance (n := 4)) 3 {0,3} := by decide
  have h1 : separated (pathDistance (n := 4)) 3 {1} := by decide
  have h2 : separated (pathDistance (n := 4)) 3 {2} := by decide
  unfold prob expect
  rw [p045t10_coded_weighted]
  norm_num [h01, h02, h03, h1, h2]

private theorem p045t10_coded_off_vector (z : Assignment 4)
    (hz : z ∉ ({![false,false,false,false], ![true,true,true,true],
      ![true,true,false,false], ![false,false,true,true],
      ![true,false,false,false], ![false,true,true,true]} : Finset (Assignment 4))) :
    clusteredTreatment pathDistance true (1/2) z = 0 := by
  classical
  have he : z = ![z 0, z 1, z 2, z 3] := by
    ext i
    fin_cases i <;> rfl
  have hz' : ![z 0, z 1, z 2, z 3] ∉
      ({![false,false,false,false], ![true,true,true,true],
        ![true,true,false,false], ![false,false,true,true],
        ![true,false,false,false], ![false,true,true,true]} : Finset (Assignment 4)) := by
    rwa [← he]
  rw [p045t10_coded_treatment]
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> cases h3 : z 3 <;>
    (norm_num [h0, h1, h2, h3] at hz' <;> norm_num [h0, h1, h2, h3])

/-- P045-T10: the exact coded and repaired four-path sampler laws. -/
theorem cluster_sampler_counterexample_proof :
    let d := pathDistance (n := 4)
    terminalCentres d 3 true {0,1} = 1/12 ∧
    terminalCentres d 3 true {0,2} = 1/12 ∧
    terminalCentres d 3 true {0,3} = 1/3 ∧
    terminalCentres d 3 true {1} = 1/4 ∧
    terminalCentres d 3 true {2} = 1/4 ∧
    (∑ S : Finset (Fin 4), terminalCentres d 3 true S) = 1 ∧
    prob (terminalCentres d 3 true) (fun S => ¬separated d 3 S) = 1/6 ∧
    clusteredTreatment d true (1/2) ![false,false,false,false] = 3/8 ∧
    clusteredTreatment d true (1/2) ![true,true,true,true] = 3/8 ∧
    clusteredTreatment d true (1/2) ![true,true,false,false] = 5/48 ∧
    clusteredTreatment d true (1/2) ![false,false,true,true] = 5/48 ∧
    clusteredTreatment d true (1/2) ![true,false,false,false] = 1/48 ∧
    clusteredTreatment d true (1/2) ![false,true,true,true] = 1/48 ∧
    (∀ z : Assignment 4, z ∉ ({![false,false,false,false], ![true,true,true,true],
      ![true,true,false,false], ![false,false,true,true], ![true,false,false,false], ![false,true,true,true]} : Finset (Assignment 4)) →
      clusteredTreatment d true (1/2) z = 0) ∧
    terminalCentres d 3 false {0,3} = 1/2 ∧
    terminalCentres d 3 false {1} = 1/4 ∧
    terminalCentres d 3 false {2} = 1/4 ∧
    clusteredTreatment d false (1/2) ![false,false,false,false] = 3/8 ∧
    clusteredTreatment d false (1/2) ![true,true,true,true] = 3/8 ∧
    clusteredTreatment d false (1/2) ![true,true,false,false] = 1/8 ∧
    clusteredTreatment d false (1/2) ![false,false,true,true] = 1/8 ∧
    clusteredTreatment d false (1/2) ![true,false,false,false] = 0 ∧
    clusteredTreatment d false (1/2) ![false,true,true,true] = 0 := by
  classical
  dsimp only
  refine ⟨p045t10_pair_mass 1 (by decide) (by decide),
    p045t10_pair_mass 2 (by decide) (by decide), p045t10_net_masses.2.2,
    p045t10_net_masses.1, p045t10_net_masses.2.1,
    p045t10_coded_total, p045t10_failure_probability, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, p045t10_coded_off_vector,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    norm_num [p045t10_coded_treatment, p045t10_repaired_table, p045t10_repaired_treatment] <;>
      simp +decide

end

end AronowAudit.P045.Wave1
