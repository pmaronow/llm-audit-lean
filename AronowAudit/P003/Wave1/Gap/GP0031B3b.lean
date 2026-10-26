import AronowAudit.P003.P003_Audit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
Corrected lattice filling and the interval-length bound.
The marked-unit identities act directly on the binomial count weights.
-/

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

private lemma GP0031B3b_mem_randomStates_iff (v q : Counts) (m : ℕ) :
    q ∈ randomStates v m ↔
      q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = m := by
  constructor
  · exact random_state_facts v m q
  · rintro ⟨ha,hb,hc,hd,ht⟩
    have hsum : q.a+q.b+q.c+q.d = m := ht
    have he : m-q.a-q.b-q.c = q.d := by omega
    simp only [randomStates,List.mem_flatMap,List.mem_filterMap,List.mem_range]
    refine ⟨q.a,?_,q.b,?_,q.c,?_,?_⟩
    · omega
    · omega
    · omega
    · simp only [he,if_pos hd]

/-- Disjoint blocks can be recognized by a tag on each of their elements. -/
private lemma GP0031B3b_tagged_flatMap_nodup {A B : Type*} (xs : List A)
    (f : A → List B) (tag : B → A) (hx : xs.Nodup)
    (hf : ∀ a ∈ xs, (f a).Nodup)
    (htag : ∀ a, ∀ b ∈ f a, tag b = a) :
    (xs.flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨hf,?_⟩
  apply hx.imp
  intro a b hab q hqa hqb
  exact hab ((htag a q hqa).symm.trans (htag b q hqb))

private lemma GP0031B3b_randomStates_nodup (v : Counts) (m : ℕ) :
    (randomStates v m).Nodup := by
  let block (a b : ℕ) : List Counts :=
    (List.range (min v.c (m-a-b)+1)).filterMap fun c =>
      if m-a-b-c ≤ v.d then some ⟨a,b,c,m-a-b-c⟩ else none
  have hblock (a b : ℕ) : (block a b).Nodup := by
    apply List.Nodup.filterMap (l := List.range (min v.c (m-a-b)+1))
      (f := fun c => if m-a-b-c ≤ v.d then
        some (⟨a,b,c,m-a-b-c⟩ : Counts) else none)
    · intro c c' q hc hc'
      change (if m-a-b-c ≤ v.d then
        some (⟨a,b,c,m-a-b-c⟩ : Counts) else none) = some q at hc
      change (if m-a-b-c' ≤ v.d then
        some (⟨a,b,c',m-a-b-c'⟩ : Counts) else none) = some q at hc'
      by_cases hd : m-a-b-c ≤ v.d
      · by_cases hd' : m-a-b-c' ≤ v.d
        · simp only [if_pos hd,Option.some.injEq] at hc
          simp only [if_pos hd',Option.some.injEq] at hc'
          have he := congrArg Counts.c (hc.trans hc'.symm)
          exact he
        · simp [hd'] at hc'
      · simp [hd] at hc
    · exact List.nodup_range
  have htag (a b : ℕ) (q : Counts) (hq : q ∈ block a b) :
      q.a = a ∧ q.b = b := by
    simp only [block,List.mem_filterMap] at hq
    obtain ⟨c,hc,hret⟩ := hq
    by_cases hd : m-a-b-c ≤ v.d
    · simp only [if_pos hd,Option.some.injEq] at hret
      subst q
      exact ⟨rfl,rfl⟩
    · simp [hd] at hret
  have hinner (a : ℕ) :
      ((List.range (min v.b (m-a)+1)).flatMap (block a)).Nodup := by
    apply GP0031B3b_tagged_flatMap_nodup _ _ Counts.b (List.nodup_range)
    · intro b hb
      exact hblock a b
    · intro b q hq
      exact (htag a b q hq).2
  change ((List.range (min v.a m+1)).flatMap fun a =>
    (List.range (min v.b (m-a)+1)).flatMap (block a)).Nodup
  apply GP0031B3b_tagged_flatMap_nodup _ _ Counts.a (List.nodup_range)
  · intro a ha
    exact hinner a
  · intro a q hq
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    exact (htag a b q hq).1

private def GP0031B3b_get (v : Counts) : Fin 4 → ℕ := ![v.a,v.b,v.c,v.d]
private def GP0031B3b_pack (f : Fin 4 → ℕ) : Counts := ⟨f 0,f 1,f 2,f 3⟩
private lemma GP0031B3b_get_pack (f : Fin 4 → ℕ) (i : Fin 4) :
    GP0031B3b_get (GP0031B3b_pack f) i = f i := by
  fin_cases i <;> rfl
private lemma GP0031B3b_coord_ext (q r : Counts)
    (h : ∀ i, GP0031B3b_get q i = GP0031B3b_get r i) : q = r := by
  exact Counts.ext (h 0) (h 1) (h 2) (h 3)
private def GP0031B3b_inc (v : Counts) (i : Fin 4) : Counts :=
  GP0031B3b_pack (fun j => GP0031B3b_get v j + if j = i then 1 else 0)
private def GP0031B3b_dec (v : Counts) (i : Fin 4) : Counts :=
  GP0031B3b_pack (fun j => GP0031B3b_get v j - if j = i then 1 else 0)
private lemma GP0031B3b_get_inc (v : Counts) (i j : Fin 4) :
    GP0031B3b_get (GP0031B3b_inc v i) j = GP0031B3b_get v j + if j = i then 1 else 0 :=
  GP0031B3b_get_pack _ _
private lemma GP0031B3b_get_dec (v : Counts) (i j : Fin 4) :
    GP0031B3b_get (GP0031B3b_dec v i) j = GP0031B3b_get v j - if j = i then 1 else 0 :=
  GP0031B3b_get_pack _ _
private lemma GP0031B3b_inc_total (v : Counts) (i : Fin 4) :
    (GP0031B3b_inc v i).total = v.total + 1 := by
  fin_cases i <;> simp [GP0031B3b_inc, GP0031B3b_pack, GP0031B3b_get, Counts.total] <;> omega
private lemma GP0031B3b_dec_total (v : Counts) (i : Fin 4)
    (hi : 0 < GP0031B3b_get v i) :
    (GP0031B3b_dec v i).total = v.total - 1 := by
  fin_cases i <;> simp_all [GP0031B3b_dec, GP0031B3b_pack, GP0031B3b_get, Counts.total] <;> omega
private lemma GP0031B3b_dec_inc (v : Counts) (i : Fin 4) :
    GP0031B3b_dec (GP0031B3b_inc v i) i = v := by
  apply GP0031B3b_coord_ext
  intro j
  simp only [GP0031B3b_get_dec, GP0031B3b_get_inc, Nat.add_sub_cancel]
private lemma GP0031B3b_inc_dec (v : Counts) (i : Fin 4)
    (hi : 0 < GP0031B3b_get v i) :
    GP0031B3b_inc (GP0031B3b_dec v i) i = v := by
  apply GP0031B3b_coord_ext
  intro j
  simp only [GP0031B3b_get_dec, GP0031B3b_get_inc]
  split_ifs with h
  · subst j; omega
  · omega
private lemma GP0031B3b_mem_coord (v q : Counts) (m : ℕ) :
    q ∈ randomStates v m ↔
      (∀ i, GP0031B3b_get q i ≤ GP0031B3b_get v i) ∧ q.total = m := by
  rw [GP0031B3b_mem_randomStates_iff]
  constructor
  · rintro ⟨ha,hb,hc,hd,ht⟩
    refine ⟨?_,ht⟩
    intro i; fin_cases i <;> assumption
  · rintro ⟨h,ht⟩
    exact ⟨h 0,h 1,h 2,h 3,ht⟩
private lemma GP0031B3b_mem_inc (v q : Counts) (m : ℕ) (i : Fin 4)
    (hi : 0 < GP0031B3b_get v i) (hm : 0 < m) :
    GP0031B3b_inc q i ∈ randomStates v m ↔
      q ∈ randomStates (GP0031B3b_dec v i) (m-1) := by
  rw [GP0031B3b_mem_coord, GP0031B3b_mem_coord, GP0031B3b_inc_total]
  simp only [GP0031B3b_get_inc, GP0031B3b_get_dec]
  constructor
  · rintro ⟨h,ht⟩
    refine ⟨?_,by omega⟩
    intro j
    have hj := h j
    split_ifs at * <;> omega
  · rintro ⟨h,ht⟩
    refine ⟨?_,by omega⟩
    intro j
    have hj := h j
    split_ifs with he
    · subst j
      simp only [ite_true] at hj
      omega
    · simpa [he] using hj

private lemma GP0031B3b_weight_mark (v q : Counts) (i : Fin 4)
    (hi : 0 < GP0031B3b_get v i) :
    multiplicity v (GP0031B3b_inc q i) * GP0031B3b_get (GP0031B3b_inc q i) i =
      GP0031B3b_get v i * multiplicity (GP0031B3b_dec v i) q := by
  have h (a b : ℕ) (ha : 0 < a) : a.choose (b+1) * (b+1) = a * (a-1).choose b := by
    have hh := Nat.add_one_mul_choose_eq (a-1) b
    simpa [Nat.sub_add_cancel ha] using hh.symm
  fin_cases i
  all_goals simp_all [GP0031B3b_get, GP0031B3b_inc, GP0031B3b_dec, GP0031B3b_pack,
    multiplicity, binomial_eq_choose]
  · convert congrArg (fun z => z * v.b.choose q.b * v.c.choose q.c * v.d.choose q.d)
      (h v.a q.a hi) using 1 <;> ring
  · convert congrArg (fun z => z * v.a.choose q.a * v.c.choose q.c * v.d.choose q.d)
      (h v.b q.b hi) using 1 <;> ring
  · convert congrArg (fun z => z * v.a.choose q.a * v.b.choose q.b * v.d.choose q.d)
      (h v.c q.c hi) using 1 <;> ring
  · convert congrArg (fun z => z * v.a.choose q.a * v.b.choose q.b * v.c.choose q.c)
      (h v.d q.d hi) using 1 <;> ring

private lemma GP0031B3b_sum_mark (v : Counts) (m : ℕ) (i : Fin 4)
    (hi : 0 < GP0031B3b_get v i) (hm : 0 < m) (F : Counts → ℝ) :
    (∑ q ∈ (randomStates v m).toFinset,
      (multiplicity v q : ℝ) * GP0031B3b_get q i * F q) =
      (GP0031B3b_get v i : ℝ) *
        ∑ q ∈ (randomStates (GP0031B3b_dec v i) (m-1)).toFinset,
          (multiplicity (GP0031B3b_dec v i) q : ℝ) * F (GP0031B3b_inc q i) := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ q ∈ (randomStates v m).toFinset.filter (fun q => 0 < GP0031B3b_get q i),
        (multiplicity v q : ℝ) * GP0031B3b_get q i * F q := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q hq hn
      have hz : GP0031B3b_get q i = 0 := by
        simpa only [Finset.mem_filter, hq, true_and, not_lt, Nat.le_zero] using hn
      simp only [hz, Nat.cast_zero, mul_zero, zero_mul]
    _ = _ := by
      apply Finset.sum_bij (fun q _ => GP0031B3b_dec q i)
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hq,hqi⟩
        apply List.mem_toFinset.mpr
        apply (GP0031B3b_mem_inc v (GP0031B3b_dec q i) m i hi hm).mp
        simpa only [GP0031B3b_inc_dec q i hqi] using List.mem_toFinset.mp hq
      · intro q hq r hr he
        have hqpos := (Finset.mem_filter.mp hq).2
        have hrpos := (Finset.mem_filter.mp hr).2
        have hh := congrArg (fun z => GP0031B3b_inc z i) he
        simpa only [GP0031B3b_inc_dec q i hqpos, GP0031B3b_inc_dec r i hrpos] using hh
      · intro q hq
        refine ⟨GP0031B3b_inc q i, ?_, GP0031B3b_dec_inc q i⟩
        apply Finset.mem_filter.mpr
        constructor
        · apply List.mem_toFinset.mpr
          exact (GP0031B3b_mem_inc v q m i hi hm).mpr (List.mem_toFinset.mp hq)
        · simp only [GP0031B3b_get_inc, ite_true]; omega
      · intro q hq
        have hqi := (Finset.mem_filter.mp hq).2
        have he := GP0031B3b_weight_mark v (GP0031B3b_dec q i) i hi
        rw [GP0031B3b_inc_dec q i hqi] at he
        rw [GP0031B3b_inc_dec q i hqi]
        have heR : (multiplicity v q : ℝ) * GP0031B3b_get q i =
            (GP0031B3b_get v i : ℝ) * multiplicity (GP0031B3b_dec v i) (GP0031B3b_dec q i) :=
          by exact_mod_cast he
        rw [heR]
        ring

private lemma GP0031B3b_mem_dec (v q : Counts) (m : ℕ) (i : Fin 4)
    (hi : 0 < GP0031B3b_get v i) :
    q ∈ randomStates (GP0031B3b_dec v i) m ↔
      q ∈ randomStates v m ∧ GP0031B3b_get q i < GP0031B3b_get v i := by
  simp only [GP0031B3b_mem_coord, GP0031B3b_get_dec]
  constructor
  · rintro ⟨h,ht⟩
    refine ⟨⟨?_,ht⟩,?_⟩
    · intro j
      have hh := h j
      split_ifs at hh <;> omega
    · have hh := h i
      simp only [ite_true] at hh
      omega
  · rintro ⟨⟨h,ht⟩,hqi⟩
    refine ⟨?_,ht⟩
    intro j
    split_ifs with hj
    · subst j; omega
    · exact h j

private lemma GP0031B3b_weight_unmark (v q : Counts) (i : Fin 4)
    (hi : 0 < GP0031B3b_get v i) :
    multiplicity v q * (GP0031B3b_get v i - GP0031B3b_get q i) =
      GP0031B3b_get v i * multiplicity (GP0031B3b_dec v i) q := by
  have h (a b : ℕ) (ha : 0 < a) : a.choose b * (a-b) = a * (a-1).choose b := by
    have hh := Nat.choose_mul_succ_eq (a-1) b
    simpa [Nat.sub_add_cancel ha, Nat.mul_comm] using hh.symm
  fin_cases i
  all_goals simp_all [GP0031B3b_get, GP0031B3b_dec, GP0031B3b_pack,
    multiplicity, binomial_eq_choose]
  · convert congrArg (fun z => z * v.b.choose q.b * v.c.choose q.c * v.d.choose q.d)
      (h v.a q.a hi) using 1 <;> ring
  · convert congrArg (fun z => z * v.a.choose q.a * v.c.choose q.c * v.d.choose q.d)
      (h v.b q.b hi) using 1 <;> ring
  · convert congrArg (fun z => z * v.a.choose q.a * v.b.choose q.b * v.d.choose q.d)
      (h v.c q.c hi) using 1 <;> ring
  · convert congrArg (fun z => z * v.a.choose q.a * v.b.choose q.b * v.c.choose q.c)
      (h v.d q.d hi) using 1 <;> ring

private lemma GP0031B3b_sum_unmark (v : Counts) (m : ℕ) (i : Fin 4)
    (hi : 0 < GP0031B3b_get v i) (F : Counts → ℝ) :
    (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ) *
      (GP0031B3b_get v i - GP0031B3b_get q i : ℕ) * F q) =
      (GP0031B3b_get v i : ℝ) *
        ∑ q ∈ (randomStates (GP0031B3b_dec v i) m).toFinset,
          (multiplicity (GP0031B3b_dec v i) q : ℝ) * F q := by
  have hsub : (randomStates (GP0031B3b_dec v i) m).toFinset ⊆ (randomStates v m).toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (((GP0031B3b_mem_dec v q m i hi).mp (List.mem_toFinset.mp hq)).1)
  calc
    _ = (GP0031B3b_get v i : ℝ) *
        ∑ q ∈ (randomStates v m).toFinset,
          (multiplicity (GP0031B3b_dec v i) q : ℝ) * F q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hh := GP0031B3b_weight_unmark v q i hi
      have hhR : (multiplicity v q : ℝ) * (GP0031B3b_get v i - GP0031B3b_get q i : ℕ) =
          (GP0031B3b_get v i : ℝ) * multiplicity (GP0031B3b_dec v i) q := by exact_mod_cast hh
      rw [hhR]
      ring
    _ = _ := by
      congr 1
      symm
      apply Finset.sum_subset hsub
      intro q hq hn
      have hnot : ¬ GP0031B3b_get q i < GP0031B3b_get v i := by
        intro hh
        exact hn (List.mem_toFinset.mpr ((GP0031B3b_mem_dec v q m i hi).mpr
          ⟨List.mem_toFinset.mp hq,hh⟩))
      have hle := ((GP0031B3b_mem_coord v q m).mp (List.mem_toFinset.mp hq)).1 i
      have hqi : GP0031B3b_get v i - GP0031B3b_get q i = 0 := by omega
      have hh := GP0031B3b_weight_unmark v q i hi
      rw [hqi, Nat.mul_zero] at hh
      have hz : multiplicity (GP0031B3b_dec v i) q = 0 := by
        exact (Nat.mul_eq_zero.mp hh.symm).resolve_left (by omega)
      simp only [hz, Nat.cast_zero, zero_mul]

private lemma GP0031B3b_sum_unit (u : Counts) (m : ℕ) (i : Fin 4)
    (hm : 0 < m) (F : Counts → ℝ) :
    (∑ q ∈ (randomStates (GP0031B3b_inc u i) m).toFinset,
      (multiplicity (GP0031B3b_inc u i) q : ℝ)*F q) =
      (∑ q ∈ (randomStates u m).toFinset, (multiplicity u q : ℝ)*F q) +
      (∑ q ∈ (randomStates u (m-1)).toFinset,
        (multiplicity u q : ℝ)*F (GP0031B3b_inc q i)) := by
  let v := GP0031B3b_inc u i
  have hi : 0 < GP0031B3b_get v i := by dsimp [v]; rw [GP0031B3b_get_inc]; simp
  have h1 := GP0031B3b_sum_mark v m i hi hm F
  have h0 := GP0031B3b_sum_unmark v m i hi F
  have hsum : (GP0031B3b_get v i : ℝ) *
      (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ)*F q) =
      (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ) *
        (GP0031B3b_get v i - GP0031B3b_get q i : ℕ)*F q) +
      (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ)*GP0031B3b_get q i*F q) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hle := ((GP0031B3b_mem_coord v q m).mp (List.mem_toFinset.mp hq)).1 i
    rw [Nat.cast_sub hle]
    ring
  rw [h0,h1, ← mul_add] at hsum
  have hiR : (GP0031B3b_get v i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  have hh := mul_left_cancel₀ hiR hsum
  simpa only [v, GP0031B3b_dec_inc] using hh

private lemma GP0031B3b_list_sum {A : Type*} [DecidableEq A] (xs : List A)
    (hx : xs.Nodup) (F : A → ℝ) :
    (xs.map F).sum = ∑ q ∈ xs.toFinset, F q := by
  induction xs with
  | nil => simp
  | cons q xs ih =>
    rcases List.nodup_cons.mp hx with ⟨hq,hxs⟩
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hq), ih hxs]

private lemma GP0031B3b_weight_sum (v : Counts) (m : ℕ) (hm : m ≤ v.total) :
    (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ)) = v.total.choose m := by
  rw [← GP0031B3b_list_sum _ (GP0031B3b_randomStates_nodup v m)]
  have hh := congrArg (fun n : ℕ => (n : ℝ)) (design_weight_total v m hm)
  simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def] using hh

private lemma GP0031B3b_first_raw (v : Counts) (m : ℕ) (i : Fin 4)
    (hm : 0 < m) (hmn : m ≤ v.total) :
    (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ) * GP0031B3b_get q i) =
      (GP0031B3b_get v i : ℝ) * (v.total-1).choose (m-1) := by
  by_cases hi : 0 < GP0031B3b_get v i
  · have hh := GP0031B3b_sum_mark v m i hi hm (fun _ => 1)
    simp only [mul_one] at hh
    rw [hh, GP0031B3b_weight_sum _ _ (by rw [GP0031B3b_dec_total v i hi]; omega),
      GP0031B3b_dec_total v i hi]
  · have hz : GP0031B3b_get v i = 0 := by omega
    rw [hz, Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro q hq
    have hle := ((GP0031B3b_mem_coord v q m).mp (List.mem_toFinset.mp hq)).1 i
    have hqi : GP0031B3b_get q i = 0 := by omega
    simp only [hqi, Nat.cast_zero, mul_zero]

private lemma GP0031B3b_second_falling (v : Counts) (m : ℕ) (i j : Fin 4)
    (hm : 2 ≤ m) (hmn : m ≤ v.total) :
    (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ) * GP0031B3b_get q i *
      ((GP0031B3b_get q j : ℝ) - if j = i then 1 else 0)) =
      (GP0031B3b_get v i : ℝ) * (GP0031B3b_get v j - if j = i then 1 else 0 : ℕ) *
        (v.total-2).choose (m-2) := by
  by_cases hi : 0 < GP0031B3b_get v i
  · rw [GP0031B3b_sum_mark v m i hi (by omega)]
    have hp : (∑ q ∈ (randomStates (GP0031B3b_dec v i) (m-1)).toFinset,
        (multiplicity (GP0031B3b_dec v i) q : ℝ) *
          ((GP0031B3b_get (GP0031B3b_inc q i) j : ℝ) - if j = i then 1 else 0)) =
        (∑ q ∈ (randomStates (GP0031B3b_dec v i) (m-1)).toFinset,
        (multiplicity (GP0031B3b_dec v i) q : ℝ) * GP0031B3b_get q j) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [GP0031B3b_get_inc]
      split_ifs <;> push_cast <;> ring
    rw [hp, GP0031B3b_first_raw _ _ _ (by omega)
      (by rw [GP0031B3b_dec_total v i hi]; omega), GP0031B3b_get_dec,
      GP0031B3b_dec_total v i hi]
    simp only [Nat.sub_sub]
    ring
  · have hz : GP0031B3b_get v i = 0 := by omega
    rw [hz, Nat.cast_zero, zero_mul, zero_mul]
    apply Finset.sum_eq_zero
    intro q hq
    have hle := ((GP0031B3b_mem_coord v q m).mp (List.mem_toFinset.mp hq)).1 i
    have hqi : GP0031B3b_get q i = 0 := by omega
    simp only [hqi, Nat.cast_zero, mul_zero, zero_mul]

private lemma GP0031B3b_second_raw (v : Counts) (m : ℕ) (i j : Fin 4)
    (hm : 0 < m) (hmn : m ≤ v.total) :
    (∑ q ∈ (randomStates v m).toFinset,
      (multiplicity v q : ℝ) * GP0031B3b_get q i * GP0031B3b_get q j) =
      (GP0031B3b_get v i : ℝ) * GP0031B3b_get v j *
        (if 2 ≤ m then ((v.total-2).choose (m-2) : ℝ) else 0) +
      if j = i then (GP0031B3b_get v i : ℝ) *
        (((v.total-1).choose (m-1) : ℝ) -
          (if 2 ≤ m then ((v.total-2).choose (m-2) : ℝ) else 0)) else 0 := by
  by_cases hi : 0 < GP0031B3b_get v i
  · by_cases hm2 : 2 ≤ m
    · rw [if_pos hm2]
      have hh := GP0031B3b_second_falling v m i j hm2 hmn
      simp_rw [mul_sub, Finset.sum_sub_distrib] at hh
      by_cases hij : j = i
      · subst j
        simp only [ite_true, mul_one] at hh ⊢
        rw [GP0031B3b_first_raw v m i hm hmn] at hh
        rw [Nat.cast_sub (by omega : 1 ≤ GP0031B3b_get v i), Nat.cast_one] at hh
        nlinarith only [hh]
      · simp only [if_neg hij, mul_zero, Finset.sum_const_zero, sub_zero,
          Nat.sub_zero, add_zero] at hh ⊢
        exact hh
    · have hm1 : m = 1 := by omega
      subst m
      simp only [show ¬ 2 ≤ 1 by omega, ite_false, Nat.sub_self, Nat.choose_zero_right,
        Nat.cast_one, sub_zero, mul_zero, zero_add, mul_one]
      calc
        _ = ∑ q ∈ (randomStates v 1).toFinset,
            if j = i then (multiplicity v q : ℝ) * GP0031B3b_get q i else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          have htot := ((GP0031B3b_mem_coord v q 1).mp (List.mem_toFinset.mp hq)).2
          have he : GP0031B3b_get q i * GP0031B3b_get q j =
              if j = i then GP0031B3b_get q i else 0 := by
            by_cases hij : j = i
            · subst j
              have hle : GP0031B3b_get q i ≤ 1 := by
                fin_cases i <;> dsimp [GP0031B3b_get] <;> dsimp [Counts.total] at htot <;> omega
              interval_cases heq : GP0031B3b_get q i <;> simp
            · fin_cases i <;> fin_cases j <;>
                simp_all [GP0031B3b_get, Counts.total] <;> omega
          split_ifs with hij
          · have heR : (GP0031B3b_get q i : ℝ) * GP0031B3b_get q j = GP0031B3b_get q i := by
              exact_mod_cast (by simpa [hij] using he)
            nlinarith only [heR]
          · have heR : (GP0031B3b_get q i : ℝ) * GP0031B3b_get q j = 0 := by
              exact_mod_cast (by simpa [hij] using he)
            nlinarith only [heR]
        _ = _ := by
          split_ifs with hij
          · simpa only [GP0031B3b_first_raw v 1 i (by omega) hmn, Nat.sub_self,
              Nat.choose_zero_right, Nat.cast_one, mul_one]
          · simp
  · have hz : GP0031B3b_get v i = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_mul]
    split_ifs <;> simp only [add_zero]
    all_goals
      apply Finset.sum_eq_zero
      intro q hq
      have hle := ((GP0031B3b_mem_coord v q m).mp (List.mem_toFinset.mp hq)).1 i
      have hqi : GP0031B3b_get q i = 0 := by omega
      simp only [hqi, Nat.cast_zero, mul_zero, zero_mul]

private lemma GP0031B3b_choose_first (n m : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (n : ℝ) * (n-1).choose (m-1) = (m : ℝ) * n.choose m := by
  have hh := Nat.add_one_mul_choose_eq (n-1) (m-1)
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hm] at hh
  exact_mod_cast hh.trans (Nat.mul_comm _ _)

private lemma GP0031B3b_choose_second (n m : ℕ) (hm : 0 < m) (hn : 2 ≤ n) :
    ((n : ℝ)-1) * (if 2 ≤ m then ((n-2).choose (m-2) : ℝ) else 0) =
      ((m : ℝ)-1) * (n-1).choose (m-1) := by
  by_cases hm2 : 2 ≤ m
  · rw [if_pos hm2]
    have hh := GP0031B3b_choose_first (n-1) (m-1) (by omega) (by omega)
    simpa only [Nat.sub_sub, Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] using hh
  · have hm1 : m = 1 := by omega
    simp [hm1]

private lemma GP0031B3b_score_first (v : Counts) (m : ℕ) (c : Fin 4 → ℝ)
    (hm : 0 < m) (hmn : m ≤ v.total) :
    (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ) *
      ∑ i, (GP0031B3b_get q i : ℝ) * c i) =
      ((v.total-1).choose (m-1) : ℝ) * ∑ i, (GP0031B3b_get v i : ℝ) * c i := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i : Fin 4, c i * ∑ q ∈ (randomStates v m).toFinset,
        (multiplicity v q : ℝ) * GP0031B3b_get q i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      simp_rw [GP0031B3b_first_raw v m _ hm hmn]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private lemma GP0031B3b_score_second (v : Counts) (m : ℕ) (c : Fin 4 → ℝ)
    (hm : 0 < m) (hmn : m ≤ v.total) :
    (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ) *
      (∑ i, (GP0031B3b_get q i : ℝ) * c i)^2) =
      (if 2 ≤ m then ((v.total-2).choose (m-2) : ℝ) else 0) *
        (∑ i, (GP0031B3b_get v i : ℝ) * c i)^2 +
      (((v.total-1).choose (m-1) : ℝ) -
        (if 2 ≤ m then ((v.total-2).choose (m-2) : ℝ) else 0)) *
        ∑ i, (GP0031B3b_get v i : ℝ) * (c i)^2 := by
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, (c i * c j) *
        ∑ q ∈ (randomStates v m).toFinset,
          (multiplicity v q : ℝ) * GP0031B3b_get q i * GP0031B3b_get q j := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      simp_rw [GP0031B3b_second_raw v m _ _ hm hmn, mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      · simp_rw [mul_ite, mul_zero]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring

private lemma GP0031B3b_score_moment (v : Counts) (m : ℕ) (c : Fin 4 → ℝ)
    (hm : 0 < m) (hmn : m ≤ v.total) (hn : 2 ≤ v.total) :
    (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ) *
      ((∑ i, (GP0031B3b_get q i : ℝ) * c i) -
        (m : ℝ)/v.total * ∑ i, (GP0031B3b_get v i : ℝ) * c i)^2) /
      v.total.choose m =
      (m : ℝ) * (v.total-m : ℕ) / ((v.total : ℝ)*((v.total : ℝ)-1)) *
        ((∑ i, (GP0031B3b_get v i : ℝ)*(c i)^2) -
          (∑ i, (GP0031B3b_get v i : ℝ)*c i)^2 / v.total) := by
  let S : ℝ := ∑ i, (GP0031B3b_get v i : ℝ)*c i
  let H : ℝ := ∑ i, (GP0031B3b_get v i : ℝ)*(c i)^2
  let D : ℝ := v.total.choose m
  let B : ℝ := (v.total-1).choose (m-1)
  let A : ℝ := if 2 ≤ m then ((v.total-2).choose (m-2) : ℝ) else 0
  have hn0 : (v.total : ℝ) ≠ 0 := by exact_mod_cast (show v.total ≠ 0 by omega)
  have hn1 : (v.total : ℝ)-1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ v.total := by exact_mod_cast hn
    linarith
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have hB := GP0031B3b_choose_first v.total m hm (by omega)
  have hA := GP0031B3b_choose_second v.total m hm hn
  change (v.total : ℝ)*B = (m : ℝ)*D at hB
  change ((v.total : ℝ)-1)*A = ((m : ℝ)-1)*B at hA
  have hB' : B = (m : ℝ)*D/v.total := (eq_div_iff hn0).mpr (by linarith)
  have hA' : A = ((m : ℝ)-1)*B/((v.total : ℝ)-1) :=
    (eq_div_iff hn1).mpr (by linarith)
  have he (x : ℝ) : (x-(m : ℝ)/v.total*S)^2 =
      x^2 - 2*((m : ℝ)/v.total*S)*x + ((m : ℝ)/v.total*S)^2 := by ring
  change (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ) *
    ((∑ i, (GP0031B3b_get q i : ℝ) * c i) - (m : ℝ)/v.total*S)^2) / D = _
  simp_rw [he]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hlin : (∑ q ∈ (randomStates v m).toFinset,
      (multiplicity v q : ℝ) * (2*((m : ℝ)/v.total*S) *
        ∑ i, (GP0031B3b_get q i : ℝ)*c i)) =
      2*((m : ℝ)/v.total*S) * (B*S) := by
    calc
      _ = 2*((m : ℝ)/v.total*S) *
          (∑ q ∈ (randomStates v m).toFinset,
            (multiplicity v q : ℝ) * ∑ i, (GP0031B3b_get q i : ℝ)*c i) := by
        symm
        convert Finset.mul_sum (randomStates v m).toFinset
          (fun q => (multiplicity v q : ℝ) * ∑ i, (GP0031B3b_get q i : ℝ)*c i)
          (2*((m : ℝ)/v.total*S)) using 1
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = _ := by rw [GP0031B3b_score_first v m c hm hmn]
  have hconst : (∑ q ∈ (randomStates v m).toFinset,
      (multiplicity v q : ℝ) * ((m : ℝ)/v.total*S)^2) =
      D*((m : ℝ)/v.total*S)^2 := by
    rw [← Finset.sum_mul, GP0031B3b_weight_sum v m hmn]
  rw [hlin, hconst, GP0031B3b_score_second v m c hm hmn]
  change (A*S^2 + (B-A)*H - 2*((m : ℝ)/v.total*S)*(B*S) +
      D*((m : ℝ)/v.total*S)^2)/D = _
  rw [hA', hB', Nat.cast_sub hmn]
  dsimp only [S, H] at *
  field_simp [hn0, hn1, hD]
  <;> ring

private def GP0031B3b_score (v q : Counts) : ℤ :=
  4*(q.a : ℤ)+2*q.b+2*q.c-2*v.a-v.b-v.c
private def GP0031B3b_g : Fin 4 → ℤ := ![2,1,1,0]

private lemma GP0031B3b_score_inc (u q : Counts) (i : Fin 4) :
    GP0031B3b_score (GP0031B3b_inc u i) q = GP0031B3b_score u q - GP0031B3b_g i := by
  fin_cases i <;> simp [GP0031B3b_score, GP0031B3b_inc, GP0031B3b_pack,
    GP0031B3b_get, GP0031B3b_g] <;> omega
private lemma GP0031B3b_score_inc_inc (u q : Counts) (i : Fin 4) :
    GP0031B3b_score (GP0031B3b_inc u i) (GP0031B3b_inc q i) =
      GP0031B3b_score u q + GP0031B3b_g i := by
  fin_cases i <;> simp [GP0031B3b_score, GP0031B3b_inc, GP0031B3b_pack,
    GP0031B3b_get, GP0031B3b_g] <;> omega

private lemma GP0031B3b_dev_score (v q : Counts) (m : ℕ)
    (hn : v.total = 2*m) (hq : q ∈ randomStates v m) :
    deviationNumerator v (observed v q) m = (m : ℤ)^2 * GP0031B3b_score v q := by
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  simp only [deviationNumerator, hn, Nat.cast_mul, Nat.cast_ofNat, observed,
    Nat.cast_add, Nat.cast_sub (show q.c ≤ v.a-q.a+v.c by omega), Nat.cast_sub ha,
    Counts.effect, GP0031B3b_score]
  ring

private lemma GP0031B3b_tail_score (v o : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (ht : v.total = o.total) :
    (tailCount v o : ℝ) =
      ∑ q ∈ (randomStates v (o.a+o.b)).toFinset,
        (multiplicity v q : ℝ) *
          (if |2*((o.a : ℤ)-o.c)-v.effect| ≤ |GP0031B3b_score v q| then 1 else 0) := by
  let m := o.a+o.b
  have hn : v.total = 2*m := by rw [ht]; dsimp [m, Counts.total]; omega
  have hobs : deviationNumerator v o m = (m : ℤ)^2 * (2*((o.a : ℤ)-o.c)-v.effect) := by
    simp only [deviationNumerator, hn, Nat.cast_mul, Nat.cast_ofNat]
    ring
  unfold tailCount
  rw [Nat.cast_list_sum]
  simp only [List.map_map, Function.comp_def]
  rw [GP0031B3b_list_sum _ (GP0031B3b_randomStates_nodup v (o.a+o.b))]
  apply Finset.sum_congr rfl
  intro q hq
  have hqmem := List.mem_toFinset.mp hq
  have hsq : 0 < ((m : ℤ)^2).natAbs := by
    apply Int.natAbs_pos.mpr
    exact pow_ne_zero _ (by exact_mod_cast ho.1.ne')
  have he : (deviationNumerator v o m).natAbs ≤
      (deviationNumerator v (observed v q) m).natAbs ↔
      |2*((o.a : ℤ)-o.c)-v.effect| ≤ |GP0031B3b_score v q| := by
    rw [hobs, GP0031B3b_dev_score v q m hn hqmem, Int.natAbs_mul, Int.natAbs_mul]
    rw [mul_le_mul_iff_right₀ hsq]
    simp only [Int.abs_eq_natAbs]
    exact Int.ofNat_le.symm
  change ((if (deviationNumerator v o m).natAbs ≤
      (deviationNumerator v (observed v q) m).natAbs then multiplicity v q else 0 : ℕ) : ℝ) = _
  simp only [he]
  split_ifs <;> simp

private lemma GP0031B3b_tail_step (X Y δ ε : ℤ) (hXY : |X-Y| ≤ 1)
    (hδε : ε ≤ δ-1) (hX : δ ≤ |X|) : ε ≤ |Y| := by
  have hh : |X| ≤ |Y|+1 := by
    calc
      |X| = |Y+(X-Y)| := by congr 1; omega
      _ ≤ |Y|+|X-Y| := abs_add_le _ _
      _ ≤ |Y|+1 := by omega
  omega

private lemma GP0031B3b_pvalue_unit (o u : Counts) (i j : Fin 4)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (ht : u.total+1 = o.total)
    (hg : |GP0031B3b_g i-GP0031B3b_g j| ≤ 1)
    (he : |2*((o.a : ℤ)-o.c)-(GP0031B3b_inc u j).effect| ≤
      |2*((o.a : ℤ)-o.c)-(GP0031B3b_inc u i).effect|-1) :
    pValue (GP0031B3b_inc u i) o ≤ pValue (GP0031B3b_inc u j) o := by
  have hti : (GP0031B3b_inc u i).total = o.total := (GP0031B3b_inc_total u i).trans ht
  have htj : (GP0031B3b_inc u j).total = o.total := (GP0031B3b_inc_total u j).trans ht
  have htail : (tailCount (GP0031B3b_inc u i) o : ℝ) ≤ tailCount (GP0031B3b_inc u j) o := by
    rw [GP0031B3b_tail_score _ _ ho hti, GP0031B3b_tail_score _ _ ho htj,
      GP0031B3b_sum_unit u (o.a+o.b) i ho.1, GP0031B3b_sum_unit u (o.a+o.b) j ho.1]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro q hq
      rw [GP0031B3b_score_inc, GP0031B3b_score_inc]
      by_cases hx : |2*((o.a : ℤ)-o.c)-(GP0031B3b_inc u i).effect| ≤
          |GP0031B3b_score u q-GP0031B3b_g i|
      · have hc : |(GP0031B3b_score u q-GP0031B3b_g i) -
            (GP0031B3b_score u q-GP0031B3b_g j)| ≤ 1 := by
          calc
            _ = |GP0031B3b_g j-GP0031B3b_g i| := by congr 1; ring
            _ = |GP0031B3b_g i-GP0031B3b_g j| := abs_sub_comm _ _
            _ ≤ 1 := hg
        have hy := GP0031B3b_tail_step (GP0031B3b_score u q-GP0031B3b_g i)
          (GP0031B3b_score u q-GP0031B3b_g j) _ _ hc he hx
        simp only [if_pos hx, if_pos hy, le_refl]
      · simp only [if_neg hx, mul_zero]
        positivity
    · apply Finset.sum_le_sum
      intro q hq
      rw [GP0031B3b_score_inc_inc, GP0031B3b_score_inc_inc]
      by_cases hx : |2*((o.a : ℤ)-o.c)-(GP0031B3b_inc u i).effect| ≤
          |GP0031B3b_score u q+GP0031B3b_g i|
      · have hc : |(GP0031B3b_score u q+GP0031B3b_g i) -
            (GP0031B3b_score u q+GP0031B3b_g j)| ≤ 1 := by
          convert hg using 1 <;> congr 1 <;> ring
        have hy := GP0031B3b_tail_step (GP0031B3b_score u q+GP0031B3b_g i)
          (GP0031B3b_score u q+GP0031B3b_g j) _ _ hc he hx
        simp only [if_pos hx, if_pos hy, le_refl]
      · simp only [if_neg hx, mul_zero]
        positivity
  unfold pValue
  rw [hti, htj]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast htail

private lemma GP0031B3b_pvalue_move (o v w : Counts) (i j : Fin 4)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (ht : v.total = o.total)
    (hi : 0 < GP0031B3b_get v i) (hw : GP0031B3b_inc (GP0031B3b_dec v i) j = w)
    (hg : |GP0031B3b_g i-GP0031B3b_g j| ≤ 1)
    (he : (2*((o.a : ℤ)-o.c) < v.effect ∧ w.effect = v.effect-1) ∨
      (v.effect < 2*((o.a : ℤ)-o.c) ∧ w.effect = v.effect+1)) :
    pValue v o ≤ pValue w o := by
  have hv := GP0031B3b_inc_dec v i hi
  have hthresh : |2*((o.a : ℤ)-o.c)-w.effect| ≤
      |2*((o.a : ℤ)-o.c)-v.effect|-1 := by
    rcases he with ⟨he,hw⟩ | ⟨he,hw⟩
    · have hold : 2*((o.a : ℤ)-o.c)-v.effect ≤ 0 := by omega
      have hnew : 2*((o.a : ℤ)-o.c)-w.effect ≤ 0 := by omega
      rw [abs_of_nonpos hold, abs_of_nonpos hnew]
      omega
    · have hold : 0 ≤ 2*((o.a : ℤ)-o.c)-v.effect := by omega
      have hnew : 0 ≤ 2*((o.a : ℤ)-o.c)-w.effect := by omega
      rw [abs_of_nonneg hold, abs_of_nonneg hnew]
      omega
  have hn : 0 < v.total := by rw [ht]; dsimp [Counts.total]; omega
  have hh := GP0031B3b_pvalue_unit o (GP0031B3b_dec v i) i j ho
    (by rw [GP0031B3b_dec_total v i hi, ← ht]; omega) hg
    (by simpa only [hv, hw] using hthresh)
  simpa only [hv, hw] using hh

private lemma GP0031B3b_t25_tau_real (v : Counts) :
    tau v = (v.effect : ℝ)/v.total := by
  simp [tau,tauQ]

private lemma GP0031B3b_t25_accepted_iff (α : ℝ) (o : Counts) (t : ℝ) :
    t ∈ accepted α o ↔
      ∃ v, Possible o v ∧ α ≤ (pValue v o : ℝ) ∧ tau v = t := by
  simp only [accepted,Finset.mem_image,List.mem_toFinset,List.mem_filter,
    decide_eq_true_eq,Possible,and_assoc]

private lemma GP0031B3b_t25_accepted_lattice (α : ℝ) (o : Counts) :
    (↑(accepted α o) : Set ℝ) ⊆ candidateLattice o := by
  intro t ht
  obtain ⟨v,hv,hp,rfl⟩ := (GP0031B3b_t25_accepted_iff α o t).mp ht
  obtain ⟨htot,heff⟩ := possible_table_facts o v hv
  exact ⟨v.effect,heff,by rw [GP0031B3b_t25_tau_real,htot]⟩

private lemma GP0031B3b_t25_candidate_bounds (o : Counts) (t : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (ht : t ∈ candidateLattice o) :
    (((o.a : ℝ)-o.c-(o.a+o.b))/o.total) ≤ t ∧
      t ≤ (((o.a : ℝ)-o.c+(o.a+o.b))/o.total) := by
  obtain ⟨e,he,rfl⟩ := ht
  simp only [candidateNumerators,List.mem_map,List.mem_range] at he
  obtain ⟨k,hk,rfl⟩ := he
  have hn : o.total = 2*(o.a+o.b) := by dsimp [Counts.total]; omega
  have hnR : (0 : ℝ) < o.total := by exact_mod_cast (show 0 < o.total by omega)
  have hkR : (k : ℝ) ≤ o.total := by exact_mod_cast (show k ≤ o.total by omega)
  have hnR' : (o.total : ℝ) = 2*((o.a : ℝ)+o.b) := by exact_mod_cast hn
  constructor
  · apply (div_le_div_iff_of_pos_right hnR).mpr
    push_cast
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  · apply (div_le_div_iff_of_pos_right hnR).mpr
    push_cast
    nlinarith

private lemma GP0031B3b_t25_centre_formula (o : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) :
    estimate o = ((2*((o.a : ℤ)-o.c) : ℤ) : ℝ)/o.total := by
  have hmR : ((o.a : ℝ)+o.b) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast ho.1)
  have hbal : (o.a : ℝ)+o.b = (o.c : ℝ)+o.d := by exact_mod_cast ho.2
  have hn : (o.total : ℝ) = 2*((o.a : ℝ)+o.b) := by
    dsimp [Counts.total]
    push_cast
    linarith
  simp only [estimate,estimateQ,Rat.cast_sub,Rat.cast_div,Rat.cast_add,
    Rat.cast_natCast,Int.cast_mul,Int.cast_sub,Int.cast_ofNat,Int.cast_natCast]
  rw [← hbal,hn]
  field_simp [hmR]
  <;> ring

private lemma GP0031B3b_t25_integer_downward_fill (P : ℤ → Prop) (s e k : ℤ)
    (hsk : s ≤ k) (hke : k ≤ e) (he : P e)
    (hstep : ∀ j : ℤ, s < j → P j → P (j-1)) : P k := by
  have hfill : ∀ d : ℕ, P (k+(d : ℤ)) → P k := by
    intro d
    induction d with
    | zero => simpa
    | succ d ih =>
      intro hd
      have hprev := hstep (k+((d+1 : ℕ) : ℤ)) (by omega) hd
      apply ih
      convert hprev using 1 <;> push_cast <;> ring
  apply hfill (e-k).toNat
  have heq : k+((e-k).toNat : ℤ) = e := by
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  simpa only [heq] using he

private lemma GP0031B3b_t25_integer_upward_fill (P : ℤ → Prop) (s e k : ℤ)
    (hek : e ≤ k) (hks : k ≤ s) (he : P e)
    (hstep : ∀ j : ℤ, j < s → P j → P (j+1)) : P k := by
  have hfill : ∀ d : ℕ, P (k-(d : ℤ)) → P k := by
    intro d
    induction d with
    | zero => simpa
    | succ d ih =>
      intro hd
      have hprev := hstep (k-((d+1 : ℕ) : ℤ)) (by omega) hd
      apply ih
      convert hprev using 1 <;> push_cast <;> ring
  apply hfill (k-e).toNat
  have heq : k-((k-e).toNat : ℤ) = e := by
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  simpa only [heq] using he

/-- This predicate keeps possibility and the actual p-value in each step. -/
private def GP0031B3b_t25_effectAccepted (α : ℝ) (o : Counts) (e : ℤ) : Prop :=
  ∃ v, Possible o v ∧ v.effect = e ∧ α ≤ (pValue v o : ℝ)

/-- A compatible one-bit change lowers the effect and increases the p-value. -/
lemma GP0031B3b_t25_possible_effect_down (o v : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hv : Possible o v)
    (he : 2*((o.a : ℤ)-o.c) < v.effect) :
    ∃ v', Possible o v' ∧ v'.effect = v.effect-1 ∧ pValue v o ≤ pValue v' o := by
  have htotal := (possible_table_facts o v hv).1
  simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range] at hv
  obtain ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩ := hv
  have hpossible (i' j' k' l' : ℕ)
      (hi' : i' ≤ o.a) (hj' : j' ≤ o.b) (hk' : k' ≤ o.c) (hl' : l' ≤ o.d) :
      Possible o ⟨i'+k',o.a-i'+l',o.c-k'+j',o.b+o.d-j'-l'⟩ := by
    simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range]
    exact ⟨i',by omega,j',by omega,k',by omega,l',by omega,rfl⟩
  by_cases hi' : i < o.a
  · refine ⟨⟨i+1+k,o.a-(i+1)+l,o.c-k+j,o.b+o.d-j-l⟩,
      hpossible (i+1) j k l (by omega) (by omega) (by omega) (by omega),?_,?_⟩
    · dsimp [Counts.effect]
      omega
    · apply GP0031B3b_pvalue_move o _ _ 1 0 ho htotal
      · dsimp [GP0031B3b_get]; omega
      · ext <;> dsimp [GP0031B3b_inc, GP0031B3b_dec, GP0031B3b_pack, GP0031B3b_get] <;> omega
      · norm_num [GP0031B3b_g]
      · apply Or.inl
        refine ⟨he,?_⟩
        dsimp [Counts.effect]
        omega
  · by_cases hj' : j < o.b
    · refine ⟨⟨i+k,o.a-i+l,o.c-k+(j+1),o.b+o.d-(j+1)-l⟩,
        hpossible i (j+1) k l (by omega) (by omega) (by omega) (by omega),?_,?_⟩
      · dsimp [Counts.effect]
        omega
      · apply GP0031B3b_pvalue_move o _ _ 3 2 ho htotal
        · dsimp [GP0031B3b_get]; omega
        · ext <;> dsimp [GP0031B3b_inc, GP0031B3b_dec, GP0031B3b_pack, GP0031B3b_get] <;> omega
        · norm_num [GP0031B3b_g]
        · apply Or.inl
          refine ⟨he,?_⟩
          dsimp [Counts.effect]
          omega
    · by_cases hk' : 0 < k
      · refine ⟨⟨i+(k-1),o.a-i+l,o.c-(k-1)+j,o.b+o.d-j-l⟩,
          hpossible i j (k-1) l (by omega) (by omega) (by omega) (by omega),?_,?_⟩
        · dsimp [Counts.effect]
          omega
        · apply GP0031B3b_pvalue_move o _ _ 0 2 ho htotal
          · dsimp [GP0031B3b_get]; omega
          · ext <;> dsimp [GP0031B3b_inc, GP0031B3b_dec, GP0031B3b_pack, GP0031B3b_get] <;> omega
          · norm_num [GP0031B3b_g]
          · apply Or.inl
            refine ⟨he,?_⟩
            dsimp [Counts.effect]
            omega
      · have hl' : 0 < l := by
          dsimp [Counts.effect] at he
          omega
        refine ⟨⟨i+k,o.a-i+(l-1),o.c-k+j,o.b+o.d-j-(l-1)⟩,
          hpossible i j k (l-1) (by omega) (by omega) (by omega) (by omega),?_,?_⟩
        · dsimp [Counts.effect]
          omega
        · apply GP0031B3b_pvalue_move o _ _ 1 3 ho htotal
          · dsimp [GP0031B3b_get]; omega
          · ext <;> dsimp [GP0031B3b_inc, GP0031B3b_dec, GP0031B3b_pack, GP0031B3b_get] <;> omega
          · norm_num [GP0031B3b_g]
          · apply Or.inl
            refine ⟨he,?_⟩
            dsimp [Counts.effect]
            omega

lemma GP0031B3b_t25_possible_effect_up (o v : Counts)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hv : Possible o v)
    (he : v.effect < 2*((o.a : ℤ)-o.c)) :
    ∃ v', Possible o v' ∧ v'.effect = v.effect+1 ∧ pValue v o ≤ pValue v' o := by
  have htotal := (possible_table_facts o v hv).1
  simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range] at hv
  obtain ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩ := hv
  have hpossible (i' j' k' l' : ℕ)
      (hi' : i' ≤ o.a) (hj' : j' ≤ o.b) (hk' : k' ≤ o.c) (hl' : l' ≤ o.d) :
      Possible o ⟨i'+k',o.a-i'+l',o.c-k'+j',o.b+o.d-j'-l'⟩ := by
    simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range]
    exact ⟨i',by omega,j',by omega,k',by omega,l',by omega,rfl⟩
  by_cases hi' : 0 < i
  · refine ⟨⟨i-1+k,o.a-(i-1)+l,o.c-k+j,o.b+o.d-j-l⟩,
      hpossible (i-1) j k l (by omega) (by omega) (by omega) (by omega),?_,?_⟩
    · dsimp [Counts.effect]
      omega
    · apply GP0031B3b_pvalue_move o _ _ 0 1 ho htotal
      · dsimp [GP0031B3b_get]; omega
      · ext <;> dsimp [GP0031B3b_inc, GP0031B3b_dec, GP0031B3b_pack, GP0031B3b_get] <;> omega
      · norm_num [GP0031B3b_g]
      · apply Or.inr
        refine ⟨he,?_⟩
        dsimp [Counts.effect]
        omega
  · by_cases hj' : 0 < j
    · refine ⟨⟨i+k,o.a-i+l,o.c-k+(j-1),o.b+o.d-(j-1)-l⟩,
        hpossible i (j-1) k l (by omega) (by omega) (by omega) (by omega),?_,?_⟩
      · dsimp [Counts.effect]
        omega
      · apply GP0031B3b_pvalue_move o _ _ 2 3 ho htotal
        · dsimp [GP0031B3b_get]; omega
        · ext <;> dsimp [GP0031B3b_inc, GP0031B3b_dec, GP0031B3b_pack, GP0031B3b_get] <;> omega
        · norm_num [GP0031B3b_g]
        · apply Or.inr
          refine ⟨he,?_⟩
          dsimp [Counts.effect]
          omega
    · by_cases hk' : k < o.c
      · refine ⟨⟨i+(k+1),o.a-i+l,o.c-(k+1)+j,o.b+o.d-j-l⟩,
          hpossible i j (k+1) l (by omega) (by omega) (by omega) (by omega),?_,?_⟩
        · dsimp [Counts.effect]
          omega
        · apply GP0031B3b_pvalue_move o _ _ 2 0 ho htotal
          · dsimp [GP0031B3b_get]; omega
          · ext <;> dsimp [GP0031B3b_inc, GP0031B3b_dec, GP0031B3b_pack, GP0031B3b_get] <;> omega
          · norm_num [GP0031B3b_g]
          · apply Or.inr
            refine ⟨he,?_⟩
            dsimp [Counts.effect]
            omega
      · have hl' : l < o.d := by
          dsimp [Counts.effect] at he
          omega
        refine ⟨⟨i+k,o.a-i+(l+1),o.c-k+j,o.b+o.d-j-(l+1)⟩,
          hpossible i j k (l+1) (by omega) (by omega) (by omega) (by omega),?_,?_⟩
        · dsimp [Counts.effect]
          omega
        · apply GP0031B3b_pvalue_move o _ _ 3 1 ho htotal
          · dsimp [GP0031B3b_get]; omega
          · ext <;> dsimp [GP0031B3b_inc, GP0031B3b_dec, GP0031B3b_pack, GP0031B3b_get] <;> omega
          · norm_num [GP0031B3b_g]
          · apply Or.inr
            refine ⟨he,?_⟩
            dsimp [Counts.effect]
            omega

/-- Iterate accepted-effect moves to obtain lattice filling toward the estimate. -/
lemma GP0031B3b_t25_star_of_integer_steps (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hdown : ∀ e : ℤ, 2*((o.a : ℤ)-o.c) < e →
      GP0031B3b_t25_effectAccepted α o e → GP0031B3b_t25_effectAccepted α o (e-1))
    (hup : ∀ e : ℤ, e < 2*((o.a : ℤ)-o.c) →
      GP0031B3b_t25_effectAccepted α o e → GP0031B3b_t25_effectAccepted α o (e+1)) :
    ∀ u ∈ accepted α o, ∀ t ∈ candidateLattice o,
      (estimate o ≤ t ∧ t ≤ u) ∨ (u ≤ t ∧ t ≤ estimate o) →
        t ∈ accepted α o := by
  intro u hu t ht hbetween
  obtain ⟨v,hv,hp,hvu⟩ := (GP0031B3b_t25_accepted_iff α o u).mp hu
  obtain ⟨k,hk,hkt⟩ := ht
  have hn : (0 : ℝ) < o.total := by
    exact_mod_cast (show 0 < o.total by dsimp [Counts.total]; omega)
  have hvt := (possible_table_facts o v hv).1
  have he : GP0031B3b_t25_effectAccepted α o v.effect := ⟨v,hv,rfl,hp⟩
  have hval : u = (v.effect : ℝ)/o.total := by rw [← hvu,GP0031B3b_t25_tau_real,hvt]
  have hcentre := GP0031B3b_t25_centre_formula o ho
  have hkacc : GP0031B3b_t25_effectAccepted α o k := by
    rcases hbetween with ⟨hst,htu⟩ | ⟨hut,hts⟩
    · rw [hcentre,hkt] at hst
      rw [hval,hkt] at htu
      have hskR := (div_le_div_iff_of_pos_right hn).mp hst
      have hkeR := (div_le_div_iff_of_pos_right hn).mp htu
      exact GP0031B3b_t25_integer_downward_fill _ (2*((o.a : ℤ)-o.c)) v.effect k
        (by exact_mod_cast hskR) (by exact_mod_cast hkeR) he hdown
    · rw [hval,hkt] at hut
      rw [hcentre,hkt] at hts
      have hekR := (div_le_div_iff_of_pos_right hn).mp hut
      have hksR := (div_le_div_iff_of_pos_right hn).mp hts
      exact GP0031B3b_t25_integer_upward_fill _ (2*((o.a : ℤ)-o.c)) v.effect k
        (by exact_mod_cast hekR) (by exact_mod_cast hksR) he hup
  obtain ⟨w,hw,heq,hp⟩ := hkacc
  have hwt := (possible_table_facts o w hw).1
  have htw : tau w = t := by rw [GP0031B3b_t25_tau_real,hwt,heq,← hkt]
  rw [← htw]
  exact accepted_of_possible α o w hw hp

/-- Lattice filling and attained finite extrema give both set equalities. -/
lemma GP0031B3b_t25_interval_equalities_of_star (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1)
    (hstar : ∀ u ∈ accepted α o, ∀ t ∈ candidateLattice o,
      (estimate o ≤ t ∧ t ≤ u) ∨ (u ≤ t ∧ t ≤ estimate o) →
        t ∈ accepted α o) :
    (↑(accepted α o) : Set ℝ) = exactInterval α o ∩ candidateLattice o ∧
    (Set.Icc (estimate o) (((o.a : ℝ)-o.c+(o.a+o.b))/o.total) ∩
      (↑(accepted α o) : Set ℝ)) =
      Set.Icc (estimate o) (upper α o) ∩ candidateLattice o := by
  have hest := balanced_estimate_in_interval o α ho hα
  have hne : (accepted α o).Nonempty := ⟨estimate o,hest.1⟩
  have hupper : upper α o ∈ accepted α o := hne.csSup_mem
  have hlower : lower α o ∈ accepted α o := hne.csInf_mem
  have hfirst : (↑(accepted α o) : Set ℝ) =
      exactInterval α o ∩ candidateLattice o := by
    ext t
    constructor
    · intro ht
      exact ⟨accepted_subset_interval α o ht,GP0031B3b_t25_accepted_lattice α o ht⟩
    · rintro ⟨⟨l,hl,u,hu,hlt,htu⟩,ht⟩
      rcases le_total (estimate o) t with hst | hts
      · exact hstar u hu t ht (Or.inl ⟨hst,htu⟩)
      · exact hstar l hl t ht (Or.inr ⟨hlt,hts⟩)
  refine ⟨hfirst,?_⟩
  have hUbound := (GP0031B3b_t25_candidate_bounds o (upper α o) ho
    (GP0031B3b_t25_accepted_lattice α o hupper)).2
  ext t
  constructor
  · rintro ⟨⟨hst,htC⟩,ht⟩
    refine ⟨⟨hst,?_⟩,GP0031B3b_t25_accepted_lattice α o ht⟩
    exact le_csSup (accepted α o).finite_toSet.bddAbove ht
  · rintro ⟨⟨hst,htU⟩,ht⟩
    have htacc := hstar (upper α o) hupper t ht (Or.inl ⟨hst,htU⟩)
    exact ⟨⟨hst,htU.trans hUbound⟩,htacc⟩

theorem corrected_lattice_interval_proof (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d) (hα : 0 < α ∧ α < 1) :
    (↑(accepted α o) : Set ℝ) = exactInterval α o ∩ candidateLattice o ∧
    (Set.Icc (estimate o) (((o.a : ℝ)-o.c+(o.a+o.b))/o.total) ∩
      (↑(accepted α o) : Set ℝ)) =
      Set.Icc (estimate o) (upper α o) ∩ candidateLattice o := by
  apply GP0031B3b_t25_interval_equalities_of_star o α ho hα
  apply GP0031B3b_t25_star_of_integer_steps o α ho
  · intro e he heacc
    obtain ⟨v,hv,hve,hp⟩ := heacc
    obtain ⟨w,hw,hwe,hpw⟩ := GP0031B3b_t25_possible_effect_down o v ho hv (by omega)
    refine ⟨w,hw,by omega,hp.trans ?_⟩
    exact_mod_cast hpw
  · intro e he heacc
    obtain ⟨v,hv,hve,hp⟩ := heacc
    obtain ⟨w,hw,hwe,hpw⟩ := GP0031B3b_t25_possible_effect_up o v ho hv (by omega)
    refine ⟨w,hw,by omega,hp.trans ?_⟩
    exact_mod_cast hpw

private lemma GP0031B3b_t31_estimate_real (o : Counts) :
    estimate o = (o.a : ℝ)/(o.a+o.b : ℕ)-(o.c : ℝ)/(o.c+o.d : ℕ) := by
  simp [estimate,estimateQ]

private lemma GP0031B3b_t31_tau_real (v : Counts) :
    tau v = (v.effect : ℝ)/v.total := by
  simp [tau,tauQ]

private lemma GP0031B3b_t31_observed_arms (v q : Counts) (m : ℕ)
    (hq : q ∈ randomStates v m) :
    (observed v q).a+(observed v q).b = m ∧
    (observed v q).c+(observed v q).d = v.total-m ∧
    (observed v q).total = v.total := by
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  dsimp [observed,Counts.total] at *
  omega

private lemma GP0031B3b_estimator_score (v q : Counts) (m : ℕ)
    (hm : 0 < m) (hml : m < v.total) (hq : q ∈ randomStates v m) :
    estimate (observed v q) - tau v =
      (∑ i : Fin 4, (GP0031B3b_get q i : ℝ) *
        (![1/(m : ℝ)+1/(v.total-m : ℕ), 1/(m : ℝ), 1/(v.total-m : ℕ), 0] i)) -
      (m : ℝ)/v.total * ∑ i : Fin 4, (GP0031B3b_get v i : ℝ) *
        (![1/(m : ℝ)+1/(v.total-m : ℕ), 1/(m : ℝ), 1/(v.total-m : ℕ), 0] i) := by
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  have har := GP0031B3b_t31_observed_arms v q m hq
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hl0 : ((v.total-m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show v.total-m ≠ 0 by omega)
  have hn0 : (v.total : ℝ) ≠ 0 := by exact_mod_cast (show v.total ≠ 0 by omega)
  have hnum : ((observed v q).c : ℝ) = (v.a : ℝ)-q.a+v.c-q.c := by
    change ((v.a-q.a+v.c-q.c : ℕ) : ℝ) = _
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub ha]
  rw [GP0031B3b_t31_estimate_real, har.1, har.2.1, hnum, GP0031B3b_t31_tau_real]
  simp only [Fin.sum_univ_succ, GP0031B3b_get, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, mul_zero, observed, Nat.cast_add, Counts.effect, Int.cast_sub,
    Int.cast_natCast]
  have hl0' : (v.total : ℝ)-(m : ℝ) ≠ 0 := by
    rw [← Nat.cast_sub (by omega : m ≤ v.total)]
    exact hl0
  rw [Nat.cast_sub (by omega : m ≤ v.total)]
  have hnR : (v.total : ℝ) = (v.a : ℝ)+v.b+v.c+v.d := by simp [Counts.total]
  field_simp [hm0, hl0', hn0]
  <;> rw [hnR] <;> ring

private lemma GP0031B3b_moment_bound (v : Counts) (m : ℕ)
    (hm : 0 < m) (hml : m < v.total) :
    designMean v m (fun q => (estimate (observed v q)-tau v)^2) ≤
      (v.total : ℝ)^2 / ((v.total-1 : ℕ)*(m : ℝ)*(v.total-m : ℕ)) := by
  let c : Fin 4 → ℝ := ![1/(m : ℝ)+1/(v.total-m : ℕ), 1/(m : ℝ), 1/(v.total-m : ℕ), 0]
  let C : ℝ := 1/(m : ℝ)+1/(v.total-m : ℕ)
  have hn : 2 ≤ v.total := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlR : (0 : ℝ) < (v.total-m : ℕ) := by exact_mod_cast (show 0 < v.total-m by omega)
  have hnR : (0 : ℝ) < v.total := by exact_mod_cast (show 0 < v.total by omega)
  have hn1R : (0 : ℝ) < (v.total : ℝ)-1 := by
    have hh : (2 : ℝ) ≤ v.total := by exact_mod_cast hn
    linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc (i : Fin 4) : 0 ≤ c i ∧ c i ≤ C := by
    fin_cases i <;> dsimp [c, C] <;> constructor <;>
      (first | positivity | linarith [one_div_pos.mpr hmR, one_div_pos.mpr hlR])
  have hsq (i : Fin 4) : (c i)^2 ≤ C^2 := by
    have hh := hc i
    nlinarith
  have hH : (∑ i : Fin 4, (GP0031B3b_get v i : ℝ)*(c i)^2) ≤ (v.total : ℝ)*C^2 := by
    calc
      _ ≤ ∑ i : Fin 4, (GP0031B3b_get v i : ℝ)*C^2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hsq i) (Nat.cast_nonneg _)
      _ = _ := by
        simp only [Fin.sum_univ_succ, GP0031B3b_get, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Fin.sum_univ_zero, add_zero, Counts.total, Nat.cast_add]
        ring
  have hrep : designMean v m (fun q => (estimate (observed v q)-tau v)^2) =
      (∑ q ∈ (randomStates v m).toFinset, (multiplicity v q : ℝ) *
        ((∑ i, (GP0031B3b_get q i : ℝ)*c i) -
          (m : ℝ)/v.total * ∑ i, (GP0031B3b_get v i : ℝ)*c i)^2) / v.total.choose m := by
    unfold designMean
    rw [GP0031B3b_list_sum _ (GP0031B3b_randomStates_nodup v m)]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    dsimp only
    rw [GP0031B3b_estimator_score v q m hm hml (List.mem_toFinset.mp hq)]
  rw [hrep, GP0031B3b_score_moment v m c hm (by omega) hn]
  have hK : 0 ≤ (m : ℝ)*(v.total-m : ℕ)/((v.total : ℝ)*((v.total : ℝ)-1)) := by positivity
  calc
    _ ≤ (m : ℝ)*(v.total-m : ℕ)/((v.total : ℝ)*((v.total : ℝ)-1)) *
        ((v.total : ℝ)*C^2) := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact (sub_le_self _ (div_nonneg (sq_nonneg _) hnR.le)).trans hH
    _ = _ := by
      dsimp [C]
      rw [Nat.cast_sub (by omega : m ≤ v.total), Nat.cast_sub (by omega : 1 ≤ v.total)]
      have hl0' : (v.total : ℝ)-(m : ℝ) ≠ 0 := by
        rw [← Nat.cast_sub (by omega : m ≤ v.total)]
        exact hlR.ne'
      field_simp [hmR.ne', hl0', hnR.ne', hn1R.ne']
      <;> ring

private lemma GP0031B3b_t31_deviation_scaled (v o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (ht : v.total = o.total) :
    (deviationNumerator v o (o.a+o.b) : ℝ) =
      (o.total : ℝ)*(o.a+o.b : ℕ)*(o.c+o.d : ℕ)*(estimate o-tau v) := by
  have hm : ((o.a+o.b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have hl : ((o.c+o.d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ho.2.ne'
  have hn : (o.total : ℝ) ≠ 0 := by
    exact_mod_cast (show o.total ≠ 0 by dsimp [Counts.total]; omega)
  have hnR : (o.total : ℝ) = (o.a+o.b : ℕ)+(o.c+o.d : ℕ) := by
    simp only [Counts.total,Nat.cast_add]
    ring
  rw [GP0031B3b_t31_estimate_real,GP0031B3b_t31_tau_real]
  simp only [deviationNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast,ht]
  field_simp [hm,hl,hn]
  rw [hnR]
  ring

/-- Markov's squared-tail argument for the actual implemented p-value.
It also covers zero observed deviation, without dividing by that deviation. -/
lemma GP0031B3b_t31_tail_second_moment (v o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (ht : v.total = o.total) :
    (estimate o-tau v)^2*(pValue v o : ℝ) ≤
      designMean v (o.a+o.b) (fun q => (estimate (observed v q)-tau v)^2) := by
  let m : ℕ := o.a+o.b
  let C : ℝ := (o.total : ℝ)*(o.a+o.b : ℕ)*(o.c+o.d : ℕ)
  let E : Counts → Prop := fun q =>
    (deviationNumerator v o m).natAbs ≤
      (deviationNumerator v (observed v q) m).natAbs
  have hn : 0 < o.total := by dsimp [Counts.total]; omega
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by exact_mod_cast hn) (by exact_mod_cast ho.1))
      (by exact_mod_cast ho.2)
  have hmle : m ≤ v.total := by dsimp [m,Counts.total] at *; omega
  have hD : (0 : ℝ) < v.total.choose m := by exact_mod_cast Nat.choose_pos hmle
  have hprob : (pValue v o : ℝ) =
      ((randomStates v m).map fun q => if E q then (multiplicity v q : ℝ) else 0).sum /
        v.total.choose m := by
    unfold pValue tailCount
    rw [Rat.cast_div, Rat.cast_natCast, binomial_eq_choose]
    congr 1
    rw [Nat.cast_list_sum]
    simp only [List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    change ((if E q then multiplicity v q else 0 : ℕ) : ℝ) = _
    split_ifs <;> simp
  have hpoint (q : Counts) (hq : q ∈ randomStates v m) (hE : E q) :
      (estimate o-tau v)^2 ≤ (estimate (observed v q)-tau v)^2 := by
    have har := GP0031B3b_t31_observed_arms v q m hq
    have hqpos : 0 < (observed v q).a+(observed v q).b ∧
        0 < (observed v q).c+(observed v q).d := by
      rw [har.1,har.2.1]
      constructor
      · exact ho.1
      · have hot : o.total = o.a + o.b + (o.c + o.d) := by
          simp [Counts.total, Nat.add_assoc]
        rw [ht, hot]
        dsimp [m]
        omega
    have hqo := GP0031B3b_t31_deviation_scaled v (observed v q) hqpos har.2.2.symm
    have hctrl : v.total-m = o.c+o.d := by
      dsimp [m,Counts.total] at *
      omega
    rw [har.1,har.2.1,har.2.2,hctrl,ht] at hqo
    have hoD := GP0031B3b_t31_deviation_scaled v o ho ht
    have hprod : deviationNumerator v o m * deviationNumerator v o m ≤
        deviationNumerator v (observed v q) m *
          deviationNumerator v (observed v q) m :=
      (Int.natAbs_le_iff_mul_self_le).mp hE
    have hsq : (deviationNumerator v o m : ℝ)^2 ≤
        (deviationNumerator v (observed v q) m : ℝ)^2 := by
      have hprodR : (deviationNumerator v o m : ℝ)*(deviationNumerator v o m : ℝ) ≤
          (deviationNumerator v (observed v q) m : ℝ)*
            (deviationNumerator v (observed v q) m : ℝ) := by exact_mod_cast hprod
      simpa only [pow_two] using hprodR
    change (deviationNumerator v o (o.a+o.b) : ℝ)^2 ≤ _ at hsq
    rw [hoD,hqo] at hsq
    change (C*(estimate o-tau v))^2 ≤
      (C*(estimate (observed v q)-tau v))^2 at hsq
    have hsq' : C^2*(estimate o-tau v)^2 ≤
        C^2*(estimate (observed v q)-tau v)^2 := by
      simpa only [mul_pow] using hsq
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hC)).mp (by simpa [mul_comm] using hsq')
  have hsum := list_real_sum_le (randomStates v m)
    (fun q => if E q then (multiplicity v q : ℝ)*(estimate o-tau v)^2 else 0)
    (fun q => (multiplicity v q : ℝ)*(estimate (observed v q)-tau v)^2)
    (by
      intro q hq
      by_cases hE : E q
      · simp only [if_pos hE]
        exact mul_le_mul_of_nonneg_left (hpoint q hq hE) (Nat.cast_nonneg _)
      · simp only [if_neg hE]
        positivity)
  rw [hprob]
  change _ ≤ ((randomStates v m).map fun q =>
    (multiplicity v q : ℝ)*(estimate (observed v q)-tau v)^2).sum / v.total.choose m
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hD.le
  convert hsum using 1
  simp only [← List.sum_map_mul_left, mul_ite, mul_zero]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  split_ifs <;> ring

/-- An accepted effect inherits a radius bound from its centered second moment. -/
lemma GP0031B3b_t31_radius_of_moment_bound (o : Counts) (α V : ℝ)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hα : 0 < α)
    (hM : ∀ v, Possible o v →
      designMean v (o.a+o.b) (fun q => (estimate (observed v q)-tau v)^2) ≤ V) :
    ∀ t ∈ accepted α o, |t-estimate o| ≤ Real.sqrt (V/α) := by
  intro t ht
  obtain ⟨v,hv,hp,rfl⟩ := (GP0031B3b_t25_accepted_iff α o t).mp ht
  have htot := (possible_table_facts o v hv).1
  have htail := GP0031B3b_t31_tail_second_moment v o ho htot
  have hbound : (estimate o-tau v)^2*α ≤ V :=
    (mul_le_mul_of_nonneg_left hp (sq_nonneg _)).trans (htail.trans (hM v hv))
  have hsq : (tau v-estimate o)^2 ≤ V/α := by
    apply (le_div_iff₀ hα).mpr
    nlinarith
  exact Real.abs_le_sqrt hsq

lemma GP0031B3b_t31_endpoints_of_radius (o : Counts) (α R : ℝ)
    (hne : (accepted α o).Nonempty)
    (hR : ∀ t ∈ accepted α o, |t-estimate o| ≤ R) :
    upper α o-lower α o ≤ 2*R := by
  have hu : upper α o ∈ accepted α o := hne.csSup_mem
  have hl : lower α o ∈ accepted α o := hne.csInf_mem
  have hU := (abs_le.mp (hR (upper α o) hu)).2
  have hL := (abs_le.mp (hR (lower α o) hl)).1
  linarith

/-- Tail inversion, finite extrema, and simplification to the printed constant. -/
lemma GP0031B3b_t31_interval_length_of_moment_bound (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hα : 0 < α ∧ α < 1)
    (hne : (accepted α o).Nonempty)
    (hM : ∀ v, Possible o v →
      designMean v (o.a+o.b) (fun q => (estimate (observed v q)-tau v)^2) ≤
        (o.total : ℝ)^2/((o.total-1 : ℕ)*(o.a+o.b : ℕ)*(o.c+o.d : ℕ))) :
    upper α o-lower α o ≤ Real.sqrt
      ((4/α)*(o.total : ℝ)/(o.total-1 : ℕ)*
        ((o.total : ℝ)/((o.a+o.b : ℕ)*(o.c+o.d : ℕ)))) := by
  let V : ℝ := (o.total : ℝ)^2 /
    ((o.total-1 : ℕ)*(o.a+o.b : ℕ)*(o.c+o.d : ℕ))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hrad := GP0031B3b_t31_radius_of_moment_bound o α V ho hα.1 hM
  have hlen := GP0031B3b_t31_endpoints_of_radius o α (Real.sqrt (V/α)) hne hrad
  have hn : 2 ≤ o.total := by dsimp [Counts.total]; omega
  have hn1 : (((o.total-1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show o.total-1 ≠ 0 by omega)
  have hm : (((o.a+o.b : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast ho.1.ne'
  have hl : (((o.c+o.d : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast ho.2.ne'
  have hconst : (4/α)*(o.total : ℝ)/(o.total-1 : ℕ)*
        ((o.total : ℝ)/((o.a+o.b : ℕ)*(o.c+o.d : ℕ))) = 4*(V/α) := by
    dsimp [V]
    field_simp [hα.1.ne',hn1,hm,hl]
    <;> ring
  have hroot : 2*Real.sqrt (V/α) = Real.sqrt (4*(V/α)) := by
    have hs : (Real.sqrt (V/α))^2 = V/α := Real.sq_sqrt (div_nonneg hV hα.1.le)
    have hs' : (Real.sqrt (4*(V/α)))^2 = 4*(V/α) :=
      Real.sq_sqrt (mul_nonneg (by norm_num) (div_nonneg hV hα.1.le))
    have hp := Real.sqrt_nonneg (V/α)
    have hp' := Real.sqrt_nonneg (4*(V/α))
    nlinarith
  rw [hconst,← hroot]
  exact hlen

theorem interval_length_bound_proof (o : Counts) (α : ℝ)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hα : 0 < α ∧ α < 1)
    (hne : (accepted α o).Nonempty) :
    upper α o-lower α o ≤ Real.sqrt
      ((4/α)*(o.total : ℝ)/(o.total-1 : ℕ)*
        ((o.total : ℝ)/((o.a+o.b : ℕ)*(o.c+o.d : ℕ)))) := by
  apply GP0031B3b_t31_interval_length_of_moment_bound o α ho hα hne
  intro v hv
  have ht := (possible_table_facts o v hv).1
  have hctrl : v.total-(o.a+o.b) = o.c+o.d := by
    rw [ht]
    dsimp [Counts.total]
    omega
  have hm : o.a+o.b < v.total := by
    rw [ht]
    dsimp [Counts.total]
    omega
  have hb := GP0031B3b_moment_bound v (o.a+o.b) ho.1 hm
  rw [hctrl, ht] at hb
  exact hb

end AronowAudit.P003.Wave1
