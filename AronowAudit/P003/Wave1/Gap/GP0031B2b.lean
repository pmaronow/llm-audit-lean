import AronowAudit.P003.P003_Audit
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Balanced completion inclusion and missing-data coverage.

The tail comparison works directly with the compressed count distribution.
Pascal's identity splits a population containing one distinguished individual
into its treated and control cases. Changing one observed outcome toward the
plus completion increases its effect by one, changes every centered score by
one in absolute value, and decreases the observed tail threshold. Iteration
bounds the upper endpoint; guarded outcome complementation bounds the lower.
-/

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

lemma GP0031B2b_corrected_stratum_count_randomStates_iff (v q : Counts) (m : ℕ) :
    q ∈ randomStates v m ↔
      q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = m := by
  constructor
  · exact random_state_facts v m q
  · rintro ⟨ha, hb, hc, hd, ht⟩
    have hs : q.a + q.b + q.c + q.d = m := ht
    simp only [randomStates, List.mem_flatMap, List.mem_filterMap, List.mem_range]
    refine ⟨q.a, ?_, q.b, ?_, q.c, ?_, ?_⟩
    · exact Nat.lt_succ_of_le (le_min ha (by omega))
    · exact Nat.lt_succ_of_le (le_min hb (by omega))
    · exact Nat.lt_succ_of_le (le_min hc (by omega))
    · have he : m-q.a-q.b-q.c = q.d := by omega
      simp only [he, if_pos hd]

lemma GP0031B2b_corrected_stratum_count_mem (n : ℕ) (v : Counts) :
    v ∈ allCounts n ↔ v.total = n := by
  rw [allCounts, List.mem_toFinset, GP0031B2b_corrected_stratum_count_randomStates_iff]
  change (v.a ≤ n ∧ v.b ≤ n ∧ v.c ≤ n ∧ v.d ≤ n ∧ v.total = n) ↔ _
  constructor
  · exact fun h => h.2.2.2.2
  · intro ht
    dsimp [Counts.total] at ht
    exact ⟨by omega, by omega, by omega, by omega, ht⟩

def GP0031B2b_balanced_completion_inclusion_reverse (v : Counts) : Counts :=
  ⟨v.d, v.c, v.b, v.a⟩

lemma GP0031B2b_balanced_completion_inclusion_reverse_reverse (v : Counts) :
    GP0031B2b_balanced_completion_inclusion_reverse (GP0031B2b_balanced_completion_inclusion_reverse v) = v := by
  cases v
  rfl

lemma GP0031B2b_balanced_completion_inclusion_complement_complement (o : Counts) :
    complementObserved (complementObserved o) = o := by
  cases o
  rfl

lemma GP0031B2b_balanced_completion_inclusion_reverse_total (v : Counts) :
    (GP0031B2b_balanced_completion_inclusion_reverse v).total = v.total := by
  dsimp [GP0031B2b_balanced_completion_inclusion_reverse, Counts.total]
  omega

lemma GP0031B2b_balanced_completion_inclusion_reverse_effect (v : Counts) :
    (GP0031B2b_balanced_completion_inclusion_reverse v).effect = -v.effect := by
  dsimp [GP0031B2b_balanced_completion_inclusion_reverse, Counts.effect]
  ring

lemma GP0031B2b_balanced_completion_inclusion_reverse_tau (v : Counts) :
    tau (GP0031B2b_balanced_completion_inclusion_reverse v) = -tau v := by
  have hQ : tauQ (GP0031B2b_balanced_completion_inclusion_reverse v) = -tauQ v := by
    unfold tauQ
    rw [GP0031B2b_balanced_completion_inclusion_reverse_total,
      GP0031B2b_balanced_completion_inclusion_reverse_effect]
    push_cast
    ring
  simpa only [tau, Rat.cast_neg] using congrArg (fun x : ℚ => (x : ℝ)) hQ

/-- Positive arms are necessary here because rational division is total. -/
lemma GP0031B2b_balanced_completion_inclusion_complement_estimate (o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) :
    estimate (complementObserved o) = -estimate o := by
  have h₀ : (o.a : ℚ)+o.b ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast ho.1)
  have h₁ : (o.c : ℚ)+o.d ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast ho.2)
  have hQ : estimateQ (complementObserved o) = -estimateQ o := by
    dsimp [estimateQ, complementObserved]
    rw [add_comm (o.b : ℚ) (o.a : ℚ), add_comm (o.d : ℚ) (o.c : ℚ)]
    field_simp [h₀, h₁]
    ring
  simpa only [estimate, Rat.cast_neg] using congrArg (fun x : ℚ => (x : ℝ)) hQ

lemma GP0031B2b_balanced_completion_inclusion_possible_forward (o v : Counts)
    (hv : Possible o v) :
    Possible (complementObserved o) (GP0031B2b_balanced_completion_inclusion_reverse v) := by
  simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map,
    List.mem_range] at hv ⊢
  rcases hv with ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩
  dsimp [complementObserved]
  refine ⟨o.b-j, by omega, o.a-i, by omega,
    o.d-l, by omega, o.c-k, by omega, ?_⟩
  ext <;> dsimp [GP0031B2b_balanced_completion_inclusion_reverse] <;> omega

private lemma GP0031B2b_balanced_completion_inclusion_flatMap_nodup
    {A B : Type*} (xs : List A) (f : A → List B) (g : B → A)
    (hx : xs.Nodup) (hf : ∀ a ∈ xs, (f a).Nodup)
    (hg : ∀ a ∈ xs, ∀ b ∈ f a, g b = a) : (xs.flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨hf, ?_⟩
  -- Strengthen the pairwise relation only on members of the source list.
  apply (List.pairwise_iff_getElem).mpr
  intro i j hi hj hij
  intro b hbi hbj
  have hgi := hg xs[i] (List.getElem_mem hi) b hbi
  have hgj := hg xs[j] (List.getElem_mem hj) b hbj
  have he : xs[i] = xs[j] := hgi.symm.trans hgj
  have hidx : i = j := (List.Nodup.getElem_inj_iff hx).mp he
  omega

lemma GP0031B2b_balanced_completion_inclusion_randomStates_nodup (v : Counts) (m : ℕ) :
    (randomStates v m).Nodup := by
  let inner (a b : ℕ) : List Counts :=
    (List.range (min v.c (m-a-b)+1)).filterMap fun c =>
      if m-a-b-c ≤ v.d then some ⟨a,b,c,m-a-b-c⟩ else none
  have hinner (a b : ℕ) : (inner a b).Nodup := by
    apply List.Nodup.filterMap (l := List.range (min v.c (m-a-b)+1))
      (f := fun c => if m-a-b-c ≤ v.d then some (⟨a,b,c,m-a-b-c⟩ : Counts) else none)
      ?_ List.nodup_range
    intro c c' q hc hc'
    split_ifs at hc hc'
    · exact congrArg Counts.c (Option.some.inj (hc.trans hc'.symm))
    all_goals simp_all
  have hinner_coords (a b : ℕ) (q : Counts) (hq : q ∈ inner a b) :
      q.a = a ∧ q.b = b := by
    simp only [inner, List.mem_filterMap] at hq
    obtain ⟨c,hc,hret⟩ := hq
    split_ifs at hret with hd
    · simp only [Option.some.injEq] at hret
      subst q
      exact ⟨rfl,rfl⟩

  let middle (a : ℕ) : List Counts :=
    (List.range (min v.b (m-a)+1)).flatMap (inner a)
  have hmiddle (a : ℕ) : (middle a).Nodup := by
    apply GP0031B2b_balanced_completion_inclusion_flatMap_nodup _ (inner a) Counts.b
      List.nodup_range (fun b _ => hinner a b)
    intro b hb q hq
    exact (hinner_coords a b q hq).2
  have hmiddle_coord (a : ℕ) (q : Counts) (hq : q ∈ middle a) : q.a = a := by
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    exact (hinner_coords a b q hq).1
  change ((List.range (min v.a m+1)).flatMap middle).Nodup
  apply GP0031B2b_balanced_completion_inclusion_flatMap_nodup _ middle Counts.a
    List.nodup_range (fun a _ => hmiddle a)
  intro a ha q hq
  exact hmiddle_coord a q hq

lemma GP0031B2b_balanced_completion_inclusion_reverse_state (v q : Counts) (m : ℕ)
    (hq : q ∈ randomStates v m) :
    GP0031B2b_balanced_completion_inclusion_reverse q ∈
      randomStates (GP0031B2b_balanced_completion_inclusion_reverse v) m := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  apply (GP0031B2b_corrected_stratum_count_randomStates_iff _ _ _).mpr
  exact ⟨hd,hc,hb,ha, by rw [GP0031B2b_balanced_completion_inclusion_reverse_total, ht]⟩

lemma GP0031B2b_balanced_completion_inclusion_reverse_observed (v q : Counts)
    (ha : q.a ≤ v.a) (hb : q.b ≤ v.b) (hc : q.c ≤ v.c) (hd : q.d ≤ v.d) :
    observed (GP0031B2b_balanced_completion_inclusion_reverse v)
      (GP0031B2b_balanced_completion_inclusion_reverse q) = complementObserved (observed v q) := by
  ext <;> dsimp [observed, GP0031B2b_balanced_completion_inclusion_reverse, complementObserved] <;> omega

lemma GP0031B2b_balanced_completion_inclusion_reverse_multiplicity (v q : Counts) :
    multiplicity (GP0031B2b_balanced_completion_inclusion_reverse v)
      (GP0031B2b_balanced_completion_inclusion_reverse q) = multiplicity v q := by
  dsimp [multiplicity, GP0031B2b_balanced_completion_inclusion_reverse]
  ring

lemma GP0031B2b_balanced_completion_inclusion_complement_deviation (v o : Counts)
    (hn : v.total = o.total) :
    deviationNumerator (GP0031B2b_balanced_completion_inclusion_reverse v)
      (complementObserved o) (o.a+o.b) = -deviationNumerator v o (o.a+o.b) := by
  have hZ : (v.total : ℤ) = (o.a : ℤ)+o.b+o.c+o.d := by
    exact_mod_cast hn
  unfold deviationNumerator
  rw [GP0031B2b_balanced_completion_inclusion_reverse_total,
    GP0031B2b_balanced_completion_inclusion_reverse_effect]
  dsimp [complementObserved]
  push_cast
  rw [hZ]
  ring

/-- The outcome-complementation p-value identity requires equal table totals,
even when both observed arms are positive. -/
lemma GP0031B2b_balanced_completion_inclusion_complement_pValue (v o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hn : v.total = o.total) :
    pValue (⟨v.d,v.c,v.b,v.a⟩ : Counts) (complementObserved o) = pValue v o := by
  change pValue (GP0031B2b_balanced_completion_inclusion_reverse v) (complementObserved o) = _
  have hm : (complementObserved o).a+(complementObserved o).b = o.a+o.b := by
    dsimp [complementObserved]
    omega
  have htail : tailCount (GP0031B2b_balanced_completion_inclusion_reverse v) (complementObserved o) =
      tailCount v o := by
    unfold tailCount
    rw [hm]
    rw [← List.sum_toFinset _ (GP0031B2b_balanced_completion_inclusion_randomStates_nodup _ _),
      ← List.sum_toFinset _ (GP0031B2b_balanced_completion_inclusion_randomStates_nodup _ _)]
    symm
    apply Finset.sum_nbij' GP0031B2b_balanced_completion_inclusion_reverse
      GP0031B2b_balanced_completion_inclusion_reverse
    · intro q hq
      exact List.mem_toFinset.mpr (GP0031B2b_balanced_completion_inclusion_reverse_state _ _ _
        (List.mem_toFinset.mp hq))
    · intro q hq
      have h := GP0031B2b_balanced_completion_inclusion_reverse_state _ _ _ (List.mem_toFinset.mp hq)
      simpa only [GP0031B2b_balanced_completion_inclusion_reverse_reverse, List.mem_toFinset] using h
    · intro q hq
      exact GP0031B2b_balanced_completion_inclusion_reverse_reverse q
    · intro q hq
      exact GP0031B2b_balanced_completion_inclusion_reverse_reverse q
    · intro q hq
      have hq' := List.mem_toFinset.mp hq
      obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v (o.a+o.b) q hq'
      have hobs : v.total = (observed v q).total := by
        dsimp [observed, Counts.total]
        omega
      have hmq : (observed v q).a+(observed v q).b = o.a+o.b := by
        dsimp [observed]
        change q.a+q.b+(q.c+q.d) = o.a+o.b
        dsimp [Counts.total] at ht
        omega
      rw [GP0031B2b_balanced_completion_inclusion_reverse_observed v q ha hb hc hd,
        GP0031B2b_balanced_completion_inclusion_reverse_multiplicity]
      have hdev := GP0031B2b_balanced_completion_inclusion_complement_deviation v (observed v q) hobs
      rw [hmq] at hdev
      rw [hdev, GP0031B2b_balanced_completion_inclusion_complement_deviation v o hn,
        Int.natAbs_neg, Int.natAbs_neg]
  unfold pValue
  rw [htail, GP0031B2b_balanced_completion_inclusion_reverse_total, hm]

lemma GP0031B2b_balanced_completion_inclusion_accepted_spec (α : ℝ) (o : Counts) (t : ℝ) :
    t ∈ accepted α o ↔ ∃ v, Possible o v ∧ α ≤ (pValue v o : ℝ) ∧ tau v = t := by
  simp only [accepted, Finset.mem_image, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq, Possible, and_assoc]

/-- Acceptance is transported through the possibility bijection. Every
p-value call gets its total equality from the actual possible-table witness. -/
lemma GP0031B2b_balanced_completion_inclusion_complement_accepted (α : ℝ) (o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) :
    accepted α (complementObserved o) = (accepted α o).image (fun t => -t) := by
  have hoC : 0 < (complementObserved o).a+(complementObserved o).b ∧
      0 < (complementObserved o).c+(complementObserved o).d := by
    dsimp [complementObserved]
    constructor <;> omega
  ext t
  constructor
  · intro ht
    obtain ⟨v,hv,hp,rfl⟩ := (GP0031B2b_balanced_completion_inclusion_accepted_spec _ _ _).mp ht
    have hn : v.total = (complementObserved o).total := (possible_table_facts _ _ hv).1
    have hvC := GP0031B2b_balanced_completion_inclusion_possible_forward _ _ hv
    rw [GP0031B2b_balanced_completion_inclusion_complement_complement] at hvC
    have hpC := GP0031B2b_balanced_completion_inclusion_complement_pValue v (complementObserved o) hoC hn
    rw [GP0031B2b_balanced_completion_inclusion_complement_complement] at hpC
    have hacc : tau (GP0031B2b_balanced_completion_inclusion_reverse v) ∈ accepted α o := by
      apply accepted_of_possible _ _ _ hvC
      change α ≤ (pValue (⟨v.d,v.c,v.b,v.a⟩ : Counts) o : ℝ)
      rw [hpC]
      exact hp
    apply Finset.mem_image.mpr
    exact ⟨_,hacc,by rw [GP0031B2b_balanced_completion_inclusion_reverse_tau, neg_neg]⟩
  · intro ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v,hv,hp,rfl⟩ := (GP0031B2b_balanced_completion_inclusion_accepted_spec _ _ _).mp hs
    have hn : v.total = o.total := (possible_table_facts _ _ hv).1
    rw [← GP0031B2b_balanced_completion_inclusion_reverse_tau]
    apply accepted_of_possible _ _ _ (GP0031B2b_balanced_completion_inclusion_possible_forward _ _ hv)
    change α ≤ (pValue (⟨v.d,v.c,v.b,v.a⟩ : Counts) (complementObserved o) : ℝ)
    rw [GP0031B2b_balanced_completion_inclusion_complement_pValue v o ho hn]
    exact hp

lemma GP0031B2b_balanced_completion_inclusion_completion_arms (o r c : Counts)
    (hr : r ∈ missingMasks o) (hc : c ∈ completions o r) :
    c.a+c.b = o.a+o.b ∧ c.c+c.d = o.c+o.d := by
  obtain ⟨ha,hb,hc',hd⟩ := missing_mask_facts o r hr
  simp only [completions, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨t,ht,s,hs,rfl⟩ := hc
  dsimp
  constructor <;> omega

/-- The guards needed for complementation in the lower-endpoint argument. -/
lemma GP0031B2b_balanced_completion_inclusion_plus_mem (o r : Counts)
    (hr : r ∈ missingMasks o) : plusCompletion o r ∈ completions o r := by
  obtain ⟨ha,hb,hc,hd⟩ := missing_mask_facts o r hr
  simp only [completions, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨r.a+r.b, by omega, 0, by omega, ?_⟩
  ext <;> dsimp [plusCompletion] <;> omega

lemma GP0031B2b_balanced_completion_inclusion_minus_mem (o r : Counts)
    (hr : r ∈ missingMasks o) : minusCompletion o r ∈ completions o r := by
  obtain ⟨ha,hb,hc,hd⟩ := missing_mask_facts o r hr
  simp only [completions, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨0, by omega, r.c+r.d, by omega, ?_⟩
  ext <;> dsimp [minusCompletion] <;> omega

lemma GP0031B2b_balanced_completion_inclusion_complement_nonempty (α : ℝ) (o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) :
    (accepted α (complementObserved o)).Nonempty ↔ (accepted α o).Nonempty := by
  rw [GP0031B2b_balanced_completion_inclusion_complement_accepted α o ho]
  exact Finset.image_nonempty

lemma GP0031B2b_balanced_completion_inclusion_complement_upper (α : ℝ) (o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) (hne : (accepted α o).Nonempty) :
    upper α (complementObserved o) = -lower α o := by
  change sSup (↑(accepted α (complementObserved o)) : Set ℝ) = _
  apply IsGreatest.csSup_eq
  constructor
  · rw [GP0031B2b_balanced_completion_inclusion_complement_accepted α o ho]
    exact Finset.mem_image.mpr ⟨lower α o, hne.csInf_mem, rfl⟩
  · intro t ht
    rw [GP0031B2b_balanced_completion_inclusion_complement_accepted α o ho] at ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    apply neg_le_neg
    exact csInf_le (accepted α o).finite_toSet.bddBelow hs

/-- The whole endpoint, including its empty-accepted-set fallback, negates.
This avoids any use of an unjustified extremum of an empty set. -/
lemma GP0031B2b_balanced_completion_inclusion_complement_endpoint (α : ℝ) (o : Counts)
    (ho : 0 < o.a+o.b ∧ 0 < o.c+o.d) :
    (if (accepted α (complementObserved o)).Nonempty then
        max (upper α (complementObserved o)) (estimate (complementObserved o))
      else estimate (complementObserved o)) =
    -(if (accepted α o).Nonempty then min (lower α o) (estimate o) else estimate o) := by
  by_cases hne : (accepted α o).Nonempty
  · have hneC := (GP0031B2b_balanced_completion_inclusion_complement_nonempty α o ho).mpr hne
    rw [if_pos hneC, if_pos hne,
      GP0031B2b_balanced_completion_inclusion_complement_upper α o ho hne,
      GP0031B2b_balanced_completion_inclusion_complement_estimate o ho]
    by_cases hle : lower α o ≤ estimate o
    · rw [min_eq_left hle, max_eq_left (neg_le_neg hle)]
    · have hge : estimate o ≤ lower α o := le_of_not_ge hle
      rw [min_eq_right hge, max_eq_right (neg_le_neg hge)]
  · have hneC := mt (GP0031B2b_balanced_completion_inclusion_complement_nonempty α o ho).mp hne
    rw [if_neg hneC, if_neg hne,
      GP0031B2b_balanced_completion_inclusion_complement_estimate o ho]

/-! The observed arms in the balanced design both have size `m`; they are positive when `0 < m`. -/

lemma GP0031B2b_balanced_missing_coverage_observed_arms (v : Counts) (m : ℕ)
    (hn : v.total = 2*m) (q : Counts) (hq : q ∈ randomStates v m) :
    (observed v q).a+(observed v q).b = m ∧
      (observed v q).c+(observed v q).d = m := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  dsimp [observed]
  dsimp [Counts.total] at hn ht
  constructor <;> omega


/-! A one-individual decomposition of the actual binomial weights. -/
def GP0031B2b_coord (v : Counts) (i : Fin 4) : ℕ := ![v.a,v.b,v.c,v.d] i

def GP0031B2b_add (v : Counts) (i : Fin 4) : Counts :=
  ⟨v.a + if i = 0 then 1 else 0, v.b + if i = 1 then 1 else 0,
   v.c + if i = 2 then 1 else 0, v.d + if i = 3 then 1 else 0⟩

def GP0031B2b_sub (v : Counts) (i : Fin 4) : Counts :=
  ⟨v.a - if i = 0 then 1 else 0, v.b - if i = 1 then 1 else 0,
   v.c - if i = 2 then 1 else 0, v.d - if i = 3 then 1 else 0⟩

lemma GP0031B2b_add_total (v : Counts) (i : Fin 4) :
    (GP0031B2b_add v i).total = v.total + 1 := by
  fin_cases i <;> simp [GP0031B2b_add, Counts.total] <;> omega

lemma GP0031B2b_sub_total (v : Counts) (i : Fin 4)
    (h : 0 < GP0031B2b_coord v i) :
    (GP0031B2b_sub v i).total + 1 = v.total := by
  fin_cases i <;> simp [GP0031B2b_coord] at h <;>
    simp [GP0031B2b_sub, Counts.total] <;> omega

lemma GP0031B2b_sub_add (v : Counts) (i : Fin 4) :
    GP0031B2b_sub (GP0031B2b_add v i) i = v := by
  fin_cases i <;> ext <;> simp [GP0031B2b_sub, GP0031B2b_add]

lemma GP0031B2b_add_sub (v : Counts) (i : Fin 4)
    (h : 0 < GP0031B2b_coord v i) :
    GP0031B2b_add (GP0031B2b_sub v i) i = v := by
  fin_cases i <;> simp [GP0031B2b_coord] at h <;>
    ext <;> simp [GP0031B2b_sub, GP0031B2b_add] <;> omega

lemma GP0031B2b_coord_add (v : Counts) (i : Fin 4) :
    0 < GP0031B2b_coord (GP0031B2b_add v i) i := by
  fin_cases i <;> simp [GP0031B2b_coord, GP0031B2b_add]

lemma GP0031B2b_mult_add (v q : Counts) (i : Fin 4) :
    multiplicity (GP0031B2b_add v i) q = multiplicity v q +
      if 0 < GP0031B2b_coord q i then multiplicity v (GP0031B2b_sub q i) else 0 := by
  rcases q with ⟨a,b,c,d⟩
  fin_cases i
  · cases a <;> simp [GP0031B2b_add, GP0031B2b_coord, GP0031B2b_sub,
      multiplicity, binomial_eq_choose, Nat.choose_succ_succ] <;> ring
  · cases b <;> simp [GP0031B2b_add, GP0031B2b_coord, GP0031B2b_sub,
      multiplicity, binomial_eq_choose, Nat.choose_succ_succ] <;> ring
  · cases c <;> simp [GP0031B2b_add, GP0031B2b_coord, GP0031B2b_sub,
      multiplicity, binomial_eq_choose, Nat.choose_succ_succ] <;> ring
  · cases d <;> simp [GP0031B2b_add, GP0031B2b_coord, GP0031B2b_sub,
      multiplicity, binomial_eq_choose, Nat.choose_succ_succ] <;> ring

noncomputable def GP0031B2b_weighted (v : Counts) (m : ℕ) (f : Counts → ℕ) : ℕ :=
  ∑ q ∈ allCounts m, multiplicity v q * f q

lemma GP0031B2b_weighted_add (v : Counts) (m : ℕ) (i : Fin 4) (f : Counts → ℕ) :
    GP0031B2b_weighted (GP0031B2b_add v i) (m+1) f =
      GP0031B2b_weighted v (m+1) f +
      GP0031B2b_weighted v m (fun q => f (GP0031B2b_add q i)) := by
  unfold GP0031B2b_weighted
  simp_rw [GP0031B2b_mult_add, add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  have he : (∑ q ∈ allCounts (m+1),
      (if 0 < GP0031B2b_coord q i then multiplicity v (GP0031B2b_sub q i) else 0) * f q) =
      ∑ q ∈ (allCounts (m+1)).filter (fun q => 0 < GP0031B2b_coord q i),
        multiplicity v (GP0031B2b_sub q i) * f q := by
    simp only [Finset.sum_filter, ite_mul, zero_mul]
  rw [he]
  symm
  apply Finset.sum_nbij' (fun q => GP0031B2b_add q i) (fun q => GP0031B2b_sub q i)
  · intro q hq
    apply Finset.mem_filter.mpr
    refine ⟨?_, GP0031B2b_coord_add q i⟩
    rw [GP0031B2b_corrected_stratum_count_mem, GP0031B2b_add_total,
      (GP0031B2b_corrected_stratum_count_mem _ _).mp hq]
  · intro q hq
    obtain ⟨hq,hpos⟩ := Finset.mem_filter.mp hq
    rw [GP0031B2b_corrected_stratum_count_mem] at hq ⊢
    have ht := GP0031B2b_sub_total q i hpos
    omega
  · intro q _
    exact GP0031B2b_sub_add q i
  · intro q hq
    exact GP0031B2b_add_sub q i (Finset.mem_filter.mp hq).2
  · intro q _
    rw [GP0031B2b_sub_add]


lemma GP0031B2b_mult_zero (v q : Counts) (m : ℕ) (ht : q.total = m)
    (hq : q ∉ randomStates v m) : multiplicity v q = 0 := by
  by_cases ha : q.a ≤ v.a
  · by_cases hb : q.b ≤ v.b
    · by_cases hc : q.c ≤ v.c
      · by_cases hd : q.d ≤ v.d
        · exact False.elim (hq ((GP0031B2b_corrected_stratum_count_randomStates_iff _ _ _).mpr
            ⟨ha,hb,hc,hd,ht⟩))
        · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hd)]
      · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc)]
    · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hb)]
  · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]

lemma GP0031B2b_weighted_list (v : Counts) (m : ℕ) (f : Counts → ℕ) :
    GP0031B2b_weighted v m f =
      ((randomStates v m).map fun q => multiplicity v q * f q).sum := by
  rw [← List.sum_toFinset _ (GP0031B2b_balanced_completion_inclusion_randomStates_nodup _ _)]
  unfold GP0031B2b_weighted
  symm
  apply Finset.sum_subset
  · intro q hq
    rw [GP0031B2b_corrected_stratum_count_mem]
    exact (random_state_facts v m q (List.mem_toFinset.mp hq)).2.2.2.2
  · intro q hq hnot
    have hz := GP0031B2b_mult_zero v q m
      ((GP0031B2b_corrected_stratum_count_mem _ _).mp hq)
      (fun h => hnot (List.mem_toFinset.mpr h))
    rw [hz, zero_mul]

def GP0031B2b_score (v q : Counts) : ℤ :=
  4*(q.a : ℤ)+2*q.b+2*q.c-2*v.a-v.b-v.c

def GP0031B2b_threshold (v o : Counts) : ℤ := 2*((o.a : ℤ)-o.c)-v.effect

def GP0031B2b_tailIndicator (v o q : Counts) : ℕ :=
  if (GP0031B2b_threshold v o).natAbs ≤ (GP0031B2b_score v q).natAbs then 1 else 0

lemma GP0031B2b_dev_obs (v o : Counts) (m : ℕ)
    (hn : v.total = 2*m) :
    deviationNumerator v o m = (m : ℤ)^2 * GP0031B2b_threshold v o := by
  unfold deviationNumerator GP0031B2b_threshold
  rw [hn]
  push_cast
  ring

lemma GP0031B2b_dev_state (v q : Counts) (m : ℕ)
    (hn : v.total = 2*m) (hq : q ∈ randomStates v m) :
    deviationNumerator v (observed v q) m = (m : ℤ)^2 * GP0031B2b_score v q := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  rw [GP0031B2b_dev_obs v (observed v q) m hn]
  congr 1
  dsimp [GP0031B2b_threshold, GP0031B2b_score, observed, Counts.effect]
  rw [Nat.cast_sub (by omega : q.c ≤ v.a-q.a+v.c), Nat.cast_add, Nat.cast_sub ha]
  push_cast
  ring

lemma GP0031B2b_tail_weighted (v o : Counts) (m : ℕ)
    (hm : 0 < m) (hn : v.total = 2*m) (ho : o.a+o.b = m) :
    tailCount v o = GP0031B2b_weighted v m (GP0031B2b_tailIndicator v o) := by
  rw [GP0031B2b_weighted_list]
  unfold tailCount
  rw [ho]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  rw [GP0031B2b_dev_state v q m hn hq, GP0031B2b_dev_obs v o m hn]
  simp only [Int.natAbs_mul]
  have hpos : 0 < ((m : ℤ)^2).natAbs := by positivity
  have he : ((m : ℤ)^2).natAbs * (GP0031B2b_threshold v o).natAbs ≤
      ((m : ℤ)^2).natAbs * (GP0031B2b_score v q).natAbs ↔
      (GP0031B2b_threshold v o).natAbs ≤ (GP0031B2b_score v q).natAbs :=
    mul_le_mul_iff_right₀ hpos
  simp only [he, GP0031B2b_tailIndicator]
  split_ifs <;> simp

lemma GP0031B2b_tail_indicator_mono (v v' o o' q q' : Counts)
    (ht : GP0031B2b_threshold v' o' = GP0031B2b_threshold v o + 1)
    (hneg : GP0031B2b_threshold v' o' ≤ 0)
    (hs : GP0031B2b_score v' q' = GP0031B2b_score v q + 1 ∨
      GP0031B2b_score v' q' = GP0031B2b_score v q - 1) :
    GP0031B2b_tailIndicator v o q ≤ GP0031B2b_tailIndicator v' o' q' := by
  unfold GP0031B2b_tailIndicator
  split_ifs with h h'
  · rfl
  · exfalso
    have ha := Int.natAbs_eq (GP0031B2b_threshold v o)
    have hb := Int.natAbs_eq (GP0031B2b_threshold v' o')
    have hc := Int.natAbs_eq (GP0031B2b_score v q)
    have hd := Int.natAbs_eq (GP0031B2b_score v' q')
    omega
  all_goals omega


lemma GP0031B2b_pvalue_step (u o o' : Counts) (i j : Fin 4) (m : ℕ)
    (hm : 0 < m) (hn : u.total+1 = 2*m)
    (ho : o.a+o.b = m) (ho' : o'.a+o'.b = m)
    (ht : GP0031B2b_threshold (GP0031B2b_add u i) o' =
      GP0031B2b_threshold (GP0031B2b_add u j) o + 1)
    (hneg : GP0031B2b_threshold (GP0031B2b_add u i) o' ≤ 0)
    (hs : ∀ q, GP0031B2b_score (GP0031B2b_add u i) q =
      GP0031B2b_score (GP0031B2b_add u j) q + 1 ∨
      GP0031B2b_score (GP0031B2b_add u i) q =
      GP0031B2b_score (GP0031B2b_add u j) q - 1)
    (hs' : ∀ q, GP0031B2b_score (GP0031B2b_add u i) (GP0031B2b_add q i) =
      GP0031B2b_score (GP0031B2b_add u j) (GP0031B2b_add q j) + 1 ∨
      GP0031B2b_score (GP0031B2b_add u i) (GP0031B2b_add q i) =
      GP0031B2b_score (GP0031B2b_add u j) (GP0031B2b_add q j) - 1) :
    pValue (GP0031B2b_add u j) o ≤ pValue (GP0031B2b_add u i) o' := by
  have hn' (k : Fin 4) : (GP0031B2b_add u k).total = 2*m := by
    rw [GP0031B2b_add_total, hn]
  unfold pValue
  rw [hn' i, hn' j, ho, ho']
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  rw [GP0031B2b_tail_weighted _ _ m hm (hn' j) ho,
    GP0031B2b_tail_weighted _ _ m hm (hn' i) ho']
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [GP0031B2b_weighted_add, GP0031B2b_weighted_add]
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro q _
    exact Nat.mul_le_mul_left _ (GP0031B2b_tail_indicator_mono _ _ _ _ _ _ ht hneg (hs q))
  · apply Finset.sum_le_sum
    intro q _
    exact Nat.mul_le_mul_left _ (GP0031B2b_tail_indicator_mono _ _ _ _ _ _ ht hneg (hs' q))

lemma GP0031B2b_treated_step (u : Counts) (a b c d m : ℕ) (i j : Fin 4)
    (hij : (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3))
    (hm : 0 < m) (hn : u.total+1 = 2*m) (ho : a+b+1 = m)
    (hneg : GP0031B2b_threshold (GP0031B2b_add u j) ⟨a,b+1,c,d⟩ ≤ -1) :
    pValue (GP0031B2b_add u j) ⟨a,b+1,c,d⟩ ≤
      pValue (GP0031B2b_add u i) ⟨a+1,b,c,d⟩ := by
  have ht : GP0031B2b_threshold (GP0031B2b_add u i) ⟨a+1,b,c,d⟩ =
      GP0031B2b_threshold (GP0031B2b_add u j) ⟨a,b+1,c,d⟩ + 1 := by
    rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [GP0031B2b_threshold, GP0031B2b_add, Counts.effect] <;> omega
  apply GP0031B2b_pvalue_step u _ _ i j m hm hn (by dsimp; omega) (by dsimp; omega) ht
    (by omega)
  · intro q
    rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> right <;>
      simp [GP0031B2b_score, GP0031B2b_add] <;> omega
  · intro q
    rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> left <;>
      simp [GP0031B2b_score, GP0031B2b_add] <;> omega

lemma GP0031B2b_control_step (u : Counts) (a b c d m : ℕ) (i j : Fin 4)
    (hij : (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 2))
    (hm : 0 < m) (hn : u.total+1 = 2*m) (ho : a+b = m)
    (hneg : GP0031B2b_threshold (GP0031B2b_add u j) ⟨a,b,c+1,d⟩ ≤ -1) :
    pValue (GP0031B2b_add u j) ⟨a,b,c+1,d⟩ ≤
      pValue (GP0031B2b_add u i) ⟨a,b,c,d+1⟩ := by
  have ht : GP0031B2b_threshold (GP0031B2b_add u i) ⟨a,b,c,d+1⟩ =
      GP0031B2b_threshold (GP0031B2b_add u j) ⟨a,b,c+1,d⟩ + 1 := by
    rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [GP0031B2b_threshold, GP0031B2b_add, Counts.effect] <;> omega
  apply GP0031B2b_pvalue_step u _ _ i j m hm hn ho ho ht (by omega)
  · intro q
    rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> left <;>
      simp [GP0031B2b_score, GP0031B2b_add] <;> omega
  · intro q
    rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> right <;>
      simp [GP0031B2b_score, GP0031B2b_add] <;> omega


lemma GP0031B2b_possible_treated (a b c d m : ℕ) (v : Counts)
    (hm : 0 < m) (ho : a+b+1 = m) (hc : c+d = m)
    (hv : Possible ⟨a,b+1,c,d⟩ v)
    (hneg : GP0031B2b_threshold v ⟨a,b+1,c,d⟩ ≤ -1) :
    ∃ v', Possible ⟨a+1,b,c,d⟩ v' ∧ v'.total = v.total ∧
      v'.effect = v.effect+1 ∧ pValue v ⟨a,b+1,c,d⟩ ≤ pValue v' ⟨a+1,b,c,d⟩ := by
  have hn := (possible_table_facts _ _ hv).1
  simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range] at hv
  obtain ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩ := hv
  by_cases hj0 : j = 0
  · subst j
    let u : Counts := ⟨i+k,a-i+l,c-k,b+d-l⟩
    have he : GP0031B2b_add u 3 = (⟨i+k,a-i+l,c-k+0,b+1+d-0-l⟩ : Counts) := by
      ext <;> simp [GP0031B2b_add, u] <;> omega
    refine ⟨GP0031B2b_add u 1, ?_, ?_, ?_, ?_⟩
    · simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range]
      refine ⟨i, by omega, 0, by omega,
        k, by omega, l, by omega, ?_⟩
      ext <;> simp [GP0031B2b_add, u] <;> omega
    · rw [← he, GP0031B2b_add_total, GP0031B2b_add_total]
    · simp [GP0031B2b_add, Counts.effect, u]; omega
    · rw [← he]
      refine GP0031B2b_treated_step u a b c d m 1 3 (Or.inr ⟨rfl,rfl⟩) hm ?_ ho ?_
      · rw [← GP0031B2b_add_total u 3, he, hn]
        dsimp [Counts.total]
        omega
      · simpa only [he] using hneg
  · have hjp : 0 < j := by omega
    let u : Counts := ⟨i+k,a-i+l,c-k+(j-1),b+1+d-j-l⟩
    have he : GP0031B2b_add u 2 = (⟨i+k,a-i+l,c-k+j,b+1+d-j-l⟩ : Counts) := by
      ext <;> simp [GP0031B2b_add, u] <;> omega
    refine ⟨GP0031B2b_add u 0, ?_, ?_, ?_, ?_⟩
    · simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range]
      refine ⟨i+1, by omega, j-1, by omega,
        k, by omega, l, by omega, ?_⟩
      ext <;> simp [GP0031B2b_add, u] <;> omega
    · rw [← he, GP0031B2b_add_total, GP0031B2b_add_total]
    · simp [GP0031B2b_add, Counts.effect, u]; omega
    · rw [← he]
      refine GP0031B2b_treated_step u a b c d m 0 2 (Or.inl ⟨rfl,rfl⟩) hm ?_ ho ?_
      · rw [← GP0031B2b_add_total u 2, he, hn]
        dsimp [Counts.total]
        omega
      · simpa only [he] using hneg

lemma GP0031B2b_possible_control (a b c d m : ℕ) (v : Counts)
    (hm : 0 < m) (ho : a+b = m) (hc : c+d+1 = m)
    (hv : Possible ⟨a,b,c+1,d⟩ v)
    (hneg : GP0031B2b_threshold v ⟨a,b,c+1,d⟩ ≤ -1) :
    ∃ v', Possible ⟨a,b,c,d+1⟩ v' ∧ v'.total = v.total ∧
      v'.effect = v.effect+1 ∧ pValue v ⟨a,b,c+1,d⟩ ≤ pValue v' ⟨a,b,c,d+1⟩ := by
  have hn := (possible_table_facts _ _ hv).1
  simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range] at hv
  obtain ⟨i,hi,j,hj,k,hk,l,hl,rfl⟩ := hv
  by_cases hk0 : k = 0
  · subst k
    let u : Counts := ⟨i,a-i+l,c+j,b+d-j-l⟩
    have he : GP0031B2b_add u 2 = (⟨i+0,a-i+l,c+1-0+j,b+d-j-l⟩ : Counts) := by
      ext <;> simp [GP0031B2b_add, u] <;> omega
    refine ⟨GP0031B2b_add u 3, ?_, ?_, ?_, ?_⟩
    · simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range]
      refine ⟨i, by omega, j, by omega,
        0, by omega, l, by omega, ?_⟩
      ext <;> simp [GP0031B2b_add, u] <;> omega
    · rw [← he, GP0031B2b_add_total, GP0031B2b_add_total]
    · simp [GP0031B2b_add, Counts.effect, u]; omega
    · rw [← he]
      refine GP0031B2b_control_step u a b c d m 3 2 (Or.inr ⟨rfl,rfl⟩) hm ?_ ho ?_
      · rw [← GP0031B2b_add_total u 2, he, hn]
        dsimp [Counts.total]
        omega
      · simpa only [he] using hneg
  · have hkp : 0 < k := by omega
    let u : Counts := ⟨i+(k-1),a-i+l,c+1-k+j,b+d-j-l⟩
    have he : GP0031B2b_add u 0 = (⟨i+k,a-i+l,c+1-k+j,b+d-j-l⟩ : Counts) := by
      ext <;> simp [GP0031B2b_add, u] <;> omega
    refine ⟨GP0031B2b_add u 1, ?_, ?_, ?_, ?_⟩
    · simp only [Possible, possibleTables, List.mem_flatMap, List.mem_map, List.mem_range]
      refine ⟨i, by omega, j, by omega,
        k-1, by omega, l+1, by omega, ?_⟩
      ext <;> simp [GP0031B2b_add, u] <;> omega
    · rw [← he, GP0031B2b_add_total, GP0031B2b_add_total]
    · simp [GP0031B2b_add, Counts.effect, u]; omega
    · rw [← he]
      refine GP0031B2b_control_step u a b c d m 1 0 (Or.inl ⟨rfl,rfl⟩) hm ?_ ho ?_
      · rw [← GP0031B2b_add_total u 0, he, hn]
        dsimp [Counts.total]
        omega
      · simpa only [he] using hneg


lemma GP0031B2b_transport (h : Counts) (m : ℕ) (hm : 0 < m)
    (hh : h.a+h.b = m ∧ h.c+h.d = m)
    (o v : Counts) (ho : o.a+o.b = m ∧ o.c+o.d = m)
    (hv : Possible o v) (ha : o.a ≤ h.a) (hc : h.c ≤ o.c)
    (ht : 2*((h.a : ℤ)-h.c) < v.effect) :
    ∃ v', Possible h v' ∧ v.effect ≤ v'.effect ∧ pValue v o ≤ pValue v' h := by
  generalize he : h.a-o.a+(o.c-h.c) = k
  induction k using Nat.strong_induction_on generalizing o v with
  | h k ih =>
    by_cases hat : o.a < h.a
    · have hb : 0 < o.b := by omega
      have heo : (⟨o.a,(o.b-1)+1,o.c,o.d⟩ : Counts) = o := by ext <;> dsimp <;> omega
      have hneg : GP0031B2b_threshold v ⟨o.a,(o.b-1)+1,o.c,o.d⟩ ≤ -1 := by
        dsimp [GP0031B2b_threshold]
        omega
      obtain ⟨w,hw,hn,hwE,hp⟩ := GP0031B2b_possible_treated o.a (o.b-1) o.c o.d m v
        hm (by omega) ho.2 (heo ▸ hv) hneg
      let o' : Counts := ⟨o.a+1,o.b-1,o.c,o.d⟩
      have hk : h.a-o'.a+(o'.c-h.c) < k := by dsimp [o']; omega
      obtain ⟨v',hv',hE,hp'⟩ := ih _ hk o' w (by dsimp [o']; constructor <;> omega)
        hw (by dsimp [o']; omega) (by dsimp [o']; exact hc) (by omega) rfl
      refine ⟨v',hv',by omega,?_⟩
      rw [heo] at hp
      exact le_trans hp hp'
    · by_cases hct : h.c < o.c
      · have heo : (⟨o.a,o.b,(o.c-1)+1,o.d⟩ : Counts) = o := by ext <;> dsimp <;> omega
        have hneg : GP0031B2b_threshold v ⟨o.a,o.b,(o.c-1)+1,o.d⟩ ≤ -1 := by
          dsimp [GP0031B2b_threshold]
          omega
        obtain ⟨w,hw,hn,hwE,hp⟩ := GP0031B2b_possible_control o.a o.b (o.c-1) o.d m v
          hm ho.1 (by omega) (heo ▸ hv) hneg
        let o' : Counts := ⟨o.a,o.b,o.c-1,o.d+1⟩
        have hk : h.a-o'.a+(o'.c-h.c) < k := by dsimp [o']; omega
        obtain ⟨v',hv',hE,hp'⟩ := ih _ hk o' w (by dsimp [o']; constructor <;> omega)
          hw (by dsimp [o']; exact ha) (by dsimp [o']; omega) (by omega) rfl
        refine ⟨v',hv',by omega,?_⟩
        rw [heo] at hp
        exact le_trans hp hp'
      · have hoe : o = h := by ext <;> omega
        subst o
        exact ⟨v,hv,le_rfl,le_rfl⟩

lemma GP0031B2b_tau_formula (v : Counts) : tau v = (v.effect : ℝ)/v.total := by
  simp only [tau, tauQ, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]

lemma GP0031B2b_estimate_formula (o : Counts) (m : ℕ)
    (ho : o.a+o.b = m ∧ o.c+o.d = m) :
    estimate o = ((o.a : ℝ)-o.c)/m := by
  have hq₁ : (o.a : ℚ)+o.b = m := by exact_mod_cast ho.1
  have hq₂ : (o.c : ℚ)+o.d = m := by exact_mod_cast ho.2
  simp only [estimate, estimateQ, hq₁, hq₂, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast]
  ring

lemma GP0031B2b_accepted_upper (o h : Counts) (m : ℕ) (hm : 0 < m)
    (ho : o.a+o.b = m ∧ o.c+o.d = m) (hh : h.a+h.b = m ∧ h.c+h.d = m)
    (ha : o.a ≤ h.a) (hc : h.c ≤ o.c) (α t : ℝ) (ht : t ∈ accepted α o) :
    t ≤ if (accepted α h).Nonempty then max (upper α h) (estimate h) else estimate h := by
  by_cases htE : t ≤ estimate h
  · split_ifs
    · exact le_trans htE (le_max_right _ _)
    · exact htE
  · obtain ⟨v,hv,hp,rfl⟩ := (GP0031B2b_balanced_completion_inclusion_accepted_spec _ _ _).mp ht
    have hn : v.total = 2*m := by
      rw [(possible_table_facts _ _ hv).1]
      dsimp [Counts.total]
      omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hE : 2*((h.a : ℤ)-h.c) < v.effect := by
      rw [GP0031B2b_tau_formula, hn, GP0031B2b_estimate_formula h m hh] at htE
      push_cast at htE
      have hmul : (h.a : ℝ)-h.c < (v.effect : ℝ)/2 := by
        have hgt := lt_of_not_ge htE
        field_simp at hgt ⊢
        nlinarith
      exact_mod_cast (show 2*((h.a : ℝ)-h.c) < (v.effect : ℝ) by linarith)
    obtain ⟨w,hw,hvw,hp'⟩ := GP0031B2b_transport h m hm hh o v ho hv ha hc hE
    have hacc : tau w ∈ accepted α h := accepted_of_possible α h w hw
      (le_trans hp (by exact_mod_cast hp'))
    have hne : (accepted α h).Nonempty := ⟨_,hacc⟩
    rw [if_pos hne]
    apply le_trans _ (le_max_left _ _)
    apply le_trans _ (le_csSup (accepted α h).finite_toSet.bddAbove hacc)
    rw [GP0031B2b_tau_formula, GP0031B2b_tau_formula, hn,
      (possible_table_facts _ _ hw).1]
    have hhn : h.total = 2*m := by dsimp [Counts.total]; omega
    rw [hhn]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hvw


lemma GP0031B2b_accepted_lower (o h : Counts) (m : ℕ) (hm : 0 < m)
    (ho : o.a+o.b = m ∧ o.c+o.d = m) (hh : h.a+h.b = m ∧ h.c+h.d = m)
    (ha : h.a ≤ o.a) (hc : o.c ≤ h.c) (α t : ℝ) (ht : t ∈ accepted α o) :
    (if (accepted α h).Nonempty then min (lower α h) (estimate h) else estimate h) ≤ t := by
  have hoP : 0 < o.a+o.b ∧ 0 < o.c+o.d := by omega
  have hhP : 0 < h.a+h.b ∧ 0 < h.c+h.d := by omega
  have htC : -t ∈ accepted α (complementObserved o) := by
    rw [GP0031B2b_balanced_completion_inclusion_complement_accepted α o hoP]
    exact Finset.mem_image.mpr ⟨t,ht,rfl⟩
  have hbound := GP0031B2b_accepted_upper (complementObserved o) (complementObserved h) m hm
    (by dsimp [complementObserved]; constructor <;> omega)
    (by dsimp [complementObserved]; constructor <;> omega)
    (by dsimp [complementObserved]; omega)
    (by dsimp [complementObserved]; omega) α (-t) htC
  rw [GP0031B2b_balanced_completion_inclusion_complement_endpoint α h hhP] at hbound
  linarith

lemma GP0031B2b_completion_bounds (o r c : Counts)
    (hr : r ∈ missingMasks o) (hc : c ∈ completions o r) :
    (minusCompletion o r).a ≤ c.a ∧ c.a ≤ (plusCompletion o r).a ∧
    (plusCompletion o r).c ≤ c.c ∧ c.c ≤ (minusCompletion o r).c := by
  obtain ⟨ha,hb,hc',hd⟩ := missing_mask_facts o r hr
  simp only [completions, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨t,ht,s,hs,rfl⟩ := hc
  dsimp [minusCompletion, plusCompletion]
  omega

theorem balanced_completion_inclusion_proof (o r : Counts) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (ho : 0 < o.a+o.b ∧ o.a+o.b = o.c+o.d)
    (hr : r ∈ missingMasks o) : completionUnion α o r ⊆ missingInterval α o r := by
  intro t ht
  obtain ⟨c,hc,l,hl,u,hu,hlt,htu⟩ := ht
  let m := o.a+o.b
  have hm : 0 < m := ho.1
  have hcM : c.a+c.b = m ∧ c.c+c.d = m := by
    obtain ⟨ha,hb⟩ := GP0031B2b_balanced_completion_inclusion_completion_arms o r c hr hc
    exact ⟨ha,hb.trans ho.2.symm⟩
  have hloM : (minusCompletion o r).a+(minusCompletion o r).b = m ∧
      (minusCompletion o r).c+(minusCompletion o r).d = m := by
    obtain ⟨ha,hb⟩ := GP0031B2b_balanced_completion_inclusion_completion_arms o r _ hr
      (GP0031B2b_balanced_completion_inclusion_minus_mem o r hr)
    exact ⟨ha,hb.trans ho.2.symm⟩
  have hhiM : (plusCompletion o r).a+(plusCompletion o r).b = m ∧
      (plusCompletion o r).c+(plusCompletion o r).d = m := by
    obtain ⟨ha,hb⟩ := GP0031B2b_balanced_completion_inclusion_completion_arms o r _ hr
      (GP0031B2b_balanced_completion_inclusion_plus_mem o r hr)
    exact ⟨ha,hb.trans ho.2.symm⟩
  obtain ⟨ha,hb,hd,he⟩ := GP0031B2b_completion_bounds o r c hr hc
  constructor
  · exact le_trans (GP0031B2b_accepted_lower c _ m hm hcM hloM ha he α l hl) hlt
  · exact le_trans htu (GP0031B2b_accepted_upper c _ m hm hcM hhiM hb hd α u hu)

theorem balanced_missing_coverage_proof (v : Counts) (m : ℕ) (α : ℝ)
    (hm : 0 < m) (hn : v.total = 2*m) (hα : 0 < α ∧ α < 1)
    (μ : Counts → Counts → ℝ) (hμ : IsMissingLaw v m μ) :
    missingProb v m μ (fun q r => tau v ∈ missingInterval α (observed v q) r)
      ≥ 1-α := by
  have hcover := exact_coverage v m α ⟨hm,by omega⟩ hα
  apply le_trans hcover
  apply missing_probability_of_pointwise v m μ hμ
    (fun q => tau v ∈ exactInterval α (observed v q))
    (fun q r => tau v ∈ missingInterval α (observed v q) r)
  intro q hq r hr ht
  obtain ⟨ha,hb⟩ := GP0031B2b_balanced_missing_coverage_observed_arms v m hn q hq
  apply balanced_completion_inclusion_proof (observed v q) r α hα
    ⟨by omega,by omega⟩ hr
  exact complete_interval_subset_union α (observed v q) r hr ht

end AronowAudit.P003.Wave1
