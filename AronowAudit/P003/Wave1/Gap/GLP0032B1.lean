import AronowAudit.P003.P003_Audit
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments
import Mathlib.Data.Fintype.Pi

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

def neyman_typeCount (q : Counts) (t : Bool × Bool) : ℕ :=
  if t.1 then (if t.2 then q.a else q.b) else (if t.2 then q.c else q.d)

def neyman_pack (f : Bool × Bool → ℕ) : Counts :=
  ⟨f (true,true), f (true,false), f (false,true), f (false,false)⟩

lemma neyman_typeCount_pack (f : Bool × Bool → ℕ) (t : Bool × Bool) :
    neyman_typeCount (neyman_pack f) t = f t := by
  rcases t with ⟨a,b⟩
  cases a <;> cases b <;> rfl

lemma neyman_sum_types (q : Counts) : ∑ t, neyman_typeCount q t = q.total := by
  simp [Fintype.sum_prod_type, neyman_typeCount, Counts.total, add_comm, add_left_comm]

def neyman_treated {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) : Counts :=
  neyman_pack (fun t => (z.filter fun i => w i = t).card)

lemma neyman_treated_total {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) :
    (neyman_treated w z).total = z.card := by
  rw [← neyman_sum_types]
  simp only [neyman_treated, neyman_typeCount_pack]
  exact (Finset.card_eq_sum_card_fiberwise (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) ).symm

lemma neyman_partition_card {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (w : α → β) (k : β → ℕ) :
    (Finset.univ.filter fun z : Finset α => ∀ t, (z.filter fun i => w i = t).card = k t).card =
      ∏ t, ((Finset.univ.filter fun i => w i = t).card).choose (k t) := by
  let B (t : β) : Finset (Finset α) :=
    (Finset.univ.filter fun i => w i = t).powersetCard (k t)
  have hfilter (s : β → Finset α) (hs : s ∈ Fintype.piFinset B) (t : β) :
      ((Finset.univ.biUnion s).filter fun i => w i = t) = s t := by
    have hs' := Fintype.mem_piFinset.mp hs
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨u,hi⟩,he⟩
      have hu := (Finset.mem_powersetCard.mp (hs' u)).1 hi
      have hut : u = t := (Finset.mem_filter.mp hu).2.symm.trans he
      simpa [hut] using hi
    · intro hi
      exact ⟨⟨t,hi⟩, (Finset.mem_filter.mp
        ((Finset.mem_powersetCard.mp (hs' t)).1 hi)).2⟩
  have hcard :
      (Finset.univ.filter fun z : Finset α => ∀ t, (z.filter fun i => w i = t).card = k t).card =
        (Fintype.piFinset B).card := by
    apply Finset.card_bij (fun z _ t => z.filter fun i => w i = t)
    · intro z hz
      simp only [Fintype.mem_piFinset]
      intro t
      refine Finset.mem_powersetCard.mpr ⟨?_, (Finset.mem_filter.mp hz).2 t⟩
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    · intro z hz z' hz' he
      ext i
      have h := congrFun he (w i)
      have := congrArg (fun s : Finset α => i ∈ s) h
      simpa using this
    · intro s hs
      refine ⟨Finset.univ.biUnion s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · intro t
        rw [hfilter s hs t]
        exact (Finset.mem_powersetCard.mp (Fintype.mem_piFinset.mp hs t)).2
      · funext t
        exact hfilter s hs t
  rw [hcard, Fintype.card_piFinset]
  simp [B, Finset.card_powersetCard]

lemma neyman_randomStates_iff (v q : Counts) (m : ℕ) :
    q ∈ randomStates v m ↔
      q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = m := by
  constructor
  · exact random_state_facts v m q
  · rintro ⟨ha,hb,hc,hd,ht⟩
    have hs : q.a+q.b+q.c+q.d = m := ht
    simp only [randomStates, List.mem_flatMap, List.mem_filterMap, List.mem_range]
    refine ⟨q.a, ?_, q.b, ?_, q.c, ?_, ?_⟩
    · exact Nat.lt_succ_of_le (le_min ha (by omega))
    · exact Nat.lt_succ_of_le (le_min hb (by omega))
    · exact Nat.lt_succ_of_le (le_min hc (by omega))
    · have he : m-q.a-q.b-q.c = q.d := by omega
      simp only [he, if_pos hd]

-- Enumeration uniqueness.
private lemma neyman_flatMap_nodup
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

lemma neyman_randomStates_nodup (v : Counts) (m : ℕ) :
    (randomStates v m).Nodup := by
  let inner (a b : ℕ) : List Counts :=
    (List.range (min v.c (m-a-b)+1)).filterMap fun c =>
      if m-a-b-c ≤ v.d then some ⟨a,b,c,m-a-b-c⟩ else none
  have hinner (a b : ℕ) : (inner a b).Nodup := by
    apply List.Nodup.filterMap (l := List.range (min v.c (m-a-b)+1))
      (f := fun c => if m-a-b-c ≤ v.d then some (⟨a,b,c,m-a-b-c⟩ : Counts) else none)
      ?_ List.nodup_range
    intro c c' q hc hc'
    split_ifs at hc hc' with h1 h2
    · simp only [Option.mem_def, Option.some.injEq] at hc hc'
      exact (Counts.mk.inj (hc.trans hc'.symm)).2.2.1
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
    apply neyman_flatMap_nodup _ (inner a) Counts.b
      List.nodup_range (fun b _ => hinner a b)
    intro b hb q hq
    exact (hinner_coords a b q hq).2
  have hmiddle_coord (a : ℕ) (q : Counts) (hq : q ∈ middle a) : q.a = a := by
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    exact (hinner_coords a b q hq).1
  change ((List.range (min v.a m+1)).flatMap middle).Nodup
  apply neyman_flatMap_nodup _ middle Counts.a
    List.nodup_range (fun a _ => hmiddle a)
  intro a ha q hq
  exact hmiddle_coord a q hq

lemma neyman_treated_eq {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) (q : Counts) :
    neyman_treated w z = q ↔ ∀ t, (z.filter fun i => w i = t).card = neyman_typeCount q t := by
  constructor
  · intro h t
    rw [← h]
    exact (neyman_typeCount_pack (fun u => (z.filter fun i => w i = u).card) t).symm
  · intro h
    exact Counts.ext (h (true,true)) (h (true,false)) (h (false,true)) (h (false,false))

lemma neyman_treated_mem {n : ℕ} (w : PotentialTable n) (v : Counts)
    (hw : tableCounts w = v) (m : ℕ) (z : Assignment n m) :
    neyman_treated w z.val ∈ randomStates v m := by
  have hle (t : Bool × Bool) :
      (z.val.filter fun i => w i = t).card ≤ (Finset.univ.filter fun i => w i = t).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  rw [neyman_randomStates_iff]
  subst v
  exact ⟨hle (true,true), hle (true,false), hle (false,true), hle (false,false),
    (neyman_treated_total w z.val).trans z.property⟩

lemma neyman_fiber_card {n : ℕ} (w : PotentialTable n) (v q : Counts)
    (hw : tableCounts w = v) (m : ℕ) (ht : q.total = m) :
    ((Finset.univ : Finset (Assignment n m)).filter fun z => neyman_treated w z.val = q).card =
      multiplicity v q := by
  have he :
      ((Finset.univ : Finset (Assignment n m)).filter fun z => neyman_treated w z.val = q).card =
      (Finset.univ.filter fun z : Finset (Fin n) =>
        ∀ t, (z.filter fun i => w i = t).card = neyman_typeCount q t).card := by
    apply Finset.card_bij (fun z _ => z.val)
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (neyman_treated_eq w z.val q).mp (Finset.mem_filter.mp hz).2⟩
    · intro z hz z' hz' he
      exact Subtype.ext he
    · intro z hz
      have hq := (neyman_treated_eq w z q).mpr (Finset.mem_filter.mp hz).2
      have hcard : z.card = m := by
        rw [← neyman_treated_total w z, hq, ht]
      exact ⟨⟨z,hcard⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
  rw [he, neyman_partition_card]
  subst v
  simp [Fintype.prod_prod_type, neyman_typeCount, multiplicity, tableCounts,
    binomial_eq_choose, mul_comm, mul_assoc]

lemma neyman_sum_pushforward {n : ℕ} (w : PotentialTable n) (v : Counts)
    (hw : tableCounts w = v) (m : ℕ) (f : Counts → ℝ) :
    (∑ z : Assignment n m, f (neyman_treated w z.val)) =
      ((randomStates v m).map fun q => (multiplicity v q : ℝ) * f q).sum := by
  have h := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Assignment n m)))
    (t := (randomStates v m).toFinset) (g := fun z => neyman_treated w z.val)
    (fun z _ => List.mem_toFinset.mpr (neyman_treated_mem w v hw m z)) f
  rw [← h]
  have hs (q : Counts) (hq : q ∈ (randomStates v m).toFinset) :
      (∑ z ∈ (Finset.univ : Finset (Assignment n m)) with neyman_treated w z.val = q, f q) =
        (multiplicity v q : ℝ) * f q := by
    rw [Finset.sum_const, nsmul_eq_mul,
      neyman_fiber_card w v q hw m (random_state_facts v m q (List.mem_toFinset.mp hq)).2.2.2.2]
  simp_rw [Finset.sum_congr rfl hs]
  exact List.sum_toFinset _ (neyman_randomStates_nodup v m)

lemma neyman_assignment_card (n m : ℕ) : Fintype.card (Assignment n m) = n.choose m := by
  simp [Assignment, Fintype.card_finset_len]

lemma neyman_mean_pushforward {n : ℕ} (w : PotentialTable n) (v : Counts)
    (hw : tableCounts w = v) (hn : v.total = n) (m : ℕ) (f : Counts → ℝ) :
    (∑ z : Assignment n m, f (neyman_treated w z.val)) / Fintype.card (Assignment n m) =
      designMean v m f := by
  rw [neyman_sum_pushforward w v hw m f, neyman_assignment_card, ← hn]
  rfl

lemma neyman_table_total {n : ℕ} (w : PotentialTable n) : (tableCounts w).total = n := by
  simpa [neyman_treated, neyman_pack, tableCounts] using neyman_treated_total w Finset.univ

lemma neyman_event_pushforward {n : ℕ} (w : PotentialTable n) (v : Counts)
    (hw : tableCounts w = v) (m : ℕ) (E : Counts → Prop) :
    uniformProb (fun z : Assignment n m => E (neyman_treated w z.val)) = designProb v m E := by
  have hn : v.total = n := hw ▸ neyman_table_total w
  have h := neyman_mean_pushforward w v hw hn m (fun q => if E q then 1 else 0)
  simpa [uniformProb, designMean, designProb, Finset.sum_boole, mul_ite] using h

lemma neyman_binary_sums {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) :
    (∑ i ∈ z, bit (w i).1) =
        (neyman_treated w z).a + ((neyman_treated w z).b : ℝ) ∧
    (∑ i ∈ z, bit (w i).2) =
        (neyman_treated w z).a + ((neyman_treated w z).c : ℝ) := by
  have h1 : ∀ i, bit (w i).1 =
      (if w i = (true,true) then (1 : ℝ) else 0) +
      (if w i = (true,false) then (1 : ℝ) else 0) := by
    intro i
    rcases h : w i with ⟨a,b⟩
    cases a <;> cases b <;> simp [bit]
  have h0 : ∀ i, bit (w i).2 =
      (if w i = (true,true) then (1 : ℝ) else 0) +
      (if w i = (false,true) then (1 : ℝ) else 0) := by
    intro i
    rcases h : w i with ⟨a,b⟩
    cases a <;> cases b <;> simp [bit]
  constructor
  · simp_rw [h1]
    simp [Finset.sum_add_distrib, neyman_treated, neyman_pack]
  · simp_rw [h0]
    simp [Finset.sum_add_distrib, neyman_treated, neyman_pack]

lemma neyman_estimator_eq {n : ℕ} (w : PotentialTable n) (v : Counts)
    (hw : tableCounts w = v) (m : ℕ) (z : Assignment n m) :
    tableEstimator w z.val = estimate (observed v (neyman_treated w z.val)) := by
  let q := neyman_treated w z.val
  have hq := random_state_facts v m q (neyman_treated_mem w v hw m z)
  have hn : v.total = n := hw ▸ neyman_table_total w
  have hs := neyman_binary_sums w z.val
  have ht := neyman_binary_sums w Finset.univ
  have hfull : (∑ i, bit (w i).2) = (v.a : ℝ)+v.c := by
    simpa only [show neyman_treated w Finset.univ = v from hw] using ht.2
  have hcomp : (∑ i, if i ∈ z.val then 0 else bit (w i).2) =
      (v.a : ℝ)+v.c-((q.a : ℝ)+q.c) := by
    rw [← hfull, ← hs.2]
    have he : (∑ i ∈ z.val, bit (w i).2) =
        ∑ i, if i ∈ z.val then bit (w i).2 else 0 := by
      simp
    rw [he]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i ∈ z.val <;> simp [h]
  have hcontrol : ((v.a-q.a+v.c-q.c : ℕ) : ℝ) =
      (v.a : ℝ)+v.c-((q.a : ℝ)+q.c) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub hq.1]
    push_cast
    ring
  have hcontrol0 : ((v.b-q.b+v.d-q.d : ℕ) : ℝ) =
      (v.b : ℝ)+v.d-((q.b : ℝ)+q.d) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub hq.2.1]
    push_cast
    ring
  have hqt : (q.a : ℝ)+q.b+q.c+q.d = m := by
    exact_mod_cast hq.2.2.2.2
  have hnt : (v.a : ℝ)+v.b+v.c+v.d = n := by
    exact_mod_cast hn
  have htreated : (∑ i, if i ∈ z.val then bit (w i).1 else 0) = (q.a : ℝ)+q.b := by
    simpa [← Finset.sum_filter] using hs.1
  simp only [tableEstimator, z.property, estimate, estimateQ,
    Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_natCast]
  change _ = ((q.a+q.b : ℕ) : ℝ) / (((q.a+q.b : ℕ) : ℝ)+((q.c+q.d : ℕ) : ℝ)) -
    ((v.a-q.a+v.c-q.c : ℕ) : ℝ) /
      (((v.a-q.a+v.c-q.c : ℕ) : ℝ)+((v.b-q.b+v.d-q.d : ℕ) : ℝ))
  rw [htreated,hcomp,hcontrol,hcontrol0]
  push_cast
  congr 1 <;> congr 1 <;> linarith

lemma neyman_exists_table (v : Counts) : ∃ w : PotentialTable v.total, tableCounts w = v := by
  let X := ((Fin v.a ⊕ Fin v.b) ⊕ Fin v.c) ⊕ Fin v.d
  let pair : X → Bool × Bool :=
    Sum.elim (Sum.elim (Sum.elim (fun _ => (true,true)) (fun _ => (true,false)))
      (fun _ => (false,true))) (fun _ => (false,false))
  let e : Fin v.total ≃ X := Fintype.equivOfCardEq (α := Fin v.total) (β := X) (by
    rw [Fintype.card_fin]
    simp [X, Counts.total])
  refine ⟨fun i => pair (e i), ?_⟩
  have h (t : Bool × Bool) :
      (Finset.univ.filter fun i : Fin v.total => pair (e i) = t).card =
      ∑ x : X, if pair x = t then 1 else 0 := by
    calc
      _ = ∑ i : Fin v.total, if pair (e i) = t then (1 : ℕ) else 0 := by
        simp only [Finset.sum_boole, Nat.cast_id]
      _ = _ := e.sum_comp (fun x : X => if pair x = t then (1 : ℕ) else 0)
  ext <;> simp only [tableCounts] <;> rw [h] <;>
    simp only [X, pair, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] <;> norm_num

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.FinitePopulationMoments

lemma neyman_uniform_E {n m : ℕ} (hm : m ≤ n) (f : Assignment n m → ℝ) :
    (completeRandomization m (by simpa using hm)).E f =
      (∑ z, f z) / Fintype.card (Assignment n m) := by
  simp only [FiniteDesign.E, completeRandomization, ← Finset.mul_sum]
  ring

lemma neyman_centered_ss {n : ℕ} (x : Fin n → ℝ) (hn : n ≠ 0) :
    (∑ i, (x i - (∑ j, x j)/(n : ℝ))^2) =
      (∑ i, (x i)^2) - (∑ i, x i)^2/(n : ℝ) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hp (i) : (x i - (∑ j, x j)/(n : ℝ))^2 =
      (x i)^2 - 2*((∑ j, x j)/(n : ℝ))*x i + ((∑ j, x j)/(n : ℝ))^2 := by ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The standard weighted-potential-outcome expansion, using the actual
uniform-subset sample-mean variance theorem. -/
lemma neyman_variance_general (n m : ℕ) (hm : 0 < m ∧ m < n) (x y : Fin n → ℝ) :
    (completeRandomization m (by simpa using hm.2.le)).Var (diffInMeans m x y) =
      popVar x / m + popVar y / (n-m : ℕ) - popVar (fun i => x i-y i) / n := by
  let D := completeRandomization (V := Fin n) m (by simpa using hm.2.le)
  let l := n-m
  let c : Fin n → ℝ := fun i => x i/(m : ℝ)+y i/(l : ℝ)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.1.ne'
  have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hm.2).ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (lt_trans hm.1 hm.2).ne'
  have hnl : (n : ℝ) = (m : ℝ)+(l : ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le hm.2.le).symm
  have hrep : diffInMeans m x y = fun z : Assignment n m =>
      (m : ℝ)*sampleMean m c z - (∑ i, y i)/(l : ℝ) := by
    funext z
    have hs : (∑ i, if i ∈ z.val then c i else 0) =
        (∑ i, if i ∈ z.val then x i else 0)/(m : ℝ) +
        (∑ i, if i ∈ z.val then y i else 0)/(l : ℝ) := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i ∈ z.val <;> simp [h,c]
    have hy : (∑ i, if i ∈ z.val then 0 else y i) =
        (∑ i, y i) - (∑ i, if i ∈ z.val then y i else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i ∈ z.val <;> simp [h]
    simp only [diffInMeans, treatedMean, controlMean, Fintype.card_fin, sampleMean]
    rw [hs,hy]
    change _/(m : ℝ)-_/(l : ℝ) = (m : ℝ)*(_/(m : ℝ)) - _
    field_simp
    ring
  have hshift (X : Assignment n m → ℝ) (a : ℝ) :
      D.Var (fun z => X z-a) = D.Var X := by
    unfold FiniteDesign.Var
    rw [D.E_sub, D.E_const]
    apply D.E_congr
    intro z
    congr 1
    ring
  change D.Var _ = _
  rw [hrep, hshift, D.Var_const_mul]
  have hv := Var_sampleMean (U := Fin n) m (by simpa using hm.2.le) hm.1
    (by simpa using (by omega : 2 ≤ n)) c
  change D.Var (sampleMean m c) = _ at hv
  rw [hv]
  have hcmean : popMean c = popMean x/(m : ℝ)+popMean y/(l : ℝ) := by
    simp only [popMean, c, Finset.sum_add_distrib, ← Finset.sum_div]
    ring
  have hemean : popMean (fun i => x i-y i) = popMean x-popMean y := by
    simp only [popMean, Finset.sum_sub_distrib, sub_div]
  have hp (i : Fin n) :
      ((m : ℝ)*l/n) * (c i-(popMean x/(m : ℝ)+popMean y/(l : ℝ)))^2 =
      (x i-popMean x)^2/(m : ℝ) + (y i-popMean y)^2/(l : ℝ) -
        ((x i-y i)-(popMean x-popMean y))^2/(n : ℝ) := by
    dsimp [c]
    rw [hnl]
    field_simp
    ring
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun i _ => hp i)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_div] at hs
  have hfactor : (m : ℝ)^2 * (1/(m : ℝ)-1/(Fintype.card (Fin n) : ℝ)) =
      (m : ℝ)*l/n := by
    simp only [Fintype.card_fin]
    rw [hnl]
    field_simp
    ring
  rw [← mul_assoc, hfactor]
  unfold popVar
  simp only [Fintype.card_fin]
  rw [hcmean, hemean]
  change _ = _/(m : ℝ)+_/(l : ℝ)-_
  linear_combination (1/((n : ℝ)-1))*hs

lemma neyman_estimator_diff {n : ℕ} (w : PotentialTable n) (m : ℕ) (hm : m ≤ n) :
    (fun z : Assignment n m => tableEstimator w z.val) =
      diffInMeans m (fun i => bit (w i).1) (fun i => bit (w i).2) := by
  funext z
  simp only [tableEstimator, z.property, diffInMeans, treatedMean, controlMean,
    Fintype.card_fin, Nat.cast_sub hm]

lemma neyman_estimator_pushforward {n : ℕ} (w : PotentialTable n) (v : Counts)
    (hw : tableCounts w = v) (m : ℕ) (hm : m ≤ n) (f : ℝ → ℝ) :
    (completeRandomization m (by simpa using hm)).E (fun z : Assignment n m =>
      f (tableEstimator w z.val)) = designMean v m (fun q => f (estimate (observed v q))) := by
  rw [neyman_uniform_E hm]
  simp_rw [neyman_estimator_eq w v hw m]
  exact neyman_mean_pushforward w v hw (hw ▸ neyman_table_total w) m
    (fun q => f (estimate (observed v q)))

lemma neyman_binary_statistics {n : ℕ} (w : PotentialTable n) (v : Counts)
    (hw : tableCounts w = v) (hn : 2 ≤ n) :
    popVar (fun i => bit (w i).1) = binarySampleVariance n (v.a+v.b) ∧
    popVar (fun i => bit (w i).2) = binarySampleVariance n (v.a+v.c) ∧
    popVar (fun i => bit (w i).1-bit (w i).2) = effectSampleVariance v := by
  have hnn : n ≠ 0 := by omega
  have htotal : v.total = n := hw ▸ neyman_table_total w
  have hs := corrected_sate w (by omega : 0 < n)
  rw [hw] at hs
  have hsub : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ n)
  have hsq (b : Bool) : (bit b)^2 = bit b := by cases b <;> norm_num [bit]
  have hvar (x : Fin n → ℝ) :
      popVar x = ((∑ i, (x i)^2)-(∑ i, x i)^2/n)/((n : ℝ)-1) := by
    simp only [popVar, popMean, Fintype.card_fin]
    rw [neyman_centered_ss x hnn]
  have heffect : (∑ i, (bit (w i).1-bit (w i).2)^2) = (v.b : ℝ)+v.c := by
    have hp (i) : (bit (w i).1-bit (w i).2)^2 =
        (if w i = (true,false) then (1 : ℝ) else 0) +
        (if w i = (false,true) then (1 : ℝ) else 0) := by
      rcases h : w i with ⟨a,b⟩
      cases a <;> cases b <;> norm_num [bit]
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    have h := congrArg (fun u : Counts => (u.b : ℝ)+u.c) hw
    simpa [tableCounts] using h
  refine ⟨?_, ?_, ?_⟩
  · rw [hvar]
    simp_rw [hsq, hs.2.1]
    simp [binarySampleVariance, hsub, Nat.cast_add]
  · rw [hvar]
    simp_rw [hsq, hs.2.2.1]
    simp [binarySampleVariance, hsub, Nat.cast_add]
  · rw [hvar, heffect, Finset.sum_sub_distrib, hs.2.1, hs.2.2.1]
    simp only [effectSampleVariance, htotal, hsub, Counts.effect, Int.cast_sub, Int.cast_natCast]
    congr 2
    ring

lemma neyman_binary_variance_le (n k : ℕ) (_hn : 2 ≤ n) (hk : k ≤ n) :
    binarySampleVariance n k ≤ (n : ℝ)/(n-1 : ℕ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hkr : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hs : 0 ≤ (k : ℝ)^2/(n : ℝ) := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  linarith

lemma neyman_effect_variance_nonneg (v : Counts) (hn : 2 ≤ v.total) :
    0 ≤ effectSampleVariance v := by
  obtain ⟨w,hw⟩ := neyman_exists_table v
  rw [← (neyman_binary_statistics w v hw hn).2.2]
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · simp only [Fintype.card_fin]
    have h : (2 : ℝ) ≤ v.total := by exact_mod_cast hn
    linarith

lemma neyman_finite_moments (v : Counts) (m : ℕ) (hm : 0 < m ∧ m < v.total) :
    designMean v m (fun q => estimate (observed v q)) = tau v ∧
    designVariance v m =
      binarySampleVariance v.total (v.a+v.b)/m +
      binarySampleVariance v.total (v.a+v.c)/(v.total-m : ℕ) -
      effectSampleVariance v/v.total := by
  obtain ⟨w,hw⟩ := neyman_exists_table v
  let D := completeRandomization (V := Fin v.total) m (by simpa using hm.2.le)
  let T : Assignment v.total m → ℝ := fun z => tableEstimator w z.val
  have hT : T = diffInMeans m (fun i => bit (w i).1) (fun i => bit (w i).2) :=
    neyman_estimator_diff w m hm.2.le
  have hmean : D.E T = designMean v m (fun q => estimate (observed v q)) :=
    neyman_estimator_pushforward w v hw m hm.2.le id
  have hmu : D.E T = tau v := by
    rw [hT]
    have h := E_diffInMeans_eq_sate (U := Fin v.total) m hm.1
      (by simpa using hm.2) (fun i => bit (w i).1) (fun i => bit (w i).2)
    have h' : D.E (diffInMeans m (fun i => bit (w i).1) (fun i => bit (w i).2)) =
        tableTau w := by
      simpa only [sateEstimand, tableTau, Fintype.card_fin] using h
    rw [h', (corrected_sate w (lt_trans hm.1 hm.2)).2.2.2, hw]
  have hvariance : D.Var T = designVariance v m := by
    unfold FiniteDesign.Var designVariance
    rw [hmean]
    exact neyman_estimator_pushforward w v hw m hm.2.le
      (fun t => (t-designMean v m (fun q => estimate (observed v q)))^2)
  refine ⟨hmean.symm.trans hmu, ?_⟩
  rw [← hvariance, hT, neyman_variance_general v.total m hm]
  have hs := neyman_binary_statistics w v hw (by omega : 2 ≤ v.total)
  rw [hs.1, hs.2.1, hs.2.2]

lemma neyman_variance_upper (v : Counts) (m : ℕ) (hm : 0 < m ∧ m < v.total) :
    binarySampleVariance v.total (v.a+v.b)/m +
      binarySampleVariance v.total (v.a+v.c)/(v.total-m : ℕ) -
      effectSampleVariance v/v.total ≤ (v.total : ℝ)^2 /
      ((v.total-1 : ℕ)*(m : ℝ)*(v.total-m : ℕ)) := by
  have hn : 2 ≤ v.total := by omega
  have h1 := neyman_binary_variance_le v.total (v.a+v.b) hn
    (by dsimp [Counts.total]; omega)
  have h0 := neyman_binary_variance_le v.total (v.a+v.c) hn
    (by dsimp [Counts.total]; omega)
  have he := neyman_effect_variance_nonneg v hn
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.1.ne'
  have hlR : ((v.total-m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hm.2).ne'
  have hn1R : ((v.total-1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : v.total-1 ≠ 0)
  calc
    _ ≤ ((v.total : ℝ)/(v.total-1 : ℕ))/m +
        ((v.total : ℝ)/(v.total-1 : ℕ))/(v.total-m : ℕ) := by
      exact (sub_le_self _ (div_nonneg he (Nat.cast_nonneg _))).trans
        (add_le_add (div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _))
          (div_le_div_of_nonneg_right h0 (Nat.cast_nonneg _)))
    _ = _ := by
      have hl : ((v.total-m : ℕ) : ℝ) = (v.total : ℝ)-m := Nat.cast_sub hm.2.le
      field_simp
      rw [hl]
      ring

lemma neyman_observed_arms (v q : Counts) (m : ℕ) (hq : q ∈ randomStates v m) :
    (observed v q).total = v.total ∧ (observed v q).a+(observed v q).b = m := by
  obtain ⟨ha,hb,hc,hd,ht⟩ := random_state_facts v m q hq
  dsimp [observed, Counts.total] at ht ⊢
  omega


theorem neyman_finite_identity_proof (v : Counts) (m : ℕ) (hm : 0 < m ∧ m < v.total) :
    designMean v m (fun q => estimate (observed v q)) = tau v ∧
    designVariance v m =
      binarySampleVariance v.total (v.a+v.b)/m +
      binarySampleVariance v.total (v.a+v.c)/(v.total-m : ℕ) -
      effectSampleVariance v/v.total ∧
    designVariance v m ≤ (v.total : ℝ)^2 /
      ((v.total-1 : ℕ)*(m : ℝ)*(v.total-m : ℕ)) := by
  have h := neyman_finite_moments v m hm
  exact ⟨h.1, h.2, h.2 ▸ neyman_variance_upper v m hm⟩

end AronowAudit.P003.Wave1
