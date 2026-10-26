import AronowAudit.P003.P003_Audit
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset



namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-! ## P003-T24: complement the four treated counts. -/

private def t24_complement (v q : Counts) : Counts :=
  ⟨v.a-q.a, v.b-q.b, v.c-q.c, v.d-q.d⟩

private lemma t24_mem_randomStates_iff (v q : Counts) (m : ℕ) :
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
    · simp only [he,if_pos hd,Option.some.injEq]

/-- Disjoint blocks can be recognized by a tag on each of their elements. -/
private lemma t24_tagged_flatMap_nodup {A B : Type*} (xs : List A)
    (f : A → List B) (tag : B → A) (hx : xs.Nodup)
    (hf : ∀ a ∈ xs, (f a).Nodup)
    (htag : ∀ a, ∀ b ∈ f a, tag b = a) :
    (xs.flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨hf,?_⟩
  apply hx.imp
  intro a b hab q hqa hqb
  exact hab ((htag a q hqa).symm.trans (htag b q hqb))

private lemma t24_randomStates_nodup (v : Counts) (m : ℕ) :
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
    apply t24_tagged_flatMap_nodup _ _ Counts.b (List.nodup_range)
    · intro b hb
      exact hblock a b
    · intro b q hq
      exact (htag a b q hq).2
  change ((List.range (min v.a m+1)).flatMap fun a =>
    (List.range (min v.b (m-a)+1)).flatMap (block a)).Nodup
  apply t24_tagged_flatMap_nodup _ _ Counts.a (List.nodup_range)
  · intro a ha
    exact hinner a
  · intro a q hq
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    exact (htag a b q hq).1

private lemma t24_complement_mem (v q : Counts) (m : ℕ)
    (hn : v.total = 2*m) (hq : q ∈ randomStates v m) :
    t24_complement v q ∈ randomStates v m := by
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  apply (t24_mem_randomStates_iff _ _ _).mpr
  dsimp [t24_complement,Counts.total] at *
  omega

private lemma t24_complement_twice (v q : Counts) (m : ℕ)
    (hq : q ∈ randomStates v m) :
    t24_complement v (t24_complement v q) = q := by
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  apply Counts.ext <;> dsimp [t24_complement] <;> omega

private lemma t24_complement_weight (v q : Counts) (m : ℕ)
    (hq : q ∈ randomStates v m) :
    multiplicity v (t24_complement v q) = multiplicity v q := by
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  simp only [multiplicity,t24_complement,binomial_eq_choose,
    Nat.choose_symm ha,Nat.choose_symm hb,Nat.choose_symm hc,Nat.choose_symm hd]

private lemma t24_reindex (v : Counts) (m : ℕ) (hn : v.total = 2*m)
    (F : Counts → ℝ) :
    ((randomStates v m).map F).sum =
      ((randomStates v m).map fun q => F (t24_complement v q)).sum := by
  have hnodup := t24_randomStates_nodup v m
  have hmap : ((randomStates v m).map (t24_complement v)).Nodup := by
    apply List.Nodup.map_on _ hnodup
    intro q hq r hr he
    have he' := congrArg (t24_complement v) he
    simpa only [t24_complement_twice v q m hq,
      t24_complement_twice v r m hr] using he'
  have hp : ((randomStates v m).map (t24_complement v)).Perm (randomStates v m) := by
    apply (List.perm_ext_iff_of_nodup hmap hnodup).mpr
    intro q
    constructor
    · intro hq
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
      exact t24_complement_mem v r m hn hr
    · intro hq
      exact List.mem_map.mpr ⟨t24_complement v q,
        t24_complement_mem v q m hn hq,t24_complement_twice v q m hq⟩
  have hs := (hp.map F).sum_eq
  simpa only [List.map_map,Function.comp_def] using hs.symm

private lemma t24_estimator_formula (v q : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (hq : q ∈ randomStates v m) :
    (m : ℝ)*estimate (observed v q) =
      2*(q.a : ℝ)+q.b+q.c-v.a-v.c := by
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  have hsum : q.a+q.b+q.c+q.d = m := ht
  have hcontrol : v.a-q.a+v.c-q.c+(v.b-q.b+v.d-q.d) = m := by
    dsimp [Counts.total] at hn
    omega
  have htreated : (q.a+q.b)+(q.c+q.d) = m := by omega
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : estimate (observed v q) =
      ((q.a : ℝ)+q.b)/m - (((v.a : ℝ)-q.a)+v.c-q.c)/m := by
    have hreal (o : Counts) : estimate o =
        (o.a : ℝ)/((o.a : ℝ)+o.b)-(o.c : ℝ)/((o.c : ℝ)+o.d) := by
      simp [estimate,estimateQ]
    have htR : ((q.a+q.b : ℕ) : ℝ)+(q.c+q.d : ℕ) = m := by
      exact_mod_cast htreated
    have hcR : ((v.a-q.a+v.c-q.c : ℕ) : ℝ)+
        (v.b-q.b+v.d-q.d : ℕ) = m := by exact_mod_cast hcontrol
    have hcnum : ((v.a-q.a+v.c-q.c : ℕ) : ℝ) =
        (v.a : ℝ)-q.a+v.c-q.c := by
      rw [Nat.cast_sub (show q.c ≤ v.a-q.a+v.c by omega),
        Nat.cast_add,Nat.cast_sub ha]
    rw [hreal]
    change ((q.a+q.b : ℕ) : ℝ)/
        (((q.a+q.b : ℕ) : ℝ)+(q.c+q.d : ℕ)) -
      ((v.a-q.a+v.c-q.c : ℕ) : ℝ)/
        (((v.a-q.a+v.c-q.c : ℕ) : ℝ)+(v.b-q.b+v.d-q.d : ℕ)) = _
    rw [htR,hcR,hcnum,Nat.cast_add]
  rw [he]
  field_simp [hmR]
  <;> ring

private lemma t24_estimator_pair_sum (v q : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) (hq : q ∈ randomStates v m) :
    estimate (observed v q) + estimate (observed v (t24_complement v q)) =
      2*tau v := by
  have hq' := t24_complement_mem v q m hn hq
  have he := t24_estimator_formula v q m hm hn hq
  have he' := t24_estimator_formula v (t24_complement v q) m hm hn hq'
  rcases random_state_facts v m q hq with ⟨ha,hb,hc,hd,ht⟩
  dsimp [t24_complement] at he'
  push_cast [Nat.cast_sub ha,Nat.cast_sub hb,Nat.cast_sub hc] at he'
  have htau : (m : ℝ)*(2*tau v) = (v.b : ℝ)-v.c := by
    have hnR : (v.total : ℝ) = 2*(m : ℝ) := by exact_mod_cast hn
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [tau,tauQ,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,
      Counts.effect,Int.cast_sub,Int.cast_natCast]
    rw [hnR]
    push_cast
    field_simp [hmR]
    <;> ring
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply mul_left_cancel₀ hmR.ne'
  dsimp only [t24_complement]
  nlinarith

private lemma t24_sum_linear (xs : List Counts) (w f : Counts → ℝ) (c : ℝ) :
    (xs.map fun q => w q*(c-f q)).sum =
      c*(xs.map w).sum-(xs.map fun q => w q*f q).sum := by
  induction xs with
  | nil => simp
  | cons q xs ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem balanced_mean_symmetry_proof (v : Counts) (m : ℕ) (hm : 0 < m)
    (hn : v.total = 2*m) :
    designMean v m (fun q => estimate (observed v q)) = tau v ∧
    ∀ t : ℝ, designProb v m (fun q => estimate (observed v q) = tau v-t) =
      designProb v m (fun q => estimate (observed v q) = tau v+t) := by
  have hmle : m ≤ v.total := by omega
  have hden : (v.total.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmle).ne'
  have hw : ((randomStates v m).map fun q => (multiplicity v q : ℝ)).sum =
      (v.total.choose m : ℝ) := by
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using
      congrArg (fun k : ℕ => (k : ℝ)) (design_weight_total v m hmle)
  constructor
  · have hr := t24_reindex v m hn
      (fun q => (multiplicity v q : ℝ)*estimate (observed v q))
    have hs : ((randomStates v m).map fun q =>
          (multiplicity v (t24_complement v q) : ℝ)*
            estimate (observed v (t24_complement v q))).sum =
        ((randomStates v m).map fun q =>
          (multiplicity v q : ℝ)*(2*tau v-estimate (observed v q))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      rw [t24_complement_weight v q m hq]
      have hp := t24_estimator_pair_sum v q m hm hn hq
      congr 1
      linarith
    rw [hs,t24_sum_linear,hw] at hr
    unfold designMean
    apply (div_eq_iff hden).mpr
    linarith
  · intro t
    unfold designProb
    congr 1
    rw [t24_reindex v m hn (fun q =>
      if estimate (observed v q) = tau v-t then (multiplicity v q : ℝ) else 0)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    rw [t24_complement_weight v q m hq]
    have hp := t24_estimator_pair_sum v q m hm hn hq
    have he : estimate (observed v (t24_complement v q)) = tau v-t ↔
        estimate (observed v q) = tau v+t := by constructor <;> intro h <;> linarith
    simp only [he]

end AronowAudit.P003.Wave1
