import AronowAudit.P003.P003_Audit
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments

/-! Exact finite proofs for P003-T18 and P003-T2.
The four-cell assignment-fibre calculation is shared by both results.
The shuffle expectation uses finite second moments of independent Monte Carlo draws;
the displayed logarithmic budget implies the sufficient bound K ≥ 64. -/

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-- Split a subset into the fibres of a finite colouring. -/
noncomputable def couplingB2_partitionEquiv {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) (q : B → ℕ) :
    {s : Finset A // ∀ b, (s.filter (fun a => f a = b)).card = q b} ≃
      ((b : B) → ↥((Finset.univ.filter (fun a => f a = b)).powersetCard (q b))) where
  toFun s b := ⟨s.val.filter (fun a => f a = b),
    Finset.mem_powersetCard.mpr ⟨by intro a ha; simpa using (Finset.mem_filter.mp ha).2,
      s.property b⟩⟩
  invFun p := ⟨Finset.univ.biUnion (fun b => (p b).val), by
    intro b
    have he : (Finset.univ.biUnion (fun c => (p c).val)).filter (fun a => f a = b) =
        (p b).val := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨c,hc⟩,hab⟩
        have hac := Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (p c).property).1 hc)
        have hcb : c = b := hac.2.symm.trans hab
        subst c
        exact hc
      · intro ha
        exact ⟨⟨b,ha⟩,
          (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (p b).property).1 ha)).2⟩
    rw [he]
    exact (Finset.mem_powersetCard.mp (p b).property).2⟩
  left_inv s := by
    apply Subtype.ext
    ext a
    simp
  right_inv p := by
    funext b
    apply Subtype.ext
    ext a
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨c,hc⟩,hab⟩
      have hac := Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (p c).property).1 hc)
      have hcb : c = b := hac.2.symm.trans hab
      subst c
      exact hc
    · intro ha
      exact ⟨⟨b,ha⟩,
        (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (p b).property).1 ha)).2⟩

theorem couplingB2_partition_card {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) (q : B → ℕ) :
    Fintype.card {s : Finset A // ∀ b, (s.filter (fun a => f a = b)).card = q b} =
      ∏ b, ((Finset.univ.filter (fun a => f a = b)).card).choose (q b) := by
  rw [Fintype.card_congr (couplingB2_partitionEquiv f q), Fintype.card_pi]
  simp only [Fintype.card_coe, Finset.card_powersetCard]

def couplingB2_coord (v : Counts) : Bool × Bool → ℕ
  | (true,true) => v.a
  | (true,false) => v.b
  | (false,true) => v.c
  | (false,false) => v.d

def couplingB2_treated {n : ℕ} (w : PotentialTable n) (s : Finset (Fin n)) : Counts :=
  ⟨(s.filter (fun i => w i = (true,true))).card,
   (s.filter (fun i => w i = (true,false))).card,
   (s.filter (fun i => w i = (false,true))).card,
   (s.filter (fun i => w i = (false,false))).card⟩

theorem couplingB2_coord_treated {n : ℕ} (w : PotentialTable n)
    (s : Finset (Fin n)) (b : Bool × Bool) :
    couplingB2_coord (couplingB2_treated w s) b = (s.filter (fun i => w i = b)).card := by
  rcases b with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem couplingB2_coord_table {n : ℕ} (w : PotentialTable n) (b : Bool × Bool) :
    couplingB2_coord (tableCounts w) b = (Finset.univ.filter (fun i => w i = b)).card := by
  rcases b with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem couplingB2_coord_ext {v q : Counts}
    (h : ∀ b, couplingB2_coord v b = couplingB2_coord q b) : v = q := by
  exact Counts.ext (h (true,true)) (h (true,false)) (h (false,true)) (h (false,false))

theorem couplingB2_coord_sum (v : Counts) : ∑ b, couplingB2_coord v b = v.total := by
  simp [Fintype.sum_prod_type, Fintype.sum_bool, couplingB2_coord, Counts.total]
  omega

theorem couplingB2_treated_total {n : ℕ} (w : PotentialTable n) (s : Finset (Fin n)) :
    (couplingB2_treated w s).total = s.card := by
  rw [← couplingB2_coord_sum]
  simp_rw [couplingB2_coord_treated]
  simpa using Finset.sum_card_fiberwise_eq_card_filter s Finset.univ w

theorem couplingB2_fibre_card {n m : ℕ} (w : PotentialTable n) (q : Counts)
    (hq : q.total = m) :
    Fintype.card {s : Assignment n m // couplingB2_treated w s.val = q} =
      multiplicity (tableCounts w) q := by
  let e : {s : Assignment n m // couplingB2_treated w s.val = q} ≃
      {s : Finset (Fin n) // ∀ b, (s.filter (fun i => w i = b)).card = couplingB2_coord q b} :=
    { toFun := fun s => ⟨s.val.val, by
        intro b
        rw [← couplingB2_coord_treated, s.property]⟩
      invFun := fun s => ⟨⟨s.val, by
          have he : couplingB2_treated w s.val = q := couplingB2_coord_ext (by
            intro b; rw [couplingB2_coord_treated]; exact s.property b)
          rw [← couplingB2_treated_total w, he, hq]⟩,
        couplingB2_coord_ext (by
          intro b; rw [couplingB2_coord_treated]; exact s.property b)⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }
  rw [Fintype.card_congr e, couplingB2_partition_card]
  simp only [← couplingB2_coord_table, Fintype.prod_prod_type, Fintype.prod_bool,
    couplingB2_coord, multiplicity, binomial_eq_choose]
  ring

theorem couplingB2_state_iff (v q : Counts) (m : ℕ) :
    q ∈ randomStates v m ↔
      q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = m := by
  constructor
  · exact random_state_facts v m q
  · rintro ⟨ha,hb,hc,hd,ht⟩
    have hsum : q.a + q.b + q.c + q.d = m := ht
    simp only [randomStates, List.mem_flatMap, List.mem_filterMap, List.mem_range]
    refine ⟨q.a, by omega, q.b, by omega, q.c, by omega, ?_⟩
    have he : m-q.a-q.b-q.c = q.d := by omega
    simp only [he, if_pos hd]

theorem couplingB2_nodup_flatMap {A B : Type*} (xs : List A) (f : A → List B)
    (g : B → A) (hx : xs.Nodup) (hf : ∀ a ∈ xs, (f a).Nodup)
    (hg : ∀ a ∈ xs, ∀ b ∈ f a, g b = a) : (xs.flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨hf, ?_⟩
  apply List.pairwise_iff_forall_sublist.mpr
  intro a b hab
  have ha := hab.subset (by simp : a ∈ [a,b])
  have hb := hab.subset (by simp : b ∈ [a,b])
  have hne : a ≠ b := by
    have hh := hx.sublist hab
    simpa using hh
  intro q hqa hqb
  exact hne ((hg a ha q hqa).symm.trans (hg b hb q hqb))

theorem couplingB2_states_nodup (v : Counts) (m : ℕ) : (randomStates v m).Nodup := by
  unfold randomStates
  apply couplingB2_nodup_flatMap _ _ Counts.a List.nodup_range
  · intro a ha
    apply couplingB2_nodup_flatMap _ _ Counts.b List.nodup_range
    · intro b hb
      apply List.Nodup.filterMap _ List.nodup_range
      intro c c' q hc hc'
      dsimp at hc hc'
      simp only [Option.mem_def] at hc hc'
      split_ifs at hc hc' <;> simp_all
      exact congrArg Counts.c (hc.trans hc'.symm)
    · intro b hb q hq
      simp only [List.mem_filterMap] at hq
      obtain ⟨c,hc,he⟩ := hq
      split_ifs at he <;> simp_all only [Option.some.injEq, reduceCtorEq]
      cases he
      rfl
  · intro a ha q hq
    simp only [List.mem_flatMap, List.mem_filterMap] at hq
    obtain ⟨b,hb,c,hc,he⟩ := hq
    split_ifs at he <;> simp_all only [Option.some.injEq, reduceCtorEq]
    cases he
    rfl

theorem couplingB2_treated_state {n m : ℕ} (w : PotentialTable n) (s : Assignment n m) :
    couplingB2_treated w s.val ∈ randomStates (tableCounts w) m := by
  apply (couplingB2_state_iff _ _ _).mpr
  have hle (b : Bool × Bool) :
      couplingB2_coord (couplingB2_treated w s.val) b ≤ couplingB2_coord (tableCounts w) b := by
    rw [couplingB2_coord_treated, couplingB2_coord_table]
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.2
  exact ⟨hle (true,true), hle (true,false), hle (false,true), hle (false,false),
    (couplingB2_treated_total w s.val).trans s.property⟩

theorem couplingB2_event_card {n m : ℕ} (w : PotentialTable n) (E : Counts → Prop) :
    (Finset.univ.filter (fun s : Assignment n m => E (couplingB2_treated w s.val))).card =
      ((randomStates (tableCounts w) m).map fun q =>
        if E q then multiplicity (tableCounts w) q else 0).sum := by
  rw [← List.sum_toFinset _ (couplingB2_states_nodup _ _)]
  rw [Finset.card_eq_sum_card_fiberwise
    (t := (randomStates (tableCounts w) m).toFinset)
    (f := fun s : Assignment n m => couplingB2_treated w s.val)
    (by intro s hs; exact List.mem_toFinset.mpr (couplingB2_treated_state w s))]
  apply Finset.sum_congr rfl
  intro q hq
  have hqt := (random_state_facts _ _ _ (List.mem_toFinset.mp hq)).2.2.2.2
  have hf := couplingB2_fibre_card w q hqt
  rw [Fintype.card_subtype] at hf
  by_cases he : E q
  · rw [if_pos he, ← hf]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ he,h⟩⟩
  · rw [if_neg he]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact he (hs.2 ▸ hs.1)

theorem couplingB2_cell_filter {n : ℕ} (w : PotentialTable n) (s : Finset (Fin n))
    (b : Bool × Bool) :
    s.filter (fun i => w i = b) = Finset.univ.filter (fun i => i ∈ s ∧ w i = b) := by
  ext i
  simp

theorem couplingB2_arm_counts {n : ℕ} (w : PotentialTable n) (s : Finset (Fin n)) :
    (Finset.univ.filter (fun i => i ∈ s ∧ (w i).1 = true)).card =
      (couplingB2_treated w s).a + (couplingB2_treated w s).b ∧
    (Finset.univ.filter (fun i => i ∈ s ∧ (w i).1 = false)).card =
      (couplingB2_treated w s).c + (couplingB2_treated w s).d ∧
    (Finset.univ.filter (fun i => i ∈ s ∧ (w i).2 = true)).card =
      (couplingB2_treated w s).a + (couplingB2_treated w s).c ∧
    (Finset.univ.filter (fun i => i ∈ s ∧ (w i).2 = false)).card =
      (couplingB2_treated w s).b + (couplingB2_treated w s).d := by
  dsimp [couplingB2_treated]
  simp_rw [couplingB2_cell_filter]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
  repeat' constructor
  all_goals
    apply Finset.sum_congr rfl
    intro i hi
    rcases h : w i with ⟨a,b⟩
    cases a <;> cases b <;> by_cases hs : i ∈ s <;> simp [h,hs]

theorem couplingB2_complement_coord {n : ℕ} (w : PotentialTable n) (s : Finset (Fin n))
    (b : Bool × Bool) :
    couplingB2_coord (couplingB2_treated w sᶜ) b =
      couplingB2_coord (tableCounts w) b - couplingB2_coord (couplingB2_treated w s) b := by
  simp only [couplingB2_coord_treated, couplingB2_coord_table]
  have he : (sᶜ.filter (fun i => w i = b)) =
      (Finset.univ.filter (fun i => w i = b)).filter (fun i => i ∉ s) := by
    ext i
    simp [and_comm]
  rw [he]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i => w i = b)) (p := fun i => i ∈ s)
  have hs : (Finset.univ.filter (fun i => w i = b)).filter (fun i => i ∈ s) =
      s.filter (fun i => w i = b) := by ext i; simp [and_comm]
  rw [hs] at hsum
  omega

theorem couplingB2_observed {n : ℕ} (w : PotentialTable n) (s : Finset (Fin n)) :
    unitObserved (unitOutcomes w s) s = observed (tableCounts w) (couplingB2_treated w s) := by
  have hc (b) := couplingB2_complement_coord w s b
  have hT := couplingB2_arm_counts w s
  have hC := couplingB2_arm_counts w sᶜ
  have he (b : Bool) :
      Finset.univ.filter (fun i => i ∈ s ∧ unitOutcomes w s i = b) =
        Finset.univ.filter (fun i => i ∈ s ∧ (w i).1 = b) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ s <;> simp [unitOutcomes,hi]
  have he' (b : Bool) :
      Finset.univ.filter (fun i => i ∉ s ∧ unitOutcomes w s i = b) =
        Finset.univ.filter (fun i => i ∈ sᶜ ∧ (w i).2 = b) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    by_cases hi : i ∈ s <;> simp [unitOutcomes,hi]
  apply Counts.ext
  · simpa only [unitObserved, observed, he] using hT.1
  · simpa only [unitObserved, observed, he] using hT.2.1
  · change (Finset.univ.filter (fun i => i ∉ s ∧ unitOutcomes w s i = true)).card = _
    rw [he', hC.2.2.1]
    have hca := hc (true,true)
    have hcc := hc (false,true)
    dsimp [couplingB2_coord] at hca hcc
    have hcle : (couplingB2_treated w s).c ≤ (tableCounts w).c := by
      change (s.filter (fun i => w i = (false,true))).card ≤
        (Finset.univ.filter (fun i => w i = (false,true))).card
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))
    dsimp [observed]
    omega
  · change (Finset.univ.filter (fun i => i ∉ s ∧ unitOutcomes w s i = false)).card = _
    rw [he', hC.2.2.2]
    have hcb := hc (true,false)
    have hcd := hc (false,false)
    dsimp [couplingB2_coord] at hcb hcd
    have hdle : (couplingB2_treated w s).d ≤ (tableCounts w).d := by
      change (s.filter (fun i => w i = (false,false))).card ≤
        (Finset.univ.filter (fun i => w i = (false,false))).card
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,(Finset.mem_filter.mp hi).2⟩
    dsimp [observed]
    omega

theorem couplingB2_observed_arms {n : ℕ} (y : Fin n → Bool) (s : Finset (Fin n)) :
    (unitObserved y s).a + (unitObserved y s).b = s.card ∧
    (unitObserved y s).c + (unitObserved y s).d + s.card = n := by
  have hT : (unitObserved y s).a + (unitObserved y s).b = s.card := by
    have he : ∀ i : Fin n,
        (if i ∈ s ∧ y i = true then 1 else 0) +
          (if i ∈ s ∧ y i = false then 1 else 0) = (if i ∈ s then 1 else 0 : ℕ) := by
      intro i
      cases h : y i <;> by_cases hs : i ∈ s <;> simp [h,hs]
    dsimp [unitObserved]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
    simp only [he, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, smul_eq_mul, mul_one]
    simp
  have hC : (unitObserved y s).c + (unitObserved y s).d = sᶜ.card := by
    have he : ∀ i : Fin n,
        (if i ∉ s ∧ y i = true then 1 else 0) +
          (if i ∉ s ∧ y i = false then 1 else 0) = (if i ∈ sᶜ then 1 else 0 : ℕ) := by
      intro i
      cases h : y i <;> by_cases hs : i ∈ s <;> simp [h,hs]
    dsimp [unitObserved]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
    simp only [he, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, smul_eq_mul, mul_one]
    simp
  refine ⟨hT, ?_⟩
  rw [hC, Finset.card_compl, Fintype.card_fin]
  have hs : s.card ≤ n := by simpa using Finset.card_le_univ s
  omega

theorem couplingB2_outcome_estimate {n : ℕ} (y : Fin n → Bool) (s : Finset (Fin n)) :
    outcomeEstimator y s = estimate (unitObserved y s) := by
  have ha : (∑ i, if i ∈ s then bit (y i) else 0) = ((unitObserved y s).a : ℝ) := by
    simp only [unitObserved, ← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro i hi
    cases h : y i <;> by_cases hs : i ∈ s <;> simp [bit,h,hs]
  have hc : (∑ i, if i ∈ s then 0 else bit (y i)) = ((unitObserved y s).c : ℝ) := by
    simp only [unitObserved, ← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro i hi
    cases h : y i <;> by_cases hs : i ∈ s <;> simp [bit,h,hs]
  have hT := congrArg (fun a : ℕ => (a : ℝ)) (couplingB2_observed_arms y s).1
  have hC := congrArg (fun a : ℕ => (a : ℝ)) (couplingB2_observed_arms y s).2
  push_cast at hT hC
  have hC' : ((unitObserved y s).c : ℝ) + (unitObserved y s).d = n-s.card := by
    linarith
  simp only [outcomeEstimator, ha, hc, estimate, estimateQ, Rat.cast_sub, Rat.cast_div,
    Rat.cast_add, Rat.cast_natCast, hT, hC']

theorem couplingB2_estimator_observation {n : ℕ} (w : PotentialTable n) (s : Finset (Fin n)) :
    tableEstimator w s = estimate (observed (tableCounts w) (couplingB2_treated w s)) := by
  rw [← couplingB2_observed, ← couplingB2_outcome_estimate]
  unfold tableEstimator outcomeEstimator
  congr 2 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    by_cases hs : i ∈ s <;> simp [unitOutcomes,hs]

theorem couplingB2_deviation {n m : ℕ} (v o : Counts) (hm : 0 < m) (hn : n = 2*m)
    (hv : v.total = n) (hT : o.a+o.b = m) (hC : o.c+o.d = m) :
    (deviationNumerator v o m : ℝ) = (n : ℝ)*m*m*(estimate o-tau v) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by rw [hn]; positivity
  have hnR : (n : ℝ) = 2*m := by exact_mod_cast hn
  have hTR : (o.a : ℝ)+o.b = m := by exact_mod_cast hT
  have hCR : (o.c : ℝ)+o.d = m := by exact_mod_cast hC
  simp only [deviationNumerator, estimate, estimateQ, tau, tauQ, hv, Counts.effect,
    Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_intCast,
    Int.cast_mul, Int.cast_sub, Int.cast_natCast, hTR, hCR]
  field_simp
  rw [hnR]
  ring

theorem couplingB2_tail_compare {n m : ℕ} (v o o' : Counts) (hm : 0 < m) (hn : n = 2*m)
    (hv : v.total = n) (hT : o.a+o.b = m) (hC : o.c+o.d = m)
    (hT' : o'.a+o'.b = m) (hC' : o'.c+o'.d = m) :
    ((deviationNumerator v o' m).natAbs ≥ (deviationNumerator v o m).natAbs) ↔
      |estimate o'-tau v| ≥ |estimate o-tau v| := by
  have hpos : 0 < (n : ℝ)*m*m := by
    have hnpos : 0 < n := by omega
    positivity
  change (deviationNumerator v o m).natAbs ≤ (deviationNumerator v o' m).natAbs ↔ _
  rw [← Nat.cast_le (α := ℝ), Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs,
    couplingB2_deviation v o hm hn hv hT hC,
    couplingB2_deviation v o' hm hn hv hT' hC',
    abs_mul ((n : ℝ)*m*m) (estimate o-tau v),
    abs_mul ((n : ℝ)*m*m) (estimate o'-tau v),
    abs_of_pos hpos, mul_le_mul_iff_right₀ hpos]

theorem couplingB2_pvalue {n m : ℕ} (w : PotentialTable n) (y : Fin n → Bool)
    (s : Finset (Fin n)) (hm : 0 < m) (hn : n = 2*m) (hs : s.card = m)
    (hw : PossibleTable y s w) :
    unitPValue w y s = (pValue (tableCounts w) (unitObserved y s) : ℝ) := by
  have hnpos : 0 < n := by omega
  have hv := (corrected_sate w hnpos).1
  have htau := (corrected_sate w hnpos).2.2.2
  have hT := (couplingB2_observed_arms y s).1.trans hs
  have hC : (unitObserved y s).c+(unitObserved y s).d = m := by
    have hh := (couplingB2_observed_arms y s).2
    omega
  have he (q : Assignment n s.card) :
      (|(tableEstimator w q.val-tableTau w)| ≥ |outcomeEstimator y s-tableTau w|) ↔
      (deviationNumerator (tableCounts w) (observed (tableCounts w)
        (couplingB2_treated w q.val)) m).natAbs ≥
          (deviationNumerator (tableCounts w) (unitObserved y s) m).natAbs := by
    have hq : q.val.card = m := q.property.trans hs
    have hO := couplingB2_observed_arms (unitOutcomes w q.val) q.val
    rw [couplingB2_observed] at hO
    have hT' := hO.1.trans hq
    have hC' : (observed (tableCounts w) (couplingB2_treated w q.val)).c+
        (observed (tableCounts w) (couplingB2_treated w q.val)).d = m := by omega
    rw [couplingB2_estimator_observation, couplingB2_outcome_estimate, htau]
    exact (couplingB2_tail_compare _ _ _ hm hn hv hT hC hT' hC').symm
  unfold unitPValue uniformProb pValue tailCount
  simp only [Rat.cast_div, Rat.cast_natCast, binomial_eq_choose, hT,
    Fintype.card_finset_len, Fintype.card_fin, hs, hv]
  congr 1
  have hh := couplingB2_event_card (m := s.card) w (fun q =>
    (deviationNumerator (tableCounts w) (observed (tableCounts w) q) m).natAbs ≥
      (deviationNumerator (tableCounts w) (unitObserved y s) m).natAbs)
  simpa only [← hs, he] using congrArg (fun a : ℕ => (a : ℝ)) hh

theorem couplingB2_change_at {n : ℕ} (y y' : Fin n → Bool) (z r q : Finset (Fin n))
    (w : PotentialTable n) (hy' : ∀ i, i ∉ r → y' i = y i)
    (hw : PossibleTable y' z w) (i : Fin n) :
    let yp := unitPlus y z r
    let wp := coupledPlus w yp z
    (bit (wp i).1-bit (wp i).2) = (bit (w i).1-bit (w i).2)+
      (if y' i ≠ yp i then 1 else 0) ∧
    (if i ∈ q then bit (wp i).1 else -bit (wp i).2) =
      (if i ∈ q then bit (w i).1 else -bit (w i).2)+
        (if y' i ≠ yp i ∧ (i ∈ q ↔ i ∈ z) then 1 else 0) := by
  have hobs := congrFun hw i
  change (if i ∈ z then (w i).1 else (w i).2) = y' i at hobs
  have hagree := hy' i
  clear hw hy'
  dsimp
  rcases h : w i with ⟨a,b⟩
  by_cases hz : i ∈ z <;> by_cases hr : i ∈ r <;> by_cases hq : i ∈ q <;>
    cases a <;> cases b <;> cases hY : y i <;> cases hY' : y' i <;>
      simp_all [coupledPlus, unitPlus, bit]

theorem couplingB2_compatible {n : ℕ} (w : PotentialTable n) (yp : Fin n → Bool)
    (z : Finset (Fin n)) : PossibleTable yp z (coupledPlus w yp z) := by
  funext i
  by_cases hi : i ∈ z <;> simp [unitOutcomes,coupledPlus,hi]

theorem couplingB2_compatible_estimator {n : ℕ} (w : PotentialTable n) (y : Fin n → Bool)
    (z : Finset (Fin n)) (hw : PossibleTable y z w) :
    tableEstimator w z = outcomeEstimator y z := by
  change unitOutcomes w z = y at hw
  rw [← hw]
  unfold tableEstimator outcomeEstimator
  congr 2 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    by_cases hs : i ∈ z <;> simp [unitOutcomes,hs]

theorem couplingB2_sum_changes {n : ℕ} (m : ℕ) (hm : 0 < m) (hn : n = 2*m)
    (y y' : Fin n → Bool) (z r : Finset (Fin n)) (hz : z.card = m)
    (hy' : ∀ i, i ∉ r → y' i = y i) (w : PotentialTable n) (hw : PossibleTable y' z w) :
    let yp := unitPlus y z r
    let D := Finset.univ.filter (fun i => y' i ≠ yp i)
    let d := D.card
    let wp := coupledPlus w yp z
    tableTau wp = tableTau w+(d : ℝ)/n ∧
    outcomeEstimator yp z = outcomeEstimator y' z+2*(d : ℝ)/n ∧
    (∀ q : Assignment n m,
      let N := (D.filter (fun i => (i ∈ q.val ↔ i ∈ z))).card
      N ≤ d ∧ tableEstimator wp q.val = tableEstimator w q.val+2*(N : ℝ)/n) := by
  dsimp
  let yp := unitPlus y z r
  let D := Finset.univ.filter (fun i => y' i ≠ yp i)
  let wp := coupledPlus w yp z
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by rw [hn]; positivity
  have hnR : (n : ℝ) = 2*m := by exact_mod_cast hn
  have hsum : (∑ i, (bit (wp i).1-bit (wp i).2)) =
      (∑ i, (bit (w i).1-bit (w i).2))+(D.card : ℝ) := by
    calc
      _ = ∑ i, ((bit (w i).1-bit (w i).2)+(if y' i ≠ yp i then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (couplingB2_change_at y y' z r z w hy' hw i).1
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_boole,D]
  have htau : tableTau wp = tableTau w+(D.card : ℝ)/n := by
    unfold tableTau
    rw [hsum, add_div]
  have hest (q : Finset (Fin n)) (hq : q.card = m) :
      tableEstimator wp q = tableEstimator w q+
        2*(((D.filter (fun i => (i ∈ q ↔ i ∈ z))).card : ℕ) : ℝ)/n := by
    rw [corrected_signed_sum wp q m hm hn hq, corrected_signed_sum w q m hm hn hq]
    have hs : (∑ i, if i ∈ q then bit (wp i).1 else -bit (wp i).2) =
        (∑ i, if i ∈ q then bit (w i).1 else -bit (w i).2)+
          ((D.filter (fun i => (i ∈ q ↔ i ∈ z))).card : ℝ) := by
      calc
        _ = ∑ i, ((if i ∈ q then bit (w i).1 else -bit (w i).2)+
            (if y' i ≠ yp i ∧ (i ∈ q ↔ i ∈ z) then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (couplingB2_change_at y y' z r q w hy' hw i).2
        _ = _ := by simp [Finset.sum_add_distrib,D,Finset.filter_filter]
    rw [hs, add_div]
    congr 1
    rw [hnR]
    field_simp
  have hzest := hest z hz
  simp only [iff_self, implies_true, Finset.filter_true] at hzest
  rw [couplingB2_compatible_estimator wp yp z (couplingB2_compatible w yp z),
    couplingB2_compatible_estimator w y' z hw] at hzest
  refine ⟨htau,hzest,?_⟩
  intro q
  exact ⟨Finset.card_filter_le _ _,hest q.val q.property⟩

theorem couplingB2_endpoint {n m : ℕ} (mpos : 0 < m) (hn : n = 2*m)
    (y : Fin n → Bool) (z : Finset (Fin n)) (hz : z.card = m)
    (w : PotentialTable n) (hw : PossibleTable y z w) (α : ℝ)
    (hp : α ≤ unitPValue w y z) : tableTau w ≤ upper α (unitObserved y z) := by
  have hnpos : 0 < n := by omega
  have htau := (corrected_sate w hnpos).2.2.2
  have hq : couplingB2_treated w z ∈ randomStates (tableCounts w) m :=
    couplingB2_treated_state w ⟨z,hz⟩
  have ho : unitObserved y z = observed (tableCounts w) (couplingB2_treated w z) := by
    rw [← hw]
    exact couplingB2_observed w z
  have hv : Possible (unitObserved y z) (tableCounts w) := by
    rw [ho]
    exact observed_population_possible _ _ _ hq
  have hacc := accepted_of_possible α (unitObserved y z) (tableCounts w) hv
    ((couplingB2_pvalue w y z mpos hn hz hw) ▸ hp)
  rw [htau]
  exact le_csSup (accepted α (unitObserved y z)).finite_toSet.bddAbove hacc

theorem shuffleB2_possible (m : ℕ) (v : Counts) :
    Possible ⟨0,m,0,m⟩ v ↔
      ∃ b ≤ m, ∃ c ≤ m, v = ⟨0,b,c,2*m-c-b⟩ := by
  simp only [Possible,possibleTables,List.mem_flatMap,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,j,hj,k,hk,l,hl,he⟩
    have hi0 : i = 0 := by dsimp at hi; omega
    have hk0 : k = 0 := by dsimp at hk; omega
    subst i k
    refine ⟨l,by omega,j,by omega,?_⟩
    simpa [two_mul] using he.symm
  · rintro ⟨b,hb,c,hc,rfl⟩
    refine ⟨0,by simp,c,by omega,0,by simp,b,by omega,?_⟩
    simp [two_mul]

theorem shuffleB2_line (m x j : ℕ) (v : Counts) :
    v ∈ lineGroup ⟨0,m,0,m⟩ (x : ℤ) j ↔
      x ≤ j ∧ j ≤ m ∧ v = ⟨0,j,j-x,2*m-(j-x)-j⟩ := by
  simp only [lineGroup,List.mem_filter,decide_eq_true_eq]
  change (Possible ⟨0,m,0,m⟩ v ∧ v.effect = (x : ℤ) ∧ v.a+v.b = j) ↔ _
  rw [shuffleB2_possible]
  constructor
  · rintro ⟨⟨b,hb,c,hc,rfl⟩,he,hj⟩
    dsimp [Counts.effect] at he hj
    have hbj : b = j := by omega
    have hxc : c = j-x := by omega
    subst b c
    exact ⟨by omega,hb,rfl⟩
  · rintro ⟨hx,hj,rfl⟩
    refine ⟨⟨j,hj,j-x,by omega,rfl⟩,?_,by simp⟩
    dsimp [Counts.effect]
    omega

theorem shuffleB2_first (m x j : ℕ) :
    firstOnLine ⟨0,m,0,m⟩ (x : ℤ) j =
      if x ≤ j ∧ j ≤ m then some ⟨0,j,j-x,2*m-(j-x)-j⟩ else none := by
  by_cases hj : x ≤ j ∧ j ≤ m
  · rw [if_pos hj]
    have hmem : (⟨0,j,j-x,2*m-(j-x)-j⟩ : Counts) ∈
        lineGroup ⟨0,m,0,m⟩ (x : ℤ) j := (shuffleB2_line _ _ _ _).mpr ⟨hj.1,hj.2,rfl⟩
    cases he : firstOnLine ⟨0,m,0,m⟩ (x : ℤ) j with
    | none =>
      have hnil := (minimum_b_spec (lineGroup ⟨0,m,0,m⟩ (x : ℤ) j)).1.mp he
      rw [hnil] at hmem
      cases hmem
    | some u =>
      have hu := (minimum_b_spec (lineGroup ⟨0,m,0,m⟩ (x : ℤ) j)).2 u he
      have hue := ((shuffleB2_line _ _ _ _).mp hu.1).2.2
      rw [hue]
  · rw [if_neg hj]
    apply (minimum_b_spec (lineGroup ⟨0,m,0,m⟩ (x : ℤ) j)).1.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v hv
    exact hj ⟨((shuffleB2_line _ _ _ _).mp hv).1,((shuffleB2_line _ _ _ _).mp hv).2.1⟩

theorem shuffleB2_candidates (m x : ℕ) (hx : 0 < x) :
    candidates ⟨0,m,0,m⟩ (x : ℤ) =
      ((List.range (2*m+1)).filter (fun j => x ≤ j ∧ j ≤ m)).map
        (fun j => (⟨0,j,j-x,2*m-(j-x)-j⟩ : Counts)) := by
  unfold candidates
  simp only [Counts.total,Nat.zero_add,Nat.add_zero,← two_mul]
  change (List.range (2*m+1)).flatMap _ = _
  generalize List.range (2*m+1) = xs
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    rw [List.flatMap_cons,shuffleB2_first]
    by_cases hj' : x ≤ j ∧ j ≤ m
    · simp [hj',ih]
    · simp [hj',ih]

theorem shuffleB2_filtered_range (x t : ℕ) :
    (List.range (x+t)).filter (fun j => x ≤ j) = (List.range t).map (fun j => x+j) := by
  induction t with
  | zero =>
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    simp only [List.mem_filter,List.mem_range,decide_eq_true_eq] at hj
    omega
  | succ t ih =>
    rw [Nat.add_succ, List.range_succ, List.filter_append, ih, List.range_succ,
      List.map_append]
    simp

theorem shuffleB2_candidate_list (x : ℕ) (hx : 0 < x) :
    candidates ⟨0,2*x,0,2*x⟩ (x : ℤ) =
      (List.range (x+1)).map (fun t => (⟨0,x+t,t,3*x-2*t⟩ : Counts)) := by
  rw [shuffleB2_candidates (2*x) x hx]
  have hf : (List.range (2*(2*x)+1)).filter (fun j => x ≤ j ∧ j ≤ 2*x) =
      (List.range (2*x+1)).filter (fun j => x ≤ j) := by
    rw [show 2*(2*x)+1 = (2*x+1)+(2*x) by omega, List.range_add,
      List.filter_append]
    have hz : ((List.range (2*x)).map (fun i => 2*x+1+i)).filter
        (fun j => x ≤ j ∧ j ≤ 2*x) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro j hj
      simp only [List.mem_filter,List.mem_map,List.mem_range,decide_eq_true_eq] at hj
      obtain ⟨⟨i,hi,rfl⟩,hj⟩ := hj
      omega
    rw [hz,List.append_nil]
    apply List.filter_congr
    intro j hj
    have hh := List.mem_range.mp hj
    simp only [decide_eq_decide]
    omega
  rw [hf, show 2*x+1 = x+(x+1) by omega, shuffleB2_filtered_range, List.map_map]
  apply List.map_congr_left
  intro t ht
  have htt := List.mem_range.mp ht
  dsimp
  apply Counts.ext <;> dsimp <;> omega

theorem shuffleB2_first_trace (x : ℕ) (hx : 0 < x) (reject : Counts → ℕ → Bool)
    (h : x+1 ≤ (runTests reject 0 (candidates ⟨0,2*x,0,2*x⟩ (x : ℤ))).trace.length) :
    x+1 ≤ (upperRun true ⟨0,2*x,0,2*x⟩ reject).trace.length := by
  have hm : (((-1 : ℤ)+(2*x+1))/2) = x := by omega
  have hn : ¬ ((2*x : ℤ)+1 ≤ -1+1) := by omega
  unfold upperRun
  simp only [Counts.total, Nat.zero_add, Nat.add_zero, Nat.cast_zero, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, sub_zero, mul_zero, zero_add, zero_sub, ↓reduceIte]
  rw [adaptiveSearch]
  simp only [true_and, not_true_eq_false, false_and, if_false, if_neg hn, hm,
    List.length_append]
  omega

theorem shuffleB2_card_prefix {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  let e : {i : Fin n // i.val < k} ≃ Fin k :=
    { toFun := fun i => ⟨i.val.val,i.property⟩
      invFun := fun i => ⟨⟨i.val,lt_of_lt_of_le i.isLt hk⟩,i.isLt⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [← Fintype.card_subtype,Fintype.card_congr e,Fintype.card_fin]

theorem shuffleB2_card_interval {n : ℕ} (a b : ℕ) (ha : a ≤ b) (hb : b ≤ n) :
    (Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b)).card = b-a := by
  have he : Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b) =
      (Finset.univ.filter (fun i : Fin n => i.val < b)) \
        (Finset.univ.filter (fun i : Fin n => i.val < a)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    omega
  rw [he,Finset.card_sdiff_of_subset,shuffleB2_card_prefix b hb,
    shuffleB2_card_prefix a (ha.trans hb)]
  intro i hi
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  omega

theorem shuffleB2_canonical_counts (v : Counts) :
    tableCounts (fun i : Fin v.total => canonicalPair v i.val) = v := by
  have ha : v.a ≤ v.total := by dsimp [Counts.total]; omega
  have hb : v.a+v.b ≤ v.total := by dsimp [Counts.total]; omega
  have hc : v.a+v.b+v.c ≤ v.total := by dsimp [Counts.total]; omega
  have h1 : (Finset.univ.filter fun i : Fin v.total => canonicalPair v i.val = (true,true)) =
      Finset.univ.filter (fun i : Fin v.total => i.val < v.a) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    unfold canonicalPair
    split_ifs <;> simp_all <;> omega
  have h2 : (Finset.univ.filter fun i : Fin v.total => canonicalPair v i.val = (true,false)) =
      Finset.univ.filter (fun i : Fin v.total => v.a ≤ i.val ∧ i.val < v.a+v.b) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    unfold canonicalPair
    split_ifs <;> simp_all <;> omega
  have h3 : (Finset.univ.filter fun i : Fin v.total => canonicalPair v i.val = (false,true)) =
      Finset.univ.filter (fun i : Fin v.total => v.a+v.b ≤ i.val ∧ i.val < v.a+v.b+v.c) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    unfold canonicalPair
    split_ifs <;> simp_all <;> omega
  have h4 : (Finset.univ.filter fun i : Fin v.total => canonicalPair v i.val = (false,false)) =
      Finset.univ.filter (fun i : Fin v.total => v.a+v.b+v.c ≤ i.val ∧ i.val < v.total) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    unfold canonicalPair
    split_ifs <;> simp_all <;> omega
  apply Counts.ext <;> dsimp only [tableCounts]
  · rw [h1,shuffleB2_card_prefix v.a ha]
  · rw [h2,shuffleB2_card_interval _ _ (by omega) hb]
    omega
  · rw [h3,shuffleB2_card_interval _ _ (by omega) hc]
    omega
  · rw [h4,shuffleB2_card_interval _ _ hc le_rfl]
    dsimp [Counts.total]
    omega

theorem shuffleB2_canonical_observed {n : ℕ} (v : Counts) (s : Finset (Fin n)) :
    canonicalObserved v s = unitObserved (unitOutcomes (fun i => canonicalPair v i.val) s) s := by
  apply Counts.ext <;> dsimp [canonicalObserved,unitObserved] <;> congr 1 <;> ext i <;>
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] <;>
    by_cases hs : i ∈ s <;> simp [unitOutcomes,hs]

theorem shuffleB2_zero_state (x t : ℕ) (hx : 0 < x) (ht : t ≤ x) (heven : 2 ∣ x) :
    let v : Counts := ⟨0,x+t,t,3*x-2*t⟩
    let q : Counts := ⟨0,t+x/2,0,2*x-t-x/2⟩
    v.total = 4*x ∧ q ∈ randomStates v (2*x) ∧ 0 < multiplicity v q ∧
      deviationNumerator v (observed v q) (2*x) = 0 ∧
      deviationNumerator v ⟨0,2*x,0,2*x⟩ (2*x) ≠ 0 := by
  have hhalf : 2*(x/2) = x := Nat.mul_div_cancel' heven
  dsimp
  have hv : (⟨0,x+t,t,3*x-2*t⟩ : Counts).total = 4*x := by dsimp [Counts.total]; omega
  refine ⟨hv, (couplingB2_state_iff _ _ _).mpr ?_, ?_, ?_, ?_⟩
  · dsimp [Counts.total]
    omega
  · unfold multiplicity
    simp only [binomial_eq_choose]
    apply mul_pos
    · apply mul_pos
      · apply mul_pos
        · exact Nat.choose_pos (by omega)
        · exact Nat.choose_pos (by omega)
      · exact Nat.choose_pos (by omega)
    · exact Nat.choose_pos (by omega)
  · have hsub : 2*x-t-x/2 ≤ 3*x-2*t := by omega
    have hsub' : t+x/2 ≤ x+t := by omega
    simp only [deviationNumerator,observed,Counts.effect,hv,Nat.cast_zero,sub_zero,
      zero_add,Nat.sub_zero,Int.natCast_sub hsub',Int.natCast_sub hsub]
    push_cast
    have hhalf' : 2*(x/2 : ℕ) = x := hhalf
    have hhR : (x : ℤ) = 2*(x/2 : ℕ) := by exact_mod_cast hhalf'.symm
    rw [hhR]
    have hd : (2*((x/2 : ℕ) : ℤ))/2 = ((x/2 : ℕ) : ℤ) := by omega
    rw [hd]
    ring
  · simp only [deviationNumerator,Counts.effect,hv,Nat.cast_zero,sub_zero,zero_add,
      mul_zero,sub_self,zero_sub]
    push_cast
    have hxZ : (0 : ℤ) < x := by exact_mod_cast hx
    convert mul_ne_zero (by norm_num : (-4 : ℤ) ≠ 0) (pow_ne_zero 3 hxZ.ne') using 1 <;> ring

theorem shuffleB2_runTests_indexed (reject : Counts → ℕ → Bool) (idx : ℕ) (xs : List Counts)
    (h : ∀ k (hk : k < xs.length), reject xs[k] (idx+k) = true) :
    (runTests reject idx xs).trace.length = xs.length := by
  induction xs generalizing idx with
  | nil => rfl
  | cons v vs ih =>
    have hv := h 0 (by simp)
    simp only [List.getElem_cons_zero,Nat.add_zero] at hv
    simp only [runTests,hv,↓reduceIte,List.length_cons]
    rw [ih]
    intro k hk
    have hh := h (k+1) (by simpa using Nat.succ_lt_succ hk)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem shuffleB2_zero_assignment (x t : ℕ) (hx : 0 < x) (ht : t ≤ x) (heven : 2 ∣ x) :
    ∃ s : Assignment (4*x) (2*x),
      deviationNumerator ⟨0,x+t,t,3*x-2*t⟩
        (canonicalObserved ⟨0,x+t,t,3*x-2*t⟩ s.val) (2*x) = 0 := by
  let v : Counts := ⟨0,x+t,t,3*x-2*t⟩
  let q : Counts := ⟨0,t+x/2,0,2*x-t-x/2⟩
  have hstate := shuffleB2_zero_state x t hx ht heven
  rcases hstate with ⟨hv,hq,hmult,hzero,hobs⟩
  change v.total = 4*x at hv
  let w : PotentialTable (4*x) := fun i => canonicalPair v i.val
  have hcounts : tableCounts w = v := by
    dsimp only [w]
    rw [← hv]
    exact shuffleB2_canonical_counts v
  have hqt : q.total = 2*x := (random_state_facts v (2*x) q hq).2.2.2.2
  have hcard : 0 < Fintype.card {s : Assignment (4*x) (2*x) // couplingB2_treated w s.val = q} := by
    rw [couplingB2_fibre_card w q hqt,hcounts]
    exact hmult
  obtain ⟨⟨s,hs⟩⟩ := Fintype.card_pos_iff.mp hcard
  refine ⟨s,?_⟩
  rw [shuffleB2_canonical_observed,couplingB2_observed]
  change deviationNumerator v (observed (tableCounts w) (couplingB2_treated w s.val)) (2*x) = 0
  rw [hcounts,hs]
  exact hzero

theorem shuffleB2_positive_pool (x K : ℕ) (hx : 0 < x) (heven : 2 ∣ x) :
    0 < uniformProb (fun pool : Fin (2*testBudget (4*x)+1) → Fin K → Assignment (4*x) (4*x/2) =>
      (x+1)*K*(4*x-1) ≤ upperShuffleCost (1/2) (1/8) ⟨0,2*x,0,2*x⟩ pool) := by
  classical
  have hhalfn : 4*x/2 = 2*x := by omega
  have hc : ∀ t : Fin (x+1), ∃ s : Assignment (4*x) (4*x/2),
      deviationNumerator ⟨0,x+t.val,t.val,3*x-2*t.val⟩
        (canonicalObserved ⟨0,x+t.val,t.val,3*x-2*t.val⟩ s.val) (2*x) = 0 := by
    intro t
    change ∃ s : {s : Finset (Fin (4*x)) // s.card = 4*x/2}, _
    rw [hhalfn]
    exact shuffleB2_zero_assignment x t.val hx (by omega) heven
  choose S hS using hc
  let pool : Fin (2*testBudget (4*x)+1) → Fin K → Assignment (4*x) (4*x/2) :=
    fun b _ => if h : b.val < x+1 then S ⟨b.val,h⟩ else S ⟨0,by omega⟩
  have hbudget : 4*x+1 ≤ testBudget (4*x) := by
    unfold testBudget
    simpa using Nat.mul_le_mul_left (4*x+1) (show 1 ≤ Nat.log2 (4*x+1)+3 by omega)
  have hreject (t : ℕ) (ht : t < x+1) :
      approximateReject (1/2) (1/8) ⟨0,2*x,0,2*x⟩ pool
        ⟨0,x+t,t,3*x-2*t⟩ t = true := by
    have hb : t < 2*testBudget (4*x)+1 := by omega
    have hbatch (i : Fin K) : batch pool t i = (S ⟨t,ht⟩).val := by
      simp [batch,pool,Nat.mod_eq_of_lt hb,Nat.le_of_lt_succ ht]
    have hzero := hS ⟨t,ht⟩
    have hobs := (shuffleB2_zero_state x t hx (by omega) heven).2.2.2.2
    have hnat : 0 < (deviationNumerator ⟨0,x+t,t,3*x-2*t⟩ ⟨0,2*x,0,2*x⟩ (2*x)).natAbs :=
      Int.natAbs_pos.mpr hobs
    have hm : monteMean ⟨0,x+t,t,3*x-2*t⟩ ⟨0,2*x,0,2*x⟩ (batch pool t) = 0 := by
      unfold monteMean
      simp only [Nat.zero_add,hbatch,hzero,Int.natAbs_zero,
        show ¬ 0 ≥ (deviationNumerator ⟨0,x+t,t,3*x-2*t⟩ ⟨0,2*x,0,2*x⟩ (2*x)).natAbs by omega,
        ↓reduceIte,Finset.sum_const_zero,zero_div]
    norm_num [approximateReject,hm]
  have hrun : (runTests (approximateReject (1/2) (1/8) ⟨0,2*x,0,2*x⟩ pool) 0
      (candidates ⟨0,2*x,0,2*x⟩ (x : ℤ))).trace.length = x+1 := by
    rw [shuffleB2_runTests_indexed]
    · rw [shuffleB2_candidate_list x hx,List.length_map,List.length_range]
    · rw [shuffleB2_candidate_list x hx]
      intro t ht
      simp only [List.length_map,List.length_range] at ht
      simpa only [List.getElem_map,List.getElem_range,Nat.zero_add] using hreject t ht
  have htrace := shuffleB2_first_trace x hx
    (approximateReject (1/2) (1/8) ⟨0,2*x,0,2*x⟩ pool) hrun.ge
  have hcost : (x+1)*K*(4*x-1) ≤ upperShuffleCost (1/2) (1/8) ⟨0,2*x,0,2*x⟩ pool :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right K htrace)
  unfold uniformProb
  apply div_pos
  · apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine ⟨pool,?_⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hcost
  · apply Nat.cast_pos.mpr
    exact Fintype.card_pos_iff.mpr ⟨pool⟩

noncomputable def shuffleB2_mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a)/Fintype.card A

theorem shuffleB2_mean_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    shuffleB2_mean (fun a => f (e a)) = shuffleB2_mean f := by
  unfold shuffleB2_mean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem shuffleB2_mean_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    shuffleB2_mean f = shuffleB2_mean (fun a => shuffleB2_mean (fun b => f (a,b))) := by
  simp only [shuffleB2_mean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    Finset.sum_div,div_div,mul_comm]

theorem shuffleB2_mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    shuffleB2_mean (fun _ : A => c) = c := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [shuffleB2_mean,hc]

theorem shuffleB2_mean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    shuffleB2_mean (fun a => f a+g a) = shuffleB2_mean f+shuffleB2_mean g := by
  simp only [shuffleB2_mean,Finset.sum_add_distrib,add_div]

theorem shuffleB2_mean_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    shuffleB2_mean (fun a => f a-g a) = shuffleB2_mean f-shuffleB2_mean g := by
  simp only [shuffleB2_mean,Finset.sum_sub_distrib,sub_div]

theorem shuffleB2_mean_mul {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    shuffleB2_mean (fun a => c*f a) = c*shuffleB2_mean f := by
  unfold shuffleB2_mean
  rw [← Finset.mul_sum]
  ring

theorem shuffleB2_mean_sum {A I : Type*} [Fintype A] [Fintype I] (f : I → A → ℝ) :
    shuffleB2_mean (fun a => ∑ i, f i a) = ∑ i, shuffleB2_mean (f i) := by
  unfold shuffleB2_mean
  rw [Finset.sum_comm,Finset.sum_div]

theorem shuffleB2_mean_congr {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a = g a) :
    shuffleB2_mean f = shuffleB2_mean g := by
  congr 1
  exact funext h

theorem shuffleB2_mean_proj {A I : Type*} [Fintype A] [Fintype I] [Nonempty A]
    [DecidableEq I] (i : I) (f : A → ℝ) :
    shuffleB2_mean (fun x : I → A => f (x i)) = shuffleB2_mean f := by
  have he := shuffleB2_mean_equiv (Equiv.funSplitAt i A) (fun p => f p.1)
  change shuffleB2_mean (fun x : I → A => f (x i)) = _ at he
  rw [he,shuffleB2_mean_prod]
  simp only [shuffleB2_mean_const]

theorem shuffleB2_mean_two {A I : Type*} [Fintype A] [Fintype I] [Nonempty A]
    [DecidableEq I] (i j : I) (hij : j ≠ i) (f g : A → ℝ) :
    shuffleB2_mean (fun x : I → A => f (x i)*g (x j)) =
      shuffleB2_mean f*shuffleB2_mean g := by
  let e := Equiv.funSplitAt i A
  have he := shuffleB2_mean_equiv e (fun p => f p.1*g (p.2 ⟨j,hij⟩))
  change shuffleB2_mean (fun x : I → A => f (x i)*g (x j)) = _ at he
  rw [he,shuffleB2_mean_prod]
  simp_rw [shuffleB2_mean_mul,shuffleB2_mean_proj]
  unfold shuffleB2_mean
  rw [← Finset.sum_mul]
  ring

theorem shuffleB2_mean_mono {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    shuffleB2_mean f ≤ shuffleB2_mean g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun a _ => h a)

theorem shuffleB2_prob_mean {A : Type*} [Fintype A] (E : A → Prop) :
    uniformProb E = shuffleB2_mean (fun a => if E a then 1 else 0) := by
  simp only [uniformProb,shuffleB2_mean,Finset.sum_boole]


theorem shuffleB2_markov {A : Type*} [Fintype A] (E : A → Prop) (X : A → ℝ)
    (hX : ∀ a, 0 ≤ X a) (c : ℝ) (hc : 0 < c) (hE : ∀ a, E a → c ≤ X a) :
    uniformProb E ≤ shuffleB2_mean X/c := by
  rw [le_div_iff₀ hc,shuffleB2_prob_mean,mul_comm _ c,← shuffleB2_mean_mul]
  apply shuffleB2_mean_mono
  intro a
  by_cases ha : E a
  · simpa only [if_pos ha,mul_one] using hE a ha
  · simpa only [if_neg ha,mul_zero] using hX a

theorem shuffleB2_iid_second {A : Type*} [Fintype A] [Nonempty A]
    (E : A → Prop) (K : ℕ) (hK : 0 < K) :
    shuffleB2_mean (fun x : Fin K → A =>
      ((∑ i, if E (x i) then (1 : ℝ) else 0)/(K : ℝ)-uniformProb E)^2) ≤
        uniformProb E/K := by
  classical
  let B : A → ℝ := fun a => if E a then 1 else 0
  let p := uniformProb E
  have hp : shuffleB2_mean B = p := (shuffleB2_prob_mean E).symm
  have hc : shuffleB2_mean (fun a => B a-p) = 0 := by
    rw [shuffleB2_mean_sub,shuffleB2_mean_const,hp,sub_self]
  have hdiag : shuffleB2_mean (fun a => (B a-p)^2) ≤ p := by
    have he : (fun a => (B a-p)^2) = (fun a => B a-2*p*B a+p^2) := by
      funext a
      have hb : B a^2 = B a := by dsimp [B]; split_ifs <;> norm_num
      nlinarith
    rw [he,shuffleB2_mean_add,shuffleB2_mean_sub,shuffleB2_mean_mul,
      shuffleB2_mean_const,hp]
    nlinarith [sq_nonneg p]
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have he (x : Fin K → A) :
      ((∑ i, B (x i))/(K : ℝ)-p)^2 =
        ((∑ i : Fin K, ∑ j : Fin K, (B (x i)-p)*(B (x j)-p)))*(K : ℝ)⁻¹^2 := by
    rw [← Finset.sum_mul_sum]
    have hs : (∑ i : Fin K, (B (x i)-p)) = (∑ i, B (x i))-K*p := by
      simp [Finset.sum_sub_distrib]
    rw [hs]
    field_simp <;> ring
  change shuffleB2_mean (fun x : Fin K → A => ((∑ i, B (x i))/(K : ℝ)-p)^2) ≤ p/K
  simp_rw [he]
  have hm : shuffleB2_mean (fun x : Fin K → A =>
      ∑ i : Fin K, ∑ j : Fin K, (B (x i)-p)*(B (x j)-p)) ≤ K*p := by
    rw [shuffleB2_mean_sum]
    calc
      _ ≤ ∑ i : Fin K, p := by
        apply Finset.sum_le_sum
        intro i hi
        rw [shuffleB2_mean_sum]
        calc
          _ = shuffleB2_mean (fun a => (B a-p)^2) := by
            rw [Finset.sum_eq_single i]
            · simpa only [pow_two] using shuffleB2_mean_proj i (fun a => (B a-p)*(B a-p))
            · intro j hj hji
              rw [shuffleB2_mean_two i j hji (fun a => B a-p) (fun a => B a-p),hc,mul_zero]
            · simp
          _ ≤ p := hdiag
      _ = _ := by simp
  calc
    _ = shuffleB2_mean (fun x : Fin K → A =>
        ∑ i : Fin K, ∑ j : Fin K, (B (x i)-p)*(B (x j)-p)) * (K : ℝ)⁻¹^2 := by
      unfold shuffleB2_mean
      rw [← Finset.sum_mul]
      ring
    _ ≤ (K*p)*(K : ℝ)⁻¹^2 := mul_le_mul_of_nonneg_right hm (sq_nonneg _)
    _ = p/K := by field_simp <;> ring

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.FinitePopulationMoments

theorem shuffleB2_complete_mean {n m : ℕ} (hm : m ≤ Fintype.card (Fin n))
    (f : Assignment n m → ℝ) : (completeRandomization m hm).E f = shuffleB2_mean f := by
  change (∑ s, (1/(Fintype.card (Assignment n m) : ℝ))*f s) = _
  rw [← Finset.mul_sum]
  dsimp [shuffleB2_mean]
  ring

theorem shuffleB2_popVar_bound {n : ℕ} (hn : 2 ≤ n) (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) : popVar f ≤ (n : ℝ)/(4*(n-1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (0 : ℝ) < n-1 := by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let u := popMean f
  have hsum : (∑ i, f i) = n*u := by
    dsimp [u,popMean]
    simp only [Fintype.card_fin]
    field_simp
  have hsquare : (∑ i, f i^2) ≤ ∑ i, f i := by
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [(hf i).1,(hf i).2]
  have he : (∑ i, (f i-u)^2) = (∑ i, f i^2)-2*u*(∑ i,f i)+n*u^2 := by
    calc
      _ = ∑ i, (f i^2-2*u*f i+u^2) := by apply Finset.sum_congr rfl; intro i hi; ring
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
        ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hb : (∑ i, (f i-u)^2) ≤ n/4 := by
    rw [hsum] at hsquare he
    have hh := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (u-1/2))
    nlinarith
  change (∑ i, (f i-u)^2)/((Fintype.card (Fin n) : ℝ)-1) ≤ _
  rw [Fintype.card_fin]
  calc
    _ ≤ ((n : ℝ)/4)/(n-1) := div_le_div_of_nonneg_right hb hn1.le
    _ = _ := by field_simp <;> ring

theorem shuffleB2_sample_identity {n m : ℕ} (w : PotentialTable n) (hm : 0 < m)
    (hn : n = 2*m) (s : Assignment n m) :
    tableEstimator w s.val-tableTau w =
      sampleMean m (fun i => bit (w i).1+bit (w i).2) s-
        popMean (fun i => bit (w i).1+bit (w i).2) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by rw [hn]; positivity
  have hnR : (n : ℝ) = 2*m := by exact_mod_cast hn
  rw [corrected_signed_sum w s.val m hm hn s.property]
  unfold tableTau sampleMean popMean
  simp only [Fintype.card_fin]
  have he : (∑ i, if i ∈ s.val then bit (w i).1 else -bit (w i).2) =
      (∑ i, if i ∈ s.val then bit (w i).1+bit (w i).2 else 0)-∑ i,bit (w i).2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  field_simp
  rw [hnR]
  ring

theorem shuffleB2_table_second {n m : ℕ} (w : PotentialTable n) (hm : 0 < m)
    (hn : n = 2*m) (hf : ∀ i, bit (w i).1+bit (w i).2 ≤ 1) :
    shuffleB2_mean (fun s : Assignment n m => (tableEstimator w s.val-tableTau w)^2) ≤
      1/(4*((n : ℝ)-1)) := by
  have hmn : m ≤ Fintype.card (Fin n) := by simp; omega
  have hn2 : 2 ≤ Fintype.card (Fin n) := by simp; omega
  have hnR : (n : ℝ) = 2*m := by exact_mod_cast hn
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by rw [hn]; positivity
  let f : Fin n → ℝ := fun i => bit (w i).1+bit (w i).2
  have hf0 (i) : 0 ≤ f i := by dsimp [f,bit]; positivity
  have hv := Var_sampleMean m hmn hm hn2 f
  rw [FiniteDesign.Var,E_sampleMean m hmn hm f,shuffleB2_complete_mean] at hv
  have he : shuffleB2_mean (fun s : Assignment n m => (tableEstimator w s.val-tableTau w)^2) =
      shuffleB2_mean (fun s : Assignment n m => (sampleMean m f s-popMean f)^2) := by
    apply shuffleB2_mean_congr
    intro s
    rw [shuffleB2_sample_identity w hm hn s]
  rw [he,hv,Fintype.card_fin]
  have hb := shuffleB2_popVar_bound (by simpa using hn2) f (fun i => ⟨hf0 i,hf i⟩)
  have hcoef : 1/(m : ℝ)-1/(n : ℝ) = 1/(n : ℝ) := by
    field_simp
    linarith
  rw [hcoef]
  calc
    _ ≤ (1/(n : ℝ))*((n : ℝ)/(4*(n-1))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp <;> ring

theorem shuffleB2_canonical_estimator {n : ℕ} (v : Counts) (s : Finset (Fin n)) :
    tableEstimator (fun i => canonicalPair v i.val) s = estimate (canonicalObserved v s) := by
  rw [shuffleB2_canonical_observed,← couplingB2_outcome_estimate]
  exact couplingB2_compatible_estimator _ _ _ rfl

theorem shuffleB2_candidate_tail (x t : ℕ) (hx : 16 ≤ x) (ht : t ≤ x) :
    uniformProb (fun s : Assignment (4*x) (4*x/2) =>
      (deviationNumerator ⟨0,x+t,t,3*x-2*t⟩
        (canonicalObserved ⟨0,x+t,t,3*x-2*t⟩ s.val) (2*x)).natAbs ≥
          (deviationNumerator ⟨0,x+t,t,3*x-2*t⟩ ⟨0,2*x,0,2*x⟩ (2*x)).natAbs) ≤
            4/(((4*x : ℕ) : ℝ)-1) := by
  classical
  let v : Counts := ⟨0,x+t,t,3*x-2*t⟩
  let o : Counts := ⟨0,2*x,0,2*x⟩
  let w : PotentialTable (4*x) := fun i => canonicalPair v i.val
  have hv : v.total = 4*x := by dsimp [v,Counts.total]; omega
  have hm : 0 < 2*x := by omega
  have hhalf : 4*x/2 = 2*x := by omega
  have hn : 4*x = 2*(2*x) := by omega
  have htauV : tau v = (1/4 : ℝ) := by
    simp only [tau,tauQ,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast,hv]
    dsimp [Counts.effect,v]
    push_cast
    field_simp
    ring
  have hcounts : tableCounts w = v := by
    dsimp only [w]
    rw [← hv]
    exact shuffleB2_canonical_counts v
  have htau : tableTau w = (1/4 : ℝ) := by
    rw [(corrected_sate w (by omega)).2.2.2,hcounts,htauV]
  have hobs : estimate o = 0 := by simp [o,estimate,estimateQ]
  have hf (i : Fin (4*x)) : bit (w i).1+bit (w i).2 ≤ 1 := by
    dsimp [w,v,canonicalPair]
    split_ifs <;> norm_num [bit]
  have hsecond := shuffleB2_table_second w (m := 4*x/2) (by omega) (by omega) hf
  have he (s : Assignment (4*x) (4*x/2)) :
      (deviationNumerator v (canonicalObserved v s.val) (2*x)).natAbs ≥
        (deviationNumerator v o (2*x)).natAbs ↔
          (1/4 : ℝ) ≤ |tableEstimator w s.val-tableTau w| := by
    have hs : s.val.card = 2*x := s.property.trans hhalf
    have hO := couplingB2_observed_arms (unitOutcomes w s.val) s.val
    have hOeq : unitObserved (unitOutcomes w s.val) s.val = canonicalObserved v s.val :=
      (shuffleB2_canonical_observed v s.val).symm
    rw [hOeq] at hO
    have hT' := hO.1.trans hs
    have hC' : (canonicalObserved v s.val).c+(canonicalObserved v s.val).d = 2*x := by omega
    rw [couplingB2_tail_compare v o _ hm hn hv (by simp [o]) (by simp [o]) hT' hC',
      ← shuffleB2_canonical_estimator,htauV,hobs,htau]
    norm_num [w]
  have hmark := shuffleB2_markov
    (fun s : Assignment (4*x) (4*x/2) =>
      (deviationNumerator v (canonicalObserved v s.val) (2*x)).natAbs ≥
        (deviationNumerator v o (2*x)).natAbs)
    (fun s => (tableEstimator w s.val-tableTau w)^2) (fun s => sq_nonneg _) (1/16)
    (by norm_num) (by
      intro s hs
      have hh := (he s).mp hs
      nlinarith [sq_abs (tableEstimator w s.val-tableTau w)])
  change uniformProb _ ≤ _ at hmark
  calc
    _ ≤ _ := hmark
    _ ≤ (1/(4*((4*x : ℕ) : ℝ)-4))/(1/16) := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      convert hsecond using 1 <;> ring
    _ = _ := by
      push_cast
      field_simp
      ring

theorem shuffleB2_batch_accept {A : Type*} [Fintype A] [Nonempty A]
    (E : A → Prop) (hp : uniformProb E ≤ 1/8) (K : ℕ) (hK : 0 < K) :
    uniformProb (fun x : Fin K → A =>
      (3/8 : ℝ) ≤ (∑ i, if E (x i) then (1 : ℝ) else 0)/(K : ℝ)) ≤
        16*uniformProb E/K := by
  have h := shuffleB2_markov
    (fun x : Fin K → A => (3/8 : ℝ) ≤ (∑ i, if E (x i) then (1 : ℝ) else 0)/(K : ℝ))
    (fun x => ((∑ i, if E (x i) then (1 : ℝ) else 0)/(K : ℝ)-uniformProb E)^2)
    (fun x => sq_nonneg _) (1/16) (by norm_num) (by
      intro x hx
      nlinarith)
  calc
    _ ≤ _ := h
    _ ≤ (uniformProb E/K)/(1/16) :=
      div_le_div_of_nonneg_right (shuffleB2_iid_second E K hK) (by norm_num)
    _ = _ := by ring

theorem shuffleB2_prob_proj {A I : Type*} [Fintype A] [Fintype I] [Nonempty A]
    [DecidableEq I] (i : I) (E : A → Prop) :
    uniformProb (fun x : I → A => E (x i)) = uniformProb E := by
  rw [shuffleB2_prob_mean,shuffleB2_prob_mean]
  exact shuffleB2_mean_proj i (fun a => if E a then 1 else 0)

theorem shuffleB2_prob_union {A I : Type*} [Fintype A] [Fintype I]
    (E : I → A → Prop) : uniformProb (fun a => ∃ i, E i a) ≤ ∑ i, uniformProb (E i) := by
  classical
  simp_rw [shuffleB2_prob_mean]
  rw [← shuffleB2_mean_sum]
  apply shuffleB2_mean_mono
  intro a
  by_cases h : ∃ i, E i a
  · obtain ⟨i,hi⟩ := h
    rw [if_pos ⟨i,hi⟩]
    calc
      (1 : ℝ) = if E i a then 1 else 0 := by rw [if_pos hi]
      _ ≤ ∑ j, if E j a then 1 else 0 := Finset.single_le_sum
        (f := fun j => if E j a then (1 : ℝ) else 0)
        (fun j hj => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun i hi => by split_ifs <;> norm_num)

theorem shuffleB2_prob_compl {A : Type*} [Fintype A] [Nonempty A] (E : A → Prop) :
    uniformProb (fun a => ¬E a) = 1-uniformProb E := by
  rw [shuffleB2_prob_mean,shuffleB2_prob_mean]
  calc
    _ = shuffleB2_mean (fun a => 1-(if E a then 1 else 0)) := by
      apply shuffleB2_mean_congr
      intro a
      by_cases h : E a <;> simp only [h,not_true_eq_false,not_false_eq_true,
        if_true,if_false,sub_self,sub_zero]
    _ = _ := by rw [shuffleB2_mean_sub,shuffleB2_mean_const]

theorem shuffleB2_assignment_nonempty (n m : ℕ) (hm : m ≤ n) : Nonempty (Assignment n m) := by
  apply Fintype.card_pos_iff.mp
  rw [Fintype.card_finset_len,Fintype.card_fin]
  exact Nat.choose_pos hm

theorem shuffleB2_monte_cast {n K m : ℕ} (v o : Counts) (hT : o.a+o.b = m)
    (draws : Fin K → Assignment n (n/2)) :
    (monteMean v o (fun i => (draws i).val) : ℝ) =
      (∑ i, if (deviationNumerator v (canonicalObserved v (draws i).val) m).natAbs ≥
        (deviationNumerator v o m).natAbs then (1 : ℝ) else 0)/(K : ℝ) := by
  unfold monteMean
  rw [hT]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> norm_cast

theorem shuffleB2_expected_of_good {A : Type*} [Fintype A] (C : A → ℝ) (G : A → Prop)
    (B : ℝ) (hB : 0 ≤ B) (hC : ∀ a, 0 ≤ C a) (hG : ∀ a, G a → B ≤ C a)
    (hP : 1/2 ≤ uniformProb G) : B/2 ≤ shuffleB2_mean C := by
  have hh : B*uniformProb G ≤ shuffleB2_mean C := by
    rw [shuffleB2_prob_mean,← shuffleB2_mean_mul]
    apply shuffleB2_mean_mono
    intro a
    by_cases ha : G a
    · simpa only [if_pos ha,mul_one] using hG a ha
    · simpa only [if_neg ha,mul_zero] using hC a
  have hp := mul_le_mul_of_nonneg_left hP hB
  linarith

theorem shuffleB2_expected (x K : ℕ) (hx : 16 ≤ x) (hK : 64 ≤ K) :
    ((x+1 : ℕ) : ℝ)*K*((4*x-1 : ℕ) : ℝ)/2 ≤
      expectedUpperShuffleCost (1/2) (1/8) (4*x) K ⟨0,2*x,0,2*x⟩ := by
  classical
  let A := Assignment (4*x) (4*x/2)
  letI instNonemptyShuffleB2 : Nonempty A := shuffleB2_assignment_nonempty _ _ (by omega)
  let Pool := Fin (2*testBudget (4*x)+1) → Fin K → A
  let v : Fin (x+1) → Counts := fun t => ⟨0,x+t.val,t.val,3*x-2*t.val⟩
  let o : Counts := ⟨0,2*x,0,2*x⟩
  have hbudget : 4*x+1 ≤ testBudget (4*x) := by
    unfold testBudget
    simpa using Nat.mul_le_mul_left (4*x+1) (show 1 ≤ Nat.log2 (4*x+1)+3 by omega)
  let index (t : Fin (x+1)) : Fin (2*testBudget (4*x)+1) := ⟨t.val,by omega⟩
  let Tail (t : Fin (x+1)) (s : A) : Prop :=
    (deviationNumerator (v t) (canonicalObserved (v t) s.val) (2*x)).natAbs ≥
      (deviationNumerator (v t) o (2*x)).natAbs
  let Accept (t : Fin (x+1)) (pool : Pool) : Prop :=
    (3/8 : ℝ) ≤ (∑ i, @ite ℝ (Tail t (pool (index t) i))
      (Classical.propDecidable _) 1 0)/(K : ℝ)
  let G (pool : Pool) : Prop := ¬∃ t, Accept t pool
  have hden : (0 : ℝ) < ((4*x : ℕ) : ℝ)-1 := by
    have hh : (16 : ℝ) ≤ x := by exact_mod_cast hx
    push_cast
    linarith
  have htail (t : Fin (x+1)) : uniformProb (Tail t) ≤ 4/(((4*x : ℕ) : ℝ)-1) :=
    shuffleB2_candidate_tail x t.val hx (by omega)
  have htail' (t : Fin (x+1)) : uniformProb (Tail t) ≤ 1/8 := by
    apply (htail t).trans
    rw [div_le_iff₀ hden]
    have hh : (16 : ℝ) ≤ x := by exact_mod_cast hx
    push_cast
    linarith
  have hacc (t : Fin (x+1)) : uniformProb (Accept t) ≤
      64/((((4*x : ℕ) : ℝ)-1)*K) := by
    have hh := shuffleB2_batch_accept (Tail t) (htail' t) K (by omega)
    have hproj := shuffleB2_prob_proj (index t)
      (fun draws : Fin K → A => (3/8 : ℝ) ≤
        (∑ i, @ite ℝ (Tail t (draws i)) (Classical.propDecidable _) 1 0)/(K : ℝ))
    change uniformProb (Accept t) = _ at hproj
    rw [hproj]
    calc
      _ ≤ 16*uniformProb (Tail t)/K := hh
      _ ≤ 16*(4/(((4*x : ℕ) : ℝ)-1))/K := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_left (htail t) (by norm_num)
      _ = _ := by field_simp <;> ring
  have hP : 1/2 ≤ uniformProb G := by
    rw [shuffleB2_prob_compl]
    have hU := (shuffleB2_prob_union Accept).trans
      (Finset.sum_le_sum (fun t ht => hacc t))
    have hsum : (∑ t : Fin (x+1), 64/((((4*x : ℕ) : ℝ)-1)*K)) ≤ 1/2 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hKR : (64 : ℝ) ≤ K := by exact_mod_cast hK
      have hxR : (16 : ℝ) ≤ x := by exact_mod_cast hx
      rw [← mul_div_assoc,div_le_iff₀ (mul_pos hden (by linarith))]
      push_cast
      nlinarith
    linarith
  have htrace (pool : Pool) (hg : G pool) :
      x+1 ≤ (upperRun true o (approximateReject (1/2) (1/8) o pool)).trace.length := by
    apply shuffleB2_first_trace x (by omega)
    have hr : (runTests (approximateReject (1/2) (1/8) o pool) 0
        (candidates o (x : ℤ))).trace.length = x+1 := by
      rw [shuffleB2_runTests_indexed]
      · rw [shuffleB2_candidate_list x (by omega),List.length_map,List.length_range]
      · rw [shuffleB2_candidate_list x (by omega)]
        intro t ht
        simp only [List.length_map,List.length_range] at ht
        simp only [List.getElem_map,List.getElem_range,Nat.zero_add]
        have hg' : ¬Accept ⟨t,ht⟩ pool := by intro ha; exact hg ⟨⟨t,ht⟩,ha⟩
        have hb : t < 2*testBudget (4*x)+1 := by omega
        have hdraw : batch pool t = fun i => (pool (index ⟨t,ht⟩) i).val := by
          funext i
          simp only [batch,Nat.mod_eq_of_lt hb,index]
        have hm := shuffleB2_monte_cast (m := 2*x) (v ⟨t,ht⟩) o (by simp [o])
          (pool (index ⟨t,ht⟩))
        have hm' : (monteMean (v ⟨t,ht⟩) o
            (fun i => (pool (index ⟨t,ht⟩) i).val) : ℝ) =
            (∑ i, @ite ℝ (Tail ⟨t,ht⟩ (pool (index ⟨t,ht⟩) i))
              (Classical.propDecidable _) 1 0)/(K : ℝ) := by
          rw [hm]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          dsimp only [Tail]
          split_ifs <;> rfl
        unfold approximateReject
        apply decide_eq_true
        rw [hdraw]
        change (monteMean (v ⟨t,ht⟩) o (fun i => (pool (index ⟨t,ht⟩) i).val) : ℝ)+1/8 < 1/2
        rw [hm']
        change ¬ ((3/8 : ℝ) ≤ _) at hg'
        linarith
    exact hr.ge
  have hcost (pool : Pool) (hg : G pool) :
      ((x+1 : ℕ) : ℝ)*K*((4*x-1 : ℕ) : ℝ) ≤
        (upperShuffleCost (1/2) (1/8) o pool : ℝ) := by
    have hh := Nat.mul_le_mul_right (4*x-1) (Nat.mul_le_mul_right K (htrace pool hg))
    exact_mod_cast hh
  exact shuffleB2_expected_of_good (fun pool : Pool => (upperShuffleCost (1/2) (1/8) o pool : ℝ))
    G _ (by positivity) (fun pool => Nat.cast_nonneg _) hcost hP

theorem balanced_shuffle_lower_bounds_proof (r K : ℕ) (hr : 4 ≤ r) (hK : 0 < K) :
    let n : ℕ := 2^r
    let o : Counts := ⟨0,n/2,0,n/2⟩
    0 < uniformProb (fun pool : Fin (2*testBudget n+1) → Fin K → Assignment n (n/2) =>
      (n/4+1)*K*(n-1) ≤ upperShuffleCost (1/2) (1/8) o pool) ∧
    (6 ≤ r → (K : ℝ) ≥ 32*Real.log (32*(n : ℝ)*logTwo n) →
      ((n/4+1 : ℕ) : ℝ)*K*((n-1 : ℕ) : ℝ)/2 ≤
        expectedUpperShuffleCost (1/2) (1/8) n K o) := by
  dsimp
  let x : ℕ := 4*2^(r-4)
  have hx : 0 < x := by dsimp [x]; positivity
  have heven : 2 ∣ x := ⟨2*2^(r-4),by dsimp [x]; ring⟩
  have hn : 2^r = 4*x := by
    conv_lhs => rw [show r = (r-4)+4 by omega,pow_add]
    dsimp [x]
    norm_num
    ring
  have hO : (⟨0,4*x/2,0,4*x/2⟩ : Counts) = ⟨0,2*x,0,2*x⟩ := by
    ext <;> dsimp <;> omega
  rw [hn,hO,show 4*x/4 = x by omega]
  constructor
  · exact shuffleB2_positive_pool x K hx heven
  · intro hr6 hlarge
    have hn64 : 64 ≤ 2^r := by
      have hp : 0 < (2 : ℕ)^(r-6) := by positivity
      have hp' : 2^r = 2^(r-6)*64 := by
        conv_lhs => rw [show r = (r-6)+6 by omega,pow_add]
        norm_num
      omega
    have hx16 : 16 ≤ x := by omega
    have hlog : logTwo ((4*x : ℕ) : ℝ) = r := by
      rw [← hn]
      unfold logTwo
      rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
      have h2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      field_simp
    rw [hlog] at hlarge
    have hnR : (64 : ℝ) ≤ ((4*x : ℕ) : ℝ) := by exact_mod_cast (show 64 ≤ 4*x by omega)
    have hrR : (6 : ℝ) ≤ r := by exact_mod_cast hr6
    have harg : (9 : ℝ) ≤ 32*((4*x : ℕ) : ℝ)*(r : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (sub_nonneg.mpr hrR)]
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 9) harg
    have h9 : Real.log (9 : ℝ) = 2*Real.log 3 := by
      rw [show (9 : ℝ) = 3^2 by norm_num,Real.log_pow]
      norm_num
    rw [h9] at hmono
    have hk64 : 64 ≤ K := by
      have hh : (64 : ℝ) ≤ K := by nlinarith [Real.log_three_gt_d9]
      exact_mod_cast hh
    exact shuffleB2_expected x K hx16 hk64

theorem balanced_plus_coupling_proof {n : ℕ} (m : ℕ) (hm : 0 < m) (hn : n = 2*m)
    (y y' : Fin n → Bool) (z r : Finset (Fin n)) (hz : z.card = m)
    (hy' : ∀ i, i ∉ r → y' i = y i) (w : PotentialTable n)
    (hw : PossibleTable y' z w) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (hp : α ≤ unitPValue w y' z)
    (ht : outcomeEstimator (unitPlus y z r) z < tableTau w) :
    let yPlus := unitPlus y z r
    let D := Finset.univ.filter (fun i => y' i ≠ yPlus i)
    let d := D.card
    let wPlus := coupledPlus w yPlus z
    PossibleTable yPlus z wPlus ∧
    tableTau wPlus = tableTau w + (d : ℝ)/n ∧
    outcomeEstimator yPlus z = outcomeEstimator y' z + 2*(d : ℝ)/n ∧
    (∀ q : Assignment n m,
      let N := (D.filter fun i => (i ∈ q.val ↔ i ∈ z)).card
      N ≤ d ∧ tableEstimator wPlus q.val = tableEstimator w q.val + 2*(N : ℝ)/n ∧
      |(tableEstimator wPlus q.val-tableTau wPlus)-
        (tableEstimator w q.val-tableTau w)| ≤ (d : ℝ)/n) ∧
    |outcomeEstimator yPlus z-tableTau wPlus| =
      |outcomeEstimator y' z-tableTau w|-(d : ℝ)/n ∧
    unitPValue w y' z ≤ unitPValue wPlus yPlus z ∧ α ≤ unitPValue wPlus yPlus z ∧
    upper α (unitObserved yPlus z) ≥ tableTau wPlus ∧ tableTau wPlus ≥ tableTau w := by
  dsimp
  let yp := unitPlus y z r
  let D := Finset.univ.filter (fun i => y' i ≠ yp i)
  let wp := coupledPlus w yp z
  let h : ℝ := (D.card : ℝ)/n
  have hh : 0 ≤ h := by positivity
  have hcomp := couplingB2_compatible w yp z
  obtain ⟨htau,hobs,hrand⟩ := couplingB2_sum_changes m hm hn y y' z r hz hy' w hw
  change tableTau wp = tableTau w+h at htau
  change outcomeEstimator yp z = outcomeEstimator y' z+2*(D.card : ℝ)/n at hobs
  have hbound (q : Assignment n m) :
      |(tableEstimator wp q.val-tableTau wp)-(tableEstimator w q.val-tableTau w)| ≤ h := by
    obtain ⟨hle,he⟩ := hrand q
    change tableEstimator wp q.val = tableEstimator w q.val+
      2*((D.filter fun i => (i ∈ q.val ↔ i ∈ z)).card : ℝ)/n at he
    rw [he,htau]
    apply abs_le.mpr
    have hNN : (0 : ℝ) ≤ ((D.filter fun i => (i ∈ q.val ↔ i ∈ z)).card : ℝ)/n :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hNd : (((D.filter fun i => (i ∈ q.val ↔ i ∈ z)).card : ℝ)/n) ≤ h := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hle
    change -(h) ≤ _ ∧ _ ≤ h
    simp only [mul_div_assoc]
    constructor <;> linarith
  have hdev : |outcomeEstimator yp z-tableTau wp| =
      |outcomeEstimator y' z-tableTau w|-h := by
    have hobs' : outcomeEstimator yp z = outcomeEstimator y' z+2*h := by
      rw [hobs]
      dsimp [h]
      ring
    have htau' : tableTau wp = tableTau w+h := htau
    have hlt : outcomeEstimator y' z < tableTau w := by change _ < _ at ht; linarith
    have hlt' : outcomeEstimator yp z < tableTau wp := by change _ < _ at ht; linarith
    rw [abs_of_neg (sub_neg.mpr hlt'), abs_of_neg (sub_neg.mpr hlt), hobs', htau']
    ring
  have hpmono : unitPValue w y' z ≤ unitPValue wp yp z := by
    unfold unitPValue uniformProb
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro q hq
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hq ⊢
    have hq' : q.val.card = m := q.property.trans hz
    have hb := hbound ⟨q.val,hq'⟩
    rw [hdev]
    have ht := abs_sub_abs_le_abs_sub (tableEstimator w q.val-tableTau w)
      (tableEstimator wp q.val-tableTau wp)
    rw [abs_sub_comm (tableEstimator w q.val-tableTau w)
      (tableEstimator wp q.val-tableTau wp)] at ht
    linarith
  have hpnew := hp.trans hpmono
  refine ⟨hcomp,htau,hobs,?_,hdev,hpmono,hpnew,
    couplingB2_endpoint hm hn yp z hz wp hcomp α hpnew,?_⟩
  · intro q
    exact ⟨(hrand q).1,(hrand q).2,hbound q⟩
  · rw [htau]
    exact le_add_of_nonneg_right hh

end AronowAudit.P003.Wave1
