import AronowAudit.P009.P009_CompleteConditional
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Fintype.Powerset

/-!
P009-T18: exact complete-randomization count laws and likelihood ratios.
The finite counting bridge below counts actual Boolean assignments.
-/

namespace AronowAudit.P009.Wave1

open scoped BigOperators
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000

def t18_count {α : Type*} [Fintype α] (z : α → Bool) : ℕ :=
  ∑ j, if z j then 1 else 0

def t18_countOn {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (z : α → Bool) : ℕ :=
  ∑ j : {j // p j}, if z j then 1 else 0

def t18_boolFinset (α : Type*) [Fintype α] : (α → Bool) ≃ Finset α where
  toFun z := Finset.univ.filter (fun j => z j = true)
  invFun s := fun j => decide (j ∈ s)
  left_inv z := by funext j; cases h : z j <;> simp [h]
  right_inv s := by ext j; simp

lemma t18_count_card {α : Type*} [Fintype α] (z : α → Bool) :
    t18_count z = (t18_boolFinset α z).card := by
  change (∑ j, if z j then (1:ℕ) else 0) =
    (Finset.univ.filter (fun j => z j = true)).card
  rw [Finset.card_filter]

lemma t18_cube_count {α : Type*} [Fintype α] [DecidableEq α] (t : ℕ) :
    (∑ z : α → Bool, if t18_count z = t then (1 : ℝ) else 0) =
      ((Fintype.card α).choose t : ℝ) := by
  calc
    _ = ∑ s : Finset α, if s.card = t then (1 : ℝ) else 0 := by
      apply Fintype.sum_equiv (t18_boolFinset α)
      intro z
      rw [t18_count_card]
    _ = _ := by simp [Finset.sum_boole]

lemma t18_count_split {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (z : α → Bool) :
    t18_count z = t18_countOn p z + t18_countOn (fun j => ¬p j) z := by
  simpa [t18_count, t18_countOn] using
    (Fintype.sum_subtype_add_sum_subtype p (fun j => if z j then (1:ℕ) else 0)).symm

/-- Split a Boolean assignment into the mask and its complement, and count each part. -/
lemma t18_cube_mask_count {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (m t : ℕ)
    (ht : t ≤ m) :
    (∑ z : α → Bool, if t18_count z = m ∧ t18_countOn p z = t then (1 : ℝ) else 0) =
      ((Fintype.card {j // p j}).choose t : ℝ) *
        (((Fintype.card α - Fintype.card {j // p j})).choose (m-t) : ℝ) := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Bool)
  calc
    _ = ∑ w : ({j // p j} → Bool) × ({j // ¬p j} → Bool),
        (if t18_count w.1 = t then (1 : ℝ) else 0) *
        (if t18_count w.2 = m-t then 1 else 0) := by
      apply Fintype.sum_equiv e
      intro z
      have hs := t18_count_split p z
      change (if t18_count z = m ∧ t18_countOn p z = t then (1:ℝ) else 0) =
        (if t18_countOn p z = t then 1 else 0) *
        (if t18_countOn (fun j => ¬p j) z = m-t then 1 else 0)
      have he : (t18_count z = m ∧ t18_countOn p z = t) ↔
          (t18_countOn p z = t ∧ t18_countOn (fun j => ¬p j) z = m-t) := by omega
      simp only [he]
      split_ifs <;> simp_all
    _ = _ := by
      rw [Fintype.sum_prod_type]
      dsimp only
      calc
        _ = (∑ x : {j // p j} → Bool, if t18_count x = t then (1:ℝ) else 0) *
            (∑ y : {j // ¬p j} → Bool, if t18_count y = m-t then (1:ℝ) else 0) := by
          rw [Finset.sum_mul_sum]
        _ = _ := by
          have hh := congrArg₂ (fun x y : ℝ => x*y)
            (t18_cube_count (α := {j // p j}) t)
            (t18_cube_count (α := {j // ¬p j}) (m-t))
          simp only [Fintype.card_subtype_compl] at hh
          convert hh using 1 <;> congr!

/-- Exchange the roles of the fixed mask and the sampled treated subset. -/
lemma t18_choose_exchange (n m r t : ℕ) (hm : m ≤ n) (hrm : r ≤ m)
    (hrc : r ≤ n-m) (ht : t ≤ r) :
    (r.choose t : ℝ) * ((n-r).choose (m-t) : ℝ) / (n.choose m : ℝ) =
      hypergeomMass n m r t := by
  have hmr : m-t ≤ n-r := by omega
  have hrt : r-t ≤ n-m := by omega
  have hr : r ≤ n := by omega
  have htm : t ≤ m := by omega
  have he : n-r-(m-t) = n-m-(r-t) := by omega
  unfold hypergeomMass
  rw [Nat.cast_choose ℝ ht, Nat.cast_choose ℝ hmr, Nat.cast_choose ℝ hm,
    Nat.cast_choose ℝ htm, Nat.cast_choose ℝ hrt, Nat.cast_choose ℝ hr, he]
  have hf (k : ℕ) : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp
  <;> ring

/-- The complete-design count formula on an arbitrary mask of coordinates. -/
lemma t18_complete_count {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (p : Fin n → Prop) [DecidablePred p] (t : ℕ) (ht : t ≤ Fintype.card {j // p j})
    (hrm : Fintype.card {j // p j} ≤ m)
    (hrc : Fintype.card {j // p j} ≤ n-m) :
    prob E.design (fun z => t18_countOn p z = t) =
      hypergeomMass n m (Fintype.card {j // p j}) t := by
  have htm : t ≤ m := ht.trans hrm
  calc
    _ = (∑ z : Assignment n,
        if t18_count z = m ∧ t18_countOn p z = t then (1:ℝ) else 0) /
        (n.choose m : ℝ) := by
      unfold prob mean
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      rw [hCR.2.2]
      change (if t18_count z = m then _ else _) * _ = _
      split_ifs <;> simp_all
    _ = _ := by
      have hs := t18_cube_mask_count p m t htm
      simp only [Fintype.card_fin] at hs
      rw [hs]
      exact t18_choose_exchange n m _ t hCR.2.1.le hrm hrc ht

def t18_others {n : ℕ} (E : Experiment n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ i ∧ Interferes E j i)

lemma t18_others_card {n : ℕ} (E : Experiment n) (i : Fin n) :
    (t18_others E i).card = incoming E i - 1 := by
  have he : t18_others E i = (Finset.univ.filter (fun j => Interferes E j i)).erase i := by
    ext j
    simp [t18_others, and_comm]
  rw [he, Finset.card_erase_of_mem
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl rfl⟩)]
  rfl

lemma t18_own_not_mem {n : ℕ} (E : Experiment n) (i : Fin n) : i ∉ t18_others E i := by
  simp [t18_others]

lemma t18_countOn_finset {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset α) (z : α → Bool) :
    t18_countOn (fun j => j ∈ H) z = ∑ j ∈ H, if z j then (1:ℕ) else 0 := by
  unfold t18_countOn
  convert (Finset.sum_coe_sort H (fun j => if z j then (1:ℕ) else 0)) using 1 <;> congr!

lemma t18_countIncoming {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) :
    treatedIncoming E i z = t18_countOn (fun j => j ∈ t18_others E i) z := by
  rw [t18_countOn_finset]
  unfold treatedIncoming t18_others
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i <;> by_cases hI : Interferes E j i <;>
    cases hz : z j <;> simp [hji, hI, hz]

lemma t18_real_countOn {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset α) (z : α → Bool) :
    (t18_countOn (fun j => j ∈ H) z : ℝ) = ∑ j ∈ H, bit (z j) := by
  rw [t18_countOn_finset, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases z j <;> norm_num [bit]

lemma t18_countOn_congr {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset α) (z z' : α → Bool)
    (hz : ∀ j ∈ H, z j = z' j) :
    t18_countOn (fun j => j ∈ H) z = t18_countOn (fun j => j ∈ H) z' := by
  simp only [t18_countOn_finset]
  exact Finset.sum_congr rfl (fun j hj => by rw [hz j hj])

lemma t18_marginal_bounds {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (i : Fin n) (b : Bool) : 0 < marginal E i b ∧ marginal E i b < 1 := by
  have hn : (0:ℝ) < n := by exact_mod_cast lt_trans hCR.1 hCR.2.1
  have hm : (0:ℝ) < m := by exact_mod_cast hCR.1
  have hmn : (m:ℝ) < n := by exact_mod_cast hCR.2.1
  cases b
  · rw [CompleteConditional.complete_marginal_false E m hCR i]
    constructor
    · have := (div_lt_one hn).mpr hmn
      linarith
    · have := div_pos hm hn
      linarith
  · rw [CompleteConditional.complete_marginal_true E m hCR i]
    exact ⟨div_pos hm hn, (div_lt_one hn).mpr hmn⟩

/-- Symmetry outside a mask identifies the joint probability of any mask event
whose treated count is fixed. This applies to a count event and to a vector atom. -/
lemma t18_event_joint {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H : Finset (Fin n)) (i : Fin n) (hi : i ∉ H)
    (A : Assignment n → Prop) (t : ℕ)
    (hA : DependsOn (fun z => if A z then (1:ℝ) else 0) (H : Set (Fin n)))
    (ht : ∀ z, A z → t18_countOn (fun j => j ∈ H) z = t) (b : Bool) :
    ((n:ℝ)-H.card) * (marginal E i b *
      cmean E.design (fun z => z i = b) (fun z => if A z then 1 else 0)) =
    ((n:ℝ)*marginal E i b - bit b*(t:ℝ) - (1-bit b)*((H.card:ℝ)-t)) *
      prob E.design A := by
  have hp := (t18_marginal_bounds E m hCR i b).1.ne'
  have hcancel : marginal E i b *
      cmean E.design (fun z => z i = b) (fun z => if A z then 1 else 0) =
      mean E.design (fun z => if z i = b then (if A z then 1 else 0) else 0) := by
    unfold cmean
    change prob E.design (fun z => z i = b) * (_ / prob E.design (fun z => z i = b)) = _
    have hp' : prob E.design (fun z => z i = b) ≠ 0 := hp
    field_simp [hp']
  rw [hcancel]
  have hw := CompleteConditional.conditional_weighted_count E m hCR H i hi
    (fun z => if A z then (1:ℝ) else 0) hA
  have hcount : mean E.design (fun z => (∑ j ∈ H, bit (z j)) *
      (if A z then (1:ℝ) else 0)) = (t:ℝ)*prob E.design A := by
    change _ = (t:ℝ) * mean E.design (fun z => if A z then 1 else 0)
    rw [← mean_const_mul]
    apply congrArg (mean E.design)
    funext z
    by_cases hz : A z
    · have hh := congrArg (fun k : ℕ => (k:ℝ)) (ht z hz)
      rw [t18_real_countOn] at hh
      simp [hz, hh]
    · simp [hz]
  rw [hcount] at hw
  change ((n:ℝ)-H.card)*mean E.design (fun z => bit (z i)*(if A z then 1 else 0)) =
    (m:ℝ)*prob E.design A-(t:ℝ)*prob E.design A at hw
  have htrue : mean E.design (fun z => if z i = true then (if A z then (1:ℝ) else 0) else 0) =
      mean E.design (fun z => bit (z i)*(if A z then 1 else 0)) := by
    congr 1
    funext z
    cases z i <;> simp [bit]
  have hfalse : mean E.design (fun z => if z i = false then (if A z then (1:ℝ) else 0) else 0) =
      prob E.design A - mean E.design (fun z => bit (z i)*(if A z then 1 else 0)) := by
    change _ = mean E.design (fun z => if A z then (1:ℝ) else 0) - _
    rw [← mean_sub]
    congr 1
    funext z
    cases z i <;> simp [bit]
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast (lt_trans hCR.1 hCR.2.1).ne'
  simp only [bit] at hw
  cases b
  · rw [hfalse, CompleteConditional.complete_marginal_false E m hCR i]
    simp only [bit, Bool.false_eq_true, ite_false, zero_mul, sub_zero,
      one_mul]
    have he : (n:ℝ)*(1-(m:ℝ)/n)=(n:ℝ)-m := by field_simp
    rw [he]
    nlinarith [hw]
  · rw [htrue, CompleteConditional.complete_marginal_true E m hCR i]
    simp only [bit, ite_true, one_mul, sub_self, zero_mul, sub_zero]
    have he : (n:ℝ)*((m:ℝ)/n)=(m:ℝ) := by field_simp
    rw [he]
    nlinarith [hw]

lemma t18_count_event_depends {n : ℕ} (H : Finset (Fin n)) (t : ℕ) :
    DependsOn (fun z => if t18_countOn (fun j => j ∈ H) z = t then (1:ℝ) else 0)
      (H : Set (Fin n)) := by
  intro z z' h
  have he := t18_countOn_congr H z z' h
  simp only [he]

/-- Bayes' identity after the symmetric outside count, with every denominator nonzero. -/
lemma t18_event_deviation {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H : Finset (Fin n)) (i : Fin n) (hi : i ∉ H) (hH : H.card < n)
    (A : Assignment n → Prop) (t : ℕ)
    (hA : DependsOn (fun z => if A z then (1:ℝ) else 0) (H : Set (Fin n)))
    (ht : ∀ z, A z → t18_countOn (fun j => j ∈ H) z = t)
    (hQ : 0 < prob E.design A) (b : Bool) :
    cmean E.design (fun z => z i = b) (fun z => if A z then 1 else 0) /
      prob E.design A - 1 =
      (marginal E i b*(H.card:ℝ) - bit b*(t:ℝ) - (1-bit b)*((H.card:ℝ)-t)) /
        (marginal E i b*((n:ℝ)-H.card)) := by
  have hp := (t18_marginal_bounds E m hCR i b).1
  have hnH : (0:ℝ) < (n:ℝ)-H.card := sub_pos.mpr (by exact_mod_cast hH)
  have hw := t18_event_joint E m hCR H i hi A t hA ht b
  apply (eq_div_iff (mul_pos hp hnH).ne').mpr
  field_simp [hQ.ne']
  nlinarith [hw]

/-- The same bound includes the empty mask, so vector atoms need no exceptional case. -/
lemma t18_event_bound {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H : Finset (Fin n)) (i : Fin n) (hi : i ∉ H) (hH : H.card < n)
    (A : Assignment n → Prop) (t : ℕ)
    (hA : DependsOn (fun z => if A z then (1:ℝ) else 0) (H : Set (Fin n)))
    (ht : ∀ z, A z → t18_countOn (fun j => j ∈ H) z = t)
    (htH : t ≤ H.card) (hQ : 0 < prob E.design A) (b : Bool) :
    |cmean E.design (fun z => z i = b) (fun z => if A z then 1 else 0) /
      prob E.design A - 1| ≤ (H.card:ℝ)/(marginal E i b*((n:ℝ)-H.card)) := by
  rw [t18_event_deviation E m hCR H i hi hH A t hA ht hQ b, abs_div]
  have hp := t18_marginal_bounds E m hCR i b
  have hnH : (0:ℝ) < (n:ℝ)-H.card := sub_pos.mpr (by exact_mod_cast hH)
  rw [abs_of_pos (mul_pos hp.1 hnH)]
  apply div_le_div_of_nonneg_right _ (mul_pos hp.1 hnH).le
  have htr : (t:ℝ) ≤ H.card := by exact_mod_cast htH
  have hpr : 0 ≤ marginal E i b*(H.card:ℝ) := mul_nonneg hp.1.le (Nat.cast_nonneg _)
  have hpr' : marginal E i b*(H.card:ℝ) ≤ (H.card:ℝ) :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) hp.2.le
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  have hr0 : (0:ℝ) ≤ H.card := Nat.cast_nonneg H.card
  cases b <;> simp only [bit, Bool.false_eq_true, ite_false, ite_true, zero_mul, one_mul,
    sub_self, sub_zero] <;> apply abs_le.mpr <;> constructor <;>
    nlinarith [ht0, hr0]

lemma t18_scalar_comparisons (n c r T : ℕ) (p : ℝ) (hp : 0 < p)
    (hrc : r ≤ c) (hcn : c < n) (hT : 0 < T) (hTc : T ≤ n-c) :
    (r:ℝ)/(p*((n:ℝ)-r)) ≤ (c:ℝ)/(p*((n:ℝ)-c)) ∧
    (c:ℝ)/(p*((n:ℝ)-c)) ≤ (c:ℝ)/(p*(T:ℝ)) := by
  have hnr : (0:ℝ) < (n:ℝ)-r := sub_pos.mpr (by exact_mod_cast hrc.trans_lt hcn)
  have hnc : (0:ℝ) < (n:ℝ)-c := sub_pos.mpr (by exact_mod_cast hcn)
  have hTr : (0:ℝ) < T := by exact_mod_cast hT
  have hrc' : (r:ℝ) ≤ c := by exact_mod_cast hrc
  have hTc' : (T:ℝ) ≤ (n:ℝ)-c := by
    rw [← Nat.cast_sub hcn.le]
    exact_mod_cast hTc
  constructor
  · apply (div_le_div_iff₀ (mul_pos hp hnr) (mul_pos hp hnc)).mpr
    nlinarith [mul_nonneg (mul_nonneg hp.le (Nat.cast_nonneg n)) (sub_nonneg.mpr hrc')]
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg c) (mul_pos hp hTr)
      (mul_le_mul_of_nonneg_left hTc' hp.le)

lemma t18_choose_true_ratio (N M : ℕ) (hM : 0 < M) (hMN : M ≤ N) :
    ((N-1).choose (M-1) : ℝ)/(N.choose M : ℝ) = (M:ℝ)/N := by
  have hN : 0 < N := lt_of_lt_of_le hM hMN
  have hid : N*(N-1).choose (M-1) = N.choose M*M := by
    have heN : N-1+1=N := by omega
    have heM : M-1+1=M := by omega
    simpa only [heN, heM] using Nat.add_one_mul_choose_eq (N-1) (M-1)
  have hC : (N.choose M : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hMN).ne'
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  apply (div_eq_div_iff hC hNr).mpr
  exact_mod_cast (by nlinarith [hid] : (N-1).choose (M-1)*N=M*N.choose M)

lemma t18_choose_false_ratio (N M : ℕ) (hMN : M < N) :
    ((N-1).choose M : ℝ)/(N.choose M : ℝ) = ((N-M:ℕ):ℝ)/N := by
  have hN : 0 < N := by omega
  have hid : (N-1).choose M*N = N.choose M*(N-M) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ N)] using
      Nat.choose_mul_succ_eq (N-1) M
  have hC : (N.choose M : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hMN.le).ne'
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  apply (div_eq_div_iff hC hNr).mpr
  exact_mod_cast (by nlinarith [hid] : (N-1).choose M*N=(N-M)*N.choose M)

lemma t18_hypergeom_true_step (n m r t : ℕ) (hm : m < n) (hrm : r < m)
    (hrc : r < n-m) (ht : t ≤ r) :
    hypergeomMass (n-1) (m-1) r t =
      hypergeomMass n m r t * ((m:ℝ)-t) / ((n:ℝ)-r) / ((m:ℝ)/n) := by
  have hr : r ≤ n := by omega
  have hmt : m-t ≤ n-r := by omega
  have hB : ((n-r).choose (m-t) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmt).ne'
  have hD : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm.le).ne'
  have hD' : ((n-1).choose (m-1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : m-1 ≤ n-1)).ne'
  have hBratio : ((n-1-r).choose (m-1-t) : ℝ) / ((n-r).choose (m-t) : ℝ) =
      ((m:ℝ)-t)/((n:ℝ)-r) := by
    have heN : n-1-r = (n-r)-1 := by omega
    have heM : m-1-t = (m-t)-1 := by omega
    rw [heN, heM, t18_choose_true_ratio (n-r) (m-t) (by omega) hmt,
      Nat.cast_sub (by omega : t ≤ m), Nat.cast_sub hr]
  have hDratio := t18_choose_true_ratio n m (by omega) hm.le
  rw [← t18_choose_exchange (n-1) (m-1) r t (by omega) (by omega) (by omega) ht,
    ← t18_choose_exchange n m r t hm.le hrm.le hrc.le ht]
  calc
    _ = ((r.choose t : ℝ)*((n-r).choose (m-t) : ℝ)/(n.choose m : ℝ)) *
        (((n-1-r).choose (m-1-t) : ℝ)/((n-r).choose (m-t) : ℝ)) /
        (((n-1).choose (m-1) : ℝ)/(n.choose m : ℝ)) := by
      field_simp
      <;> ring
    _ = _ := by rw [hBratio, hDratio]; ring

lemma t18_hypergeom_false_step (n m r t : ℕ) (hm : m < n) (hrm : r < m)
    (hrc : r < n-m) (ht : t ≤ r) :
    hypergeomMass (n-1) m r t =
      hypergeomMass n m r t * ((n:ℝ)-m-r+t) / ((n:ℝ)-r) / (1-(m:ℝ)/n) := by
  have hr : r ≤ n := by omega
  have hmt : m-t < n-r := by omega
  have hB : ((n-r).choose (m-t) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmt.le).ne'
  have hD : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm.le).ne'
  have hD' : ((n-1).choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : m ≤ n-1)).ne'
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hBratio : ((n-1-r).choose (m-t) : ℝ) / ((n-r).choose (m-t) : ℝ) =
      ((n:ℝ)-m-r+t)/((n:ℝ)-r) := by
    have heN : n-1-r = (n-r)-1 := by omega
    rw [heN, t18_choose_false_ratio (n-r) (m-t) hmt,
      Nat.cast_sub hmt.le, Nat.cast_sub hr, Nat.cast_sub (by omega : t ≤ m)]
    ring
  have hDratio : ((n-1).choose m : ℝ)/(n.choose m : ℝ) = 1-(m:ℝ)/n := by
    rw [t18_choose_false_ratio n m hm, Nat.cast_sub hm.le]
    field_simp
  rw [← t18_choose_exchange (n-1) m r t (by omega) (by omega) (by omega) ht,
    ← t18_choose_exchange n m r t hm.le hrm.le hrc.le ht]
  calc
    _ = ((r.choose t : ℝ)*((n-r).choose (m-t) : ℝ)/(n.choose m : ℝ)) *
        (((n-1-r).choose (m-t) : ℝ)/((n-r).choose (m-t) : ℝ)) /
        (((n-1).choose m : ℝ)/(n.choose m : ℝ)) := by
      field_simp
      <;> ring
    _ = _ := by rw [hBratio, hDratio]; ring


lemma t18_complete_finset_count {n : ℕ} (E : Experiment n) (m : ℕ) (hCR : Complete E m)
    (H : Finset (Fin n)) (t : ℕ) (ht : t ≤ H.card) (hrm : H.card ≤ m)
    (hrc : H.card ≤ n-m) :
    prob E.design (fun z => t18_countOn (fun j => j ∈ H) z = t) =
      hypergeomMass n m H.card t := by
  have hh := t18_complete_count E m hCR (fun j => j ∈ H) t
    (by simpa [Fintype.card_subtype] using ht)
    (by simpa [Fintype.card_subtype] using hrm)
    (by simpa [Fintype.card_subtype] using hrc)
  simpa [Fintype.card_subtype] using hh

lemma t18_hypergeom_pos (n m r t : ℕ) (hm : m ≤ n) (hrm : r ≤ m)
    (hrc : r ≤ n-m) (ht : t ≤ r) : 0 < hypergeomMass n m r t := by
  have h1 : (0:ℝ) < (m.choose t : ℝ) := by exact_mod_cast Nat.choose_pos (ht.trans hrm)
  have h2 : (0:ℝ) < ((n-m).choose (r-t) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : r-t ≤ n-m)
  have h3 : (0:ℝ) < (n.choose r : ℝ) := by exact_mod_cast Nat.choose_pos (hrm.trans hm)
  exact div_pos (mul_pos h1 h2) h3

/-- Conditioning on the own arm deletes one coordinate from the population. -/
lemma t18_complete_finset_conditional {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (H : Finset (Fin n)) (i : Fin n) (hi : i ∉ H)
    (t : ℕ) (ht : t ≤ H.card) (hrm : H.card < m) (hrc : H.card < n-m) (b : Bool) :
    cmean E.design (fun z => z i = b)
      (fun z => if t18_countOn (fun j => j ∈ H) z = t then 1 else 0) =
      hypergeomMass (n-1) (m-(if b then 1 else 0)) H.card t := by
  have hQ := t18_complete_finset_count E m hCR H t ht hrm.le hrc.le
  have hw := t18_event_joint E m hCR H i hi
    (fun z => t18_countOn (fun j => j ∈ H) z = t) t
    (by convert t18_count_event_depends H t using 1 <;> congr!)
    (fun _ hz => hz) b
  have hw' : ((n:ℝ)-H.card) * (marginal E i b *
      cmean E.design (fun z => z i = b)
        (fun z => if t18_countOn (fun j => j ∈ H) z = t then 1 else 0)) =
      ((n:ℝ)*marginal E i b - bit b*(t:ℝ) - (1-bit b)*((H.card:ℝ)-t)) *
        prob E.design (fun z => t18_countOn (fun j => j ∈ H) z = t) := by
    convert hw using 1 <;> congr!
  clear hw
  have hw := hw'
  have hnH : (0:ℝ) < (n:ℝ)-H.card := sub_pos.mpr (by exact_mod_cast hrm.trans hCR.2.1)
  have hp := (t18_marginal_bounds E m hCR i b).1
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast (lt_trans hCR.1 hCR.2.1).ne'
  cases b
  · simp only [Bool.false_eq_true, ite_false, Nat.sub_zero]
    rw [t18_hypergeom_false_step n m H.card t hCR.2.1 hrm hrc ht, ←hQ]
    rw [← CompleteConditional.complete_marginal_false E m hCR i]
    apply (eq_div_iff hp.ne').mpr
    apply (eq_div_iff hnH.ne').mpr
    simp only [bit, Bool.false_eq_true, ite_false, zero_mul, sub_zero, one_mul] at hw
    have he : (n:ℝ)*marginal E i false=(n:ℝ)-m := by
      rw [CompleteConditional.complete_marginal_false E m hCR i]
      field_simp
    rw [he] at hw
    nlinarith [hw]
  · simp only [ite_true]
    rw [t18_hypergeom_true_step n m H.card t hCR.2.1 hrm hrc ht, ←hQ]
    rw [← CompleteConditional.complete_marginal_true E m hCR i]
    apply (eq_div_iff hp.ne').mpr
    apply (eq_div_iff hnH.ne').mpr
    simp only [bit, ite_true, one_mul, sub_self, zero_mul, sub_zero] at hw
    have he : (n:ℝ)*marginal E i true=(m:ℝ) := by
      rw [CompleteConditional.complete_marginal_true E m hCR i]
      field_simp
    rw [he] at hw
    nlinarith [hw]


lemma t18_countOn_le {n : ℕ} (H : Finset (Fin n)) (z : Assignment n) :
    t18_countOn (fun j => j ∈ H) z ≤ H.card := by
  rw [t18_countOn_finset]
  calc
    _ ≤ ∑ _j ∈ H, (1:ℕ) := Finset.sum_le_sum (fun j _ => by cases z j <;> simp)
    _ = _ := by simp

lemma t18_masked_congr {n : ℕ} (E : Experiment n) (i : Fin n) (z z' : Assignment n)
    (h : ∀ j ∈ t18_others E i, z j = z' j) :
    maskedOthers E i z = maskedOthers E i z' := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [maskedOthers]
  · by_cases hI : Interferes E j i
    · have he := h j (by simp [t18_others, hji, hI])
      simp [maskedOthers, Function.update_of_ne hji, masked, hI, he]
    · simp [maskedOthers, Function.update_of_ne hji, masked, hI]

lemma t18_masked_count {n : ℕ} (E : Experiment n) (i : Fin n) (z : Assignment n) :
    t18_countOn (fun j => j ∈ t18_others E i) (maskedOthers E i z) =
      t18_countOn (fun j => j ∈ t18_others E i) z := by
  apply t18_countOn_congr
  intro j hj
  have hh := (Finset.mem_filter.mp hj).2
  simp [maskedOthers, Function.update_of_ne hh.1, masked, hh.2]

lemma t18_bracket (p R T : ℝ) (hp : 0 < p ∧ p < 1) (hR : 0 < R)
    (hT : 0 ≤ T ∧ T ≤ R) (b : Bool) :
    -1 < p-bit b*T/R-(1-bit b)*(R-T)/R ∧
      p-bit b*T/R-(1-bit b)*(R-T)/R < 1 := by
  have h1 : 0 ≤ T/R := div_nonneg hT.1 hR.le
  have h2 : T/R ≤ 1 := (div_le_one hR).mpr hT.2
  have h3 : 0 ≤ (R-T)/R := div_nonneg (sub_nonneg.mpr hT.2) hR.le
  have h4 : (R-T)/R ≤ 1 := (div_le_one hR).mpr (by linarith [hT.1])
  cases b <;> simp only [bit, Bool.false_eq_true, ite_false, ite_true, zero_mul, one_mul,
    sub_self, sub_zero, zero_div] <;> constructor <;> linarith

/-- P009-T18: corrected hypergeometric count laws and likelihood ratios. -/
theorem corrected_hypergeometric_proof {n : ℕ} (E : Experiment n) (m : ℕ)
    (hCR : Complete E m) (i : Fin n)
    (hc : incoming E i ≤ min m (n-m)) :
    let r := incoming E i - 1
    (∀ t, t ≤ r → prob E.design (fun z => treatedIncoming E i z = t) =
      hypergeomMass n m r t) ∧
    (∀ t b, t ≤ r → cmean E.design (fun z => z i = b)
      (fun z => if treatedIncoming E i z = t then 1 else 0) =
      hypergeomMass (n-1) (m-(if b then 1 else 0)) r t) ∧
    (r = 0 → ∀ b, cmean E.design (fun z => z i = b)
      (fun z => if treatedIncoming E i z = 0 then 1 else 0) /
        prob E.design (fun z => treatedIncoming E i z = 0) = 1) ∧
    (∀ t b, t ≤ r → 0 < r →
      cmean E.design (fun z => z i = b)
        (fun z => if treatedIncoming E i z = t then 1 else 0) /
        prob E.design (fun z => treatedIncoming E i z = t) - 1 =
          (r:ℝ)/(marginal E i b*((n:ℝ)-r)) *
            (marginal E i b - bit b*(t:ℝ)/r - (1-bit b)*((r:ℝ)-t)/r)) ∧
    (∀ t b, t ≤ r → 0 < r →
      -1 < marginal E i b-bit b*(t:ℝ)/r-(1-bit b)*((r:ℝ)-t)/r ∧
      marginal E i b-bit b*(t:ℝ)/r-(1-bit b)*((r:ℝ)-t)/r < 1 ∧
      |cmean E.design (fun z => z i = b)
        (fun z => if treatedIncoming E i z = t then 1 else 0) /
        prob E.design (fun z => treatedIncoming E i z = t)-1| ≤
          (r:ℝ)/(marginal E i b*((n:ℝ)-r)) ∧
      (r:ℝ)/(marginal E i b*((n:ℝ)-r)) ≤
        (incoming E i:ℝ)/(marginal E i b*((n:ℝ)-incoming E i)) ∧
      (incoming E i:ℝ)/(marginal E i b*((n:ℝ)-incoming E i)) ≤
        (incoming E i:ℝ)/(marginal E i b*(min m (n-m):ℝ))) ∧
    (∀ w b, 0 < prob E.design (fun z => maskedOthers E i z = w) →
      |cmean E.design (fun z => z i = b) (fun z => if maskedOthers E i z = w then 1 else 0) /
        prob E.design (fun z => maskedOthers E i z = w) - 1| ≤
        (incoming E i : ℝ)/(marginal E i b * (min m (n-m):ℝ))) := by
  dsimp only
  generalize hrdef : incoming E i - 1 = r
  let H := t18_others E i
  have hcard : H.card = r := (t18_others_card E i).trans hrdef
  have hci : 1 ≤ incoming E i := CompleteMixing.incoming_positive E i
  have hcm : incoming E i ≤ m := hc.trans (min_le_left _ _)
  have hcc : incoming E i ≤ n-m := hc.trans (min_le_right _ _)
  have hcn : incoming E i < n := hcm.trans_lt hCR.2.1
  have hrm : r < m := by omega
  have hrc : r < n-m := by omega
  have hrn : r < n := hrm.trans hCR.2.1
  have hHn : H.card < n := by omega
  have hHm : H.card < m := by omega
  have hHc : H.card < n-m := by omega
  have hT : 0 < min m (n-m) := by omega
  have hTc : min m (n-m) ≤ n-incoming E i := by
    have h1 := min_le_left m (n-m)
    have h2 := min_le_right m (n-m)
    omega
  have hrc' : r ≤ incoming E i := by omega
  have hi : i ∉ H := t18_own_not_mem E i
  have hprob (t : ℕ) (ht : t ≤ r) :
      prob E.design (fun z => treatedIncoming E i z = t) = hypergeomMass n m r t := by
    have hh := t18_complete_finset_count E m hCR H t (by omega) hHm.le hHc.le
    simpa only [hcard, t18_countIncoming] using hh
  have hcond (t : ℕ) (b : Bool) (ht : t ≤ r) :
      cmean E.design (fun z => z i = b)
        (fun z => if treatedIncoming E i z = t then 1 else 0) =
      hypergeomMass (n-1) (m-(if b then 1 else 0)) r t := by
    have hh := t18_complete_finset_conditional E m hCR H i hi t (by omega) hHm hHc b
    simpa only [hcard, t18_countIncoming] using hh
  have hQ (t : ℕ) (ht : t ≤ r) :
      0 < prob E.design (fun z => treatedIncoming E i z = t) := by
    rw [hprob t ht]
    exact t18_hypergeom_pos n m r t hCR.2.1.le hrm.le hrc.le ht
  have hdev (t : ℕ) (b : Bool) (ht : t ≤ r) :
      cmean E.design (fun z => z i = b)
        (fun z => if treatedIncoming E i z = t then 1 else 0) /
        prob E.design (fun z => treatedIncoming E i z = t) - 1 =
      (marginal E i b*(r:ℝ)-bit b*(t:ℝ)-(1-bit b)*((r:ℝ)-t)) /
        (marginal E i b*((n:ℝ)-r)) := by
    have hh := t18_event_deviation E m hCR H i hi hHn
      (fun z => t18_countOn (fun j => j ∈ H) z = t) t
      (by convert t18_count_event_depends H t using 1 <;> congr!)
      (fun _ hz => hz) (by simpa only [t18_countIncoming] using hQ t ht) b
    convert hh using 1 <;> (try simp only [t18_countIncoming, hcard]) <;> congr!
  have hbound (t : ℕ) (b : Bool) (ht : t ≤ r) :
      |cmean E.design (fun z => z i = b)
        (fun z => if treatedIncoming E i z = t then 1 else 0) /
        prob E.design (fun z => treatedIncoming E i z = t) - 1| ≤
      (r:ℝ)/(marginal E i b*((n:ℝ)-r)) := by
    have hh := t18_event_bound E m hCR H i hi hHn
      (fun z => t18_countOn (fun j => j ∈ H) z = t) t
      (by convert t18_count_event_depends H t using 1 <;> congr!)
      (fun _ hz => hz) (by omega)
      (by simpa only [t18_countIncoming] using hQ t ht) b
    convert hh using 1 <;> (try simp only [t18_countIncoming, hcard]) <;> congr!
  have hcompare (b : Bool) := t18_scalar_comparisons n (incoming E i) r (min m (n-m))
    (marginal E i b) (t18_marginal_bounds E m hCR i b).1 hrc' hcn hT hTc
  simp only [Nat.cast_min, Nat.cast_sub hCR.2.1.le] at hcompare
  refine ⟨hprob, hcond, ?_, ?_, ?_, ?_⟩
  · intro hr0 b
    have hh := hdev 0 b (Nat.zero_le r)
    simp only [hr0, Nat.cast_zero, mul_zero, zero_mul, sub_zero, zero_div] at hh
    linarith
  · intro t b ht hrpos
    rw [hdev t b ht]
    have hp := (t18_marginal_bounds E m hCR i b).1
    have hnr : (0:ℝ) < (n:ℝ)-r := sub_pos.mpr (by exact_mod_cast hrn)
    have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    field_simp [hp.ne', hnr.ne', hr0]
    <;> ring
  · intro t b ht hrpos
    have hp := t18_marginal_bounds E m hCR i b
    have hbr := t18_bracket (marginal E i b) (r:ℝ) (t:ℝ) hp
      (by exact_mod_cast hrpos) ⟨Nat.cast_nonneg _, by exact_mod_cast ht⟩ b
    exact ⟨hbr.1, hbr.2, hbound t b ht, (hcompare b).1, (hcompare b).2⟩
  · intro w b hw
    let t := t18_countOn (fun j => j ∈ H) w
    have hA : DependsOn (fun z => if maskedOthers E i z = w then (1:ℝ) else 0)
        (H : Set (Fin n)) := by
      intro z z' hz
      have he := t18_masked_congr E i z z' hz
      simp only [he]
    have htA (z : Assignment n) (hz : maskedOthers E i z = w) :
        t18_countOn (fun j => j ∈ H) z = t := by
      calc
        _ = t18_countOn (fun j => j ∈ H) (maskedOthers E i z) :=
          (t18_masked_count E i z).symm
        _ = _ := by rw [hz]
    have hh := t18_event_bound E m hCR H i hi hHn
      (fun z => maskedOthers E i z = w) t
      (by convert hA using 1 <;> congr!) htA (t18_countOn_le H w) hw b
    have hh' :
        |cmean E.design (fun z => z i = b) (fun z => if maskedOthers E i z = w then 1 else 0) /
          prob E.design (fun z => maskedOthers E i z = w) - 1| ≤
          (r:ℝ)/(marginal E i b*((n:ℝ)-r)) := by
      convert hh using 1 <;> (try simp only [hcard]) <;> congr!
    exact hh'.trans ((hcompare b).1.trans (hcompare b).2)

end
end AronowAudit.P009.Wave1
