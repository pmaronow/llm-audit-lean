import AronowAudit.P003.P003_Audit
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Factorial.Basic

namespace AronowAudit.P003.Wave1

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

/-! Finite-rank and canonical-table lemmas. -/

lemma glp0032b4_gmc_uniform_reindex {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) :
    uniformProb (fun a => P (e a)) = uniformProb P := by
  have hc : (Finset.univ.filter (fun a => P (e a))).card =
      (Finset.univ.filter P).card := by
    let e' : {a // a ∈ Finset.univ.filter (fun a => P (e a))} ≃
        {b // b ∈ Finset.univ.filter P} :=
      { toFun := fun a => ⟨e a.val,by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp a.property).2⟩⟩
        invFun := fun b => ⟨e.symm b.val,by simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply] using (Finset.mem_filter.mp b.property).2⟩
        left_inv := by intro a; apply Subtype.ext; simp
        right_inv := by intro b; apply Subtype.ext; simp }
    simpa only [Fintype.card_coe] using Fintype.card_congr e'
  unfold uniformProb
  rw [hc,Fintype.card_congr e]

lemma glp0032b4_gmc_finite_rank {A : Type*} [Fintype A] [Nonempty A]
    (K : ℕ) (s : A → ℝ) (α : ℝ) (hα : 0 ≤ α) :
    uniformProb (fun x : Fin (K+1) → A =>
      (∑ j : Fin (K+1), if s (x 0) ≤ s (x j) then (1 : ℝ) else 0)/(K+1) ≤ α) ≤ α := by
  let L : ℝ := K+1
  let rank (x : Fin (K+1) → A) (i : Fin (K+1)) : ℝ :=
    ∑ j, if s (x i) ≤ s (x j) then 1 else 0
  let bad (x : Fin (K+1) → A) (i : Fin (K+1)) : Prop := rank x i ≤ α*L
  have hL : (0 : ℝ) < L := by dsimp [L]; positivity
  have hpoint (x : Fin (K+1) → A) :
      (∑ i, if bad x i then (1 : ℝ) else 0) ≤ α*L := by
    let B := Finset.univ.filter (bad x)
    by_cases hB : B.Nonempty
    · obtain ⟨i,hi,hmin⟩ := B.exists_min_image (fun i => s (x i)) hB
      have hle : (∑ j, if bad x j then (1 : ℝ) else 0) ≤ rank x i := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hb : bad x j
        · have hs : s (x i) ≤ s (x j) := hmin j (by simp [B,hb])
          simp only [if_pos hb,if_pos hs]
          exact le_rfl
        · simp only [if_neg hb]
          split_ifs <;> norm_num
      exact hle.trans ((Finset.mem_filter.mp hi).2)
    · have hn : ∀ i, ¬ bad x i := by
        intro i hi
        exact hB ⟨i,by simp [B,hi]⟩
      simp only [if_neg (hn _),Finset.sum_const_zero]
      exact mul_nonneg hα hL.le
  have hswap (i : Fin (K+1)) :
      (∑ x : Fin (K+1) → A, if bad x i then (1 : ℝ) else 0) =
        ∑ x : Fin (K+1) → A, if bad x 0 then (1 : ℝ) else 0 := by
    let σ := Equiv.swap i (0 : Fin (K+1))
    let e : (Fin (K+1) → A) ≃ (Fin (K+1) → A) :=
      { toFun := fun x j => x (σ j)
        invFun := fun x j => x (σ j)
        left_inv := by intro x; funext j; simp [σ]
        right_inv := by intro x; funext j; simp [σ] }
    have hr (x : Fin (K+1) → A) : rank (e x) 0 = rank x i := by
      dsimp [rank,e]
      simp only [show σ 0 = i by simp [σ]]
      exact Equiv.sum_comp σ (fun j => if s (x i) ≤ s (x j) then (1 : ℝ) else 0)
    calc
      _ = ∑ x, if bad (e x) 0 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [bad,hr]
      _ = _ := Equiv.sum_comp e (fun x => if bad x 0 then (1 : ℝ) else 0)
  have havg := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_comm] at havg
  simp_rw [hswap] at havg
  have hcard : (0 : ℝ) < Fintype.card (Fin (K+1) → A) := by
    exact_mod_cast Fintype.card_pos
  have hevent (x : Fin (K+1) → A) :
      ((∑ j, if s (x 0) ≤ s (x j) then (1 : ℝ) else 0)/(K+1) ≤ α) ↔ bad x 0 := by
    exact div_le_iff₀ hL
  simp only [hevent]
  unfold uniformProb
  rw [div_le_iff₀ hcard]
  have hcount : ((Finset.univ.filter (fun x => bad x 0)).card : ℝ) =
      ∑ x : Fin (K+1) → A, if bad x 0 then (1 : ℝ) else 0 := by simp
  rw [hcount]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at havg
  have hcancel := (mul_le_mul_iff_right₀ hL).mp (show
      (L : ℝ)*(∑ x : Fin (K+1) → A, if bad x 0 then (1 : ℝ) else 0) ≤
      (L : ℝ)*(α*(Fintype.card (Fin (K+1) → A) : ℝ)) by
        convert havg using 1 <;> dsimp [L] <;> push_cast <;> ring)
  exact hcancel

lemma glp0032b4_gmc_segment_card (n a b : ℕ) (h : a+b ≤ n) :
    (Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < a+b)).card = b := by
  let e : Fin b ≃ {i : Fin n // i ∈ Finset.univ.filter
      (fun i : Fin n => a ≤ i.val ∧ i.val < a+b)} :=
    { toFun := fun k => ⟨⟨a+k.val,by omega⟩,by
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        constructor <;> omega⟩
      invFun := fun i => ⟨i.val.val-a,by have := (Finset.mem_filter.mp i.property).2; omega⟩
      left_inv := by intro k; apply Fin.ext; dsimp; omega
      right_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        have := (Finset.mem_filter.mp i.property).2
        dsimp
        omega }
  simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr e).symm

lemma glp0032b4_gmc_canonical_type_cards (v : Counts) :
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (true,true))).card = v.a ∧
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (true,false))).card = v.b ∧
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (false,true))).card = v.c ∧
    (Finset.univ.filter (fun i : Fin v.total => canonicalPair v i.val = (false,false))).card = v.d := by
  have hseg := glp0032b4_gmc_segment_card v.total
  have hp (i : Fin v.total) :
      (canonicalPair v i.val = (true,true) ↔ 0 ≤ i.val ∧ i.val < 0+v.a) ∧
      (canonicalPair v i.val = (true,false) ↔ v.a ≤ i.val ∧ i.val < v.a+v.b) ∧
      (canonicalPair v i.val = (false,true) ↔ v.a+v.b ≤ i.val ∧ i.val < (v.a+v.b)+v.c) ∧
      (canonicalPair v i.val = (false,false) ↔ v.a+v.b+v.c ≤ i.val ∧
        i.val < (v.a+v.b+v.c)+v.d) := by
    have hi := i.isLt
    dsimp [Counts.total] at hi
    unfold canonicalPair
    split_ifs <;> simp_all <;> omega
  simp_rw [(hp _).1,(hp _).2.1,(hp _).2.2.1,(hp _).2.2.2]
  exact ⟨hseg 0 v.a (by dsimp [Counts.total]; omega),
    hseg v.a v.b (by dsimp [Counts.total]; omega),
    hseg (v.a+v.b) v.c (by dsimp [Counts.total]; omega),
    hseg (v.a+v.b+v.c) v.d (by dsimp [Counts.total]; omega)⟩

lemma glp0032b4_gmc_pair_split {I : Type*} [DecidableEq I]
    (s : Finset I) (w : I → Bool × Bool) (b : Bool) :
    (s.filter (fun i => (w i).1 = b)).card =
      (s.filter (fun i => w i = (b,true))).card +
      (s.filter (fun i => w i = (b,false))).card ∧
    (s.filter (fun i => (w i).2 = b)).card =
      (s.filter (fun i => w i = (true,b))).card +
      (s.filter (fun i => w i = (false,b))).card := by
  constructor
  · have h := Finset.card_filter_add_card_filter_not
      (s := s.filter (fun i => (w i).1 = b)) (fun i => (w i).2 = true)
    have he (i : I) :
        ((w i).1 = b ∧ (w i).2 = true ↔ w i = (b,true)) ∧
        ((w i).1 = b ∧ ¬ (w i).2 = true ↔ w i = (b,false)) := by
      rcases w i with ⟨u,t⟩
      cases u <;> cases t <;> cases b <;> simp
    simpa only [Finset.filter_filter,(he _).1,(he _).2] using h.symm
  · have h := Finset.card_filter_add_card_filter_not
      (s := s.filter (fun i => (w i).2 = b)) (fun i => (w i).1 = true)
    have he (i : I) :
        ((w i).2 = b ∧ (w i).1 = true ↔ w i = (true,b)) ∧
        ((w i).2 = b ∧ ¬ (w i).1 = true ↔ w i = (false,b)) := by
      rcases w i with ⟨u,t⟩
      cases u <;> cases t <;> cases b <;> simp
    simpa only [Finset.filter_filter,(he _).1,(he _).2] using h.symm

lemma glp0032b4_gmc_observed_bridge (v : Counts) (z : Finset (Fin v.total)) :
    observed v (treatedCounts v z) = canonicalObserved v z := by
  let w := fun i : Fin v.total => canonicalPair v i.val
  have hcard := glp0032b4_gmc_canonical_type_cards v
  have hsub (b : Bool × Bool) :
      (z.filter (fun i => w i = b)).card ≤
        (Finset.univ.filter (fun i => w i = b)).card := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  have hqc : (z.filter (fun i => w i = (false,true))).card ≤ v.c := by
    simpa only [w, hcard.2.2.1] using hsub (false,true)
  have hqd : (z.filter (fun i => w i = (false,false))).card ≤ v.d := by
    simpa only [w, hcard.2.2.2] using hsub (false,false)
  have hcontrol (b : Bool × Bool) :
      ((Finset.univ \ z).filter (fun i => w i = b)).card =
        (Finset.univ.filter (fun i => w i = b)).card - (z.filter (fun i => w i = b)).card := by
    have he : (Finset.univ \ z).filter (fun i => w i = b) =
        (Finset.univ.filter (fun i => w i = b)) \ (z.filter (fun i => w i = b)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
      tauto
    rw [he,Finset.card_sdiff_of_subset (by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩)]
  have ht (b : Bool) :
      (Finset.univ.filter (fun i => i ∈ z ∧ (w i).1 = b)) =
        z.filter (fun i => (w i).1 = b) := by ext i; simp
  have hc (b : Bool) :
      (Finset.univ.filter (fun i => i ∉ z ∧ (w i).2 = b)) =
        (Finset.univ \ z).filter (fun i => (w i).2 = b) := by ext i; simp
  apply Counts.ext
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [ht true,(glp0032b4_gmc_pair_split z w true).1]
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [ht false,(glp0032b4_gmc_pair_split z w false).1]
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [hc true,(glp0032b4_gmc_pair_split (Finset.univ \ z) w true).2,
      hcontrol,hcontrol,hcard.1,hcard.2.2.1]
    dsimp [w] at *
    omega
  · dsimp [observed,treatedCounts,canonicalObserved]
    rw [hc false,(glp0032b4_gmc_pair_split (Finset.univ \ z) w false).2,
      hcontrol,hcontrol,hcard.2.1,hcard.2.2.2]
    dsimp [w] at *
    omega


/-! Elementary finite averaging. -/

noncomputable def glp0032b4_gmc_avg {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

lemma glp0032b4_gmc_avg_congr {A : Type*} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a = g a) : glp0032b4_gmc_avg f = glp0032b4_gmc_avg g := by
  unfold glp0032b4_gmc_avg
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

lemma glp0032b4_gmc_avg_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    glp0032b4_gmc_avg (fun a => f (e a)) = glp0032b4_gmc_avg f := by
  unfold glp0032b4_gmc_avg
  rw [Equiv.sum_comp e, Fintype.card_congr e]

lemma glp0032b4_gmc_avg_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    glp0032b4_gmc_avg (fun _ : A => c) = c := by
  have h : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [glp0032b4_gmc_avg, h]

lemma glp0032b4_gmc_avg_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A × B → ℝ) :
    glp0032b4_gmc_avg f =
      glp0032b4_gmc_avg (fun a => glp0032b4_gmc_avg (fun b => f (a,b))) := by
  simp only [glp0032b4_gmc_avg, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type, div_eq_mul_inv, mul_inv_rev, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma glp0032b4_gmc_avg_comm {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → ℝ) :
    glp0032b4_gmc_avg (fun a => glp0032b4_gmc_avg (f a)) =
      glp0032b4_gmc_avg (fun b => glp0032b4_gmc_avg (fun a => f a b)) := by
  change (glp0032b4_gmc_avg (fun a => glp0032b4_gmc_avg (fun b => f a b))) = _
  rw [← glp0032b4_gmc_avg_prod (fun p : A × B => f p.1 p.2),
    ← glp0032b4_gmc_avg_prod (fun p : B × A => f p.2 p.1)]
  exact glp0032b4_gmc_avg_equiv (Equiv.prodComm A B) (fun p => f p.2 p.1)

lemma glp0032b4_gmc_avg_pair {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → ℝ) :
    glp0032b4_gmc_avg (fun a => glp0032b4_gmc_avg (fun b => f a b)) =
      glp0032b4_gmc_avg (fun p : A × B => f p.1 p.2) :=
  (glp0032b4_gmc_avg_prod (fun p : A × B => f p.1 p.2)).symm

lemma glp0032b4_gmc_avg_ite {A : Type*} [Fintype A] [Nonempty A]
    (p : A → Prop) [DecidablePred p] (x y : ℝ) :
    glp0032b4_gmc_avg (fun a => if p a then x else y) =
      ((Finset.univ.filter p).card : ℝ) / Fintype.card A * x +
      (1 - ((Finset.univ.filter p).card : ℝ) / Fintype.card A) * y := by
  have h : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ a, if p a then x else y) =
      ((Finset.univ.filter p).card : ℝ)*x +
      ((Fintype.card A : ℝ) - (Finset.univ.filter p).card)*y := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) p
    have hc' : ((Finset.univ.filter (fun a => ¬p a)).card : ℝ) =
        (Fintype.card A : ℝ) - (Finset.univ.filter p).card := by
      have hc' : ((Finset.univ.filter p).card : ℝ) +
          (Finset.univ.filter (fun a => ¬p a)).card = Fintype.card A := by
        exact_mod_cast hc
      linarith
    simpa only [nsmul_eq_mul, hc']
  unfold glp0032b4_gmc_avg
  rw [hsum]
  field_simp
  <;> ring

lemma glp0032b4_gmc_residue_avg (N r : ℕ) (hN : 0 < N) (hr : 0 < r) (hdvd : r ∣ N)
    (f : Fin r → ℝ) :
    glp0032b4_gmc_avg (fun s : Fin N => f ⟨s.val % r, Nat.mod_lt _ hr⟩) =
      glp0032b4_gmc_avg f := by
  have hk : 0 < N/r := Nat.div_pos (Nat.le_of_dvd hN hdvd) hr
  letI instGLP0032B4Local1 : Nonempty (Fin (N/r)) := ⟨⟨0,hk⟩⟩
  let e : Fin (N/r) × Fin r ≃ Fin N :=
    finProdFinEquiv.trans (finCongr (Nat.div_mul_cancel hdvd))
  rw [← glp0032b4_gmc_avg_equiv e]
  have he (p : Fin (N/r) × Fin r) : (e p).val % r = p.2.val := by
    dsimp [e, finProdFinEquiv]
    simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.2.isLt]
  conv_lhs =>
    arg 1
    ext p
    rw [show (⟨(e p).val % r, Nat.mod_lt _ hr⟩ : Fin r) = p.2 by
      apply Fin.ext; exact he p]
  rw [glp0032b4_gmc_avg_prod]
  change glp0032b4_gmc_avg (fun _ : Fin (N/r) => glp0032b4_gmc_avg f) = _
  exact glp0032b4_gmc_avg_const _

abbrev glp0032b4_gmc_subcounts {n : ℕ} (w : PotentialTable n) (z : Finset (Fin n)) : Counts :=
  ⟨(z.filter fun i => w i = (true,true)).card,
   (z.filter fun i => w i = (true,false)).card,
   (z.filter fun i => w i = (false,true)).card,
   (z.filter fun i => w i = (false,false)).card⟩

lemma glp0032b4_gmc_card_update {I T : Type*} [DecidableEq I] [DecidableEq T]
    (w : I → T) (z : Finset I) (i : I) (t u : T) :
    ((z.filter (fun j => Function.update w i t j = u)).card : ℤ) =
      (z.filter (fun j => w j = u)).card +
      if i ∈ z then (if t = u then 1 else 0) - (if w i = u then 1 else 0) else 0 := by
  have hc (f : I → T) : ((z.filter (fun j => f j = u)).card : ℤ) =
      ∑ j ∈ z, if f j = u then (1 : ℤ) else 0 := by simp
  rw [hc, hc]
  have he : (fun j => if Function.update w i t j = u then (1 : ℤ) else 0) =
      Function.update (fun j => if w j = u then (1 : ℤ) else 0) i
        (if t = u then 1 else 0) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [he]
  by_cases hi : i ∈ z
  · rw [if_pos hi, Finset.sum_update_of_mem hi]
    have h := Finset.sum_update_of_mem hi
      (fun j => if w j = u then (1 : ℤ) else 0)
      (if w i = u then (1 : ℤ) else 0)
    rw [Function.update_eq_self] at h
    linarith
  · rw [if_neg hi, Finset.sum_update_of_notMem hi]
    ring

abbrev glp0032b4_gmc_move {n : ℕ} (w : PotentialTable n) (i j : Fin n) : PotentialTable n :=
  Function.update (Function.update w i (true,false)) j (false,true)

lemma glp0032b4_gmc_move_counts {n : ℕ} (w : PotentialTable n)
    (i j : Fin n) (hi : w i = (true,true)) (hj : w j = (false,false))
    (z : Finset (Fin n)) :
    glp0032b4_gmc_subcounts (glp0032b4_gmc_move w i j) z =
      ⟨if i ∉ z then (glp0032b4_gmc_subcounts w z).a else
          (glp0032b4_gmc_subcounts w z).a-1,
       if i ∉ z then (glp0032b4_gmc_subcounts w z).b else
          (glp0032b4_gmc_subcounts w z).b+1,
       if j ∉ z then (glp0032b4_gmc_subcounts w z).c else
          (glp0032b4_gmc_subcounts w z).c+1,
       if j ∉ z then (glp0032b4_gmc_subcounts w z).d else
          (glp0032b4_gmc_subcounts w z).d-1⟩ := by
  have hji : j ≠ i := by intro h; subst j; rw [hi] at hj; cases hj
  have hj' : Function.update w i (true,false) j = (false,false) := by simp [hji, hj]
  have ha := glp0032b4_gmc_card_update w z i (true,false) (true,true)
  have hb := glp0032b4_gmc_card_update w z i (true,false) (true,false)
  have hc := glp0032b4_gmc_card_update w z i (true,false) (false,true)
  have hd := glp0032b4_gmc_card_update w z i (true,false) (false,false)
  have ha' := glp0032b4_gmc_card_update (Function.update w i (true,false)) z j
    (false,true) (true,true)
  have hb' := glp0032b4_gmc_card_update (Function.update w i (true,false)) z j
    (false,true) (true,false)
  have hc' := glp0032b4_gmc_card_update (Function.update w i (true,false)) z j
    (false,true) (false,true)
  have hd' := glp0032b4_gmc_card_update (Function.update w i (true,false)) z j
    (false,true) (false,false)
  by_cases hiz : i ∈ z <;> by_cases hjz : j ∈ z <;>
    simp [hi, hj', hiz, hjz] at ha hb hc hd ha' hb' hc' hd' <;>
    apply Counts.ext <;>
    simp only [glp0032b4_gmc_subcounts, glp0032b4_gmc_move, Counts.a, Counts.b,
      Counts.c, Counts.d, hiz, hjz, not_true_eq_false, not_false_eq_true, if_true, if_false] <;>
    omega

lemma glp0032b4_gmc_move_total {n : ℕ} (w : PotentialTable n)
    (i j : Fin n) (hi : w i = (true,true)) (hj : w j = (false,false)) :
    tableCounts (glp0032b4_gmc_move w i j) = reuseVector (tableCounts w) 1 := by
  have h := glp0032b4_gmc_move_counts w i j hi hj Finset.univ
  simpa [glp0032b4_gmc_subcounts, tableCounts, reuseVector] using h

def glp0032b4_gmc_assignment_equiv {n : ℕ} (m : ℕ) (π : Fin n ≃ Fin n) :
    Assignment n m ≃ Assignment n m where
  toFun z := ⟨z.val.map π.toEmbedding, by rw [Finset.card_map]; exact z.property⟩
  invFun z := ⟨z.val.map π.symm.toEmbedding, by rw [Finset.card_map]; exact z.property⟩
  left_inv z := by apply Subtype.ext; simp [Finset.map_map]
  right_inv z := by apply Subtype.ext; simp [Finset.map_map]

lemma glp0032b4_gmc_relabel {n : ℕ} (w w' : PotentialTable n)
    (hc : tableCounts w = tableCounts w') (m : ℕ) (f : Counts → ℝ) :
    glp0032b4_gmc_avg (fun z : Assignment n m => f (glp0032b4_gmc_subcounts w z.val)) =
    glp0032b4_gmc_avg (fun z : Assignment n m => f (glp0032b4_gmc_subcounts w' z.val)) := by
  have hf (u : Bool × Bool) : Fintype.card {i // w i = u} = Fintype.card {i // w' i = u} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases u with ⟨a,b⟩
    cases a <;> cases b
    · exact congrArg Counts.d hc
    · exact congrArg Counts.c hc
    · exact congrArg Counts.b hc
    · exact congrArg Counts.a hc
  let π := Equiv.ofFiberEquiv (fun u => Fintype.equivOfCardEq (hf u))
  have hπ (i : Fin n) : w' (π i) = w i :=
    Equiv.ofFiberEquiv_map (fun u => Fintype.equivOfCardEq (hf u)) i
  let e := glp0032b4_gmc_assignment_equiv m π
  have he (z : Assignment n m) :
      glp0032b4_gmc_subcounts w' (e z).val = glp0032b4_gmc_subcounts w z.val := by
    have hfilter (u : Bool × Bool) :
        ((e z).val.filter (fun i => w' i = u)).card =
        (z.val.filter (fun i => w i = u)).card := by
      change ((z.val.map π.toEmbedding).filter _).card = _
      rw [Finset.filter_map]
      simp only [Function.comp_apply, Equiv.toEmbedding_apply, hπ, Finset.card_map]
    exact Counts.ext (hfilter _) (hfilter _) (hfilter _) (hfilter _)
  rw [← glp0032b4_gmc_avg_equiv e
    (fun z => f (glp0032b4_gmc_subcounts w' z.val))]
  exact glp0032b4_gmc_avg_congr (fun z => congrArg f (he z).symm)

lemma glp0032b4_gmc_control_card {n : ℕ} (w : PotentialTable n)
    (z : Finset (Fin n)) (u : Bool × Bool) :
    (Finset.univ.filter (fun i : {i : Fin n // w i = u} => i.val ∉ z)).card =
      (Finset.univ.filter (fun i => w i = u)).card -
        (z.filter (fun i => w i = u)).card := by
  have he : (Finset.univ.filter (fun i : {i : Fin n // w i = u} => i.val ∉ z)).card =
      ((Finset.univ.filter (fun i => w i = u)).filter (fun i => i ∉ z)).card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨i.property,hi⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨⟨i,hi.1⟩, by simp [hi.2], rfl⟩
  rw [he]
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i => w i = u)) (fun i => i ∈ z)
  have hz : (Finset.univ.filter (fun i => w i = u)).filter (fun i => i ∈ z) =
      z.filter (fun i => w i = u) := by ext i; simp [and_comm]
  rw [hz] at h
  omega

lemma glp0032b4_gmc_seed_label_avg {n : ℕ} (w : PotentialTable n)
    (z : Finset (Fin n)) (u : Bool × Bool)
    (hr : 0 < (Finset.univ.filter (fun i => w i = u)).card) (x y : ℝ) :
    glp0032b4_gmc_avg (fun s : Fin n.factorial =>
      if s.val % (Finset.univ.filter (fun i => w i = u)).card <
        (Finset.univ.filter (fun i => w i = u)).card -
          (z.filter (fun i => w i = u)).card then x else y) =
    glp0032b4_gmc_avg (fun i : {i : Fin n // w i = u} => if i.val ∉ z then x else y) := by
  let r := (Finset.univ.filter (fun i => w i = u)).card
  let t := (z.filter (fun i => w i = u)).card
  have hrn : r ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin n => w i = u))
  have hdvd : r ∣ n.factorial := Nat.dvd_factorial hr hrn
  letI instGLP0032B4Local2 : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  letI instGLP0032B4Local3 : Nonempty {i : Fin n // w i = u} :=
    Fintype.card_pos_iff.mp (by simpa [Fintype.card_subtype, r] using hr)
  change glp0032b4_gmc_avg (fun s : Fin n.factorial => if s.val % r < r-t then x else y) = _
  rw [glp0032b4_gmc_residue_avg n.factorial r (Nat.factorial_pos n) hr hdvd
    (fun k => if k.val < r-t then x else y)]
  rw [glp0032b4_gmc_avg_ite, glp0032b4_gmc_avg_ite]
  have hfin : (Finset.univ.filter (fun k : Fin r => k.val < r-t)).card = r-t := by
    simpa using glp0032b4_gmc_segment_card r 0 (r-t) (by omega)
  rw [hfin, glp0032b4_gmc_control_card]
  simp only [Fintype.card_fin, Fintype.card_subtype]
  rfl

lemma glp0032b4_gmc_seed_label_fun {n : ℕ} (w : PotentialTable n)
    (z : Finset (Fin n)) (u : Bool × Bool)
    (hr : 0 < (Finset.univ.filter (fun i => w i = u)).card) (F : Bool → ℝ) :
    glp0032b4_gmc_avg (fun s : Fin n.factorial =>
      F (decide (s.val % (Finset.univ.filter (fun i => w i = u)).card <
        (Finset.univ.filter (fun i => w i = u)).card -
          (z.filter (fun i => w i = u)).card))) =
    glp0032b4_gmc_avg (fun i : {i : Fin n // w i = u} => F (decide (i.val ∉ z))) := by
  have h (p : Prop) [Decidable p] : F (decide p) = if p then F true else F false := by
    split_ifs with hp <;> simp [hp]
  simp_rw [h]
  exact glp0032b4_gmc_seed_label_avg w z u hr (F true) (F false)

abbrev glp0032b4_gmc_update (q : Counts) (c₀ c₁ : Bool) : Counts :=
  ⟨if c₁ then q.a else q.a-1, if c₁ then q.b else q.b+1,
   if c₀ then q.c else q.c+1, if c₀ then q.d else q.d-1⟩

lemma glp0032b4_gmc_update_eq (v q : Counts) (s₀ s₁ : ℕ) :
    updateTreated v q s₀ s₁ = glp0032b4_gmc_update q
      (decide (s₀ % v.d < v.d-q.d)) (decide (s₁ % v.a < v.a-q.a)) := by
  simp [updateTreated, glp0032b4_gmc_update]

lemma glp0032b4_gmc_canonical_counts (v : Counts) :
    tableCounts (fun i : Fin v.total => canonicalPair v i.val) = v := by
  obtain ⟨ha,hb,hc,hd⟩ := glp0032b4_gmc_canonical_type_cards v
  exact Counts.ext ha hb hc hd

lemma glp0032b4_gmc_canonical_counts_n {n : ℕ} (v : Counts) (hn : v.total = n) :
    tableCounts (fun i : Fin n => canonicalPair v i.val) = v := by
  subst n
  exact glp0032b4_gmc_canonical_counts v

lemma glp0032b4_gmc_step {n : ℕ} (v : Counts) (hn : v.total = n)
    (m : ℕ) (ha : 0 < v.a) (hd : 0 < v.d) (f : Counts → ℝ) :
    glp0032b4_gmc_avg (fun p : Assignment n m × (Fin n.factorial × Fin n.factorial) =>
      f (updateTreated v (treatedCounts v p.1.val) p.2.1.val p.2.2.val)) =
    glp0032b4_gmc_avg (fun z : Assignment n m =>
      f (treatedCounts (reuseVector v 1) z.val)) := by
  subst n
  let w : PotentialTable v.total := fun i => canonicalPair v i.val
  let C := {i : Fin v.total // w i = (true,true)}
  let D := {i : Fin v.total // w i = (false,false)}
  have hw : tableCounts w = v := glp0032b4_gmc_canonical_counts v
  have hC : Fintype.card C = v.a := by
    simpa only [C, Fintype.card_subtype, tableCounts] using congrArg Counts.a hw
  have hD : Fintype.card D = v.d := by
    simpa only [D, Fintype.card_subtype, tableCounts] using congrArg Counts.d hw
  have hca : (Finset.univ.filter (fun i => w i = (true,true))).card = v.a :=
    congrArg Counts.a hw
  have hcd : (Finset.univ.filter (fun i => w i = (false,false))).card = v.d :=
    congrArg Counts.d hw
  letI instGLP0032B4Local4 : Nonempty C := Fintype.card_pos_iff.mp (by omega)
  letI instGLP0032B4Local5 : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have hkernel (z : Assignment v.total m) :
      glp0032b4_gmc_avg (fun s₀ : Fin v.total.factorial =>
        glp0032b4_gmc_avg (fun s₁ : Fin v.total.factorial =>
          f (updateTreated v (treatedCounts v z.val) s₀.val s₁.val))) =
      glp0032b4_gmc_avg (fun j : D => glp0032b4_gmc_avg (fun i : C =>
        f (glp0032b4_gmc_subcounts (glp0032b4_gmc_move w i.val j.val) z.val))) := by
    let q := treatedCounts v z.val
    have hs₁ (s₀ : Fin v.total.factorial) := glp0032b4_gmc_seed_label_fun w z.val
      (true,true) (by simpa only [← hC, C, Fintype.card_subtype] using ha)
      (fun b => f (glp0032b4_gmc_update q (decide (s₀.val % v.d < v.d-q.d)) b))
    have hs₀ (i : C) := glp0032b4_gmc_seed_label_fun w z.val
      (false,false) (by simpa only [← hD, D, Fintype.card_subtype] using hd)
      (fun b => f (glp0032b4_gmc_update q b (decide (i.val ∉ z.val))))
    calc
      _ = glp0032b4_gmc_avg (fun s₀ : Fin v.total.factorial =>
          glp0032b4_gmc_avg (fun i : C => f (glp0032b4_gmc_update q
            (decide (s₀.val % v.d < v.d-q.d)) (decide (i.val ∉ z.val))))) := by
        apply glp0032b4_gmc_avg_congr
        intro s₀
        simpa only [glp0032b4_gmc_update_eq, hca,
          glp0032b4_gmc_subcounts, treatedCounts, w, q] using hs₁ s₀
      _ = glp0032b4_gmc_avg (fun i : C => glp0032b4_gmc_avg (fun s₀ : Fin v.total.factorial =>
          f (glp0032b4_gmc_update q (decide (s₀.val % v.d < v.d-q.d))
            (decide (i.val ∉ z.val))))) := glp0032b4_gmc_avg_comm _
      _ = glp0032b4_gmc_avg (fun i : C => glp0032b4_gmc_avg (fun j : D =>
          f (glp0032b4_gmc_update q (decide (j.val ∉ z.val))
            (decide (i.val ∉ z.val))))) := by
        apply glp0032b4_gmc_avg_congr
        intro i
        simpa only [hcd, glp0032b4_gmc_subcounts, treatedCounts, w, q] using hs₀ i
      _ = glp0032b4_gmc_avg (fun j : D => glp0032b4_gmc_avg (fun i : C =>
          f (glp0032b4_gmc_update q (decide (j.val ∉ z.val))
            (decide (i.val ∉ z.val))))) := glp0032b4_gmc_avg_comm _
      _ = _ := by
        apply glp0032b4_gmc_avg_congr
        intro j
        apply glp0032b4_gmc_avg_congr
        intro i
        rw [glp0032b4_gmc_move_counts w i.val j.val i.property j.property]
        simp [glp0032b4_gmc_update, q, treatedCounts, w]
  have hnew : (reuseVector v 1).total = v.total := by
    dsimp [reuseVector, Counts.total]; omega
  let w' : PotentialTable v.total := fun i => canonicalPair (reuseVector v 1) i.val
  have hw' : tableCounts w' = reuseVector v 1 := by
    exact glp0032b4_gmc_canonical_counts_n (reuseVector v 1) hnew
  rw [glp0032b4_gmc_avg_prod]
  calc
    _ = glp0032b4_gmc_avg (fun z : Assignment v.total m =>
        glp0032b4_gmc_avg (fun j : D => glp0032b4_gmc_avg (fun i : C =>
          f (glp0032b4_gmc_subcounts (glp0032b4_gmc_move w i.val j.val) z.val)))) := by
      apply glp0032b4_gmc_avg_congr
      intro z
      rw [glp0032b4_gmc_avg_prod]
      exact hkernel z
    _ = glp0032b4_gmc_avg (fun j : D => glp0032b4_gmc_avg (fun i : C =>
        glp0032b4_gmc_avg (fun z : Assignment v.total m =>
          f (glp0032b4_gmc_subcounts (glp0032b4_gmc_move w i.val j.val) z.val)))) := by
      rw [glp0032b4_gmc_avg_comm]
      apply glp0032b4_gmc_avg_congr
      intro j
      exact glp0032b4_gmc_avg_comm _
    _ = glp0032b4_gmc_avg (fun j : D => glp0032b4_gmc_avg (fun i : C =>
        glp0032b4_gmc_avg (fun z : Assignment v.total m => f (glp0032b4_gmc_subcounts w' z.val)))) := by
      apply glp0032b4_gmc_avg_congr
      intro j
      apply glp0032b4_gmc_avg_congr
      intro i
      apply glp0032b4_gmc_relabel
      rw [glp0032b4_gmc_move_total w i.val j.val i.property j.property, hw, hw']
    _ = _ := by
      simp only [glp0032b4_gmc_avg_const]
      rfl

lemma glp0032b4_gmc_avg_refresh {I S : Type*} [Fintype I] [Fintype S]
    [DecidableEq I] [Nonempty S] (i : I) (H : (I → S) → ℝ) :
    glp0032b4_gmc_avg H = glp0032b4_gmc_avg (fun s : I → S =>
      glp0032b4_gmc_avg (fun a : S => H (Function.update s i a))) := by
  let e : ((I → S) × S) ≃ ((I → S) × S) :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := by intro p; ext j <;> simp
      right_inv := by intro p; ext j <;> simp }
  have h := glp0032b4_gmc_avg_equiv e (fun p => H p.1)
  rw [glp0032b4_gmc_avg_prod, glp0032b4_gmc_avg_prod] at h
  simpa [e, glp0032b4_gmc_avg_const] using h.symm

lemma glp0032b4_gmc_avg_eval {I S : Type*} [Fintype I] [Fintype S]
    [DecidableEq I] [Nonempty S] (i : I) (H : S → ℝ) :
    glp0032b4_gmc_avg (fun s : I → S => H (s i)) = glp0032b4_gmc_avg H := by
  rw [glp0032b4_gmc_avg_refresh i]
  simp only [Function.update_self, glp0032b4_gmc_avg_const]

def glp0032b4_gmc_cons_equiv (A : Type*) (k : ℕ) :
    A × (Fin k → A) ≃ (Fin (k+1) → A) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv := by intro p; rfl
  right_inv := by intro x; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma glp0032b4_gmc_pi_law {A B C : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (k : ℕ) (g : Fin k → A → C) (h : Fin k → B → C)
    (hlaw : ∀ i (f : C → ℝ), glp0032b4_gmc_avg (fun a => f (g i a)) =
      glp0032b4_gmc_avg (fun b => f (h i b))) (f : (Fin k → C) → ℝ) :
    glp0032b4_gmc_avg (fun x : Fin k → A => f (fun i => g i (x i))) =
    glp0032b4_gmc_avg (fun x : Fin k → B => f (fun i => h i (x i))) := by
  induction k with
  | zero =>
    have he (x : Fin 0 → A) (y : Fin 0 → B) :
        (fun i => g i (x i)) = (fun i => h i (y i)) := by funext i; exact Fin.elim0 i
    obtain ⟨a⟩ := ‹Nonempty A›
    obtain ⟨b⟩ := ‹Nonempty B›
    let xa : Fin 0 → A := fun _ => a
    let xb : Fin 0 → B := fun _ => b
    calc
      _ = f (fun i => h i (xb i)) := by
        convert glp0032b4_gmc_avg_const (A := Fin 0 → A) (f (fun i => h i (xb i))) using 1
        apply glp0032b4_gmc_avg_congr
        intro x
        rw [he x xb]
      _ = _ := by
        symm
        convert glp0032b4_gmc_avg_const (A := Fin 0 → B) (f (fun i => g i (xa i))) using 1
        · apply glp0032b4_gmc_avg_congr
          intro y
          rw [he xa y]
        · rw [he xa xb]
  | succ k ih =>
    rw [← glp0032b4_gmc_avg_equiv (glp0032b4_gmc_cons_equiv A k)
        (fun x => f (fun i => g i (x i))),
      ← glp0032b4_gmc_avg_equiv (glp0032b4_gmc_cons_equiv B k)
        (fun x => f (fun i => h i (x i)))]
    rw [glp0032b4_gmc_avg_prod, glp0032b4_gmc_avg_prod]
    change (glp0032b4_gmc_avg (fun a : A => glp0032b4_gmc_avg (fun x : Fin k → A =>
      f (fun i => g i ((glp0032b4_gmc_cons_equiv A k) (a,x) i))))) =
      glp0032b4_gmc_avg (fun a : B => glp0032b4_gmc_avg (fun x : Fin k → B =>
        f (fun i => h i ((glp0032b4_gmc_cons_equiv B k) (a,x) i))))
    have he {D : Type} (a : D) (x : Fin k → D) (G : Fin (k+1) → D → C) :
        (fun i => G i ((glp0032b4_gmc_cons_equiv D k) (a,x) i)) =
        Fin.cons (G 0 a) (fun i => G i.succ (x i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hA := glp0032b4_gmc_avg_congr (fun a : A =>
      glp0032b4_gmc_avg_congr (fun x : Fin k → A => congrArg f (he a x g)))
    have hB := glp0032b4_gmc_avg_congr (fun a : B =>
      glp0032b4_gmc_avg_congr (fun x : Fin k → B => congrArg f (he a x h)))
    rw [hA, hB]
    calc
      _ = glp0032b4_gmc_avg (fun a : A => glp0032b4_gmc_avg (fun x : Fin k → B =>
          f (Fin.cons (g 0 a) (fun i => h i.succ (x i))))) := by
        apply glp0032b4_gmc_avg_congr
        intro a
        exact ih (fun i => g i.succ) (fun i => h i.succ) (fun i => hlaw i.succ)
          (fun x => f (Fin.cons (g 0 a) x))
      _ = _ := hlaw 0 (fun c => glp0032b4_gmc_avg (fun x : Fin k → B =>
          f (Fin.cons c (fun i => h i.succ (x i)))))

def glp0032b4_gmc_sample {n m : ℕ} (v : Counts) (z : Assignment n m)
    (s : Fin n → Fin n.factorial × Fin n.factorial) : ℕ → Counts
  | 0 => treatedCounts v z.val
  | t+1 =>
    let a := if ht : t < n then s ⟨t,ht⟩ else
      (⟨0,Nat.factorial_pos n⟩,⟨0,Nat.factorial_pos n⟩)
    updateTreated (reuseVector v t) (glp0032b4_gmc_sample v z s t) a.1.val a.2.val

lemma glp0032b4_gmc_sample_prefix {n m : ℕ} (v : Counts) (z : Assignment n m)
    (s s' : Fin n → Fin n.factorial × Fin n.factorial) (t : ℕ)
    (h : ∀ i : Fin n, i.val < t → s i = s' i) :
    glp0032b4_gmc_sample v z s t = glp0032b4_gmc_sample v z s' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih (fun i hi => h i (by omega))
    simp only [glp0032b4_gmc_sample, hp]
    by_cases ht : t < n
    · simp only [dif_pos ht, h ⟨t,ht⟩ (by change t < t+1; omega)]
    · simp only [dif_neg ht]

lemma glp0032b4_gmc_reuse_total (v : Counts) (t : ℕ) (ha : t ≤ v.a) (hd : t ≤ v.d) :
    (reuseVector v t).total = v.total := by dsimp [reuseVector, Counts.total]; omega

lemma glp0032b4_gmc_reuse_succ (v : Counts) (t : ℕ) :
    reuseVector (reuseVector v t) 1 = reuseVector v (t+1) := by
  apply Counts.ext <;> dsimp [reuseVector] <;> omega

lemma glp0032b4_gmc_sample_law {n m : ℕ} (v : Counts) (hn : v.total = n)
    (t : ℕ) (ha : t ≤ v.a) (hd : t ≤ v.d) (f : Counts → ℝ) :
    glp0032b4_gmc_avg (fun p : Assignment n m ×
        (Fin n → Fin n.factorial × Fin n.factorial) =>
      f (glp0032b4_gmc_sample v p.1 p.2 t)) =
    glp0032b4_gmc_avg (fun z : Assignment n m => f (treatedCounts (reuseVector v t) z.val)) := by
  letI instSeedNonemptyGLP0032B4 : Nonempty (Fin n.factorial) := ⟨⟨0,Nat.factorial_pos n⟩⟩
  induction t generalizing f with
  | zero =>
    rw [glp0032b4_gmc_avg_prod]
    dsimp only
    simp only [glp0032b4_gmc_sample, glp0032b4_gmc_avg_const]
    simp only [reuseVector, Nat.sub_zero, Nat.add_zero]
  | succ t ih =>
    have ht : t < n := by dsimp [Counts.total] at hn; omega
    let it : Fin n := ⟨t,ht⟩
    let S := Fin n.factorial × Fin n.factorial
    letI instGLP0032B4Local6 : Nonempty S := ⟨(⟨0,Nat.factorial_pos n⟩,⟨0,Nat.factorial_pos n⟩)⟩
    have hfresh (z : Assignment n m) (s : Fin n → S) (a : S) :
        glp0032b4_gmc_sample v z (Function.update s it a) t =
          glp0032b4_gmc_sample v z s t := by
      apply glp0032b4_gmc_sample_prefix
      intro i hi
      have hne : i ≠ it := by intro he; have := congrArg Fin.val he; dsimp [it] at this; omega
      simp [hne]
    have hstep (z : Assignment n m) (s : Fin n → S) (a : S) :
        glp0032b4_gmc_sample v z (Function.update s it a) (t+1) =
          updateTreated (reuseVector v t) (glp0032b4_gmc_sample v z s t) a.1.val a.2.val := by
      simp only [glp0032b4_gmc_sample, dif_pos ht, hfresh]
      simp only [show (⟨t,ht⟩ : Fin n) = it from rfl, Function.update_self]
    rw [glp0032b4_gmc_avg_prod]
    calc
      _ = glp0032b4_gmc_avg (fun z : Assignment n m =>
          glp0032b4_gmc_avg (fun s : Fin n → S => glp0032b4_gmc_avg (fun a : S =>
            f (updateTreated (reuseVector v t) (glp0032b4_gmc_sample v z s t)
              a.1.val a.2.val)))) := by
        apply glp0032b4_gmc_avg_congr
        intro z
        dsimp only
        calc
          _ = glp0032b4_gmc_avg (fun s : Fin n → S =>
              glp0032b4_gmc_avg (fun a : S =>
                f (glp0032b4_gmc_sample v z (Function.update s it a) (t+1)))) :=
            glp0032b4_gmc_avg_refresh (S := S) it
              (fun s => f (glp0032b4_gmc_sample v z s (t+1)))
          _ = _ := glp0032b4_gmc_avg_congr (fun s =>
            glp0032b4_gmc_avg_congr (fun a => congrArg f (hstep z s a)))
      _ = glp0032b4_gmc_avg (fun z : Assignment n m => glp0032b4_gmc_avg (fun a : S =>
          f (updateTreated (reuseVector v t) (treatedCounts (reuseVector v t) z.val)
            a.1.val a.2.val))) := by
        rw [glp0032b4_gmc_avg_pair]
        exact ih (by omega) (by omega) (fun q => glp0032b4_gmc_avg (fun a : S =>
          f (updateTreated (reuseVector v t) q a.1.val a.2.val)))
      _ = _ := by
        rw [glp0032b4_gmc_avg_pair]
        have hn' := (glp0032b4_gmc_reuse_total v t (by omega) (by omega)).trans hn
        have hh := glp0032b4_gmc_step (reuseVector v t) hn' m
          (by dsimp [reuseVector]; omega) (by dsimp [reuseVector]; omega) f
        simpa only [glp0032b4_gmc_reuse_succ] using hh

def glp0032b4_gmc_columns (n m k : ℕ) :
    ((Fin k → Assignment n m) ×
      (Fin n → Fin k → Fin n.factorial × Fin n.factorial)) ≃
    (Fin k → Assignment n m × (Fin n → Fin n.factorial × Fin n.factorial)) where
  toFun p i := (p.1 i, fun j => p.2 j i)
  invFun x := (fun i => (x i).1, fun j i => (x i).2 j)
  left_inv := by intro p; rfl
  right_inv := by intro x; rfl

lemma glp0032b4_gmc_column {n m k : ℕ} (v : Counts)
    (initial : Fin k → Assignment n m)
    (seeds : Fin n → Fin k → Fin n.factorial × Fin n.factorial) (t : ℕ) (i : Fin k) :
    glp0032b4_gmc_sample v (initial i) (fun j => seeds j i) t =
      reusedSamples v initial seeds t i := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [glp0032b4_gmc_sample, reusedSamples, ih]

lemma glp0032b4_gmc_reused_law {n m k : ℕ} [Nonempty (Assignment n m)]
    (v : Counts) (hn : v.total = n) (t : ℕ) (ha : t ≤ v.a) (hd : t ≤ v.d)
    (f : (Fin k → Counts) → ℝ) :
    glp0032b4_gmc_avg (fun p : (Fin k → Assignment n m) ×
        (Fin n → Fin k → Fin n.factorial × Fin n.factorial) =>
      f (reusedSamples v p.1 p.2 t)) =
    glp0032b4_gmc_avg (fun z : Fin k → Assignment n m =>
      f (fun i => treatedCounts (reuseVector v t) (z i).val)) := by
  letI instSeedColumnGLP0032B4 : Nonempty (Fin n.factorial) := ⟨⟨0,Nat.factorial_pos n⟩⟩
  let e := glp0032b4_gmc_columns n m k
  rw [← glp0032b4_gmc_avg_equiv e.symm
    (fun p => f (reusedSamples v p.1 p.2 t))]
  calc
    _ = glp0032b4_gmc_avg (fun x : Fin k → Assignment n m ×
        (Fin n → Fin n.factorial × Fin n.factorial) =>
        f (fun i => glp0032b4_gmc_sample v (x i).1 (x i).2 t)) := by
      apply glp0032b4_gmc_avg_congr
      intro x
      congr 1
      funext i
      exact (glp0032b4_gmc_column v (e.symm x).1 (e.symm x).2 t i).symm
    _ = _ := glp0032b4_gmc_pi_law k
      (fun _ (p : Assignment n m × (Fin n → Fin n.factorial × Fin n.factorial)) =>
        glp0032b4_gmc_sample v p.1 p.2 t)
      (fun _ (z : Assignment n m) => treatedCounts (reuseVector v t) z.val)
      (fun _ F => glp0032b4_gmc_sample_law v hn t ha hd F) f

lemma glp0032b4_gmc_randomStates_iff (v q : Counts) (m : ℕ) :
    q ∈ randomStates v m ↔
      q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d ∧ q.total = m := by
  constructor
  · exact random_state_facts v m q
  · rintro ⟨ha,hb,hc,hd,ht⟩
    have htotal : q.a+q.b+q.c+q.d = m := ht
    simp only [randomStates,List.mem_flatMap,List.mem_filterMap,List.mem_range]
    refine ⟨q.a,?_,q.b,?_,q.c,?_,?_⟩
    · omega
    · omega
    · omega
    · have he : m-q.a-q.b-q.c = q.d := by omega
      simp only [he,if_pos hd]

lemma glp0032b4_gmc_treated_legal (v : Counts) (m : ℕ) (z : Assignment v.total m) :
    treatedCounts v z.val ∈ randomStates v m := by
  let w := fun i : Fin v.total => canonicalPair v i.val
  have hcard := glp0032b4_gmc_canonical_type_cards v
  have hsub (u : Bool × Bool) : (z.val.filter (fun i => w i = u)).card ≤
      (Finset.univ.filter (fun i => w i = u)).card := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have ht := (glp0032b4_gmc_pair_split z.val w true).1
  have hf := (glp0032b4_gmc_pair_split z.val w false).1
  have hsum := Finset.card_filter_add_card_filter_not (s := z.val) (fun i => (w i).1 = true)
  have he : z.val.filter (fun i => ¬(w i).1 = true) =
      z.val.filter (fun i => (w i).1 = false) := by
    ext i
    cases h : (w i).1 <;> simp [h]
  rw [he, ht, hf, z.property] at hsum
  rw [glp0032b4_gmc_randomStates_iff]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [treatedCounts, w, hcard.1] using hsub (true,true)
  · simpa only [treatedCounts, w, hcard.2.1] using hsub (true,false)
  · simpa only [treatedCounts, w, hcard.2.2.1] using hsub (false,true)
  · simpa only [treatedCounts, w, hcard.2.2.2] using hsub (false,false)
  · simpa [treatedCounts, Counts.total, w, Nat.add_assoc] using hsum

lemma glp0032b4_gmc_observation (v : Counts) (m : ℕ) (z : Assignment v.total m) :
    Possible (canonicalObserved v z.val) v ∧ (canonicalObserved v z.val).total = v.total := by
  have hq := glp0032b4_gmc_treated_legal v m z
  rw [← glp0032b4_gmc_observed_bridge]
  have hp := observed_population_possible v m _ hq
  exact ⟨hp, (possible_table_facts _ _ hp).1.symm⟩

lemma glp0032b4_gmc_witness (v : Counts) (m : ℕ) (z : Assignment v.total m) :
    ∃ ij : Fin (v.total+1) × Fin (v.total+1), ∃ w : Counts, ∃ t : ℕ,
      firstOnLine (canonicalObserved v z.val)
        ((candidateNumerators (canonicalObserved v z.val)).reverse[ij.1.val]!) ij.2.val = some w ∧
      t ≤ v.total ∧ t ≤ w.a ∧ t ≤ w.d ∧ reuseVector w t = v ∧ w.total = v.total := by
  let o := canonicalObserved v z.val
  obtain ⟨hpossible,hot⟩ := glp0032b4_gmc_observation v m z
  change o.total = v.total at hot
  obtain ⟨he,hj,w,hw,t,ht,ha,hd,hv⟩ := corrected_general_loop o v hpossible
  have hem : v.effect ∈ (candidateNumerators o).reverse := by simpa using he
  obtain ⟨i,hi,hindex⟩ := List.mem_iff_getElem.mp hem
  have hlen : (candidateNumerators o).reverse.length = v.total+1 := by
    simp only [List.length_reverse, candidateNumerators, List.length_map, List.length_range]
    rw [hot]
  let ij : Fin (v.total+1) × Fin (v.total+1) :=
    (⟨i,by omega⟩,⟨v.a+v.b,by omega⟩)
  refine ⟨ij,w,t,?_,by omega,ha,hd,hv.symm,?_⟩
  · change firstOnLine o ((candidateNumerators o).reverse[i]!) (v.a+v.b) = some w
    have hget : (candidateNumerators o).reverse[i]! = v.effect := by
      simpa only [getElem!_pos (candidateNumerators o).reverse i hi] using hindex
    rw [hget]
    exact hw
  · have hp := (first_on_line_spec o _ _ w hw).1
    exact (possible_table_facts o w hp).1.trans hot

theorem glp0032b4_gmc_iid_rank (v : Counts) (m K : ℕ) (α : ℝ)
    (R : Counts → Counts → ℝ) (hm : 0 < m ∧ m < v.total) (hK : 0 < K)
    (hα : 0 ≤ α ∧ α ≤ 1) :
    uniformProb (fun ω : Assignment v.total m × (Fin K → Assignment v.total m) =>
      rankValue R (canonicalObserved v ω.1.val) v
        (fun i => treatedCounts v (ω.2 i).val) ≤ α) ≤ α := by
  let A := Assignment v.total m
  have hA : Nonempty A := by
    let z : Finset (Fin v.total) := Finset.univ.filter (fun i => i.val < m)
    have hz : z.card = m := by
      simpa [z] using glp0032b4_gmc_segment_card v.total 0 m (by omega)
    exact ⟨⟨z,hz⟩⟩
  letI instIIDAssignmentGLP0032B4 : Nonempty A := hA
  let e : (Fin (K+1) → A) ≃ A × (Fin K → A) :=
    { toFun := fun x => (x 0,fun i => x i.succ)
      invFun := fun x => Fin.cons x.1 x.2
      left_inv := by intro x; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      right_inv := by intro x; cases x; rfl }
  let s : A → ℝ := fun z => |R (canonicalObserved v z.val) v|
  have he (x : Fin (K+1) → A) :
      rankValue R (canonicalObserved v (e x).1.val) v
        (fun i => treatedCounts v ((e x).2 i).val) =
      (∑ j : Fin (K+1), if s (x 0) ≤ s (x j) then (1 : ℝ) else 0)/(K+1) := by
    unfold rankValue
    simp_rw [glp0032b4_gmc_observed_bridge]
    rw [Fin.sum_univ_succ]
    simp [e,s]
  rw [← glp0032b4_gmc_uniform_reindex e]
  simp_rw [he]
  exact glp0032b4_gmc_finite_rank K s α hα.1


lemma glp0032b4_gmc_assignment_nonempty (n m : ℕ) (hm : m ≤ n) : Nonempty (Assignment n m) := by
  let z : Finset (Fin n) := Finset.univ.filter (fun i => i.val < m)
  exact ⟨⟨z, by simpa [z] using glp0032b4_gmc_segment_card n 0 m (by omega)⟩⟩

lemma glp0032b4_gmc_uniform_avg {A : Type*} [Fintype A] (p : A → Prop) :
    uniformProb p = glp0032b4_gmc_avg (fun a => if p a then (1 : ℝ) else 0) := by
  simp [uniformProb, glp0032b4_gmc_avg]

lemma glp0032b4_gmc_uniform_avg_dec {A : Type*} [Fintype A] (p : A → Prop)
    [DecidablePred p] :
    uniformProb p = glp0032b4_gmc_avg (fun a => if p a then (1 : ℝ) else 0) := by
  rw [glp0032b4_gmc_uniform_avg]
  apply glp0032b4_gmc_avg_congr
  intro a
  by_cases h : p a <;> simp [h]

lemma glp0032b4_gmc_uniform_mono {A : Type*} [Fintype A] (p q : A → Prop)
    (h : ∀ a, p a → q a) : uniformProb p ≤ uniformProb q := by
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_le_card (show Finset.univ.filter p ⊆ Finset.univ.filter q from by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h a (Finset.mem_filter.mp ha).2⟩))

lemma glp0032b4_gmc_uniform_not {A : Type*} [Fintype A] [Nonempty A] (p : A → Prop) :
    uniformProb (fun a => ¬p a) = 1 - uniformProb p := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) p
  have hc : ((Finset.univ.filter (fun a => ¬p a)).card : ℝ) +
      (Finset.univ.filter p).card = Fintype.card A := by
    exact_mod_cast (show (Finset.univ.filter (fun a => ¬p a)).card +
      (Finset.univ.filter p).card = Fintype.card A by rw [← Finset.card_univ]; omega)
  have hn : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold uniformProb
  apply (eq_sub_iff_add_eq).2
  rw [← add_div]
  calc
    _ = (Fintype.card A : ℝ) / Fintype.card A := by
      congr 1
      convert hc using 1 <;> congr 4
    _ = 1 := div_self hn

lemma glp0032b4_gmc_pool_eval {J A B : Type} [Fintype J] [DecidableEq J]
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (i : J) (F : A × B → ℝ) :
    glp0032b4_gmc_avg (fun p : (J → A) × (J → B) => F (p.1 i,p.2 i)) =
      glp0032b4_gmc_avg F := by
  let e : ((J → A) × (J → B)) ≃ (J → A × B) :=
    { toFun := fun p j => (p.1 j,p.2 j)
      invFun := fun x => (fun j => (x j).1,fun j => (x j).2)
      left_inv := by intro p; rfl
      right_inv := by intro x; rfl }
  calc
    _ = glp0032b4_gmc_avg (fun x : J → A × B => F (x i)) :=
      (glp0032b4_gmc_avg_equiv e.symm (fun p => F (p.1 i,p.2 i))).symm
    _ = _ := glp0032b4_gmc_avg_eval i F

lemma glp0032b4_gmc_selected_law {n m k : ℕ} [Nonempty (Assignment n m)]
    (v : Counts)
    (I : Assignment n m → Fin (n+1) × Fin (n+1))
    (W : Assignment n m → Counts) (T : Assignment n m → ℕ)
    (hn : ∀ z, (W z).total = n) (ha : ∀ z, T z ≤ (W z).a)
    (hd : ∀ z, T z ≤ (W z).d) (hv : ∀ z, reuseVector (W z) (T z) = v)
    (f : Assignment n m → (Fin k → Counts) → ℝ) :
    glp0032b4_gmc_avg (fun ω : GeneralSpace n m k =>
      f ω.1 (reusedSamples (W ω.1) (ω.2.1 (I ω.1)) (ω.2.2 (I ω.1)) (T ω.1))) =
    glp0032b4_gmc_avg (fun p : Assignment n m × (Fin k → Assignment n m) =>
      f p.1 (fun i => treatedCounts v (p.2 i).val)) := by
  letI instSelectedSeedGLP0032B4 : Nonempty (Fin n.factorial) := ⟨⟨0,Nat.factorial_pos n⟩⟩
  let J := Fin (n+1) × Fin (n+1)
  let A := Fin k → Assignment n m
  let B := Fin n → Fin k → Fin n.factorial × Fin n.factorial
  conv_lhs => rw [glp0032b4_gmc_avg_prod]
  conv_rhs => rw [glp0032b4_gmc_avg_prod]
  apply glp0032b4_gmc_avg_congr
  intro z
  change (glp0032b4_gmc_avg (fun p : (J → A) × (J → B) =>
      f z (reusedSamples (W z) (p.1 (I z)) (p.2 (I z)) (T z)))) =
    glp0032b4_gmc_avg (fun a : A => f z (fun i => treatedCounts v (a i).val))
  calc
    _ = glp0032b4_gmc_avg (fun p : A × B =>
        f z (reusedSamples (W z) p.1 p.2 (T z))) :=
      glp0032b4_gmc_pool_eval (I z) (fun p : A × B => f z (reusedSamples (W z) p.1 p.2 (T z)))
    _ = _ := by
      have h := glp0032b4_gmc_reused_law (n := n) (m := m) (k := k)
        (W z) (hn z) (T z) (ha z) (hd z) (f z)
      simpa only [hv z] using h

theorem general_monte_coverage_proof (v : Counts) (m K : ℕ) (α : ℝ)
    (θ : Counts → ℝ) (R : Counts → Counts → ℝ)
    (hm : 0 < m ∧ m < v.total) (hK : 0 < K) (hα : 0 < α ∧ α < 1) :
    uniformProb (fun ω : GeneralSpace v.total m K => θ v ∈
      generalSet α θ R (canonicalObserved v ω.1.val) ω.2.1 ω.2.2) ≥ 1-α := by
  letI instGeneralAssignmentGLP0032B4 : Nonempty (Assignment v.total m) :=
    glp0032b4_gmc_assignment_nonempty v.total m hm.2.le
  letI instGeneralSeedGLP0032B4 : Nonempty (Fin v.total.factorial) :=
    ⟨⟨0,Nat.factorial_pos v.total⟩⟩
  choose I W T hline htn hta htd hreach htotal using glp0032b4_gmc_witness v m
  let E := fun ω : GeneralSpace v.total m K =>
    α < rankValue R (canonicalObserved v ω.1.val) v
      (reusedSamples (W ω.1) (ω.2.1 (I ω.1)) (ω.2.2 (I ω.1)) (T ω.1))
  have hmono : uniformProb E ≤ uniformProb (fun ω : GeneralSpace v.total m K => θ v ∈
      generalSet α θ R (canonicalObserved v ω.1.val) ω.2.1 ω.2.2) := by
    apply glp0032b4_gmc_uniform_mono
    intro ω hω
    refine ⟨I ω.1, W ω.1, hline ω.1, T ω.1, htn ω.1, hta ω.1, htd ω.1, ?_, ?_, ?_⟩
    · rw [hreach]
      exact (glp0032b4_gmc_observation v m ω.1).1
    · rw [hreach]
    · rw [hreach]
      exact hω
  have hprob : uniformProb E = uniformProb
      (fun p : Assignment v.total m × (Fin K → Assignment v.total m) =>
        α < rankValue R (canonicalObserved v p.1.val) v
          (fun i => treatedCounts v (p.2 i).val)) := by
    rw [glp0032b4_gmc_uniform_avg_dec, glp0032b4_gmc_uniform_avg_dec]
    exact glp0032b4_gmc_selected_law v I W T htotal hta htd hreach
      (fun z qs => if α < rankValue R (canonicalObserved v z.val) v qs then 1 else 0)
  have hr := glp0032b4_gmc_iid_rank v m K α R hm hK ⟨hα.1.le,hα.2.le⟩
  have hc := glp0032b4_gmc_uniform_not
    (fun p : Assignment v.total m × (Fin K → Assignment v.total m) =>
      rankValue R (canonicalObserved v p.1.val) v
        (fun i => treatedCounts v (p.2 i).val) ≤ α)
  simp only [not_le] at hc
  rw [hprob, hc] at hmono
  linarith

/-! The four-block fibre count identifies the preceding update law
with the exact finite design sums. -/

def glp0032b4_rpu_coord (q : Counts) (u : Bool × Bool) : ℕ :=
  if u.1 then (if u.2 then q.a else q.b) else (if u.2 then q.c else q.d)

lemma glp0032b4_rpu_coord_ext {p q : Counts}
    (h : ∀ u, glp0032b4_rpu_coord p u = glp0032b4_rpu_coord q u) : p = q :=
  Counts.ext (h (true,true)) (h (true,false)) (h (false,true)) (h (false,false))

lemma glp0032b4_rpu_subcounts_coord {n : ℕ} (w : PotentialTable n)
    (z : Finset (Fin n)) (u : Bool × Bool) :
    glp0032b4_rpu_coord (glp0032b4_gmc_subcounts w z) u =
      (z.filter (fun i => w i = u)).card := by
  rcases u with ⟨a,b⟩
  cases a <;> cases b <;> rfl

lemma glp0032b4_rpu_subcounts_total {n : ℕ} (w : PotentialTable n)
    (z : Finset (Fin n)) : (glp0032b4_gmc_subcounts w z).total = z.card := by
  have ht := (glp0032b4_gmc_pair_split z w true).1
  have hf := (glp0032b4_gmc_pair_split z w false).1
  have h := Finset.card_filter_add_card_filter_not (s := z) (fun i => (w i).1 = true)
  have he : z.filter (fun i => ¬(w i).1 = true) = z.filter (fun i => (w i).1 = false) := by
    ext i
    cases h : (w i).1 <;> simp [h]
  rw [he, ht, hf] at h
  simpa [glp0032b4_gmc_subcounts, Counts.total, Nat.add_assoc] using h

abbrev glp0032b4_rpu_block {n : ℕ} (w : PotentialTable n) (u : Bool × Bool) :=
  Finset.univ.filter (fun i => w i = u)

abbrev glp0032b4_rpu_parts {n : ℕ} (w : PotentialTable n) (q : Counts) :=
  ∀ u : Bool × Bool, {s : Finset (Fin n) // s ⊆ glp0032b4_rpu_block w u ∧
    s.card = glp0032b4_rpu_coord q u}

lemma glp0032b4_rpu_subset_card {I : Type} [Fintype I] [DecidableEq I] (s : Finset I) (k : ℕ) :
    Fintype.card {z : Finset I // z ⊆ s ∧ z.card = k} = s.card.choose k := by
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter (fun z : Finset I => z ⊆ s ∧ z.card = k)) =
      s.powersetCard k := by ext z; simp
  rw [he, Finset.card_powersetCard]

lemma glp0032b4_rpu_partition_filter {n : ℕ} (w : PotentialTable n)
    (X : (Bool × Bool) → Finset (Fin n))
    (hX : ∀ u, X u ⊆ glp0032b4_rpu_block w u) (u : Bool × Bool) :
    (Finset.univ.biUnion X).filter (fun i => w i = u) = X u := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨v,hi⟩,hu⟩
    have hv := (Finset.mem_filter.mp (hX v hi)).2
    have : v = u := hv.symm.trans hu
    simpa only [this] using hi
  · intro hi
    exact ⟨⟨u,hi⟩, (Finset.mem_filter.mp (hX u hi)).2⟩

noncomputable def glp0032b4_rpu_fiber_equiv {n : ℕ} (w : PotentialTable n) (q : Counts) :
    {z : Finset (Fin n) // glp0032b4_gmc_subcounts w z = q} ≃ glp0032b4_rpu_parts w q := by
  refine
    { toFun := fun z u => ⟨z.val.filter (fun i => w i = u), ?_, ?_⟩
      invFun := fun X => ⟨Finset.univ.biUnion (fun u => (X u).val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · rw [← glp0032b4_rpu_subcounts_coord, z.property]
  · apply glp0032b4_rpu_coord_ext
    intro u
    rw [glp0032b4_rpu_subcounts_coord,
      glp0032b4_rpu_partition_filter w (fun u => (X u).val) (fun u => (X u).property.1)]
    exact (X u).property.2
  · intro z
    apply Subtype.ext
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨u,hi,_⟩
      exact hi
    · intro hi
      exact ⟨w i,hi,rfl⟩
  · intro X
    funext u
    apply Subtype.ext
    exact glp0032b4_rpu_partition_filter w (fun u => (X u).val) (fun u => (X u).property.1) u

lemma glp0032b4_rpu_fiber_card {n : ℕ} (w : PotentialTable n) (q : Counts) :
    Fintype.card {z : Finset (Fin n) // glp0032b4_gmc_subcounts w z = q} =
      multiplicity (tableCounts w) q := by
  rw [Fintype.card_congr (glp0032b4_rpu_fiber_equiv w q)]
  simp only [glp0032b4_rpu_parts, Fintype.card_pi, glp0032b4_rpu_subset_card,
    Fintype.prod_prod_type, Fintype.prod_bool]
  simp [glp0032b4_rpu_coord, glp0032b4_rpu_block, multiplicity, tableCounts,
    binomial_eq_choose, mul_assoc]

lemma glp0032b4_rpu_assignment_fiber {n : ℕ} (w : PotentialTable n) (q : Counts)
    (m : ℕ) (ht : q.total = m) :
    Fintype.card {z : Assignment n m // glp0032b4_gmc_subcounts w z.val = q} =
      multiplicity (tableCounts w) q := by
  let e : {z : Assignment n m // glp0032b4_gmc_subcounts w z.val = q} ≃
      {z : Finset (Fin n) // glp0032b4_gmc_subcounts w z = q} :=
    { toFun := fun z => ⟨z.val.val,z.property⟩
      invFun := fun z => ⟨⟨z.val,by
        rw [← glp0032b4_rpu_subcounts_total w z.val, z.property, ht]⟩,z.property⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  rw [Fintype.card_congr e]
  exact glp0032b4_rpu_fiber_card w q

lemma glp0032b4_rpu_fiber_empty (v q : Counts) (m : ℕ) (ht : q.total ≠ m) :
    Fintype.card {z : Assignment v.total m // treatedCounts v z.val = q} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨?_⟩
  rintro ⟨z,hz⟩
  apply ht
  have h := (random_state_facts v m _ (glp0032b4_gmc_treated_legal v m z)).2.2.2.2
  simpa only [hz] using h

lemma glp0032b4_rpu_multiplicity_zero (v q : Counts) (m : ℕ)
    (ht : q.total = m) (hq : q ∉ randomStates v m) : multiplicity v q = 0 := by
  have h : ¬(q.a ≤ v.a ∧ q.b ≤ v.b ∧ q.c ≤ v.c ∧ q.d ≤ v.d) := by
    intro hh
    exact hq ((glp0032b4_gmc_randomStates_iff v q m).mpr ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,ht⟩)
  by_cases ha : q.a ≤ v.a
  · by_cases hb : q.b ≤ v.b
    · by_cases hc : q.c ≤ v.c
      · have hd : v.d < q.d := by omega
        simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt hd]
      · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc)]
    · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hb)]
  · simp [multiplicity, binomial_eq_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]

lemma glp0032b4_rpu_assignment_card (v q : Counts) (m : ℕ) :
    (Finset.univ.filter (fun z : Assignment v.total m => treatedCounts v z.val = q)).card =
      if q ∈ randomStates v m then multiplicity v q else 0 := by
  have hc : (Finset.univ.filter (fun z : Assignment v.total m => treatedCounts v z.val = q)).card =
      Fintype.card {z : Assignment v.total m // treatedCounts v z.val = q} := by
    simp only [Fintype.card_subtype]
  rw [hc]
  by_cases ht : q.total = m
  · have h := glp0032b4_rpu_assignment_fiber
      (fun i : Fin v.total => canonicalPair v i.val) q m ht
    have hh : Fintype.card {z : Assignment v.total m // treatedCounts v z.val = q} =
        multiplicity v q := by
      simp only [glp0032b4_gmc_canonical_counts] at h
      convert h using 1 <;> congr 4
    rw [hh]
    by_cases hq : q ∈ randomStates v m
    · simp only [if_pos hq]
    · rw [if_neg hq, glp0032b4_rpu_multiplicity_zero v q m ht hq]
  · rw [glp0032b4_rpu_fiber_empty v q m ht]
    have hq : q ∉ randomStates v m := by
      intro hq
      exact ht (random_state_facts v m q hq).2.2.2.2
    simp only [if_neg hq]

lemma glp0032b4_rpu_list_single (xs : List Counts) (hxs : xs.Nodup) (q : Counts)
    (f : Counts → ℝ) :
    (xs.map (fun x => if x = q then f x else 0)).sum = if q ∈ xs then f q else 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hn := List.nodup_cons.mp hxs
    by_cases ha : a = q
    · subst a
      simp [hn.1, ih hn.2]
    · simp only [List.map_cons, List.sum_cons, if_neg ha, zero_add, ih hn.2]
      simp only [List.mem_cons, ne_comm.mp ha, false_or]

-- State-list uniqueness.
lemma glp0032b4_rpu_flatMap_nodup
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

lemma glp0032b4_rpu_randomStates_nodup (v : Counts) (m : ℕ) :
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
    apply glp0032b4_rpu_flatMap_nodup _ (inner a) Counts.b
      List.nodup_range (fun b _ => hinner a b)
    intro b hb q hq
    exact (hinner_coords a b q hq).2
  have hmiddle_coord (a : ℕ) (q : Counts) (hq : q ∈ middle a) : q.a = a := by
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    exact (hinner_coords a b q hq).1
  change ((List.range (min v.a m+1)).flatMap middle).Nodup
  apply glp0032b4_rpu_flatMap_nodup _ middle Counts.a
    List.nodup_range (fun a _ => hmiddle a)
  intro a ha q hq
  exact hmiddle_coord a q hq


lemma glp0032b4_rpu_design_single (v q : Counts) (m : ℕ) :
    designProb v m (fun x => x = q) =
      (if q ∈ randomStates v m then (multiplicity v q : ℝ) else 0) / v.total.choose m := by
  unfold designProb
  convert congrArg (fun t : ℝ => t / v.total.choose m)
    (glp0032b4_rpu_list_single _ (glp0032b4_rpu_randomStates_nodup v m) q
      (fun x => (multiplicity v x : ℝ))) using 1 <;> congr 4
  funext x
  by_cases hx : x = q <;> simp [hx]

lemma glp0032b4_rpu_assignment_law {n : ℕ} (v : Counts) (hn : v.total = n)
    (m : ℕ) (q : Counts) :
    uniformProb (fun z : Assignment n m => treatedCounts v z.val = q) =
      designProb v m (fun x => x = q) := by
  subst n
  unfold uniformProb
  rw [Fintype.card_finset_len, Fintype.card_fin, glp0032b4_rpu_design_single]
  congr 1
  have h := congrArg (fun t : ℕ => (t : ℝ)) (glp0032b4_rpu_assignment_card v q m)
  push_cast at h
  convert h using 1 <;> congr 4

theorem reuse_preserves_uniform_law_proof (v : Counts) (m : ℕ)
    (hm : 0 < m ∧ m < v.total) (ha : 0 < v.a) (hd : 0 < v.d) (q' : Counts) :
    uniformProb (fun ω : Assignment v.total m ×
        (Fin v.total.factorial × Fin v.total.factorial) =>
      updateTreated v (treatedCounts v ω.1.val) ω.2.1.val ω.2.2.val = q') =
    designProb (reuseVector v 1) m (fun q => q = q') := by
  rw [glp0032b4_gmc_uniform_avg_dec]
  have h := glp0032b4_gmc_step v rfl m ha hd (fun q => if q = q' then 1 else 0)
  calc
    _ = glp0032b4_gmc_avg (fun z : Assignment v.total m =>
        if treatedCounts (reuseVector v 1) z.val = q' then 1 else 0) := h
    _ = uniformProb (fun z : Assignment v.total m => treatedCounts (reuseVector v 1) z.val = q') :=
      (glp0032b4_gmc_uniform_avg_dec _).symm
    _ = _ := glp0032b4_rpu_assignment_law (reuseVector v 1)
      (glp0032b4_gmc_reuse_total v 1 (by omega) (by omega)) m q'

end AronowAudit.P003.Wave1
