import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P004a.WH.W1.P.T3_L3

noncomputable section

open AronowAudit.P004
open scoped BigOperators Classical

def successes {n : ℕ} (z : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => z i = true)

theorem pattern_mass {n : ℕ} (q : ℝ) (s : Finset (Fin n)) :
    (∑ z : Fin n → Bool, if successes z = s then ∏ i, coin q (z i) else 0) =
      ∏ i : Fin n, (∑ b : Bool, if (b = true ↔ i ∈ s) then coin q b else 0) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.prod_ite_zero]
  congr 1
  simp only [successes, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]

theorem pattern_binomial {n : ℕ} (q : ℝ)
    (hq : (∑ b : Bool, if b = true then coin q b else 0) = q)
    (hr : (∑ b : Bool, if b = false then coin q b else 0) = 1-q)
    (s : Finset (Fin n)) :
    (∑ z : Fin n → Bool, if successes z = s then ∏ i, coin q (z i) else 0) =
      q ^ s.card * (1-q) ^ (n-s.card) := by
  rw [pattern_mass]
  have hi (i : Fin n) :
      (∑ b : Bool, if (b = true ↔ i ∈ s) then coin q b else 0) =
        if i ∈ s then q else 1-q := by
    by_cases h : i ∈ s
    · simpa [h] using hq
    · simpa [h] using hr
  simp_rw [hi]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const,
    Finset.filter_not, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Fintype.card_fin]

theorem binomial_law (n : ℕ) (q : ℝ)
    (hq : (∑ b : Bool, if b = true then coin q b else 0) = q)
    (hr : (∑ b : Bool, if b = false then coin q b else 0) = 1-q)
    (F : ℕ → ℝ) :
    (∑ z : Fin n → Bool, (∏ i, coin q (z i)) * F ((successes z).card)) =
      ∑ b ∈ Finset.range (n+1), (n.choose b : ℝ) * q^b * (1-q)^(n-b) * F b := by
  have hf := Finset.sum_fiberwise (Finset.univ : Finset (Fin n → Bool))
    successes (fun z => (∏ i, coin q (z i)) * F ((successes z).card))
  rw [← hf]
  have hs (s : Finset (Fin n)) :
      (∑ z ∈ Finset.univ.filter (fun z : Fin n → Bool => successes z = s),
        (∏ i, coin q (z i)) * F ((successes z).card)) =
      (q^s.card * (1-q)^(n-s.card)) * F s.card := by
    calc
      _ = (∑ z : Fin n → Bool, if successes z = s then ∏ i, coin q (z i) else 0) * F s.card := by
        rw [Finset.sum_mul, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : successes z = s <;> simp [hz]
      _ = _ := by rw [pattern_binomial q hq hr]
  simp_rw [hs]
  rw [← Finset.powerset_univ, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    _ = ∑ s ∈ Finset.powersetCard b (Finset.univ : Finset (Fin n)),
        q^b * (1-q)^(n-b) * F b := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_powersetCard.mp hs).2]
    _ = _ := by simp [Finset.card_powersetCard]; ring

theorem residue_sum (N a : ℕ) (ha : a < 8) :
    (∑ i : Fin N, if i.val % 8 = a then 1 else 0) =
      N / 8 + if a < N % 8 then 1 else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    have hm : N % 8 < 8 := Nat.mod_lt N (by decide)
    have hd : N % 8 + 8 * (N / 8) = N := Nat.mod_add_div N 8
    have hm' : (N+1) % 8 < 8 := Nat.mod_lt (N+1) (by decide)
    have hd' : (N+1) % 8 + 8 * ((N+1) / 8) = N+1 := Nat.mod_add_div (N+1) 8
    split_ifs <;> omega

theorem residue_card (N a : ℕ) (ha : a < 8) :
    (Finset.univ.filter (fun i : Fin N => i.val % 8 = a)).card =
      N / 8 + if a < N % 8 then 1 else 0 := by
  have hs : (Finset.univ.filter (fun i : Fin N => i.val % 8 = a)).card =
      ∑ i : Fin N, if i.val % 8 = a then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hs]
  exact residue_sum N a ha

abbrev PosIdx (r : ℕ) := {i : Fin (8*r) // i.val % 8 = 0}
abbrev NegIdx (r : ℕ) := {i : Fin (8*r) // i.val % 8 = 1}
abbrev LowIdx (r : ℕ) := {i : Fin (8*r) // ¬ activeGroup (8*r) i}

theorem pos_card (r : ℕ) [Fintype (PosIdx r)] : Fintype.card (PosIdx r) = r := by
  rw [Fintype.card_subtype]
  have h := residue_card (8*r) 0 (by decide)
  simpa using h

theorem neg_card (r : ℕ) [Fintype (NegIdx r)] : Fintype.card (NegIdx r) = r := by
  rw [Fintype.card_subtype]
  have h := residue_card (8*r) 1 (by decide)
  simpa using h

theorem high_card (r : ℕ) :
    (Finset.univ.filter (fun i : Fin (8*r) => i.val % 8 < 2)).card = 2*r := by
  have hc : (Finset.univ.filter (fun i : Fin (8*r) => i.val % 8 < 2)).card =
      ∑ i : Fin (8*r), if i.val % 8 < 2 then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hs : (∑ i : Fin (8*r), if i.val % 8 < 2 then 1 else 0) =
      ∑ i : Fin (8*r), ((if i.val % 8 = 0 then 1 else 0) +
        (if i.val % 8 = 1 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hm : i.val % 8 < 8 := Nat.mod_lt _ (by decide)
    by_cases h0 : i.val % 8 = 0 <;> by_cases h1 : i.val % 8 = 1 <;> simp_all <;> omega
  rw [hc, hs, Finset.sum_add_distrib, residue_sum (8*r) 0 (by decide), residue_sum (8*r) 1 (by decide)]
  simp [Nat.mul_mod_right]
  ring

theorem low_card (r : ℕ) [Fintype (LowIdx r)] : Fintype.card (LowIdx r) = 6*r := by
  let s : Finset (Fin (8*r)) := Finset.univ.filter (fun i => ¬ i.val % 8 < 2)
  have hs : ∀ i : Fin (8*r), i ∈ s ↔ ¬ activeGroup (8*r) i := by
    intro i
    dsimp [s]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (¬ i.val % 8 < 2) ↔ ¬ (i.val % 8 < 2)
    rfl
  have hcard : Fintype.card (LowIdx r) = s.card := by
    simpa [LowIdx] using (Fintype.card_of_subtype s hs)
  have hsum := (Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (8*r)))) (p := fun i => i.val % 8 < 2))
  have hhigh : (Finset.univ.filter (fun i : Fin (8*r) => i.val % 8 < 2)).card = 2*r := high_card r
  rw [hhigh] at hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  rw [hcard]
  dsimp [s]
  omega

def indexToSum (r : ℕ) (i : Fin (8*r)) : PosIdx r ⊕ (NegIdx r ⊕ LowIdx r) :=
  if h0 : i.val % 8 = 0 then Sum.inl ⟨i, h0⟩
  else if h1 : i.val % 8 = 1 then Sum.inr (Sum.inl ⟨i, h1⟩)
  else Sum.inr (Sum.inr ⟨i, by
    intro hh
    have hm : i.val % 8 < 8 := Nat.mod_lt _ (by decide)
    dsimp [SAP.P004a.activeGroup] at hh
    omega⟩)

def indexSplit (r : ℕ) : Fin (8*r) ≃ PosIdx r ⊕ (NegIdx r ⊕ LowIdx r) where
  toFun := indexToSum r
  invFun x := match x with
    | Sum.inl a => a.1
    | Sum.inr (Sum.inl b) => b.1
    | Sum.inr (Sum.inr c) => c.1
  left_inv i := by
    by_cases h0 : i.val % 8 = 0
    · simp [indexToSum, h0]
    · by_cases h1 : i.val % 8 = 1
      · simp [indexToSum, h0, h1]
      · have hl : ¬ SAP.P004a.activeGroup (8*r) i := by
          dsimp [SAP.P004a.activeGroup]
          have hm := Nat.mod_lt i.val (by decide : 0 < 8)
          omega
        simp [indexToSum, h0, h1, hl]
  right_inv x := by
    cases x with
    | inl a =>
        have h0 := a.2
        simp [indexToSum, h0]
    | inr y =>
      cases y with
      | inl b =>
          have h0 : b.1.val % 8 ≠ 0 := by omega
          have h1 := b.2
          simp [indexToSum, h0, h1]
      | inr c =>
          have h0 : c.1.val % 8 ≠ 0 := by
            intro hh
            have hm : c.1.val % 8 < 8 := Nat.mod_lt _ (by decide)
            have ha : SAP.P004a.activeGroup (8*r) c.1 := by
              dsimp [SAP.P004a.activeGroup]
              omega
            exact c.2 ha
          have h1 : c.1.val % 8 ≠ 1 := by
            intro hh
            have ha : SAP.P004a.activeGroup (8*r) c.1 := by
              dsimp [SAP.P004a.activeGroup]
              omega
            exact c.2 ha
          simp [indexToSum, h0, h1]


theorem indexSplit_pos (r : ℕ) (a : PosIdx r) :
    indexSplit r a.1 = Sum.inl a := by
  simp [indexSplit, indexToSum, a.2]

theorem indexSplit_neg (r : ℕ) (b : NegIdx r) :
    indexSplit r b.1 = Sum.inr (Sum.inl b) := by
  have h0 : b.1.val % 8 ≠ 0 := by omega
  simp [indexSplit, indexToSum, h0, b.2]

theorem indexSplit_low (r : ℕ) (c : LowIdx r) :
    indexSplit r c.1 = Sum.inr (Sum.inr c) := by
  have h0 : c.1.val % 8 ≠ 0 := by
    intro hh
    apply c.2
    dsimp [SAP.P004a.activeGroup]
    omega
  have h1 : c.1.val % 8 ≠ 1 := by
    intro hh
    apply c.2
    dsimp [SAP.P004a.activeGroup]
    omega
  simp [indexSplit, indexToSum, h0, h1]

def sumFunctionEquiv {α β γ : Type} :
    ((α ⊕ (β ⊕ γ)) → Bool) ≃ ((α → Bool) × ((β → Bool) × (γ → Bool))) where
  toFun f := ((fun a => f (Sum.inl a)), ((fun b => f (Sum.inr (Sum.inl b))),
    fun c => f (Sum.inr (Sum.inr c))))
  invFun x := fun s => match s with
    | Sum.inl a => x.1 a
    | Sum.inr (Sum.inl b) => x.2.1 b
    | Sum.inr (Sum.inr c) => x.2.2 c
  left_inv f := by funext s; cases s with | inl a => rfl | inr y => cases y <;> rfl
  right_inv x := by
    rcases x with ⟨f, g, h⟩
    congr 1 <;> funext i <;> rfl

def assignmentGroupsEquiv (r : ℕ) :
    Assignment (8*r) ≃ ((PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool))) :=
  (Equiv.arrowCongr (indexSplit r) (Equiv.refl Bool)).trans sumFunctionEquiv

@[simp] theorem assignmentGroupsEquiv_pos (r : ℕ) (z : Assignment (8*r))
    (i : PosIdx r) : (assignmentGroupsEquiv r z).1 i = z i.1 := by
  simp [assignmentGroupsEquiv, sumFunctionEquiv, indexSplit, indexToSum, i.2]

@[simp] theorem assignmentGroupsEquiv_neg (r : ℕ) (z : Assignment (8*r))
    (i : NegIdx r) : (assignmentGroupsEquiv r z).2.1 i = z i.1 := by
  have h0 : i.1.val % 8 ≠ 0 := by omega
  simp [assignmentGroupsEquiv, sumFunctionEquiv, indexSplit, indexToSum, h0, i.2]

@[simp] theorem assignmentGroupsEquiv_low (r : ℕ) (z : Assignment (8*r))
    (i : LowIdx r) : (assignmentGroupsEquiv r z).2.2 i = z i.1 := by
  have h0 : i.1.val % 8 ≠ 0 := by
    intro hh
    have ha : SAP.P004a.activeGroup (8*r) i.1 := by dsimp [SAP.P004a.activeGroup]; omega
    exact i.2 ha
  have h1 : i.1.val % 8 ≠ 1 := by
    intro hh
    have ha : SAP.P004a.activeGroup (8*r) i.1 := by dsimp [SAP.P004a.activeGroup]; omega
    exact i.2 ha
  simp [assignmentGroupsEquiv, sumFunctionEquiv, indexSplit, indexToSum, h0, h1]

def trueCount {α : Type} [Fintype α] (f : α → Bool) : ℕ :=
  (Finset.univ.filter (fun i => f i = true)).card

theorem trueCount_sum {α : Type} [Fintype α] (f : α → Bool) :
    trueCount f = ∑ i : α, if f i = true then 1 else 0 := by
  unfold trueCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

def posMark (r : ℕ) (z : Assignment (8*r)) :
    (PosIdx r ⊕ (NegIdx r ⊕ LowIdx r)) → ℕ
  | Sum.inl i => if z i.1 = true then 1 else 0
  | Sum.inr _ => 0

def negMark (r : ℕ) (z : Assignment (8*r)) :
    (PosIdx r ⊕ (NegIdx r ⊕ LowIdx r)) → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) => if z i.1 = true then 1 else 0
  | Sum.inr (Sum.inr _) => 0

def lowMark (r : ℕ) (z : Assignment (8*r)) :
    (PosIdx r ⊕ (NegIdx r ⊕ LowIdx r)) → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr i) => if z i.1 = true then 1 else 0

theorem pos_sum_reindex (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (z : Assignment (8*r)) :
    (∑ i : Fin (8*r), if i.val % 8 = 0 ∧ z i = true then 1 else 0) =
      ∑ i : PosIdx r, if z i.1 = true then 1 else 0 := by
  have h := Fintype.sum_equiv (indexSplit r)
    (fun i : Fin (8*r) => if i.val % 8 = 0 ∧ z i = true then (1 : ℕ) else 0)
    (posMark r z) (by
      intro i
      cases hx : indexSplit r i with
      | inl a =>
          have hv : i = a.1 := (indexSplit r).injective (by rw [hx, indexSplit_pos])
          subst i
          simp [posMark, hx, a.2]
      | inr y =>
        cases y with
        | inl b =>
            have hv : i = b.1 := (indexSplit r).injective (by rw [hx, indexSplit_neg])
            subst i
            have hb : b.1.val % 8 ≠ 0 := by omega
            simp [posMark, hx, hb]
        | inr c =>
            have hv : i = c.1 := (indexSplit r).injective (by rw [hx, indexSplit_low])
            subst i
            have h0 : c.1.val % 8 ≠ 0 := by
              intro hh
              apply c.2
              change c.1.val % 8 < 2
              omega
            simp [posMark, hx, h0])
  simpa [posMark, Fintype.sum_sum_type] using h

theorem neg_sum_reindex (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (z : Assignment (8*r)) :
    (∑ i : Fin (8*r), if i.val % 8 = 1 ∧ z i = true then 1 else 0) =
      ∑ i : NegIdx r, if z i.1 = true then 1 else 0 := by
  have h := Fintype.sum_equiv (indexSplit r)
    (fun i : Fin (8*r) => if i.val % 8 = 1 ∧ z i = true then (1 : ℕ) else 0)
    (negMark r z) (by
      intro i
      cases hx : indexSplit r i with
      | inl a =>
          have hv : i = a.1 := (indexSplit r).injective (by rw [hx, indexSplit_pos])
          subst i
          have ha : a.1.val % 8 ≠ 1 := by omega
          simp [negMark, hx, ha]
      | inr y =>
        cases y with
        | inl b =>
            have hv : i = b.1 := (indexSplit r).injective (by rw [hx, indexSplit_neg])
            subst i
            simp [negMark, hx, b.2]
        | inr c =>
            have hv : i = c.1 := (indexSplit r).injective (by rw [hx, indexSplit_low])
            subst i
            have h1 : c.1.val % 8 ≠ 1 := by
              intro hh
              apply c.2
              change c.1.val % 8 < 2
              omega
            simp [negMark, hx, h1])
  simpa [negMark, Fintype.sum_sum_type] using h

theorem low_sum_reindex (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (z : Assignment (8*r)) :
    (∑ i : Fin (8*r), if ¬ SAP.P004a.activeGroup (8*r) i ∧ z i = true then 1 else 0) =
      ∑ i : LowIdx r, if z i.1 = true then 1 else 0 := by
  have h := Fintype.sum_equiv (indexSplit r)
    (fun i : Fin (8*r) => if ¬ SAP.P004a.activeGroup (8*r) i ∧ z i = true then (1 : ℕ) else 0)
    (lowMark r z) (by
      intro i
      cases hx : indexSplit r i with
      | inl a =>
          have hv : i = a.1 := (indexSplit r).injective (by rw [hx, indexSplit_pos])
          subst i
          simp [lowMark, hx, SAP.P004a.activeGroup, a.2]
      | inr y =>
        cases y with
        | inl b =>
            have hv : i = b.1 := (indexSplit r).injective (by rw [hx, indexSplit_neg])
            subst i
            simp [lowMark, hx, SAP.P004a.activeGroup, b.2]
        | inr c =>
            have hv : i = c.1 := (indexSplit r).injective (by rw [hx, indexSplit_low])
            subst i
            simp [lowMark, hx, c.2])
  simpa [lowMark, Fintype.sum_sum_type] using h


theorem filter_card_sum {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ i : α, if p i then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem active_pos_count (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (z : Assignment (8*r)) :
    w1ActiveCount (8*r) z 0 = ∑ i : PosIdx r, if z i.1 = true then 1 else 0 := by
  unfold w1ActiveCount
  rw [filter_card_sum]
  exact pos_sum_reindex r z

theorem active_neg_count (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (z : Assignment (8*r)) :
    w1ActiveCount (8*r) z 1 = ∑ i : NegIdx r, if z i.1 = true then 1 else 0 := by
  unfold w1ActiveCount
  rw [filter_card_sum]
  exact neg_sum_reindex r z

theorem active_low_count (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (z : Assignment (8*r)) :
    w1ActiveLowCount (8*r) z = ∑ i : LowIdx r, if z i.1 = true then 1 else 0 := by
  unfold w1ActiveLowCount
  rw [filter_card_sum]
  exact low_sum_reindex r z

theorem activeP_formula (N : ℕ) :
    w1ActiveP N = fun i => if SAP.P004a.activeGroup N i then 1/2 else 1/10 := by
  funext i
  by_cases hi : SAP.P004a.activeGroup N i
  · have hdot : dot (SAP.P004a.activeO N i) SAP.P004a.activeTheta = 0 := by
      simp [SAP.P004a.dot, SAP.P004a.activeO, SAP.P004a.activeTheta, hi,
        Fin.sum_univ_succ]
    simp only [w1ActiveP, SAP.P004a.propensities, hdot, if_pos hi,
      SAP.P004a.logistic, Real.exp_zero]
    norm_num
  · have hdot : dot (SAP.P004a.activeO N i) SAP.P004a.activeTheta = -Real.log 9 := by
      simp [SAP.P004a.dot, SAP.P004a.activeO, SAP.P004a.activeTheta, hi,
        Fin.sum_univ_succ]
    simp only [w1ActiveP, SAP.P004a.propensities, hdot, if_neg hi,
      SAP.P004a.logistic, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<9)]
    norm_num

theorem activeP_pos (r : ℕ) (i : PosIdx r) : w1ActiveP (8*r) i.1 = 1/2 := by
  rw [activeP_formula]
  simp [SAP.P004a.activeGroup, i.2]

theorem activeP_neg (r : ℕ) (i : NegIdx r) : w1ActiveP (8*r) i.1 = 1/2 := by
  rw [activeP_formula]
  have hi : SAP.P004a.activeGroup (8*r) i.1 := by
    dsimp [SAP.P004a.activeGroup]
    omega
  simp [hi]

theorem activeP_low (r : ℕ) (i : LowIdx r) : w1ActiveP (8*r) i.1 = 1/10 := by
  rw [activeP_formula]
  simp [i.2]

theorem assignmentGroupsEquiv_symm_pos (r : ℕ)
    (x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool))) (i : PosIdx r) :
    (assignmentGroupsEquiv r).symm x i.1 = x.1 i := by
  have he := (assignmentGroupsEquiv r).apply_symm_apply x
  have h := congrArg (fun y => y.1 i) he
  simpa only [assignmentGroupsEquiv_pos] using h

theorem assignmentGroupsEquiv_symm_neg (r : ℕ)
    (x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool))) (i : NegIdx r) :
    (assignmentGroupsEquiv r).symm x i.1 = x.2.1 i := by
  have he := (assignmentGroupsEquiv r).apply_symm_apply x
  have h := congrArg (fun y => y.2.1 i) he
  simpa only [assignmentGroupsEquiv_neg] using h

theorem assignmentGroupsEquiv_symm_low (r : ℕ)
    (x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool))) (i : LowIdx r) :
    (assignmentGroupsEquiv r).symm x i.1 = x.2.2 i := by
  have he := (assignmentGroupsEquiv r).apply_symm_apply x
  have h := congrArg (fun y => y.2.2 i) he
  simpa only [assignmentGroupsEquiv_low] using h

theorem split_count_pos (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool))) :
    w1ActiveCount (8*r) ((assignmentGroupsEquiv r).symm x) 0 = trueCount x.1 := by
  rw [active_pos_count, trueCount_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [assignmentGroupsEquiv_symm_pos]

theorem split_count_neg (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool))) :
    w1ActiveCount (8*r) ((assignmentGroupsEquiv r).symm x) 1 = trueCount x.2.1 := by
  rw [active_neg_count, trueCount_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [assignmentGroupsEquiv_symm_neg]

theorem split_count_low (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool))) :
    w1ActiveLowCount (8*r) ((assignmentGroupsEquiv r).symm x) = trueCount x.2.2 := by
  rw [active_low_count, trueCount_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [assignmentGroupsEquiv_symm_low]

theorem binomial_law_type {α : Type} [Fintype α] [Fintype (α → Bool)] (n : ℕ)
    (hc : Fintype.card α = n) (q : ℝ)
    (hq : (∑ b : Bool, if b = true then coin q b else 0) = q)
    (hr : (∑ b : Bool, if b = false then coin q b else 0) = 1-q)
    (F : ℕ → ℝ) :
    (∑ f : α → Bool, (∏ i, coin q (f i)) * F (trueCount f)) =
      ∑ b ∈ Finset.range (n+1), (n.choose b : ℝ) * q^b * (1-q)^(n-b) * F b := by
  let e : Fin n ≃ α := (Fintype.equivFinOfCardEq hc).symm
  let ee : (α → Bool) ≃ (Fin n → Bool) :=
    (Equiv.arrowCongr e (Equiv.refl Bool)).symm
  have hsum : ∀ f : α → Bool,
      trueCount f = (successes (ee f)).card := by
    intro f
    calc
      trueCount f = ∑ i : α, if f i = true then 1 else 0 := trueCount_sum f
      _ = ∑ j : Fin n, if f (e j) = true then 1 else 0 := by
        symm
        exact Fintype.sum_equiv e _ _ (by intro j; rfl)
      _ = (successes (ee f)).card := by
        symm
        unfold successes
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        simp [ee, Equiv.arrowCongr]
  have hprod : ∀ f : α → Bool,
      (∏ i : α, coin q (f i)) = ∏ j : Fin n, coin q (ee f j) := by
    intro f
    symm
    exact Fintype.prod_equiv e _ _ (by intro j; simp [ee, Equiv.arrowCongr])
  calc
    _ = ∑ f : α → Bool, (∏ j : Fin n, coin q (ee f j)) * F ((successes (ee f)).card) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [hprod f, hsum f]
    _ = ∑ z : Fin n → Bool, (∏ j : Fin n, coin q (z j)) * F ((successes z).card) :=
      Fintype.sum_equiv ee _ _ (by intro f; rfl)
    _ = _ := binomial_law n q hq hr F

def splitWeight (r : ℕ)
    (x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool))) :
    (PosIdx r ⊕ (NegIdx r ⊕ LowIdx r)) → ℝ
  | Sum.inl i => coin (1/2) (x.1 i)
  | Sum.inr (Sum.inl i) => coin (1/2) (x.2.1 i)
  | Sum.inr (Sum.inr i) => coin (1/10) (x.2.2 i)

theorem designWeight_split (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    (x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool))) :
    designWeight (w1ActiveP (8*r)) ((assignmentGroupsEquiv r).symm x) =
      (∏ i : PosIdx r, coin (1/2) (x.1 i)) *
        ((∏ i : NegIdx r, coin (1/2) (x.2.1 i)) *
          ∏ i : LowIdx r, coin (1/10) (x.2.2 i)) := by
  unfold designWeight
  calc
    _ = ∏ s : PosIdx r ⊕ (NegIdx r ⊕ LowIdx r), splitWeight r x s :=
      Fintype.prod_equiv (indexSplit r) _ _ (by
        intro i
        cases hx : indexSplit r i with
        | inl a =>
            have hv : i = a.1 := (indexSplit r).injective (by rw [hx, indexSplit_pos])
            subst i
            simp [splitWeight, hx, activeP_pos, assignmentGroupsEquiv_symm_pos]
        | inr y =>
          cases y with
          | inl b =>
              have hv : i = b.1 := (indexSplit r).injective (by rw [hx, indexSplit_neg])
              subst i
              simp [splitWeight, hx, activeP_neg, assignmentGroupsEquiv_symm_neg]
          | inr c =>
              have hv : i = c.1 := (indexSplit r).injective (by rw [hx, indexSplit_low])
              subst i
              simp [splitWeight, hx, activeP_low, assignmentGroupsEquiv_symm_low])
    _ = _ := by simp [splitWeight, Fintype.prod_sum_type]

def assignmentWeight {α : Type} [Fintype α] (q : ℝ) (f : α → Bool) : ℝ :=
  ∏ i, coin q (f i)

theorem triple_binomial_law {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype (α → Bool)] [Fintype (β → Bool)] [Fintype (γ → Bool)]
    (n m l : ℕ) (ha : Fintype.card α = n) (hb : Fintype.card β = m)
    (hc : Fintype.card γ = l) (qH qL : ℝ)
    (hHt : (∑ b : Bool, if b = true then coin qH b else 0) = qH)
    (hHf : (∑ b : Bool, if b = false then coin qH b else 0) = 1-qH)
    (hLt : (∑ b : Bool, if b = true then coin qL b else 0) = qL)
    (hLf : (∑ b : Bool, if b = false then coin qL b else 0) = 1-qL)
    (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ x : (α → Bool) × ((β → Bool) × (γ → Bool)),
      (assignmentWeight qH x.1 * (assignmentWeight qH x.2.1 * assignmentWeight qL x.2.2)) *
        F (trueCount x.1) (trueCount x.2.1) (trueCount x.2.2)) =
    ∑ u ∈ Finset.range (n+1), (n.choose u : ℝ) * qH^u * (1-qH)^(n-u) *
      ∑ v ∈ Finset.range (m+1), (m.choose v : ℝ) * qH^v * (1-qH)^(m-v) *
        ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) * F u v j := by
  have hfactor :
      (∑ x : (α → Bool) × ((β → Bool) × (γ → Bool)),
        (assignmentWeight qH x.1 * (assignmentWeight qH x.2.1 * assignmentWeight qL x.2.2)) *
          F (trueCount x.1) (trueCount x.2.1) (trueCount x.2.2)) =
      ∑ f : α → Bool, assignmentWeight qH f *
        ∑ g : β → Bool, assignmentWeight qH g *
          ∑ h : γ → Bool, assignmentWeight qL h * F (trueCount f) (trueCount g) (trueCount h) := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro f _
    calc
      _ = ∑ g : β → Bool, assignmentWeight qH f *
          (assignmentWeight qH g * ∑ h : γ → Bool,
            assignmentWeight qL h * F (trueCount f) (trueCount g) (trueCount h)) := by
        apply Finset.sum_congr rfl
        intro g _
        calc
          _ = ∑ h : γ → Bool, (assignmentWeight qH f * assignmentWeight qH g) *
              (assignmentWeight qL h * F (trueCount f) (trueCount g) (trueCount h)) := by
            apply Finset.sum_congr rfl
            intro h _
            ring
          _ = (assignmentWeight qH f * assignmentWeight qH g) *
              ∑ h : γ → Bool, assignmentWeight qL h * F (trueCount f) (trueCount g) (trueCount h) := by
            rw [← Finset.mul_sum]
          _ = assignmentWeight qH f * (assignmentWeight qH g *
              ∑ h : γ → Bool, assignmentWeight qL h * F (trueCount f) (trueCount g) (trueCount h)) := by ring
      _ = assignmentWeight qH f * ∑ g : β → Bool, assignmentWeight qH g *
          ∑ h : γ → Bool, assignmentWeight qL h * F (trueCount f) (trueCount g) (trueCount h) := by
        rw [Finset.mul_sum]
  have hC (f : α → Bool) (g : β → Bool) :
      (∑ h : γ → Bool, assignmentWeight qL h * F (trueCount f) (trueCount g) (trueCount h)) =
        ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) * F (trueCount f) (trueCount g) j := by
    simpa [assignmentWeight] using
      (binomial_law_type (α := γ) l hc qL hLt hLf (fun j => F (trueCount f) (trueCount g) j))
  have hB (f : α → Bool) :
      (∑ g : β → Bool, assignmentWeight qH g *
        ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) *
          F (trueCount f) (trueCount g) j) =
        ∑ v ∈ Finset.range (m+1), (m.choose v : ℝ) * qH^v * (1-qH)^(m-v) *
          ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) *
            F (trueCount f) v j := by
    simpa [assignmentWeight] using
      (binomial_law_type (α := β) m hb qH hHt hHf (fun v =>
        ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) *
          F (trueCount f) v j))
  have hA :
      (∑ f : α → Bool, assignmentWeight qH f *
        ∑ v ∈ Finset.range (m+1), (m.choose v : ℝ) * qH^v * (1-qH)^(m-v) *
          ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) *
            F (trueCount f) v j) =
        ∑ u ∈ Finset.range (n+1), (n.choose u : ℝ) * qH^u * (1-qH)^(n-u) *
          ∑ v ∈ Finset.range (m+1), (m.choose v : ℝ) * qH^v * (1-qH)^(m-v) *
            ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) * F u v j := by
    simpa [assignmentWeight] using
      (binomial_law_type (α := α) n ha qH hHt hHf (fun u =>
        ∑ v ∈ Finset.range (m+1), (m.choose v : ℝ) * qH^v * (1-qH)^(m-v) *
          ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) * F u v j))
  calc
    _ = ∑ f : α → Bool, assignmentWeight qH f *
        ∑ g : β → Bool, assignmentWeight qH g *
          ∑ h : γ → Bool, assignmentWeight qL h * F (trueCount f) (trueCount g) (trueCount h) := hfactor
    _ = ∑ f : α → Bool, assignmentWeight qH f *
        ∑ g : β → Bool, assignmentWeight qH g *
          ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) *
            F (trueCount f) (trueCount g) j := by
          apply Finset.sum_congr rfl
          intro f _
          apply congrArg (fun t => assignmentWeight qH f * t)
          apply Finset.sum_congr rfl
          intro g _
          exact congrArg (fun t => assignmentWeight qH g * t) (hC f g)
    _ = ∑ f : α → Bool, assignmentWeight qH f *
        ∑ v ∈ Finset.range (m+1), (m.choose v : ℝ) * qH^v * (1-qH)^(m-v) *
          ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) *
            F (trueCount f) v j := by
          apply Finset.sum_congr rfl
          intro f _
          exact congrArg (fun t => assignmentWeight qH f * t) (hB f)
    _ = ∑ u ∈ Finset.range (n+1), (n.choose u : ℝ) * qH^u * (1-qH)^(n-u) *
        ∑ v ∈ Finset.range (m+1), (m.choose v : ℝ) * qH^v * (1-qH)^(m-v) *
          ∑ j ∈ Finset.range (l+1), (l.choose j : ℝ) * qL^j * (1-qL)^(l-j) * F u v j := hA

theorem halfFactor (n k : ℕ) (hk : k ≤ n) :
    (1/2 : ℝ)^k * (1/2)^(n-k) = (1/2)^n := by
  rw [← pow_add]
  congr 1
  omega

theorem halfPair (r u v : ℕ) (hu : u ≤ r) (hv : v ≤ r) :
    ((r.choose u : ℝ) * (1/2)^u * (1/2)^(r-u)) *
      ((r.choose v : ℝ) * (1/2)^v * (1/2)^(r-v)) =
        ((r.choose u : ℝ) * (r.choose v : ℝ)) / (2:ℝ)^(2*r) := by
  calc
    _ = (r.choose u : ℝ) * (r.choose v : ℝ) *
        ((1/2:ℝ)^u * (1/2)^(r-u)) * ((1/2:ℝ)^v * (1/2)^(r-v)) := by ring
    _ = (r.choose u : ℝ) * (r.choose v : ℝ) * (1/2:ℝ)^r * (1/2:ℝ)^r := by
      rw [halfFactor r u hu, halfFactor r v hv]
    _ = (r.choose u : ℝ) * (r.choose v : ℝ) * (1/2:ℝ)^(2*r) := by
      have hp : (1/2:ℝ)^r * (1/2:ℝ)^r = (1/2:ℝ)^(r+r) := by
        rw [← pow_add]
      calc
        _ = (r.choose u : ℝ) * (r.choose v : ℝ) *
            ((1/2:ℝ)^r * (1/2:ℝ)^r) := by ring
        _ = (r.choose u : ℝ) * (r.choose v : ℝ) * (1/2:ℝ)^(r+r) := by rw [hp]
        _ = (r.choose u : ℝ) * (r.choose v : ℝ) * (1/2:ℝ)^(2*r) := by
          rw [show r+r=2*r by omega]
    _ = (r.choose u : ℝ) * (r.choose v : ℝ) / (2:ℝ)^(2*r) := by
      rw [show (1/2:ℝ)^(2*r) = (1:ℝ)/(2:ℝ)^(2*r) by
        simpa using (div_pow (1:ℝ) (2:ℝ) (2*r)).symm]
      ring

theorem active_reindex (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    [instPF : Fintype (PosIdx r → Bool)] [instNF : Fintype (NegIdx r → Bool)]
    [instLF : Fintype (LowIdx r → Bool)]
    (F : ℕ → ℕ → ℕ → ℝ) :
    expect (w1ActiveP (8*r)) (fun z =>
      F (w1ActiveCount (8*r) z 0) (w1ActiveCount (8*r) z 1) (w1ActiveLowCount (8*r) z)) =
      ∑ x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool)),
        (assignmentWeight (1/2:ℝ) x.1 *
          (assignmentWeight (1/2:ℝ) x.2.1 * assignmentWeight (1/10:ℝ) x.2.2)) *
          F (trueCount x.1) (trueCount x.2.1) (trueCount x.2.2) := by
  classical
  change (∑ z : Assignment (8*r), designWeight (w1ActiveP (8*r)) z *
    F (w1ActiveCount (8*r) z 0) (w1ActiveCount (8*r) z 1) (w1ActiveLowCount (8*r) z)) = _
  symm
  exact Fintype.sum_equiv (assignmentGroupsEquiv r).symm
    (fun x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool)) =>
      (assignmentWeight (1/2:ℝ) x.1 *
        (assignmentWeight (1/2:ℝ) x.2.1 * assignmentWeight (1/10:ℝ) x.2.2)) *
        F (trueCount x.1) (trueCount x.2.1) (trueCount x.2.2))
    (fun z : Assignment (8*r) => designWeight (w1ActiveP (8*r)) z *
      F (w1ActiveCount (8*r) z 0) (w1ActiveCount (8*r) z 1)
        (w1ActiveLowCount (8*r) z)) (by
      intro x
      unfold assignmentWeight
      rw [designWeight_split, split_count_pos, split_count_neg, split_count_low]
      )

theorem split_assignment_range_law (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    [instPF : Fintype (PosIdx r → Bool)] [instNF : Fintype (NegIdx r → Bool)]
    [instLF : Fintype (LowIdx r → Bool)]
    (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool)),
      (assignmentWeight (1/2:ℝ) x.1 *
        (assignmentWeight (1/2:ℝ) x.2.1 * assignmentWeight (1/10:ℝ) x.2.2)) *
        F (trueCount x.1) (trueCount x.2.1) (trueCount x.2.2)) =
      ∑ u ∈ Finset.range (r+1), (r.choose u : ℝ) * (1/2)^u * (1-(1/2:ℝ))^(r-u) *
        ∑ v ∈ Finset.range (r+1), (r.choose v : ℝ) * (1/2)^v * (1-(1/2:ℝ))^(r-v) *
          ∑ j ∈ Finset.range (6*r+1), ((6*r).choose j : ℝ) * (1/10)^j *
            (1-(1/10:ℝ))^(6*r-j) * F u v j := by
  classical
  have hHt : (∑ b : Bool, if b = true then coin (1/2:ℝ) b else 0) = 1/2 := by
    norm_num [coin, Fintype.sum_bool]
  have hHf : (∑ b : Bool, if b = false then coin (1/2:ℝ) b else 0) = 1-(1/2:ℝ) := by
    norm_num [coin, Fintype.sum_bool]
  have hLt : (∑ b : Bool, if b = true then coin (1/10:ℝ) b else 0) = 1/10 := by
    norm_num [coin, Fintype.sum_bool]
  have hLf : (∑ b : Bool, if b = false then coin (1/10:ℝ) b else 0) = 1-(1/10:ℝ) := by
    norm_num [coin, Fintype.sum_bool]
  exact @triple_binomial_law
    (PosIdx r) (NegIdx r) (LowIdx r)
    instP instN instL
    instPF instNF instLF
    r r (6*r) (@pos_card r instP) (@neg_card r instN) (@low_card r instL)
    (1/2:ℝ) (1/10:ℝ) hHt hHf hLt hLf F

theorem split_assignment_range_law_normalized (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    [instPF : Fintype (PosIdx r → Bool)] [instNF : Fintype (NegIdx r → Bool)]
    [instLF : Fintype (LowIdx r → Bool)]
    (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ x : (PosIdx r → Bool) × ((NegIdx r → Bool) × (LowIdx r → Bool)),
      (assignmentWeight (1/2:ℝ) x.1 *
        (assignmentWeight (1/2:ℝ) x.2.1 * assignmentWeight (1/10:ℝ) x.2.2)) *
        F (trueCount x.1) (trueCount x.2.1) (trueCount x.2.2)) =
      ∑ u ∈ Finset.range (r+1), (r.choose u : ℝ) * (1/2)^u * (1/2)^(r-u) *
        ∑ v ∈ Finset.range (r+1), (r.choose v : ℝ) * (1/2)^v * (1/2)^(r-v) *
          ∑ j ∈ Finset.range (6*r+1), ((6*r).choose j : ℝ) * (1/10)^j *
            (9/10)^(6*r-j) * F u v j := by
  rw [split_assignment_range_law]
  have hhalf : (1:ℝ) - (1/2:ℝ) = 1/2 := by norm_num
  have hnine : (1:ℝ) - (1/10:ℝ) = 9/10 := by norm_num
  rw [hhalf, hnine]

theorem active_count_range_law (r : ℕ) [instP : Fintype (PosIdx r)]
    [instN : Fintype (NegIdx r)] [instL : Fintype (LowIdx r)]
    [instPF : Fintype (PosIdx r → Bool)] [instNF : Fintype (NegIdx r → Bool)]
    [instLF : Fintype (LowIdx r → Bool)]
    (F : ℕ → ℕ → ℕ → ℝ) :
    expect (w1ActiveP (8*r)) (fun z =>
      F (w1ActiveCount (8*r) z 0) (w1ActiveCount (8*r) z 1) (w1ActiveLowCount (8*r) z)) =
        ∑ u ∈ Finset.range (r+1), (r.choose u : ℝ) * (1/2)^u * (1/2)^(r-u) *
          ∑ v ∈ Finset.range (r+1), (r.choose v : ℝ) * (1/2)^v * (1/2)^(r-v) *
            ∑ j ∈ Finset.range (6*r+1), ((6*r).choose j : ℝ) * (1/10)^j *
              (9/10)^(6*r-j) * F u v j := by
  calc
    _ = _ := active_reindex r F
    _ = _ := split_assignment_range_law_normalized r F

theorem range_to_fin (r : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ u ∈ Finset.range (r+1), (r.choose u : ℝ) * (1/2)^u * (1/2)^(r-u) *
      ∑ v ∈ Finset.range (r+1), (r.choose v : ℝ) * (1/2)^v * (1/2)^(r-v) *
        ∑ j ∈ Finset.range (6*r+1), ((6*r).choose j : ℝ) * (1/10)^j *
          (9/10)^(6*r-j) * F u v j) =
      ∑ u : Fin (r+1), ∑ v : Fin (r+1), ∑ j : Fin (6*r+1),
        (((r.choose u.val : ℝ) * (r.choose v.val : ℝ)) / (2:ℝ)^(2*r)) *
          (((6*r).choose j.val : ℝ) * (1/10)^j.val * (9/10)^(6*r-j.val)) *
            F u.val v.val j.val := by
  classical
  simp only [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro u _
  have hu : u.val ≤ r := Nat.le_of_lt_succ u.isLt
  calc
    _ = ∑ v : Fin (r+1),
        ((r.choose u.val : ℝ) * (1/2)^u.val * (1/2)^(r-u.val)) *
          (((r.choose v.val : ℝ) * (1/2)^v.val * (1/2)^(r-v.val)) *
            ∑ j : Fin (6*r+1), ((6*r).choose j.val : ℝ) * (1/10)^j.val *
              (9/10)^(6*r-j.val) * F u.val v.val j.val) := by
      rw [Finset.mul_sum]
    _ = ∑ v : Fin (r+1), ∑ j : Fin (6*r+1),
        (((r.choose u.val : ℝ) * (r.choose v.val : ℝ)) / (2:ℝ)^(2*r)) *
          (((6*r).choose j.val : ℝ) * (1/10)^j.val * (9/10)^(6*r-j.val)) *
            F u.val v.val j.val := by
      apply Finset.sum_congr rfl
      intro v _
      have hv : v.val ≤ r := Nat.le_of_lt_succ v.isLt
      calc
        _ = ∑ j : Fin (6*r+1),
            (((r.choose u.val : ℝ) * (r.choose v.val : ℝ)) / (2:ℝ)^(2*r)) *
              (((6*r).choose j.val : ℝ) * (1/10)^j.val * (9/10)^(6*r-j.val)) *
                F u.val v.val j.val := by
          have hp := halfPair r u.val v.val hu hv
          calc
            _ = ((r.choose u.val : ℝ) * (1/2)^u.val * (1/2)^(r-u.val) *
                ((r.choose v.val : ℝ) * (1/2)^v.val * (1/2)^(r-v.val))) *
                  ∑ j : Fin (6*r+1), ((6*r).choose j.val : ℝ) * (1/10)^j.val *
                    (9/10)^(6*r-j.val) * F u.val v.val j.val := by ring
            _ = ((r.choose u.val : ℝ) * (r.choose v.val : ℝ) / (2:ℝ)^(2*r)) *
                  ∑ j : Fin (6*r+1), ((6*r).choose j.val : ℝ) * (1/10)^j.val *
                    (9/10)^(6*r-j.val) * F u.val v.val j.val := by rw [hp]
            _ = ∑ j : Fin (6*r+1),
                (((r.choose u.val : ℝ) * (r.choose v.val : ℝ)) / (2:ℝ)^(2*r)) *
                  (((6*r).choose j.val : ℝ) * (1/10)^j.val * (9/10)^(6*r-j.val)) *
                    F u.val v.val j.val := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring

end
end SAP.P004a.WH.W1.P.T3_L3

open SAP.P004a.WH.W1.P.T3_L3

theorem SAP.P004a.WH.W1.T3_L3_proof : SAP.P004a.WH.W1.T3_L3 := by
  classical
  intro r hr F
  calc
    _ = _ := active_count_range_law r F
    _ = _ := range_to_fin r F

