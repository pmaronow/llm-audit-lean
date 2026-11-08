import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096

namespace SAP.P019a.WH.W1.P.T9_L1
open SAP.P019a SAP.P019a.Bridge MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
open Classical

private theorem mean_int (f : Fin 128 → ℤ) :
    (uniformFin 128 (by norm_num)).mean (fun ω => (f ω : ℝ)) =
      ((∑ ω, f ω : ℤ) : ℝ) / 128 := by
  simp only [FiniteLaw.mean, uniformFin, Int.cast_sum]
  rw [← Finset.mul_sum]
  norm_num only [Nat.cast_ofNat]
  ring

private def suffixInt (ω : Fin 128) (j : ℕ) : ℤ :=
  ∏ i ∈ Finset.Ico (j+1) 5, AronowAudit.P019.integerSign (fairBit ω (i+2))

private def integerPrefixLocal (ω : Fin 128) (k : ℕ) : ℤ :=
  ∏ i ∈ Finset.range k, AronowAudit.P019.integerSign (fairBit ω (i+2))

private def Wint (j : Fin 5) (ω : Fin 128) : ℕ :=
  if AronowAudit.P019.integerSign (fairBit ω 1) * integerPrefixLocal ω j.val = 1 then 2 else 1

private def Yint (j : Fin 5) (ω : Fin 128) : Bool :=
  fairBit ω 0 && decide (suffixInt ω j.val = 1)

private def Vint (j : Fin 5) (ω : Fin 128) : ℕ :=
  Wint j ω + if fairBit ω 0 && fairBit ω (j.val+2) then 1 else 0

private theorem sign_cast (b : Bool) :
    (AronowAudit.P019.integerSign b : ℝ) = bitSign b := by
  cases b <;> norm_num [AronowAudit.P019.integerSign, bitSign]

private theorem prefix_cast (ω : Fin 128) (k : ℕ) :
    (integerPrefixLocal ω k : ℝ) = prefixSign ω k := by
  unfold integerPrefixLocal prefixSign
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  have hb : fairBit ω (i+2) = fairBit ω (i+2) := rfl
  cases h : fairBit ω (i+2) <;>
    simp [AronowAudit.P019.integerSign, bitSign, h, hb]

private theorem suffix_cast (ω : Fin 128) (j : ℕ) :
    (suffixInt ω j : ℝ) = suffixSign ω j := by
  simp [suffixInt, suffixSign, sign_cast]

private theorem W_eq (j : Fin 5) (ω : Fin 128) :
    (sequentialStudy j).W ω = Wint j ω := by
  have h : bitSign (fairBit ω 1) * prefixSign ω j.val = 1 ↔
      AronowAudit.P019.integerSign (fairBit ω 1) * integerPrefixLocal ω j.val = 1 := by
    have hc : ((AronowAudit.P019.integerSign (fairBit ω 1) * integerPrefixLocal ω j.val : ℤ) : ℝ) =
        bitSign (fairBit ω 1) * prefixSign ω j.val := by
      rw [Int.cast_mul, sign_cast, prefix_cast]
    constructor
    · intro hp
      have hcast : ((AronowAudit.P019.integerSign (fairBit ω 1) * integerPrefixLocal ω j.val : ℤ) : ℝ) = 1 := by
        rw [hc, hp]
      exact_mod_cast hcast
    · intro hp
      have hcast : ((AronowAudit.P019.integerSign (fairBit ω 1) * integerPrefixLocal ω j.val : ℤ) : ℝ) = 1 := by
        simpa using congrArg (fun n : ℤ => (n : ℝ)) hp
      rw [hc] at hcast
      exact_mod_cast hcast
  simp only [sequentialStudy, Wint, h]

private theorem Y_eq (j : Fin 5) (ω : Fin 128) :
    (sequentialStudy j).Y ω = Yint j ω := by
  have h : suffixSign ω j.val = 1 ↔ suffixInt ω j.val = 1 := by
    rw [← suffix_cast, ← Int.cast_one]
    exact Int.cast_inj
  simp only [sequentialStudy, Yint, h]

private theorem Z_eq (j : Fin 5) (ω : Fin 128) :
    (sequentialStudy j).Z ω = fairBit ω (j.val+2) := rfl

private theorem V_eq (j : Fin 5) (ω : Fin 128) :
    (sequentialStudy j).V ω = Vint j ω := by
  change (sequentialStudy j).W ω + _ = _
  rw [W_eq]
  rfl

private theorem law_eq (j : Fin 5) :
    (sequentialStudy j).law = uniformFin 128 (by norm_num) := rfl

private theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

private theorem prefix_sq (ω : Fin 128) (k : ℕ) : prefixSign ω k ^ 2 = 1 := by
  unfold prefixSign
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  exact bitSign_sq _

private theorem prefix_delete (j : Fin 5) (ω t : Fin 128)
    (h : ∀ k : Fin 5, k ≠ j → fairBit t (k.val+2) = fairBit ω (k.val+2)) :
    prefixSign t j.val = prefixSign ω j.val := by
  unfold prefixSign
  apply Finset.prod_congr rfl
  intro i hi
  have hik : i < j.val := Finset.mem_range.mp hi
  let hk : Fin 5 := ⟨i, by omega⟩
  have hkval : hk.val = i := rfl
  have hne : hk ≠ j := by
    intro he
    have heval := congrArg Fin.val he
    rw [hkval] at heval
    omega
  have hb := h hk hne
  rw [hkval] at hb
  exact congrArg bitSign hb

private theorem suffix_delete (j : Fin 5) (ω t : Fin 128)
    (h : ∀ k : Fin 5, k ≠ j → fairBit t (k.val+2) = fairBit ω (k.val+2)) :
    suffixSign t j.val = suffixSign ω j.val := by
  unfold suffixSign
  apply Finset.prod_congr rfl
  intro i hi
  have hik : j.val+1 ≤ i ∧ i < 5 := Finset.mem_Ico.mp hi
  let hk : Fin 5 := ⟨i, by omega⟩
  have hkval : hk.val = i := rfl
  have hne : hk ≠ j := by
    intro he
    have heval := congrArg Fin.val he
    rw [hkval] at heval
    omega
  have hb := h hk hne
  rw [hkval] at hb
  exact congrArg bitSign hb

private def cellNum (j : Fin 5) (z y : Bool) (n : Fin 3) : ℤ :=
  if j.val < 4 then
    if y then
      if z then (![16, 40, 104] : Fin 3 → ℤ) n else (![16, 24, 40] : Fin 3 → ℤ) n
    else
      if z then (![48, 88, 184] : Fin 3 → ℤ) n else (![48, 72, 120] : Fin 3 → ℤ) n
  else
    if z && y then (![32, 80, 208] : Fin 3 → ℤ) n
    else (![32, 48, 80] : Fin 3 → ℤ) n

private theorem cell_table : ∀ (j : Fin 5) (z y : Bool) (n : Fin 3),
    (∑ ω : Fin 128, if fairBit ω (j.val+2) = z ∧ Yint j ω = y
      then (Vint j ω : ℤ)^n.val else 0) = cellNum j z y n := by
  decide

private theorem cell_moment (j : Fin 5) (z y : Bool) (n : Fin 3) :
    (sequentialStudy j).law.mean (fun ω => if (sequentialStudy j).cell z y ω
      then ((sequentialStudy j).V ω : ℝ)^n.val else 0) =
        (cellNum j z y n : ℝ) / 128 := by
  have h := mean_int (fun ω =>
    if fairBit ω (j.val+2) = z ∧ Yint j ω = y
      then (Vint j ω : ℤ)^n.val else 0)
  rw [cell_table] at h
  simpa only [Study.cell, Y_eq, Z_eq, V_eq, law_eq,
    Int.cast_ite, Int.cast_pow, Int.cast_natCast, Int.cast_zero] using h

private theorem cell_mass (j : Fin 5) (z y : Bool) :
    (sequentialStudy j).law.prob ((sequentialStudy j).cell z y) =
      if j.val < 4 then (if y then 1/8 else 3/8) else 1/4 := by
  have h := cell_moment j z y 0
  simp only [Fin.val_zero, pow_zero] at h
  change (sequentialStudy j).law.mean _ = _
  rw [h]
  fin_cases j <;> cases z <;> cases y <;> norm_num [cellNum]

private theorem cell_variance (j : Fin 5) (z y : Bool) :
    (sequentialStudy j).law.cv (fun ω => ((sequentialStudy j).V ω : ℝ))
        ((sequentialStudy j).cell z y) =
      if j.val < 4 ∧ z = true ∧ y = false then 17/36 else 1/4 := by
  unfold FiniteLaw.cv FiniteLaw.ce
  rw [cell_mass]
  have h1 := cell_moment j z y 1
  have h2 := cell_moment j z y 2
  simp only [Fin.val_one, pow_one] at h1
  change (sequentialStudy j).law.mean (fun ω => if (sequentialStudy j).cell z y ω
      then ((sequentialStudy j).V ω : ℝ)^2 else 0) = _ at h2
  rw [h1, h2]
  fin_cases j <;> cases z <;> cases y <;> norm_num [cellNum]

private theorem y_table : ∀ j : Fin 5,
    (∑ ω : Fin 128, (if Yint j ω then 1 else 0 : ℤ)) =
      (if j.val < 4 then 32 else 64) := by
  decide

private theorem y_mass (j : Fin 5) :
    (sequentialStudy j).law.prob (fun ω => (sequentialStudy j).Y ω = true) =
      if j.val < 4 then 1/4 else 1/2 := by
  have h := mean_int (fun ω => if Yint j ω = true then 1 else 0)
  rw [y_table] at h
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero] at h
  change (uniformFin 128 (by norm_num)).mean _ = _
  simp only [Y_eq]
  rw [h]
  split_ifs <;> norm_num

private theorem y_mass_uniform (j : Fin 5) :
    (uniformFin 128 (by norm_num)).prob (fun ω => Yint j ω = true) =
      if j.val < 4 then 1/4 else 1/2 := by
  have h := mean_int (fun ω => if Yint j ω = true then 1 else 0)
  rw [y_table] at h
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero] at h
  change (uniformFin 128 (by norm_num)).mean _ = _
  rw [h]
  split_ifs <;> norm_num

private theorem bool_variance (P : FiniteLaw (Fin 128)) (b : Fin 128 → Bool) :
    P.variance (fun ω => bitVal (b ω)) =
      P.prob (fun ω => b ω = true) - (P.prob (fun ω => b ω = true))^2 := by
  unfold FiniteLaw.variance FiniteLaw.prob
  congr 1
  · congr 1
    funext ω
    cases b ω <;> norm_num [bitVal]

private theorem treatment_mass (j : Fin 5) :
    (sequentialStudy j).law.prob
      (fun ω => (sequentialStudy j).Z ω = true) = 1/2 := by
  change (uniformFin 128 (by norm_num)).prob
    (fun ω => fairBit ω (j.val+2) = true) = 1/2
  change (uniformFin 128 (by norm_num)).mean
    (fun ω => if fairBit ω (j.val+2) = true then 1 else 0) = 1/2
  have h := mean_int (fun ω => if fairBit ω (j.val+2) = true then 1 else 0)
  have ht : ∀ j : Fin 5,
      (∑ ω : Fin 128, (if fairBit ω (j.val+2) = true then 1 else 0 : ℤ)) = 64 := by
    decide
  rw [ht] at h
  norm_num only [Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_ofNat] at h
  exact h

private theorem z_variance (j : Fin 5) :
    (sequentialStudy j).law.variance
      (fun ω => bitVal ((sequentialStudy j).Z ω)) = 1/4 := by
  rw [bool_variance]
  have hz := treatment_mass j
  rw [hz]
  norm_num

private theorem y_variance (j : Fin 5) :
    (sequentialStudy j).law.variance
      (fun ω => bitVal ((sequentialStudy j).Y ω)) =
      if j.val < 4 then 3/16 else 1/4 := by
  rw [bool_variance, y_mass]
  split_ifs <;> norm_num

private theorem affirmative_w_table : ∀ j : Fin 5,
    (∑ ω : Fin 128, if Yint j ω = true then (Wint j ω : ℤ) else 0) =
      (if j.val < 4 then 48 else 96) := by
  decide

private theorem affirmative_w (j : Fin 5) :
    (sequentialStudy j).law.ce (fun ω => ((sequentialStudy j).W ω : ℝ))
      (fun ω => (sequentialStudy j).Y ω = true) = 3/2 := by
  unfold FiniteLaw.ce
  rw [y_mass]
  have h := mean_int (fun ω => if Yint j ω = true then (Wint j ω : ℤ) else 0)
  rw [affirmative_w_table] at h
  simp only [Int.cast_ite, Int.cast_natCast, Int.cast_zero] at h
  simp only [W_eq, Y_eq, law_eq]
  rw [h]
  split_ifs <;> norm_num

private def bits7 : Fin 7 → Fin 128 → Bool := fun i ω => fairBit ω i.val

private def bitVector (ω : Fin 128) : Fin 7 → Bool := fun i => bits7 i ω

private theorem bitVector_injective : Function.Injective bitVector := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 7
  · have hb := congrFun h ⟨k, hk⟩
    have hb' : fairBit x k = fairBit y k := by
      simpa only [bitVector, bits7] using hb
    have hp : ((x.val / 2^k) % 2 = 1) ↔ ((y.val / 2^k) % 2 = 1) := by
      constructor
      · intro hx
        have hxb : fairBit x k = true := by simp [fairBit, hx]
        rw [hb'] at hxb
        simpa [fairBit] using hxb
      · intro hy
        have hyb : fairBit y k = true := by simp [fairBit, hy]
        rw [← hb'] at hyb
        simpa [fairBit] using hyb
    simpa [Nat.testBit, Nat.shiftRight_eq_div_pow, fairBit] using hp
  · have hk' : 7 ≤ k := Nat.le_of_not_gt hk
    have hpow : 128 ≤ 2^k := by
      calc
        128 = 2^7 := by norm_num
        _ ≤ 2^k := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk'
    have hx : x.val < 2^k := lt_of_lt_of_le x.isLt hpow
    have hy : y.val < 2^k := lt_of_lt_of_le y.isLt hpow
    simp [Nat.testBit_eq_false_of_lt hx, Nat.testBit_eq_false_of_lt hy]

private theorem bitVector_bijective : Function.Bijective bitVector := by
  apply (Fintype.bijective_iff_injective_and_card bitVector).2
  constructor
  · exact bitVector_injective
  · simp

private theorem fairSeven :
    wholeFairBits (uniformFin 128 (by norm_num)) 7 bits7 := by
  intro a
  let p : Fin 128 → Prop := fun t => ∀ i, bits7 i t = a i
  obtain ⟨ω, hω⟩ := bitVector_bijective.2 a
  have hp (t : Fin 128) : p t ↔ bitVector t = a := by
    simp only [p, bitVector, funext_iff]
  have hcard : (Finset.univ.filter (fun t : Fin 128 => bitVector t = a)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨ω, ?_⟩
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ht
      exact bitVector_injective (ht.trans hω.symm)
    · rintro rfl
      exact hω
  have hs : (∑ t : Fin 128, if bitVector t = a then (1 : ℤ) else 0) = 1 := by
    calc
      _ = ∑ t ∈ Finset.univ.filter (fun t : Fin 128 => bitVector t = a), (1 : ℤ) := by
        rw [Finset.sum_filter]
      _ = 1 := by simp [hcard]
  have hsp : (∑ t : Fin 128, if p t then (1 : ℤ) else 0) =
      ∑ t : Fin 128, if bitVector t = a then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro t _
    simp only [hp]
  have hsp' : (∑ t : Fin 128, if p t then (1 : ℤ) else 0) = 1 := hsp.trans hs
  have hm := mean_int (fun t => if p t then 1 else 0)
  rw [hsp'] at hm
  change (uniformFin 128 (by norm_num)).mean
    (fun t => if p t then 1 else 0) = (1/2 : ℝ)^7
  norm_num at hm ⊢
  exact hm

private theorem per_list (j : Fin 5) :
    let S := sequentialStudy j
    (∀ ω, (S.W ω : ℝ) = 3/2+(1/2)*bitSign (fairBit ω 1)*prefixSign ω j.val ∧
      (S.W ω = 1 ∨ S.W ω = 2)) ∧
    (∀ ω t, fairBit t 0 = fairBit ω 0 → fairBit t 1 = fairBit ω 1 →
      (∀ k : Fin 5, k ≠ j → fairBit t (k.val+2) = fairBit ω (k.val+2)) →
      S.W t = S.W ω ∧ S.X t = S.X ω ∧ S.Y t = S.Y ω) ∧
    wholeCellTable S
      (fun _ y => if j.val < 4 then (if y then 1/8 else 3/8) else 1/4)
      (fun z y => if z then (if y then 5/2 else (if j.val < 4 then 11/6 else 3/2)) else 3/2)
      (fun z y => if j.val < 4 ∧ z = true ∧ y = false then 17/36 else 1/4) ∧
    S.law.prob (fun ω => S.Y ω = true) = (if j.val < 4 then 1/4 else 1/2) ∧
    S.gamma = 1/2 ∧ S.law.variance (fun ω => bitVal (S.Z ω)) = 1/4 ∧
    S.law.variance (fun ω => bitVal (S.Y ω)) = (if j.val < 4 then 3/16 else 1/4) ∧
    S.law.ce (fun ω => (S.W ω : ℝ)) (fun ω => S.Y ω = true) = 3/2 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    constructor
    · have hq : (bitSign (fairBit ω 1) * prefixSign ω j.val)^2 = 1 := by
        rw [mul_pow, bitSign_sq, prefix_sq]
        norm_num
      rcases sq_eq_one_iff.mp hq with hq | hq
      · change ((if bitSign (fairBit ω 1) * prefixSign ω j.val = 1 then 2 else 1 : ℕ) : ℝ) =
          3/2+(1/2)*bitSign (fairBit ω 1)*prefixSign ω j.val
        rw [if_pos hq]
        nlinarith [hq]
      · have hne : bitSign (fairBit ω 1) * prefixSign ω j.val ≠ 1 := by
          rw [hq]
          norm_num
        change ((if bitSign (fairBit ω 1) * prefixSign ω j.val = 1 then 2 else 1 : ℕ) : ℝ) =
          3/2+(1/2)*bitSign (fairBit ω 1)*prefixSign ω j.val
        rw [if_neg hne]
        nlinarith [hq]
    · change (if bitSign (fairBit ω 1) * prefixSign ω j.val = 1 then 2 else 1 : ℕ) = 1 ∨
        (if bitSign (fairBit ω 1) * prefixSign ω j.val = 1 then 2 else 1 : ℕ) = 2
      split_ifs <;> omega
  · intro ω t ht0 ht1 hother
    have hp := prefix_delete j ω t hother
    have hs := suffix_delete j ω t hother
    change (sequentialStudy j).W t = (sequentialStudy j).W ω ∧
      (sequentialStudy j).X t = (sequentialStudy j).X ω ∧
        (sequentialStudy j).Y t = (sequentialStudy j).Y ω
    constructor
    · change (if bitSign (fairBit t 1) * prefixSign t j.val = 1 then 2 else 1) =
        (if bitSign (fairBit ω 1) * prefixSign ω j.val = 1 then 2 else 1)
      rw [ht1, hp]
    constructor
    · change fairBit t 0 = fairBit ω 0
      exact ht0
    · change (fairBit t 0 && decide (suffixSign t j.val = 1)) =
        (fairBit ω 0 && decide (suffixSign ω j.val = 1))
      rw [ht0, hs]
  · intro z y
    constructor
    · rw [cell_mass]; split_ifs <;> norm_num
    constructor
    · exact cell_mass j z y
    constructor
    · have h1 := cell_moment j z y 1
      simp only [Fin.val_one, pow_one] at h1
      unfold Study.listMean FiniteLaw.ce
      rw [cell_mass j z y]
      change (sequentialStudy j).law.mean _ / _ = _
      rw [h1]
      fin_cases j <;> cases z <;> cases y <;> norm_num [cellNum]
    · exact cell_variance j z y
  · exact y_mass j
  · exact treatment_mass j
  · exact z_variance j
  · exact y_variance j
  · exact affirmative_w j

end

end SAP.P019a.WH.W1.P.T9_L1

open SAP.P019a.WH.W1.P.T9_L1 SAP.P019a SAP.P019a.Bridge

theorem SAP.P019a.WH.W1.T9_L1_proof : SAP.P019a.WH.W1.T9_L1 := by
  change wholeT9Finite
  refine ⟨?_, ?_⟩
  · change wholeFairBits (uniformFin 128 (by norm_num)) 7 bits7
    exact fairSeven
  · exact fun j => per_list j
