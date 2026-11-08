import SAP.P004b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T27_L4

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

private def boolSetEquiv (α : Type*) [Fintype α] [DecidableEq α] (a : Bool) :
    (α → Bool) ≃ Finset α where
  toFun f := Finset.univ.filter (fun x => f x = a)
  invFun s x := if x ∈ s then a else !a
  left_inv f := by
    funext x
    by_cases h : f x = a
    · simp [h]
    · have hh : f x = !a := by cases a <;> cases hf : f x <;> simp_all
      rw [hh]
      simp [h]
  right_inv s := by
    ext x
    simp

private lemma bool_count_fiber (α : Type*) [Fintype α] [DecidableEq α]
    (a : Bool) (k : ℕ) :
    (Finset.univ.filter (fun f : α → Bool =>
      (Finset.univ.filter (fun x => f x = a)).card = k)).card =
      Nat.choose (Fintype.card α) k := by
  classical
  let e := boolSetEquiv α a
  let h₁ : {f : α → Bool // (Finset.univ.filter (fun x => f x = a)).card = k} ≃
      {s : Finset α // s.card = k} :=
    { toFun := fun f => ⟨e f.1, by simpa [e, boolSetEquiv] using f.2⟩
      invFun := fun s => ⟨e.symm s.1, by simpa [e, boolSetEquiv] using s.2⟩
      left_inv := by intro f; apply Subtype.ext; simp [e]
      right_inv := by intro s; apply Subtype.ext; simp [e] }
  have hcard : Fintype.card {s : Finset α // s.card = k} =
      Nat.choose (Fintype.card α) k := by
    rw [Fintype.card_of_subtype (Finset.univ.powersetCard k) (by
      intro s
      simp [Finset.mem_powersetCard])]
    simp [Finset.card_powersetCard]
  calc
    (Finset.univ.filter (fun f : α → Bool =>
        (Finset.univ.filter (fun x => f x = a)).card = k)).card =
        Fintype.card {f : α → Bool // (Finset.univ.filter (fun x => f x = a)).card = k} := by
      symm
      exact Fintype.card_of_subtype _ (by intro f; simp)
    _ = Fintype.card {s : Finset α // s.card = k} := Fintype.card_congr h₁
    _ = Nat.choose (Fintype.card α) k := hcard

private def boolCount {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Bool) (a : Bool) : ℕ :=
  (Finset.univ.filter (fun x => f x = a)).card

private lemma boolCount_real {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Bool) (a : Bool) :
    (∑ x, if f x = a then (1 : ℝ) else 0) = (boolCount f a : ℝ) := by
  classical
  unfold boolCount
  rw [← Finset.sum_filter]
  simp

private lemma armCount_join {N : ℕ} (i : Fin N) (a : Bool)
    (u : {j : Fin N // j ≠ i} → Bool) :
    armCount (AronowAudit.P004.joinAssignment i a u) a =
      (boolCount u a : ℝ) + 1 := by
  classical
  unfold armCount
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => if AronowAudit.P004.joinAssignment i a u j = a then (1 : ℝ) else 0)
    (Finset.mem_univ i)]
  rw [Finset.sum_subtype (p := fun j : Fin N => j ≠ i) (F := inferInstance)
    (Finset.univ.erase i) (by intro j; simp)
    (fun j => if AronowAudit.P004.joinAssignment i a u j = a then (1 : ℝ) else 0)]
  have hrest (j : {j : Fin N // j ≠ i}) :
      AronowAudit.P004.joinAssignment i a u j = u j := by
    simp [AronowAudit.P004.joinAssignment, j.property]
  rw [show AronowAudit.P004.joinAssignment i a u i = a by
    simp [AronowAudit.P004.joinAssignment]]
  simp_rw [hrest]
  rw [boolCount_real]
  simp

private lemma fair_weight (N : ℕ) (z : Assignment N) :
    designWeight (fun _ : Fin N => (1/2 : ℝ)) z = ((2 : ℝ)^N)⁻¹ := by
  unfold designWeight
  calc
    (∏ i, coin (1/2) (z i)) = ∏ i, (1/2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      cases z i <;> norm_num [coin]
    _ = (1/2 : ℝ)^N := by simp [Finset.prod_const]
    _ = ((2 : ℝ)^N)⁻¹ := by
      rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]

private lemma fair_prob_card {N : ℕ} (E : Assignment N → Prop) :
    prob (fun _ : Fin N => (1/2 : ℝ)) E =
      ((Finset.univ.filter E).card : ℝ) / (2 : ℝ)^N := by
  classical
  unfold prob expect
  simp_rw [fair_weight]
  calc
    (∑ z, ((2 : ℝ)^N)⁻¹ * (if E z then 1 else 0)) =
        ((2 : ℝ)^N)⁻¹ * ((Finset.univ.filter E).card : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_boole]
    _ = ((Finset.univ.filter E).card : ℝ) / (2 : ℝ)^N := by ring

private lemma expect_add_local {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) :
    expect p (fun z => X z + Y z) = expect p X + expect p Y := by
  unfold expect
  simp only [mul_add, Finset.sum_add_distrib]

private lemma expect_sub_local {N : ℕ} (p : Fin N → ℝ) (X Y : Assignment N → ℝ) :
    expect p (fun z => X z - Y z) = expect p X - expect p Y := by
  unfold expect
  simp only [mul_sub, Finset.sum_sub_distrib]

private lemma expect_mul_local {N : ℕ} (p : Fin N → ℝ) (c : ℝ) (X : Assignment N → ℝ) :
    expect p (fun z => c * X z) = c * expect p X := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

private lemma expect_const_local {N : ℕ} (p : Fin N → ℝ) (c : ℝ) :
    expect p (fun _ => c) = c := by
  simpa [AronowAudit.P004.expect, AronowAudit.P004.designWeight,
    AronowAudit.P004.coin, expect, designWeight, coin] using
      (AronowAudit.P004.expect_const p c)

private lemma expect_div_local {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) (c : ℝ) :
    expect p (fun z => X z/c) = expect p X/c := by
  simpa [AronowAudit.P004.expect, AronowAudit.P004.designWeight,
    AronowAudit.P004.coin, expect, designWeight, coin] using
      (AronowAudit.P004.expect_div p X c)

private lemma variance_div_local {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) (c : ℝ) :
    variance p (fun z => X z/c) = variance p X/c^2 := by
  simpa [AronowAudit.P004.expect, AronowAudit.P004.designWeight,
    AronowAudit.P004.coin, AronowAudit.P004.cov, AronowAudit.P004.variance,
    expect, designWeight, coin, cov, variance] using
      (AronowAudit.P004.variance_div p X c)

private lemma cov_centered_local {N : ℕ} (p : Fin N → ℝ)
    (X Y : Assignment N → ℝ) :
    cov p X Y = expect p (fun z => (X z-expect p X)*(Y z-expect p Y)) := by
  simpa [AronowAudit.P004.expect, AronowAudit.P004.designWeight,
    AronowAudit.P004.coin, AronowAudit.P004.cov,
    expect, designWeight, coin, cov] using
      (AronowAudit.P004.cov_centered p X Y)

private lemma selected_update_local {N : ℕ} (F : Assignment N → ℝ)
    (i : Fin N) (a : Bool) :
    expect (fun _ : Fin N => (1/2 : ℝ)) (fun z => if z i = a then F z else 0) =
      (1/2 : ℝ) * expect (fun _ : Fin N => (1/2 : ℝ))
        (fun z => F (Function.update z i a)) := by
  simpa [AronowAudit.P004.expect, AronowAudit.P004.designWeight,
    AronowAudit.P004.coin, expect, designWeight, coin] using
      (AronowAudit.P004.Wave1.T27_selected_update F i a)

private def firstIndex (N : ℕ) (hN : 0 < N) : Fin N := ⟨0, hN⟩

private lemma wholeFirst_eq_index {N : ℕ} (hN : 0 < N) (z : Assignment N) :
    wholeFirst z = z (firstIndex N hN) := by
  simp [wholeFirst, firstIndex, hN]

private lemma armCount_update {N : ℕ} (z : Assignment N) (i : Fin N)
    (a b : Bool) :
    armCount (Function.update z i b) a =
      armCount z a - (if z i = a then (1 : ℝ) else 0) +
        (if b = a then (1 : ℝ) else 0) := by
  classical
  unfold armCount
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => if Function.update z i b j = a then (1 : ℝ) else 0)
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add Finset.univ
    (fun j => if z j = a then (1 : ℝ) else 0) (Finset.mem_univ i)]
  have hrest :
      (∑ j ∈ Finset.univ.erase i, if Function.update z i b j = a then (1 : ℝ) else 0) =
      ∑ j ∈ Finset.univ.erase i, if z j = a then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest]
  simp [Function.update]

private lemma card_except_first {N : ℕ} (hN : 0 < N) :
    Fintype.card {j : Fin N // j ≠ firstIndex N hN} = N-1 := by
  classical
  rw [Fintype.card_of_subtype (Finset.univ.erase (firstIndex N hN)) (by
    intro j
    simp)]
  simp [Finset.card_erase_of_mem, firstIndex]

private lemma forced_count_fiber_card {N : ℕ} (hN : 0 < N) (a : Bool) (k : ℕ) :
    (Finset.univ.filter (fun z : Assignment N =>
      armCount (Function.update z (firstIndex N hN) a) a = (k+1 : ℕ))).card =
      2 * Nat.choose (N-1) k := by
  classical
  let i := firstIndex N hN
  let R := {j : Fin N // j ≠ i}
  let remCount : (R → Bool) → ℕ := fun u => boolCount u a
  let fullProp : Assignment N → Prop := fun z =>
    armCount (Function.update z i a) a = (k+1 : ℕ)
  let pairProp : Bool × (R → Bool) → Prop := fun p => remCount p.2 = k
  have hcount (z : Assignment N) : fullProp z ↔ pairProp (AronowAudit.P004.splitAssignment i z) := by
    dsimp [fullProp, pairProp, remCount, i, R]
    have hj : Function.update z (firstIndex N hN) a =
        AronowAudit.P004.joinAssignment (firstIndex N hN) a
          (fun j => z j) := by
      funext j
      by_cases hj : j = firstIndex N hN
      · subst j
        simp [AronowAudit.P004.joinAssignment, firstIndex]
      · rw [Function.update_of_ne hj]
        simp only [AronowAudit.P004.joinAssignment, dif_neg hj]
    rw [hj, armCount_join]
    have hs : (fun j : {j : Fin N // j ≠ firstIndex N hN} => z j) =
        (AronowAudit.P004.splitAssignment (firstIndex N hN) z).2 := rfl
    rw [hs]
    constructor
    · intro h
      have : (boolCount (AronowAudit.P004.splitAssignment (firstIndex N hN) z).2 a : ℝ) + 1 =
          (k : ℝ) + 1 := by simpa using h
      have hc : (boolCount (AronowAudit.P004.splitAssignment (firstIndex N hN) z).2 a : ℝ) = k := by
        linarith
      exact_mod_cast hc
    · intro h
      have hc : (boolCount (AronowAudit.P004.splitAssignment (firstIndex N hN) z).2 a : ℝ) = k := by
        exact_mod_cast h
      simp only [Nat.cast_add, Nat.cast_one]
      linarith
  let E := AronowAudit.P004.splitAssignment i
  have he : {z : Assignment N // fullProp z} ≃
      {p : Bool × (R → Bool) // pairProp p} := E.subtypeEquiv hcount
  let ep : {p : Bool × (R → Bool) // pairProp p} ≃
      Bool × {u : R → Bool // remCount u = k} :=
    { toFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
      invFun := fun b => ⟨(b.1, b.2.1), b.2.2⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro p; apply Prod.ext <;> rfl }
  have hrem : Fintype.card {u : R → Bool // remCount u = k} = Nat.choose (N-1) k := by
    have hcard : Fintype.card R = N-1 := card_except_first hN
    rw [Fintype.card_of_subtype
      (Finset.univ.filter (fun u : R → Bool => remCount u = k)) (by intro u; simp)]
    change (Finset.univ.filter (fun u : R → Bool => boolCount u a = k)).card = _
    rw [← hcard]
    exact bool_count_fiber R a k
  have hf : Fintype.card {z : Assignment N // fullProp z} =
      Fintype.card {p : Bool × (R → Bool) // pairProp p} := Fintype.card_congr he
  have hp : Fintype.card {p : Bool × (R → Bool) // pairProp p} =
      Fintype.card Bool * Fintype.card {u : R → Bool // remCount u = k} := by
    rw [Fintype.card_congr ep, Fintype.card_prod]
  calc
    (Finset.univ.filter fullProp).card = Fintype.card {z : Assignment N // fullProp z} := by
      symm
      exact Fintype.card_of_subtype (Finset.univ.filter fullProp) (by intro z; simp)
    _ = Fintype.card {p : Bool × (R → Bool) // pairProp p} := hf
    _ = Fintype.card Bool * Fintype.card {u : R → Bool // remCount u = k} := hp
    _ = 2 * Nat.choose (N-1) k := by simp [hrem]

private lemma conditional_count_mass {N : ℕ} (hN : 0 < N) (a : Bool) (k : ℕ) :
    wholeSparseCond N a (fun z => wholeSparseQ z = (k+1 : ℕ)) =
      (Nat.choose (N-1) k : ℝ) / (2 : ℝ)^(N-1) := by
  classical
  let i := firstIndex N hN
  let p := fun _ : Fin N => (1/2 : ℝ)
  have hsel : prob p (fun z => wholeFirst z = a ∧ wholeSparseQ z = (k+1 : ℕ)) =
      (1/2 : ℝ) * prob p (fun z => armCount (Function.update z i a) a = (k+1 : ℕ)) := by
    have he : (fun z => if wholeFirst z = a ∧ wholeSparseQ z = (k+1 : ℕ)
        then (1 : ℝ) else 0) =
        (fun z => if z i = a then
          (if armCount z a = (k+1 : ℕ) then (1 : ℝ) else 0) else 0) := by
      funext z
      simp only [wholeSparseQ, wholeFirst_eq_index hN z]
      by_cases hz : z i = a
      · have hz' : z (firstIndex N hN) = a := by simpa [i] using hz
        simp [hz, hz']
      · have hz' : z (firstIndex N hN) ≠ a := by simpa [i] using hz
        simp [hz, hz']
    calc
      prob p (fun z => wholeFirst z = a ∧ wholeSparseQ z = (k+1 : ℕ)) =
          expect p (fun z => if wholeFirst z = a ∧ wholeSparseQ z = (k+1 : ℕ)
            then (1 : ℝ) else 0) := by simp [prob]
      _ = expect p (fun z => if z i = a then
          (if armCount z a = (k+1 : ℕ) then (1 : ℝ) else 0) else 0) := by rw [he]
      _ = (1/2 : ℝ) * expect p
          (fun z => if armCount (Function.update z i a) a = (k+1 : ℕ)
            then (1 : ℝ) else 0) := by rw [selected_update_local]
      _ = (1/2 : ℝ) * prob p
          (fun z => armCount (Function.update z i a) a = (k+1 : ℕ)) := by simp [prob]
  have hfiber := forced_count_fiber_card hN a k
  have hprob := fair_prob_card (fun z : Assignment N =>
    armCount (Function.update z i a) a = (k+1 : ℕ))
  have hpow : (2 : ℝ)^N = (2 : ℝ)^(N-1) * 2 := by
    rw [show N = (N-1)+1 by omega, pow_succ]
    norm_num
  unfold wholeSparseCond
  rw [hsel, hprob, hfiber]
  rw [show ((2 * Nat.choose (N-1) k : ℕ) : ℝ) =
      2 * (Nat.choose (N-1) k : ℝ) by norm_num]
  rw [hpow]
  field_simp
  <;> ring

private lemma forced_count_moments {N : ℕ} (hN : 0 < N) (a : Bool) :
    expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => armCount (Function.update z (firstIndex N hN) a) a) =
        (N : ℝ)/2+1/2 ∧
    variance (fun _ : Fin N => (1/2 : ℝ))
      (fun z => armCount (Function.update z (firstIndex N hN) a) a) =
        ((N : ℝ)-1)/4 := by
  classical
  let p := fun _ : Fin N => (1/2 : ℝ)
  let i := firstIndex N hN
  let C : Assignment N → ℝ := fun z => armCount z a
  let I : Assignment N → ℝ := fun z => if z i = a then 1 else 0
  let Q : Assignment N → ℝ := fun z => armCount (Function.update z i a) a
  have hcnt0 := AronowAudit.P004.Wave1.T27_count_moments (N := N) a
  have hcnt : expect p C = (N : ℝ)/2 ∧ variance p C = (N : ℝ)/4 := by
    simpa [p, C, AronowAudit.P004.expect, AronowAudit.P004.designWeight,
      AronowAudit.P004.coin, AronowAudit.P004.armCount,
      AronowAudit.P004.variance, AronowAudit.P004.cov,
      expect, designWeight, coin, armCount, variance, cov] using hcnt0
  have hI : expect p I = 1/2 := by
    have hs := selected_update_local (fun _ : Assignment N => (1 : ℝ)) i a
    simpa [p, I, expect_const_local] using hs
  have hqfun : Q = fun z => C z + 1 - I z := by
    funext z
    dsimp [Q, C, I]
    rw [armCount_update]
    simp
    <;> ring
  have hQmean : expect p Q = (N : ℝ)/2+1/2 := by
    rw [hqfun, expect_sub_local, expect_add_local,
      expect_const_local, hcnt.1, hI]
    ring
  have hCI : expect p (fun z => C z * I z) = (N : ℝ)/4+1/4 := by
    have he : (fun z => C z * I z) =
        (fun z => if z i = a then C z else 0) := by
      funext z
      dsimp [I]
      split_ifs <;> simp
    rw [he, selected_update_local, hQmean]
    ring
  have hC2 : expect p (fun z => C z^2) = (N : ℝ)/4+((N : ℝ)/2)^2 := by
    have hv := hcnt.2
    have hmul : (fun z => C z * C z) = fun z => C z^2 := by
      funext z
      ring
    unfold variance cov at hv
    rw [hmul] at hv
    rw [hcnt.1] at hv
    nlinarith [hv]
  have hQ2 : expect p (fun z => Q z^2) = (N : ℝ)^2/4+3*(N : ℝ)/4 := by
    have hfun : (fun z => Q z^2) =
        (fun z => C z^2+2*C z-2*(C z*I z)+1-I z) := by
      funext z
      rw [hqfun]
      have hIi : I z ^ 2 = I z := by dsimp [I]; split_ifs <;> norm_num
      nlinarith [hIi]
    rw [hfun, expect_sub_local, expect_add_local,
      expect_sub_local, expect_add_local,
      expect_mul_local, expect_mul_local,
      expect_const_local, hC2, hcnt.1, hCI, hI]
    ring
  have hQvar : variance p Q = ((N : ℝ)-1)/4 := by
    unfold variance cov
    rw [show (fun z => Q z * Q z) = (fun z => Q z^2) by funext z; ring, hQ2, hQmean]
    ring
  constructor
  · simpa [p, Q, i] using hQmean
  · simpa [p, Q, i] using hQvar

private lemma selected_whole_expect {N : ℕ} (hN : 0 < N) (a : Bool)
    (F : ℝ → ℝ) :
    2 * expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => if wholeFirst z = a then F (wholeSparseQ z) else 0) =
    expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => F (armCount (Function.update z (firstIndex N hN) a) a)) := by
  classical
  let i := firstIndex N hN
  have he : (fun z => if wholeFirst z = a then F (wholeSparseQ z) else 0) =
      (fun z => if z i = a then F (armCount z a) else 0) := by
    funext z
    simp only [wholeSparseQ, wholeFirst_eq_index hN z]
    by_cases hz : z i = a
    · have hz' : z (firstIndex N hN) = a := by simpa [i] using hz
      simp [hz, hz']
    · have hz' : z (firstIndex N hN) ≠ a := by simpa [i] using hz
      simp [hz, hz']
  rw [he, selected_update_local]
  ring

private lemma conditional_moments {N : ℕ} (hN : 0 < N) (a : Bool) :
    2 * expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => if wholeFirst z = a then wholeSparseQ z/N else 0) =
        1/2+1/(2*(N : ℝ)) ∧
    2 * expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => if wholeFirst z = a then
        (wholeSparseQ z/N-(1/2+1/(2*(N : ℝ))))^2 else 0) =
        ((N : ℝ)-1)/(4*(N : ℝ)^2) := by
  let p := fun _ : Fin N => (1/2 : ℝ)
  let i := firstIndex N hN
  let Q : Assignment N → ℝ := fun z => armCount (Function.update z i a) a
  have hm := forced_count_moments hN a
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmean : expect p (fun z => Q z/N) = 1/2+1/(2*(N : ℝ)) := by
    rw [expect_div_local, hm.1]
    field_simp [hn]
    <;> ring
  have hvar : variance p (fun z => Q z/N) = ((N : ℝ)-1)/(4*(N : ℝ)^2) := by
    rw [variance_div_local, hm.2]
    field_simp [hn]
    <;> ring
  have hcenter : variance p (fun z => Q z/N) =
      expect p (fun z => (Q z/N-(1/2+1/(2*(N : ℝ))))^2) := by
    have h := cov_centered_local p (fun z => Q z/N) (fun z => Q z/N)
    rw [hmean] at h
    simpa [variance, pow_two] using h
  constructor
  · rw [selected_whole_expect hN a (fun x => x/(N : ℝ)), expect_div_local, hm.1]
    field_simp [hn]
    <;> ring
  · rw [selected_whole_expect hN a
      (fun x => (x/(N : ℝ)-(1/2+1/(2*(N : ℝ))))^2)]
    rw [← hcenter, hvar]

private lemma armCount_card {N : ℕ} (z : Assignment N) (a : Bool) :
    armCount z a = (boolCount z a : ℝ) := by
  exact boolCount_real z a

private lemma wholeSparseQ_endpoint {N : ℕ} (hN : 3 ≤ N) (z : Assignment N) :
    ¬ (2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1) ↔
      wholeSparseQ z = 1 ∨ wholeSparseQ z = N := by
  let c := boolCount z (wholeFirst z)
  have hq : wholeSparseQ z = (c : ℝ) := by
    simp [wholeSparseQ, c, armCount_card]
  have hcpos : 0 < c := by
    dsimp [c, boolCount]
    apply Finset.card_pos.mpr
    refine ⟨firstIndex N (by omega), ?_⟩
    simp [wholeFirst_eq_index (by omega) z]
  have hcle : c ≤ N := by
    dsimp [c, boolCount]
    calc
      (Finset.univ.filter (fun i => z i = wholeFirst z)).card ≤ Finset.univ.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = N := by simp
  have hsub : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    simp
  constructor
  · intro hout
    by_cases hc1 : c = 1
    · left
      rw [hq, hc1]
      norm_num
    · by_cases hcN : c = N
      · right
        rw [hq, hcN]
      · have hnat : 2 ≤ c ∧ c ≤ N-1 := by omega
        have hv : 2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1 := by
          constructor
          · rw [hq]
            exact_mod_cast hnat.1
          · rw [hq, ← hsub]
            exact_mod_cast hnat.2
        exact (hout hv).elim
  · rintro (hc1 | hcN) ⟨hl, hu⟩
    · rw [hc1] at hl
      norm_num at hl
    · rw [hcN] at hu
      have hpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      linarith

private lemma prob_congr_prop {N : ℕ} (p : Fin N → ℝ)
    {E F : Assignment N → Prop} (h : ∀ z, E z ↔ F z) : prob p E = prob p F := by
  unfold prob
  congr 1
  funext z
  simp [h z]

private lemma prob_or_disjoint {N : ℕ} (p : Fin N → ℝ)
    (E F : Assignment N → Prop) (hdis : ∀ z, ¬(E z ∧ F z)) :
    prob p (fun z => E z ∨ F z) = prob p E + prob p F := by
  unfold prob
  rw [← expect_add_local]
  congr 1
  funext z
  by_cases he : E z
  · by_cases hf : F z
    · exact (hdis z ⟨he,hf⟩).elim
    · simp [he,hf]
  · by_cases hf : F z <;> simp [he,hf]

private lemma prob_split_first {N : ℕ} (hN : 0 < N) (E : Assignment N → Prop) :
    prob (fun _ : Fin N => (1/2 : ℝ)) E =
      prob (fun _ : Fin N => (1/2 : ℝ)) (fun z => wholeFirst z = true ∧ E z) +
      prob (fun _ : Fin N => (1/2 : ℝ)) (fun z => wholeFirst z = false ∧ E z) := by
  let p := fun _ : Fin N => (1/2 : ℝ)
  have he : ∀ z, E z ↔
      (wholeFirst z = true ∧ E z) ∨ (wholeFirst z = false ∧ E z) := by
    intro z
    cases wholeFirst z <;> simp
  rw [prob_congr_prop p he]
  apply prob_or_disjoint p _ _
  intro z hboth
  rcases hboth with ⟨⟨ht, _⟩, ⟨hf, _⟩⟩
  cases wholeFirst z <;> simp_all

private lemma endpoint_joint_prob {N : ℕ} (hN : 0 < N) (a : Bool) (k : ℕ)
    (hk : k = 0 ∨ k = N-1) :
    prob (fun _ : Fin N => (1/2 : ℝ))
      (fun z => wholeFirst z = a ∧ wholeSparseQ z = (k+1 : ℕ)) =
        ((2 : ℝ)^N)⁻¹ := by
  have hm := conditional_count_mass hN a k
  unfold wholeSparseCond at hm
  have hc : (Nat.choose (N-1) k : ℝ) = 1 := by
    rcases hk with rfl | hk
    · simp
    · subst k
      simp
  rw [hc] at hm
  have hpow : (2 : ℝ)^N = (2 : ℝ)^(N-1) * 2 := by
    rw [show N = (N-1)+1 by omega, pow_succ]
    norm_num
  calc
    prob (fun _ : Fin N => (1/2 : ℝ))
        (fun z => wholeFirst z = a ∧ wholeSparseQ z = (k+1 : ℕ)) =
        (2 * prob (fun _ : Fin N => (1/2 : ℝ))
          (fun z => wholeFirst z = a ∧ wholeSparseQ z = (k+1 : ℕ)))/2 := by ring
    _ = (((2 : ℝ)^(N-1))⁻¹)/2 := by rw [hm]; field_simp
    _ = ((2 : ℝ)^N)⁻¹ := by rw [hpow]; field_simp

private lemma prob_endpoint_branch {N : ℕ} (hN : 3 ≤ N) (a : Bool) :
    prob (fun _ : Fin N => (1/2 : ℝ))
      (fun z => wholeFirst z = a ∧ ¬(2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1)) =
      2*((2 : ℝ)^N)⁻¹ := by
  let p := fun _ : Fin N => (1/2 : ℝ)
  have he : ∀ z : Assignment N, (wholeFirst z = a ∧
      ¬(2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1)) ↔
      (wholeFirst z = a ∧ wholeSparseQ z = 1) ∨
      (wholeFirst z = a ∧ wholeSparseQ z = N) := by
    intro z
    rw [wholeSparseQ_endpoint hN z]
    simp [and_or_left]
  rw [prob_congr_prop p he]
  have hdis : ∀ z : Assignment N, ¬((wholeFirst z = a ∧ wholeSparseQ z = 1) ∧
      (wholeFirst z = a ∧ wholeSparseQ z = N)) := by
    intro z ⟨⟨_, h1⟩, ⟨_, hNq⟩⟩
    have hNreal : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  rw [prob_or_disjoint p _ _ hdis]
  have hfirst0 := endpoint_joint_prob (by omega : 0 < N) a 0 (Or.inl rfl)
  have hfirst : prob (fun _ : Fin N => (1/2 : ℝ))
      (fun z => wholeFirst z = a ∧ wholeSparseQ z = 1) = ((2 : ℝ)^N)⁻¹ := by
    simpa using hfirst0
  have hlast0 := endpoint_joint_prob (by omega : 0 < N) a (N-1) (Or.inr rfl)
  have hlast : prob (fun _ : Fin N => (1/2 : ℝ))
      (fun z => wholeFirst z = a ∧ wholeSparseQ z = N) = ((2 : ℝ)^N)⁻¹ := by
    simpa [show N-1+1=N by omega] using hlast0
  rw [hfirst, hlast]
  ring

end SAP.P004b.WH.W3.P.T27_L4

open SAP.P004b SAP.P004b.WH.W3

theorem SAP.P004b.WH.W3.T27_L4_proof : SAP.P004b.WH.W3.T27_L4 := by
  intro N hN
  have hpos : 0 < N := by omega
  constructor
  · intro a k hk
    exact SAP.P004b.WH.W3.P.T27_L4.conditional_count_mass hpos a k
  constructor
  · calc
      prob (fun _ : Fin N => (1/2 : ℝ))
          (fun z => ¬(2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1)) =
          prob (fun _ : Fin N => (1/2 : ℝ))
            (fun z => wholeFirst z = true ∧
              ¬(2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1)) +
          prob (fun _ : Fin N => (1/2 : ℝ))
            (fun z => wholeFirst z = false ∧
              ¬(2 ≤ wholeSparseQ z ∧ wholeSparseQ z ≤ (N : ℝ)-1)) :=
        SAP.P004b.WH.W3.P.T27_L4.prob_split_first hpos _
      _ = 2*((2 : ℝ)^N)⁻¹+2*((2 : ℝ)^N)⁻¹ := by
        rw [SAP.P004b.WH.W3.P.T27_L4.prob_endpoint_branch hN true,
          SAP.P004b.WH.W3.P.T27_L4.prob_endpoint_branch hN false]
      _ = 4/(2 : ℝ)^N := by field_simp <;> ring
  · intro a
    exact SAP.P004b.WH.W3.P.T27_L4.conditional_moments hpos a
