import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T3_L5

open SAP.P004a SAP.P004a.WH.W1
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000

lemma low_weight_sum :
    (∑ j : Fin 49,
      (Nat.choose 48 j.val : ℝ) * (1/10 : ℝ)^j.val * (9/10 : ℝ)^(48-j.val)) = 1 := by
  let f : ℕ → ℝ := fun j =>
    (Nat.choose 48 j : ℝ) * (1/10 : ℝ)^j * (9/10 : ℝ)^(48-j)
  change (∑ j : Fin 49, f j) = 1
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [f, Finset.sum_range_succ, Nat.choose]

lemma low_weight_first_moment :
    (∑ j : Fin 49,
      (Nat.choose 48 j.val : ℝ) * (1/10 : ℝ)^j.val * (9/10 : ℝ)^(48-j.val) * j.val) = 24/5 := by
  let f : ℕ → ℝ := fun j =>
    (Nat.choose 48 j : ℝ) * (1/10 : ℝ)^j * (9/10 : ℝ)^(48-j) * j
  change (∑ j : Fin 49, f j) = 24/5
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [f, Finset.sum_range_succ, Nat.choose]

lemma low_weight_second_moment :
    (∑ j : Fin 49,
      (Nat.choose 48 j.val : ℝ) * (1/10 : ℝ)^j.val * (9/10 : ℝ)^(48-j.val) * (j.val)^2) = 684/25 := by
  let f : ℕ → ℝ := fun j =>
    (Nat.choose 48 j : ℝ) * (1/10 : ℝ)^j * (9/10 : ℝ)^(48-j) * j^2
  change (∑ j : Fin 49, f j) = 684/25
  rw [Fin.sum_univ_eq_sum_range]
  norm_num [f, Finset.sum_range_succ, Nat.choose]

lemma low_weight_const (c : ℝ) :
    (∑ j : Fin 49,
      (Nat.choose 48 j.val : ℝ) * (1/10 : ℝ)^j.val * (9/10 : ℝ)^(48-j.val) * c) = c := by
  calc
    _ = (∑ j : Fin 49,
      (Nat.choose 48 j.val : ℝ) * (1/10 : ℝ)^j.val * (9/10 : ℝ)^(48-j.val)) * c := by
        rw [Finset.sum_mul]
    _ = c := by rw [low_weight_sum]; ring

lemma low_weight_quadratic (k : ℝ) :
    (∑ j : Fin 49,
      (Nat.choose 48 j.val : ℝ) * (1/10 : ℝ)^j.val * (9/10 : ℝ)^(48-j.val) *
        (k + j.val)^2) = k^2 + (48/5)*k + 684/25 := by
  let w : Fin 49 → ℝ := fun j =>
    (Nat.choose 48 j.val : ℝ) * (1/10 : ℝ)^j.val * (9/10 : ℝ)^(48-j.val)
  calc
    _ = (∑ j : Fin 49, w j * k^2) +
        (∑ j : Fin 49, (2*k) * (w j * j.val)) +
        (∑ j : Fin 49, w j * (j.val)^2) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [w]
      ring
    _ = (∑ j : Fin 49, w j) * k^2 +
        (2*k) * (∑ j : Fin 49, w j * j.val) +
        (∑ j : Fin 49, w j * (j.val)^2) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by
      dsimp [w]
      rw [low_weight_sum, low_weight_first_moment, low_weight_second_moment]
      ring

lemma active_count_zero (N : ℕ) (z : Assignment N) :
    (∑ i : Fin N, if i.val % 8 = 0 then bit (z i) else 0) =
      (w1ActiveCount N z 0 : ℝ) := by
  have hsum : (∑ i : Fin N,
      if i.val % 8 = 0 ∧ z i = true then (1 : ℝ) else 0) =
        (w1ActiveCount N z 0 : ℝ) := by
    simpa only [w1ActiveCount] using
      (Finset.sum_boole (fun i : Fin N => i.val % 8 = 0 ∧ z i = true) Finset.univ)
  calc
    _ = ∑ i : Fin N, if i.val % 8 = 0 ∧ z i = true then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hmod : i.val % 8 = 0 <;> cases hz : z i <;>
        simp [hmod, hz, bit]
    _ = _ := hsum

lemma active_count_one (N : ℕ) (z : Assignment N) :
    (∑ i : Fin N, if i.val % 8 = 1 then bit (z i) else 0) =
      (w1ActiveCount N z 1 : ℝ) := by
  have hsum : (∑ i : Fin N,
      if i.val % 8 = 1 ∧ z i = true then (1 : ℝ) else 0) =
        (w1ActiveCount N z 1 : ℝ) := by
    simpa only [w1ActiveCount] using
      (Finset.sum_boole (fun i : Fin N => i.val % 8 = 1 ∧ z i = true) Finset.univ)
  calc
    _ = ∑ i : Fin N, if i.val % 8 = 1 ∧ z i = true then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hmod : i.val % 8 = 1 <;> cases hz : z i <;>
        simp [hmod, hz, bit]
    _ = _ := hsum

lemma active_low_count (N : ℕ) (z : Assignment N) :
    (∑ i : Fin N, if ¬ activeGroup N i then bit (z i) else 0) =
      (w1ActiveLowCount N z : ℝ) := by
  have hsum : (∑ i : Fin N,
      if ¬ activeGroup N i ∧ z i = true then (1 : ℝ) else 0) =
        (w1ActiveLowCount N z : ℝ) := by
    simpa only [w1ActiveLowCount] using
      (Finset.sum_boole (fun i : Fin N => ¬ activeGroup N i ∧ z i = true) Finset.univ)
  calc
    _ = ∑ i : Fin N, if ¬ activeGroup N i ∧ z i = true then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hg : activeGroup N i <;> cases hz : z i <;>
        simp [hg, hz, bit]
    _ = _ := hsum

lemma activeK_count (N : ℕ) (z : Assignment N) :
    w1ActiveK N z = (w1ActiveCount N z 0 : ℝ) + (w1ActiveCount N z 1 : ℝ) := by
  unfold w1ActiveK
  calc
    _ = (∑ i : Fin N, if i.val % 8 = 0 then bit (z i) else 0) +
        ∑ i : Fin N, if i.val % 8 = 1 then bit (z i) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hm : i.val % 8 < 8 := Nat.mod_lt _ (by omega)
      unfold activeGroup
      by_cases h0 : i.val % 8 = 0
      · have h1 : i.val % 8 ≠ 1 := by omega
        simp [h0, h1]
      · by_cases h1 : i.val % 8 = 1
        · simp [h0, h1]
        · have hge : ¬ i.val % 8 < 2 := by omega
          simp [h0, h1, hge]
    _ = _ := by rw [active_count_zero, active_count_one]

lemma activeS_count (N : ℕ) (z : Assignment N) :
    w1ActiveS N z = (w1ActiveCount N z 0 : ℝ) - (w1ActiveCount N z 1 : ℝ) := by
  unfold w1ActiveS
  calc
    _ = (∑ i : Fin N, if i.val % 8 = 0 then bit (z i) else 0) -
        ∑ i : Fin N, if i.val % 8 = 1 then bit (z i) else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      unfold w1ActiveSign
      by_cases h0 : i.val % 8 = 0
      · have h1 : i.val % 8 ≠ 1 := by omega
        simp [h0, h1]
      · by_cases h1 : i.val % 8 = 1 <;> simp [h0, h1]
    _ = _ := by rw [active_count_zero, active_count_one]

lemma activeJ_count (N : ℕ) (z : Assignment N) :
    w1ActiveJ N z = (w1ActiveLowCount N z : ℝ) := by
  unfold w1ActiveJ
  calc
    _ = ∑ i : Fin N, if ¬ activeGroup N i then bit (z i) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hg : activeGroup N i <;> simp [hg]
    _ = _ := active_low_count N z

lemma w1ActiveSign_zero_of_not_group (N : ℕ) (i : Fin N)
    (hi : ¬ activeGroup N i) : w1ActiveSign N i = 0 := by
  unfold w1ActiveSign activeGroup at *
  split_ifs with h0 h1
  · omega
  · omega
  · rfl

lemma w1ActiveSign_sq_of_group (N : ℕ) (i : Fin N)
    (hi : activeGroup N i) : (w1ActiveSign N i)^2 = 1 := by
  unfold w1ActiveSign activeGroup at *
  have hm : i.val % 8 < 8 := Nat.mod_lt _ (by omega)
  by_cases h0 : i.val % 8 = 0
  · simp [h0]
  · have h1 : i.val % 8 = 1 := by omega
    simp [h0, h1]

lemma w1ActiveR_expand (N : ℕ) (z : Assignment N) :
    w1ActiveR N z = w1ActiveK N z -
      2 * (w1ActiveS N z / (w1ActiveNH N * w1ActivePH N z)) * w1ActiveS N z +
      w1ActiveK N z * (w1ActiveS N z / (w1ActiveNH N * w1ActivePH N z))^2 := by
  let b := w1ActiveS N z / (w1ActiveNH N * w1ActivePH N z)
  have hterm (i : Fin N) :
      (if activeGroup N i then bit (z i) * (w1ActiveSign N i-b)^2 else 0) =
        (if activeGroup N i then bit (z i) else 0) -
          2*b*(w1ActiveSign N i*bit (z i)) +
          (if activeGroup N i then bit (z i) else 0)*b^2 := by
    by_cases hi : activeGroup N i
    · have hs := w1ActiveSign_sq_of_group N i hi
      simp only [if_pos hi]
      calc
        bit (z i) * (w1ActiveSign N i-b)^2 =
            bit (z i) * ((w1ActiveSign N i)^2 -
              2*w1ActiveSign N i*b + b^2) := by ring
        _ = bit (z i) - 2*b*(w1ActiveSign N i*bit (z i)) + bit (z i)*b^2 := by
          rw [hs]
          ring
    · have hs := w1ActiveSign_zero_of_not_group N i hi
      simp [hi, hs]
  have hmid : (∑ i : Fin N, 2*b*(w1ActiveSign N i*bit (z i))) =
      2*b*(∑ i : Fin N, w1ActiveSign N i*bit (z i)) := by
    rw [Finset.mul_sum]
  have hlast : (∑ i : Fin N,
      (if activeGroup N i then bit (z i) else 0)*b^2) =
      (∑ i : Fin N, if activeGroup N i then bit (z i) else 0)*b^2 := by
    rw [Finset.sum_mul]
  change (∑ i : Fin N, if activeGroup N i then
      bit (z i) * (w1ActiveSign N i-b)^2 else 0) = _
  calc
    _ = (∑ i : Fin N, if activeGroup N i then bit (z i) else 0) -
        (∑ i : Fin N, 2*b*(w1ActiveSign N i * bit (z i))) +
        (∑ i : Fin N, (if activeGroup N i then bit (z i) else 0)*b^2) := by
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ - 2*b*(∑ i : Fin N,
          w1ActiveSign N i * bit (z i)) +
        (∑ i : Fin N, if activeGroup N i then bit (z i) else 0)*b^2 := by
      rw [hmid, hlast]
    _ = _ := by
      rw [show (∑ i : Fin N, w1ActiveSign N i * bit (z i)) = w1ActiveS N z by rfl]
      rw [show (∑ i : Fin N, if activeGroup N i then bit (z i) else 0) =
        w1ActiveK N z by rfl]

lemma armCount_true_eq (N : ℕ) (z : Assignment N) :
    armCount z true = w1ActiveK N z + w1ActiveJ N z := by
  unfold armCount w1ActiveK w1ActiveJ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hg : activeGroup N i <;> cases hz : z i <;> simp [hg, hz, bit]

def highPH (u v : ℕ) : ℝ := w1Clip (((u+v : ℕ) : ℝ)/16)

def highWeight (u v : ℕ) : ℝ :=
  (Nat.choose 8 u : ℝ) * (Nat.choose 8 v : ℝ) / (2 : ℝ)^16

def highMeanTerm (u v : ℕ) : ℝ :=
  highWeight u v * (((u : ℝ)-(v : ℝ))/(64*highPH u v))

def highSecondTerm (u v : ℕ) : ℝ :=
  highWeight u v * (((u : ℝ)-(v : ℝ))^2/(64^2*highPH u v^2))

def highResidual (u v : ℕ) : ℝ :=
  let k := (u : ℝ)+(v : ℝ)
  let s := (u : ℝ)-(v : ℝ)
  k - 2*(s/(16*highPH u v))*s + k*(s/(16*highPH u v))^2

def highPrintedTerm (u v : ℕ) : ℝ :=
  highWeight u v * highResidual u v *
    (((u+v : ℕ) : ℝ)^2 + (48/5)*((u+v : ℕ) : ℝ) + 684/25) /
    (64^4*highPH u v^4)

def highPrintedRow (u : Fin 9) : ℝ :=
  ∑ v : Fin 9, highPrintedTerm u.val v.val

def highPrintedRowValue (u : Fin 9) : ℝ :=
  if u.val = 0 then 0 else if u.val = 1 then
    14156651450258381/132145414668288000000 else if u.val = 2 then
    24982602282793987/94389581905920000000 else if u.val = 3 then
    647512743086049690413/1689059617281146880000000 else if u.val = 4 then
    1095231908526297604807/3040307311106064384000000 else if u.val = 5 then
    50492938412458948534031369/225768964492500792665702400000 else if u.val = 6 then
    78211997509254822061711111/877990417470836415922176000000 else if u.val = 7 then
    23387207022753611407827493/1128844822462503963328512000000 else
    11059287810125296469692064273/5148926513784759265172725432320000

lemma high_printed_rows : ∀ u : Fin 9, highPrintedRow u = highPrintedRowValue u := by
  intro u
  fin_cases u <;> norm_num [highPrintedRow, highPrintedRowValue, highPrintedTerm,
    highResidual, highWeight, highPH, w1Clip, Fin.sum_univ_succ, Nat.choose]

lemma high_mean_sum :
    (∑ u : Fin 9, ∑ v : Fin 9, highMeanTerm u.val v.val) = 0 := by
  norm_num [highMeanTerm, highWeight, highPH, w1Clip,
    Fin.sum_univ_succ, Nat.choose]

lemma high_second_sum :
    (∑ u : Fin 9, ∑ v : Fin 9, highSecondTerm u.val v.val) =
      1710440723/354248294400 := by
  norm_num [highSecondTerm, highWeight, highPH, w1Clip,
    Fin.sum_univ_succ, Nat.choose]

lemma high_printed_sum :
    (∑ u : Fin 9, ∑ v : Fin 9, highPrintedTerm u.val v.val) =
      17415062510218476553980121318471/12002159705791979639097262080000000 := by
  calc
    _ = ∑ u : Fin 9, highPrintedRow u := by
      apply Finset.sum_congr rfl
      intro u hu
      rfl
    _ = _ := by
      simp_rw [high_printed_rows]
      norm_num [highPrintedRowValue, Fin.sum_univ_succ]

lemma count_bridge_const (hc : T3CountStatement) (F : ℕ → ℕ → ℝ) :
    expect (w1ActiveP 64) (fun z => F (w1ActiveCount 64 z 0) (w1ActiveCount 64 z 1)) =
      ∑ u : Fin 9, ∑ v : Fin 9, highWeight u.val v.val * F u.val v.val := by
  have hbridge := hc 8 (by norm_num) (fun u v _ => F u v)
  have hbridge' : expect (w1ActiveP 64)
      (fun z => F (w1ActiveCount 64 z 0) (w1ActiveCount 64 z 1)) =
      ∑ u : Fin 9, ∑ v : Fin 9, ∑ j : Fin 49,
        ((Nat.choose 8 u.val : ℝ)*(Nat.choose 8 v.val : ℝ)/(2 : ℝ)^16) *
          ((Nat.choose 48 j.val : ℝ)*(1/10 : ℝ)^j.val*(9/10 : ℝ)^(48-j.val)) *
          F u.val v.val := by
    simpa only [show 8*8 = 64 by norm_num] using hbridge
  calc
    _ = ∑ u : Fin 9, ∑ v : Fin 9, ∑ j : Fin 49,
        ((Nat.choose 8 u.val : ℝ)*(Nat.choose 8 v.val : ℝ)/(2 : ℝ)^16) *
          ((Nat.choose 48 j.val : ℝ)*(1/10 : ℝ)^j.val*(9/10 : ℝ)^(48-j.val)) *
          F u.val v.val := hbridge'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      calc
        _ = highWeight u.val v.val *
            (∑ j : Fin 49,
              (Nat.choose 48 j.val : ℝ)*(1/10 : ℝ)^j.val*(9/10 : ℝ)^(48-j.val) *
                F u.val v.val) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              dsimp [highWeight]
              ring
        _ = highWeight u.val v.val * F u.val v.val := by
              rw [low_weight_const]

lemma count_bridge_quadratic (hc : T3CountStatement) (G : ℕ → ℕ → ℝ) :
    expect (w1ActiveP 64) (fun z =>
      G (w1ActiveCount 64 z 0) (w1ActiveCount 64 z 1) *
        (((w1ActiveCount 64 z 0 + w1ActiveCount 64 z 1 +
          w1ActiveLowCount 64 z : ℕ) : ℝ)^2)) =
      ∑ u : Fin 9, ∑ v : Fin 9,
        highWeight u.val v.val * G u.val v.val *
          (((u.val+v.val : ℕ) : ℝ)^2 +
            (48/5)*((u.val+v.val : ℕ) : ℝ) + 684/25) := by
  have hbridge := hc 8 (by norm_num) (fun u v j =>
    G u v * (((u+v+j : ℕ) : ℝ)^2))
  have hbridge' : expect (w1ActiveP 64) (fun z =>
      G (w1ActiveCount 64 z 0) (w1ActiveCount 64 z 1) *
        (((w1ActiveCount 64 z 0 + w1ActiveCount 64 z 1 +
          w1ActiveLowCount 64 z : ℕ) : ℝ)^2)) =
      ∑ u : Fin 9, ∑ v : Fin 9, ∑ j : Fin 49,
        ((Nat.choose 8 u.val : ℝ)*(Nat.choose 8 v.val : ℝ)/(2 : ℝ)^16) *
          ((Nat.choose 48 j.val : ℝ)*(1/10 : ℝ)^j.val*(9/10 : ℝ)^(48-j.val)) *
          (G u.val v.val * (((u.val+v.val+j.val : ℕ) : ℝ)^2)) := by
    simpa only [show 8*8 = 64 by norm_num] using hbridge
  calc
    _ = ∑ u : Fin 9, ∑ v : Fin 9, ∑ j : Fin 49,
        ((Nat.choose 8 u.val : ℝ)*(Nat.choose 8 v.val : ℝ)/(2 : ℝ)^16) *
          ((Nat.choose 48 j.val : ℝ)*(1/10 : ℝ)^j.val*(9/10 : ℝ)^(48-j.val)) *
          (G u.val v.val * (((u.val+v.val+j.val : ℕ) : ℝ)^2)) := hbridge'
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      let k : ℝ := (u.val+v.val : ℕ)
      calc
        _ = highWeight u.val v.val * G u.val v.val *
            (∑ j : Fin 49,
              (Nat.choose 48 j.val : ℝ)*(1/10 : ℝ)^j.val*(9/10 : ℝ)^(48-j.val) *
                (k+j.val)^2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              dsimp [highWeight, k]
              push_cast
              ring
        _ = _ := by
              rw [low_weight_quadratic]

end
end SAP.P004a.WH.W1.P.T3_L5
open SAP.P004a.WH.W1.P.T3_L5

theorem SAP.P004a.WH.W1.T3_L5_proof : SAP.P004a.WH.W1.T3_L5 := by
  intro hf hc
  rcases hf 8 (by norm_num) with
    ⟨hcounts, _, _, _, _, _, hipw, _, _, _, _, _, _, _, hprinted, _⟩
  have hNH : w1ActiveNH 64 = 16 := by
    calc
      w1ActiveNH 64 = (64 : ℝ)/4 := hcounts.1
      _ = 16 := by norm_num
  have hPH (z : Assignment 64) :
      w1ActivePH 64 z = highPH (w1ActiveCount 64 z 0) (w1ActiveCount 64 z 1) := by
    unfold w1ActivePH highPH
    rw [hNH, activeK_count]
    apply congrArg w1Clip
    push_cast
    ring
  let Fm : ℕ → ℕ → ℝ := fun u v =>
    ((u : ℝ)-(v : ℝ))/(64*highPH u v)
  have hIPWfun : w1ActiveIPW 64 = fun z =>
      Fm (w1ActiveCount 64 z 0) (w1ActiveCount 64 z 1) := by
    funext z
    rw [hipw z, activeS_count, hPH]
    rfl
  have hmean : expect (w1ActiveP 64) (w1ActiveIPW 64) = 0 := by
    rw [hIPWfun]
    calc
      _ = ∑ u : Fin 9, ∑ v : Fin 9, highWeight u.val v.val * Fm u.val v.val :=
        count_bridge_const hc Fm
      _ = 0 := by simpa [Fm, highMeanTerm] using high_mean_sum
  have hsecond : expect (w1ActiveP 64) (fun z => (w1ActiveIPW 64 z)^2) =
      1710440723/354248294400 := by
    rw [hIPWfun]
    calc
      _ = ∑ u : Fin 9, ∑ v : Fin 9,
          highWeight u.val v.val * (Fm u.val v.val)^2 :=
        count_bridge_const hc (fun u v => (Fm u v)^2)
      _ = ∑ u : Fin 9, ∑ v : Fin 9, highSecondTerm u.val v.val := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        dsimp [Fm, highSecondTerm]
        ring
      _ = _ := high_second_sum
  have hprod : expect (w1ActiveP 64) (fun z =>
      w1ActiveIPW 64 z * w1ActiveIPW 64 z) =
      1710440723/354248294400 := by
    have hfun : (fun z : Assignment 64 =>
        w1ActiveIPW 64 z * w1ActiveIPW 64 z) =
        (fun z => (w1ActiveIPW 64 z)^2) := by
      funext z
      ring
    rw [hfun]
    exact hsecond
  have hvar : variance (w1ActiveP 64) (w1ActiveIPW 64) =
      1710440723/354248294400 := by
    unfold variance cov
    rw [hprod, hmean]
    norm_num
  let G : ℕ → ℕ → ℝ := fun u v =>
    highResidual u v/(64^4*highPH u v^4)
  have hVfun : w1ActiveVPrinted 64 = fun z =>
      G (w1ActiveCount 64 z 0) (w1ActiveCount 64 z 1) *
        (((w1ActiveCount 64 z 0 + w1ActiveCount 64 z 1 +
          w1ActiveLowCount 64 z : ℕ) : ℝ)^2) := by
    funext z
    rw [hprinted z, armCount_true_eq, w1ActiveR_expand, activeK_count,
      activeJ_count, activeS_count, hNH, hPH]
    push_cast
    dsimp [G, highResidual]
    ring
  have hexpectPrinted : expect (w1ActiveP 64) (w1ActiveVPrinted 64) =
      17415062510218476553980121318471/12002159705791979639097262080000000 := by
    rw [hVfun]
    calc
      _ = ∑ u : Fin 9, ∑ v : Fin 9,
          highWeight u.val v.val * G u.val v.val *
            (((u.val+v.val : ℕ) : ℝ)^2 +
              (48/5)*((u.val+v.val : ℕ) : ℝ) + 684/25) :=
        count_bridge_quadratic hc G
      _ = ∑ u : Fin 9, ∑ v : Fin 9, highPrintedTerm u.val v.val := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        dsimp [G, highPrintedTerm]
        ring
      _ = _ := high_printed_sum
  exact ⟨hvar, hexpectPrinted⟩
