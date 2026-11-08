import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T3_L4

open SAP.P004a.WH.W1
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Classical
noncomputable section
set_option maxHeartbeats 1000000

private theorem activeSign_sq_of_group (N : ℕ) (i : Fin N)
    (hi : activeGroup N i) : (w1ActiveSign N i)^2 = 1 := by
  have hm := Nat.mod_lt i.val (by omega : 0 < 8)
  unfold activeGroup at hi
  unfold w1ActiveSign
  by_cases h0 : i.val % 8 = 0
  · simp [h0]
  · by_cases h1 : i.val % 8 = 1
    · simp [h0, h1]
    · have : i.val % 8 < 2 := hi
      omega

private theorem activeSign_eq_zero_of_not_group (N : ℕ) (i : Fin N)
    (hi : ¬ activeGroup N i) : w1ActiveSign N i = 0 := by
  have hm := Nat.mod_lt i.val (by omega : 0 < 8)
  unfold activeGroup at hi
  unfold w1ActiveSign
  by_cases h0 : i.val % 8 = 0
  · have : i.val % 8 < 2 := by omega
    exact (hi this).elim
  · by_cases h1 : i.val % 8 = 1
    · have : i.val % 8 < 2 := by omega
      exact (hi this).elim
    · simp [h0, h1]

private theorem active_count_cast (N : ℕ) (z : Assignment N) (a : ℕ) :
    (w1ActiveCount N z a : ℝ) =
      ∑ i : Fin N, if i.val % 8 = a ∧ z i = true then (1 : ℝ) else 0 := by
  have hc : (Finset.univ.filter (fun i : Fin N => i.val % 8 = a ∧ z i = true)).card =
      ∑ i : Fin N, if i.val % 8 = a ∧ z i = true then (1 : ℕ) else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold w1ActiveCount
  rw [hc]
  norm_cast

private theorem low_count_cast (N : ℕ) (z : Assignment N) :
    (w1ActiveLowCount N z : ℝ) =
      ∑ i : Fin N, if ¬ activeGroup N i ∧ z i = true then (1 : ℝ) else 0 := by
  have hc : (Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i ∧ z i = true)).card =
      ∑ i : Fin N, if ¬ activeGroup N i ∧ z i = true then (1 : ℕ) else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold w1ActiveLowCount
  rw [hc]
  norm_cast

private theorem activeS_count (z : Assignment 32) :
    w1ActiveS 32 z = (w1ActiveCount 32 z 0 : ℝ) - w1ActiveCount 32 z 1 := by
  have hp (i : Fin 32) :
      w1ActiveSign 32 i * bit (z i) =
        (if i.val % 8 = 0 ∧ z i = true then (1 : ℝ) else 0) -
        (if i.val % 8 = 1 ∧ z i = true then (1 : ℝ) else 0) := by
    have hm := Nat.mod_lt i.val (by omega : 0 < 8)
    by_cases h0 : i.val % 8 = 0 <;> by_cases h1 : i.val % 8 = 1 <;>
      by_cases hz : z i = true <;>
      simp [w1ActiveSign, bit, h0, h1, hz] <;> omega
  rw [show w1ActiveS 32 z = ∑ i : Fin 32, w1ActiveSign 32 i * bit (z i) by rfl]
  simp_rw [hp, Finset.sum_sub_distrib, active_count_cast]

private theorem activeK_count (z : Assignment 32) :
    w1ActiveK 32 z = (w1ActiveCount 32 z 0 : ℝ) + w1ActiveCount 32 z 1 := by
  have hp (i : Fin 32) :
      (if activeGroup 32 i then bit (z i) else 0) =
        (if i.val % 8 = 0 ∧ z i = true then (1 : ℝ) else 0) +
        (if i.val % 8 = 1 ∧ z i = true then (1 : ℝ) else 0) := by
    have hm := Nat.mod_lt i.val (by omega : 0 < 8)
    by_cases h0 : i.val % 8 = 0 <;> by_cases h1 : i.val % 8 = 1 <;>
      by_cases hz : z i = true <;>
      simp [activeGroup, bit, h0, h1, hz] <;> omega
  rw [show w1ActiveK 32 z = ∑ i : Fin 32, (if activeGroup 32 i then bit (z i) else 0) by rfl]
  simp_rw [hp, Finset.sum_add_distrib, active_count_cast]

private theorem activeJ_count (z : Assignment 32) :
    w1ActiveJ 32 z = w1ActiveLowCount 32 z := by
  have hp (i : Fin 32) :
      (if activeGroup 32 i then 0 else bit (z i)) =
        if ¬ activeGroup 32 i ∧ z i = true then (1 : ℝ) else 0 := by
    by_cases hi : activeGroup 32 i <;> by_cases hz : z i = true <;>
      simp [hi, bit, hz]
  rw [show w1ActiveJ 32 z = ∑ i : Fin 32, (if activeGroup 32 i then 0 else bit (z i)) by rfl]
  simp_rw [hp, low_count_cast]

private theorem armCount_true_count (z : Assignment 32) :
    armCount z true = (w1ActiveCount 32 z 0 : ℝ) + w1ActiveCount 32 z 1 +
      w1ActiveLowCount 32 z := by
  have hp (i : Fin 32) :
      (if z i = true then (1 : ℝ) else 0) =
        (if i.val % 8 = 0 ∧ z i = true then (1 : ℝ) else 0) +
        (if i.val % 8 = 1 ∧ z i = true then (1 : ℝ) else 0) +
        (if ¬ activeGroup 32 i ∧ z i = true then (1 : ℝ) else 0) := by
    have hm := Nat.mod_lt i.val (by omega : 0 < 8)
    by_cases h0 : i.val % 8 = 0 <;> by_cases h1 : i.val % 8 = 1 <;>
      by_cases hz : z i = true <;>
      simp [activeGroup, h0, h1, hz] <;> omega
  rw [show armCount z true = ∑ i : Fin 32, if z i = true then (1 : ℝ) else 0 by rfl]
  simp_rw [hp, Finset.sum_add_distrib, active_count_cast, low_count_cast]

private theorem activeR_expansion (N : ℕ) (z : Assignment N)
    (hden : w1ActiveNH N * w1ActivePH N z ≠ 0) :
    w1ActiveR N z = w1ActiveK N z -
      2 * (w1ActiveS N z / (w1ActiveNH N * w1ActivePH N z)) * w1ActiveS N z +
      w1ActiveK N z * (w1ActiveS N z / (w1ActiveNH N * w1ActivePH N z))^2 := by
  let b := w1ActiveS N z / (w1ActiveNH N * w1ActivePH N z)
  have ht (i : Fin N) :
      (if activeGroup N i then bit (z i) * (w1ActiveSign N i - b)^2 else 0) =
        (if activeGroup N i then bit (z i) else 0) -
        2*b*(w1ActiveSign N i * bit (z i)) +
        (if activeGroup N i then bit (z i) else 0)*b^2 := by
    by_cases hi : activeGroup N i
    · have hs := activeSign_sq_of_group N i hi
      simp only [if_pos hi]
      rw [show bit (z i) * (w1ActiveSign N i - b)^2 =
        bit (z i) * (w1ActiveSign N i)^2 - 2*b*(w1ActiveSign N i*bit (z i)) +
          bit (z i)*b^2 by ring, hs]
      ring
    · have hs := activeSign_eq_zero_of_not_group N i hi
      simp [hi, hs]
  change (∑ i : Fin N, if activeGroup N i then bit (z i) *
      (w1ActiveSign N i - b)^2 else 0) = _
  simp_rw [ht]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hS : (∑ i : Fin N, 2*b*(w1ActiveSign N i * bit (z i))) =
      2*b*w1ActiveS N z := by
    rw [← Finset.mul_sum]
    simp [w1ActiveS, mul_assoc]
  have hK : (∑ i : Fin N,
      (if activeGroup N i then bit (z i) else 0)*b^2) = w1ActiveK N z*b^2 := by
    rw [← Finset.sum_mul]
    simp [w1ActiveK]
  rw [hS, hK]
  simp only [w1ActiveK]
  dsimp [b]

private def clippedH (k : ℕ) : ℝ := w1Clip ((k : ℝ) / 8)

private theorem clippedH_eq (k : ℕ) (hk : k ≤ 8) :
    clippedH k = if k = 0 then (1 : ℝ)/20 else if k = 8 then (19 : ℝ)/20 else (k : ℝ)/8 := by
  interval_cases k <;> norm_num [clippedH, w1Clip]

private def highWeight (u : ℕ) : ℝ := (Nat.choose 4 u : ℝ) / 16
private def choose24 : Fin 25 → ℕ :=
  ![1,24,276,2024,10626,42504,134596,346104,735471,1307504,1961256,
    2496144,2704156,2496144,1961256,1307504,735471,346104,134596,42504,
    10626,2024,276,24,1]

private theorem choose24_eq (j : Fin 25) : choose24 j = Nat.choose 24 j.val := by
  fin_cases j <;>
    norm_num [choose24, Nat.choose_eq_descFactorial_div_factorial,
      Nat.descFactorial, Nat.factorial]

private def lowWeight (j : Fin 25) : ℝ :=
  (choose24 j : ℝ) * (9 : ℝ)^(24-j.val) / 10^24

private theorem lowWeight_bridge (j : Fin 25) :
    lowWeight j = (Nat.choose 24 j.val : ℝ) * (1/10 : ℝ)^j.val *
      (9/10 : ℝ)^(24-j.val) := by
  have hj : j.val ≤ 24 := by omega
  have he : j.val + (24-j.val) = 24 := Nat.add_sub_of_le hj
  rw [show (Nat.choose 24 j.val : ℝ) = (choose24 j : ℝ) by rw [choose24_eq]]
  unfold lowWeight
  rw [div_pow, div_pow]
  norm_num only [one_pow]
  field_simp
  rw [mul_assoc, ← pow_add, he]
  ring

private theorem low_second_moment (k : ℕ) :
    (∑ j : Fin 25, lowWeight j * ((k : ℝ) + j.val)^2) =
      (k : ℝ)^2 + (24/5 : ℝ)*(k : ℝ) + 198/25 := by
  have h0 : (∑ j : Fin 25, lowWeight j) = 1 := by
    norm_num [lowWeight, choose24, Fin.sum_univ_succ]
  have h1 : (∑ j : Fin 25, (j.val : ℝ)*lowWeight j) = 12/5 := by
    norm_num [lowWeight, choose24, Fin.sum_univ_succ]
  have h2 : (∑ j : Fin 25, (j.val : ℝ)^2*lowWeight j) = 198/25 := by
    norm_num [lowWeight, choose24, Fin.sum_univ_succ]
  calc
    _ = ∑ j : Fin 25, lowWeight j *
          ((k : ℝ)^2 + 2*(k : ℝ)*(j.val : ℝ) + (j.val : ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ j : Fin 25, (k : ℝ)^2*lowWeight j) +
          (∑ j : Fin 25, 2*(k : ℝ)*((j.val : ℝ)*lowWeight j)) +
          ∑ j : Fin 25, (j.val : ℝ)^2*lowWeight j := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (k : ℝ)^2 * ∑ j : Fin 25, lowWeight j +
          2*(k : ℝ)*∑ j : Fin 25, (j.val : ℝ)*lowWeight j+
          ∑ j : Fin 25, (j.val : ℝ)^2*lowWeight j := by
      have ha : (∑ j : Fin 25, (k : ℝ)^2*lowWeight j) =
          (k : ℝ)^2 * ∑ j : Fin 25, lowWeight j := by
        rw [← Finset.mul_sum]
      have hb : (∑ j : Fin 25, 2*(k : ℝ)*((j.val : ℝ)*lowWeight j)) =
          2*(k : ℝ)*∑ j : Fin 25, (j.val : ℝ)*lowWeight j := by
        rw [← Finset.mul_sum]
      rw [ha, hb]
    _ = _ := by rw [h0, h1, h2]; ring

private def ipwCount (u v : ℕ) : ℝ :=
  ((u : ℝ) - v) / (32 * clippedH (u+v))

private def residualCount (u v : ℕ) : ℝ :=
  (u : ℝ) + v - 2 * (((u : ℝ)-v)/(8*clippedH (u+v))) * ((u : ℝ)-v) +
    ((u : ℝ)+v) * (((u : ℝ)-v)/(8*clippedH (u+v)))^2

private theorem high_ipw_second :
    (∑ u : Fin 5, ∑ v : Fin 5,
      highWeight u.val * highWeight v.val *
        (((u.val : ℝ) - v.val) / (32 * clippedH (u.val+v.val)))^2) =
      18239/1505280 := by
  norm_num [highWeight, clippedH, w1Clip, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial, Fin.sum_univ_succ]

private theorem high_printed_expect :
    (∑ u : Fin 5, ∑ v : Fin 5,
      highWeight u.val * highWeight v.val *
        (((u.val : ℝ) + v.val)^2 + (24/5 : ℝ)*(u.val+v.val) + 198/25) *
          (residualCount u.val v.val / (32^4 * clippedH (u.val+v.val)^4))) =
      412940740700292467/161486810505216000000 := by
  norm_num [highWeight, residualCount, clippedH, w1Clip, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial, Fin.sum_univ_succ]

private def printedCount (u v j : ℕ) : ℝ :=
  (residualCount u v) * ((u : ℝ)+(v : ℝ)+(j : ℝ))^2 /
    (32^4 * clippedH (u+v)^4)

private theorem low_total_mass : (∑ j : Fin 25, lowWeight j) = 1 := by
  norm_num [lowWeight, choose24, Fin.sum_univ_succ]

private theorem low_constant_sum (a c : ℝ) :
    (∑ j : Fin 25, a * lowWeight j * c) = a*c := by
  calc
    _ = ∑ j : Fin 25, (a*c)*lowWeight j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (a*c) * ∑ j : Fin 25, lowWeight j := by rw [← Finset.mul_sum]
    _ = _ := by rw [low_total_mass]; ring

private theorem high_ipw_mean :
    (∑ u : Fin 5, ∑ v : Fin 5,
      highWeight u.val * highWeight v.val * ipwCount u.val v.val) = 0 := by
  norm_num [highWeight, ipwCount, clippedH, w1Clip,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial,
    Fin.sum_univ_succ]

private theorem countFiber_formula (hCount : SAP.P004a.T3CountStatement)
    (F : ℕ → ℕ → ℕ → ℝ) :
    expect (w1ActiveP 32) (fun z => F (w1ActiveCount 32 z 0)
      (w1ActiveCount 32 z 1) (w1ActiveLowCount 32 z)) =
      ∑ u : Fin 5, ∑ v : Fin 5, ∑ j : Fin 25,
        highWeight u.val * highWeight v.val * lowWeight j * F u.val v.val j.val := by
  have h := hCount 4 (by omega) F
  calc
    _ = ∑ u : Fin 5, ∑ v : Fin 5, ∑ j : Fin 25,
        ((Nat.choose 4 u.val : ℝ)*(Nat.choose 4 v.val : ℝ)/(2 : ℝ)^8) *
          ((Nat.choose 24 j.val : ℝ)*(1/10 : ℝ)^j.val*(9/10 : ℝ)^(24-j.val)) *
          F u.val v.val j.val := by simpa using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro j _
      rw [lowWeight_bridge]
      unfold highWeight
      have hpow : (2 : ℝ)^8 = 256 := by norm_num
      rw [hpow]
      field_simp
      ring

end
end SAP.P004a.WH.W1.P.T3_L4

open SAP.P004a.WH.W1.P.T3_L4

theorem SAP.P004a.WH.W1.T3_L4_proof : SAP.P004a.WH.W1.T3_L4 := by
  intro hFinite hCount
  rcases hFinite 4 (by omega) with
    ⟨hgroups,hmatrix,hprop,hbeta,hame,hQ,hIpw,haug,hES,hvarS,hvarAug,
      hfitT,hfitF,hbounds,hprinted,hvarPos⟩
  rcases hgroups with ⟨hNH,hNL⟩
  norm_num at hNH hNL
  have hPH (z : Assignment 32) :
      w1ActivePH 32 z = clippedH (w1ActiveCount 32 z 0 + w1ActiveCount 32 z 1) := by
    change w1Clip (w1ActiveK 32 z / w1ActiveNH 32) = _
    rw [activeK_count z, hNH]
    simp only [clippedH, Nat.cast_add]
  have hIPWPoint (z : Assignment 32) :
      w1ActiveIPW 32 z = ipwCount (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1) := by
    rw [hIpw z, activeS_count z, hPH z]
    norm_num [ipwCount]
  have hIPWFun : w1ActiveIPW 32 = fun z => ipwCount
      (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1) := funext hIPWPoint
  have hmeanFunc :
      expect (w1ActiveP 32) (w1ActiveIPW 32) =
        expect (w1ActiveP 32) (fun z => ipwCount
          (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1)) := by
    rw [hIPWFun]
  have hmeanFiber := countFiber_formula hCount (fun u v _ => ipwCount u v)
  have hmeanReduce :
      (∑ u : Fin 5, ∑ v : Fin 5, ∑ j : Fin 25,
        highWeight u.val * highWeight v.val * lowWeight j * ipwCount u.val v.val) =
        ∑ u : Fin 5, ∑ v : Fin 5,
          highWeight u.val * highWeight v.val * ipwCount u.val v.val := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    exact low_constant_sum (highWeight u.val * highWeight v.val) (ipwCount u.val v.val)
  have hmean : expect (w1ActiveP 32) (w1ActiveIPW 32) = 0 := by
    rw [hmeanFunc]
    calc
      _ = ∑ u : Fin 5, ∑ v : Fin 5, ∑ j : Fin 25,
          highWeight u.val * highWeight v.val * lowWeight j * ipwCount u.val v.val := hmeanFiber
      _ = _ := hmeanReduce
      _ = _ := high_ipw_mean
  have hsecondFunc :
      expect (w1ActiveP 32) (fun z => (w1ActiveIPW 32 z)^2) =
        expect (w1ActiveP 32) (fun z =>
          (ipwCount (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1))^2) := by
    rw [hIPWFun]
  have hsecondFiber := countFiber_formula hCount (fun u v _ => (ipwCount u v)^2)
  have hsecondReduce :
      (∑ u : Fin 5, ∑ v : Fin 5, ∑ j : Fin 25,
        highWeight u.val * highWeight v.val * lowWeight j * (ipwCount u.val v.val)^2) =
        ∑ u : Fin 5, ∑ v : Fin 5,
          highWeight u.val * highWeight v.val * (ipwCount u.val v.val)^2 := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    exact low_constant_sum (highWeight u.val * highWeight v.val) ((ipwCount u.val v.val)^2)
  have hsecond :
      expect (w1ActiveP 32) (fun z => (w1ActiveIPW 32 z)^2) = 18239/1505280 := by
    rw [hsecondFunc]
    calc
      _ = ∑ u : Fin 5, ∑ v : Fin 5, ∑ j : Fin 25,
          highWeight u.val * highWeight v.val * lowWeight j * (ipwCount u.val v.val)^2 := hsecondFiber
      _ = _ := hsecondReduce
      _ = _ := by simpa only [ipwCount] using high_ipw_second
  have hvar : variance (w1ActiveP 32) (w1ActiveIPW 32) = 18239/1505280 := by
    unfold variance cov
    have hprod : expect (w1ActiveP 32) (fun z =>
        w1ActiveIPW 32 z * w1ActiveIPW 32 z) = 18239/1505280 := by
      simpa only [pow_two] using hsecond
    rw [hprod, hmean]
    norm_num
  have hden (z : Assignment 32) : w1ActiveNH 32 * w1ActivePH 32 z ≠ 0 := by
    apply mul_ne_zero
    · norm_num [hNH]
    · have hpos : 0 < w1ActivePH 32 z := by
        unfold w1ActivePH w1Clip
        linarith [le_max_left (1/20 : ℝ) (min (19/20) (w1ActiveK 32 z/w1ActiveNH 32))]
      exact hpos.ne'
  have hRPoint (z : Assignment 32) :
      w1ActiveR 32 z = residualCount (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1) := by
    rw [activeR_expansion 32 z (hden z), activeK_count z, activeS_count z, hNH, hPH z]
    simp [residualCount, Nat.cast_add]
  have hPrintPoint (z : Assignment 32) :
      w1ActiveVPrinted 32 z = printedCount (w1ActiveCount 32 z 0)
        (w1ActiveCount 32 z 1) (w1ActiveLowCount 32 z) := by
    rw [hprinted z, armCount_true_count z, hRPoint z, hPH z]
    dsimp [printedCount]
    push_cast
    ring
  have hPrintFun : w1ActiveVPrinted 32 = fun z => printedCount
      (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1) (w1ActiveLowCount 32 z) :=
    funext hPrintPoint
  have hprintedFunc :
      expect (w1ActiveP 32) (w1ActiveVPrinted 32) =
        expect (w1ActiveP 32) (fun z => printedCount
          (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1) (w1ActiveLowCount 32 z)) := by
    rw [hPrintFun]
  have hprintedFiber := countFiber_formula hCount (fun u v j => printedCount u v j)
  have hprintedInner (u v : Fin 5) :
      (∑ j : Fin 25,
        highWeight u.val * highWeight v.val * lowWeight j * printedCount u.val v.val j.val) =
        highWeight u.val * highWeight v.val *
          (((u.val : ℝ)+(v.val : ℝ))^2 +
            (24/5 : ℝ)*((u.val : ℝ)+(v.val : ℝ)) + 198/25) *
          (residualCount u.val v.val / (32^4 * clippedH (u.val+v.val)^4)) := by
    let a := highWeight u.val * highWeight v.val
    let c := residualCount u.val v.val / (32^4 * clippedH (u.val+v.val)^4)
    have hm := low_second_moment (u.val+v.val)
    calc
      _ = ∑ j : Fin 25, c * (a * (lowWeight j *
            ((u.val : ℝ)+(v.val : ℝ)+(j.val : ℝ))^2)) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [printedCount, a, c]
        ring
      _ = c * (a * ∑ j : Fin 25, lowWeight j *
            ((u.val : ℝ)+(v.val : ℝ)+(j.val : ℝ))^2) := by
        calc
          _ = ∑ j : Fin 25, (c*a) * (lowWeight j *
                ((u.val : ℝ)+(v.val : ℝ)+(j.val : ℝ))^2) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (c*a) * ∑ j : Fin 25, lowWeight j *
                ((u.val : ℝ)+(v.val : ℝ)+(j.val : ℝ))^2 := by rw [← Finset.mul_sum]
          _ = _ := by ring
      _ = c * (a * ((u.val : ℝ)+(v.val : ℝ))^2 +
            a * ((24/5 : ℝ)*((u.val : ℝ)+(v.val : ℝ))) + a*(198/25)) := by
        have hm' := hm
        push_cast at hm'
        rw [hm']
        push_cast
        ring
      _ = _ := by dsimp [a, c]; ring
  have hprintedReduce :
      (∑ u : Fin 5, ∑ v : Fin 5, ∑ j : Fin 25,
        highWeight u.val * highWeight v.val * lowWeight j * printedCount u.val v.val j.val) =
        ∑ u : Fin 5, ∑ v : Fin 5,
          highWeight u.val * highWeight v.val *
            (((u.val : ℝ)+(v.val : ℝ))^2 +
              (24/5 : ℝ)*((u.val : ℝ)+(v.val : ℝ)) + 198/25) *
            (residualCount u.val v.val / (32^4 * clippedH (u.val+v.val)^4)) := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    exact hprintedInner u v
  have hprinted :
      expect (w1ActiveP 32) (w1ActiveVPrinted 32) =
        412940740700292467/161486810505216000000 := by
    rw [hprintedFunc]
    calc
      _ = ∑ u : Fin 5, ∑ v : Fin 5, ∑ j : Fin 25,
          highWeight u.val * highWeight v.val * lowWeight j * printedCount u.val v.val j.val := hprintedFiber
      _ = _ := hprintedReduce
      _ = _ := high_printed_expect
  exact ⟨hvar, hprinted⟩
