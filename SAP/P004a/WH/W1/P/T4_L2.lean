import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T4_L2

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
    · omega

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
    · have hs : w1ActiveSign N i = 0 := by
        have hm := Nat.mod_lt i.val (by omega : 0 < 8)
        unfold activeGroup at hi
        unfold w1ActiveSign
        by_cases h0 : i.val % 8 = 0
        · exact (hi (by omega)).elim
        · by_cases h1 : i.val % 8 = 1
          · exact (hi (by omega)).elim
          · simp [h0, h1]
      simp [hi, hs]
  change (∑ i : Fin N, if activeGroup N i then bit (z i) *
      (w1ActiveSign N i - b)^2 else 0) = _
  simp_rw [ht]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [show (∑ i : Fin N, if activeGroup N i then bit (z i) else 0) = w1ActiveK N z by rfl]
  rw [show (∑ i : Fin N, w1ActiveSign N i * bit (z i)) = w1ActiveS N z by rfl]

private def clippedH (k : ℕ) : ℝ := w1Clip ((k : ℝ) / 8)
private def highWeight (u : ℕ) : ℝ := (Nat.choose 4 u : ℝ) / 16
private def lowWeight (j : ℕ) : ℝ :=
  (Nat.choose 24 j : ℝ) * (1/10 : ℝ)^j * (9/10 : ℝ)^(24-j)

private theorem low_mass : (∑ j : Fin 25, lowWeight j.val) = 1 := by
  have hb := add_pow (1/10 : ℝ) (9/10 : ℝ) 24
  calc
    _ = ∑ j ∈ Finset.range 25,
        (1/10 : ℝ)^j * (9/10 : ℝ)^(24-j) * (Nat.choose 24 j : ℝ) := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => lowWeight j)]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [lowWeight]
      ring
    _ = (1/10 + 9/10 : ℝ)^24 := hb.symm
    _ = 1 := by norm_num

private theorem high_ipw_mean :
    (∑ u : Fin 5, ∑ v : Fin 5,
      highWeight u.val * highWeight v.val *
        (((u.val : ℝ) - v.val) / (32 * clippedH (u.val+v.val)))) = 0 := by
  norm_num [highWeight, clippedH, w1Clip, Nat.choose, Fin.sum_univ_succ]

private theorem high_ipw_second :
    (∑ u : Fin 5, ∑ v : Fin 5,
      highWeight u.val * highWeight v.val *
        ((((u.val : ℝ) - v.val) / (32 * clippedH (u.val+v.val)))^2)) =
      18239/1505280 := by
  norm_num [highWeight, clippedH, w1Clip, Nat.choose, Fin.sum_univ_succ]

private def rawValue (u v : ℕ) : ℝ :=
  ((u : ℝ) + v - 2 * (((u : ℝ)-v)/(8*clippedH (u+v))) * ((u : ℝ)-v) +
    ((u : ℝ)+v) * (((u : ℝ)-v)/(8*clippedH (u+v)))^2) /
    (32^2 * clippedH (u+v)^2)

private theorem high_raw_expect :
    (∑ u : Fin 5, ∑ v : Fin 5,
      highWeight u.val * highWeight v.val * rawValue u.val v.val) =
        493725989/38038425600 := by
  norm_num [rawValue, highWeight, clippedH, w1Clip, Nat.choose, Fin.sum_univ_succ]

private theorem count_reduce (hbridge : T3CountStatement) (G : ℕ → ℕ → ℝ) :
    expect (w1ActiveP 32) (fun z => G (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1)) =
      ∑ u : Fin 5, ∑ v : Fin 5, highWeight u.val * highWeight v.val * G u.val v.val := by
  have hb := hbridge 4 (by norm_num) (fun u v _ => G u v)
  change expect (w1ActiveP (8*4))
      (fun z => (fun u v _ => G u v) (w1ActiveCount (8*4) z 0)
        (w1ActiveCount (8*4) z 1) (w1ActiveLowCount (8*4) z)) = _ at hb
  change expect (w1ActiveP 32)
    (fun z => G (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1)) = _
  rw [hb]
  have hcoeff (u v : Fin 5) :
      ((Nat.choose 4 u.val : ℝ) * (Nat.choose 4 v.val : ℝ) / (2 : ℝ)^8) =
        highWeight u.val * highWeight v.val := by
    simp [highWeight]
    ring
  simp_rw [hcoeff]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  calc
    (∑ j : Fin 25,
      (highWeight u.val * highWeight v.val) * lowWeight j.val * G u.val v.val) =
        (highWeight u.val * highWeight v.val * G u.val v.val) *
          ∑ j : Fin 25, lowWeight j.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = highWeight u.val * highWeight v.val * G u.val v.val := by
      rw [low_mass]
      ring

private theorem activeNH_32 : w1ActiveNH 32 = 8 := by
  change ((Finset.univ.filter (fun i : Fin 32 =>
    AronowAudit.P004.activeGroup 32 i)).card : ℝ) = 8
  rw [AronowAudit.P004.Wave1.ObservationalCoverage.active_count_formula 32]
  norm_num

private theorem activeIPW_count (z : Assignment 32) :
    w1ActiveIPW 32 z =
      ((w1ActiveCount 32 z 0 : ℝ) - w1ActiveCount 32 z 1) /
        (32 * clippedH (w1ActiveCount 32 z 0 + w1ActiveCount 32 z 1)) := by
  have h0 := AronowAudit.P004.Wave1.ObservationalCoverage.o6_proof.1 32 (by omega) z
  have hmle : AronowAudit.P004.Wave1.ObservationalCoverage.activeMLE 32 = w1ActiveMLE 32 := by
    funext z
    rfl
  have hS := activeS_count z
  have hK := activeK_count z
  have hN := activeNH_32
  have hp : w1ActivePH 32 z = clippedH (w1ActiveCount 32 z 0 + w1ActiveCount 32 z 1) := by
    rw [w1ActivePH, hN, hK]
    simp [clippedH, Nat.cast_add, div_eq_mul_inv]
  have h0' := h0
  rw [show AronowAudit.P004.Wave1.ObservationalCoverage.SAct 32 z = w1ActiveS 32 z by rfl,
      show AronowAudit.P004.Wave1.ObservationalCoverage.pHatH 32 z = w1ActivePH 32 z by rfl] at h0'
  rw [hS, hp] at h0'
  change fittedIPW (activeTable 32) (activeO 32) (w1ActiveMLE 32) z = _
  rw [← hmle]
  exact h0'

private theorem activeRaw_count (z : Assignment 32) :
    w1ActiveVRaw 32 z = rawValue (w1ActiveCount 32 z 0) (w1ActiveCount 32 z 1) := by
  have hraw := SAP.P004a.WH.W1.active_raw_formula 4 (by norm_num) z
  have hK := activeK_count z
  have hS := activeS_count z
  have hN := activeNH_32
  have hp : w1ActivePH 32 z = clippedH (w1ActiveCount 32 z 0 + w1ActiveCount 32 z 1) := by
    rw [w1ActivePH, hN, hK]
    simp [clippedH, Nat.cast_add, div_eq_mul_inv]
  have hden : w1ActiveNH 32 * w1ActivePH 32 z ≠ 0 := by
    rw [hN, hp]
    have hh : (1 : ℝ)/20 ≤ clippedH (w1ActiveCount 32 z 0 + w1ActiveCount 32 z 1) := by
      exact le_max_left _ _
    apply mul_ne_zero (by norm_num)
    exact ne_of_gt (by linarith)
  have hR := activeR_expansion 32 z hden
  rw [hraw, hR, hK, hS, hN, hp]
  dsimp [rawValue]

end
end SAP.P004a.WH.W1.P.T4_L2

open SAP.P004a.WH.W1.P.T4_L2

set_option linter.constructorNameAsVariable false

theorem SAP.P004a.WH.W1.T4_L2_proof : SAP.P004a.WH.W1.T4_L2 := by
  intro hbridge
  have hrawPoint := activeRaw_count
  have hrawExp : expect (w1ActiveP 32) (w1ActiveVRaw 32) =
      expect (w1ActiveP 32) (fun z => rawValue (w1ActiveCount 32 z 0)
        (w1ActiveCount 32 z 1)) := by
    unfold expect
    apply Finset.sum_congr rfl
    intro z hz
    rw [hrawPoint z]
  have hX : expect (w1ActiveP 32) (w1ActiveIPW 32) = 0 := by
    have hpoint := activeIPW_count
    have hrewrite : expect (w1ActiveP 32) (w1ActiveIPW 32) =
        expect (w1ActiveP 32) (fun z =>
          ((w1ActiveCount 32 z 0 : ℝ) - w1ActiveCount 32 z 1) /
            (32 * clippedH (w1ActiveCount 32 z 0 + w1ActiveCount 32 z 1))) := by
      unfold expect
      apply Finset.sum_congr rfl
      intro z hz
      rw [hpoint z]
    rw [hrewrite]
    calc
      _ = ∑ u : Fin 5, ∑ v : Fin 5,
          highWeight u.val * highWeight v.val *
            (((u.val : ℝ)-v.val)/(32*clippedH (u.val+v.val))) :=
        count_reduce hbridge (fun u v => ((u : ℝ)-v)/(32*clippedH (u+v)))
      _ = 0 := high_ipw_mean
  have hX2 : expect (w1ActiveP 32) (fun z => (w1ActiveIPW 32 z)^2) =
      18239/1505280 := by
    have hpoint := activeIPW_count
    have hrewrite : expect (w1ActiveP 32) (fun z => (w1ActiveIPW 32 z)^2) =
        expect (w1ActiveP 32) (fun z =>
          (((w1ActiveCount 32 z 0 : ℝ) - w1ActiveCount 32 z 1) /
            (32 * clippedH (w1ActiveCount 32 z 0 + w1ActiveCount 32 z 1)))^2) := by
      unfold expect
      apply Finset.sum_congr rfl
      intro z hz
      change designWeight (w1ActiveP 32) z * (w1ActiveIPW 32 z)^2 = _
      rw [hpoint z]
    rw [hrewrite]
    calc
      _ = ∑ u : Fin 5, ∑ v : Fin 5,
          highWeight u.val * highWeight v.val *
            (((u.val : ℝ)-v.val)/(32*clippedH (u.val+v.val)))^2 :=
        count_reduce hbridge (fun u v => (((u : ℝ)-v)/(32*clippedH (u+v)))^2)
      _ = 18239/1505280 := high_ipw_second
  constructor
  · calc
      expect (w1ActiveP 32) (w1ActiveVRaw 32) =
          expect (w1ActiveP 32) (fun z => rawValue (w1ActiveCount 32 z 0)
            (w1ActiveCount 32 z 1)) := hrawExp
      _ = ∑ u : Fin 5, ∑ v : Fin 5,
          highWeight u.val * highWeight v.val * rawValue u.val v.val :=
        count_reduce hbridge rawValue
      _ = 493725989/38038425600 := high_raw_expect
  · rw [variance, cov]
    have hsquare : (fun z : Assignment 32 => w1ActiveIPW 32 z * w1ActiveIPW 32 z) =
        fun z => (w1ActiveIPW 32 z)^2 := by
      funext z
      ring
    rw [hsquare, hX, hX2]
    norm_num
