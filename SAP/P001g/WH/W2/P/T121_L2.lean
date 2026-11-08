import SAP.P001g.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.WH.W2.P.T121_L2

open SAP.P001g.WH.W2

private theorem pow_eq_of_eq {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : a ^ n = b ^ n) : a = b := by
  have hab : a ≤ b := le_of_pow_le_pow_left₀ hn.ne' hb.le (by rw [h])
  have hba : b ≤ a := le_of_pow_le_pow_left₀ hn.ne' ha.le (by rw [← h])
  exact le_antisymm hab hba

private theorem disc_left_candidate : (![1, 0] : Fin 2 → ℝ) ∈ circleDiscW2 := by
  norm_num [circleDiscW2]

private theorem disc_middle_candidate :
    (![(-1 / Real.sqrt 2), (1 / Real.sqrt 2)] : Fin 2 → ℝ) ∈ circleDiscW2 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsp : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  change (-1 / Real.sqrt 2) ^ 2 + (1 / Real.sqrt 2) ^ 2 ≤ 1
  rw [div_pow, div_pow]
  rw [hs]
  field_simp
  norm_num

private theorem disc_right_candidate : (![0, -1] : Fin 2 → ℝ) ∈ circleDiscW2 := by
  norm_num [circleDiscW2]

private theorem unique_at_y0 {n : ℕ} (hn : 0 < n)
    (z v : Fin 2 → ℝ) (hz : z ∈ circleDiscW2) (hv : v ∈ circleDiscW2)
    (hmz : IsMaxOn (fun a => circleAffineW2 a 0 ^ n) circleDiscW2 z)
    (hmv : IsMaxOn (fun a => circleAffineW2 a 0 ^ n) circleDiscW2 v) : z = v := by
  have hpz : 0 < circleAffineW2 z 0 := affinePosW2 z hz 0
  have hpv : 0 < circleAffineW2 v 0 := affinePosW2 v hv 0
  have hpow : circleAffineW2 z 0 ^ n = circleAffineW2 v 0 ^ n := by
    apply le_antisymm
    · exact hmv hz
    · exact hmz hv
  have hae : circleAffineW2 z 0 = circleAffineW2 v 0 := pow_eq_of_eq hn hpz hpv hpow
  have hbestPow : circleAffineW2 (![1, 0] : Fin 2 → ℝ) 0 ^ n ≤ circleAffineW2 z 0 ^ n := by
    exact hmz disc_left_candidate
  have hbest : circleAffineW2 (![1, 0] : Fin 2 → ℝ) 0 ≤ circleAffineW2 z 0 :=
    le_of_pow_le_pow_left₀ hn.ne' (affinePosW2 z hz 0).le hbestPow
  have hz0 : z 0 = 1 := by
    simp [circleAffineW2] at hbest
    nlinarith [discBoundsW2 z hz]
  have hv0 : v 0 = 1 := by
    have hbestvPow : circleAffineW2 (![1, 0] : Fin 2 → ℝ) 0 ^ n ≤ circleAffineW2 v 0 ^ n := by
      exact hmv disc_left_candidate
    have hbestv : circleAffineW2 (![1, 0] : Fin 2 → ℝ) 0 ≤ circleAffineW2 v 0 :=
      le_of_pow_le_pow_left₀ hn.ne' (affinePosW2 v hv 0).le hbestvPow
    simp [circleAffineW2] at hbestv
    nlinarith [discBoundsW2 v hv]
  have hz1 : z 1 = 0 := by
    have hd := hz
    change z 0 ^ 2 + z 1 ^ 2 ≤ 1 at hd
    rw [hz0] at hd
    nlinarith [sq_nonneg (z 1)]
  have hv1 : v 1 = 0 := by
    have hd := hv
    change v 0 ^ 2 + v 1 ^ 2 ≤ 1 at hd
    rw [hv0] at hd
    nlinarith [sq_nonneg (v 1)]
  ext i
  fin_cases i <;> simp [hz0, hz1, hv0, hv1]

private theorem unique_at_y1 {n : ℕ} (hn : 0 < n)
    (z v : Fin 2 → ℝ) (hz : z ∈ circleDiscW2) (hv : v ∈ circleDiscW2)
    (hmz : IsMaxOn (fun a => circleAffineW2 a 1 ^ n) circleDiscW2 z)
    (hmv : IsMaxOn (fun a => circleAffineW2 a 1 ^ n) circleDiscW2 v) : z = v := by
  have hpz : 0 < circleAffineW2 z 1 := affinePosW2 z hz 1
  have hpv : 0 < circleAffineW2 v 1 := affinePosW2 v hv 1
  have hpow : circleAffineW2 z 1 ^ n = circleAffineW2 v 1 ^ n := by
    apply le_antisymm
    · exact hmv hz
    · exact hmz hv
  have hae : circleAffineW2 z 1 = circleAffineW2 v 1 := pow_eq_of_eq hn hpz hpv hpow
  let q : ℝ := Real.sqrt 2
  have hq : q ^ 2 = 2 := by dsimp [q]; exact Real.sq_sqrt (by norm_num)
  have hqpos : 0 < q := by dsimp [q]; exact Real.sqrt_pos.2 (by norm_num)
  have hlinear_bound (w : Fin 2 → ℝ) (hw : w ∈ circleDiscW2) :
      w 1 - w 0 ≤ q := by
    have hd : w 0 ^ 2 + w 1 ^ 2 ≤ 1 := hw
    have hs : (w 1 - w 0) ^ 2 + (w 0 + w 1) ^ 2 =
        2 * (w 0 ^ 2 + w 1 ^ 2) := by ring
    have hsq : (w 1 - w 0) ^ 2 ≤ q ^ 2 := by nlinarith [sq_nonneg (w 0 + w 1)]
    nlinarith [sq_nonneg (w 1 - w 0 + q), sq_nonneg (w 1 - w 0 - q)]
  have hqdiv : 1 / q - (-1 / q) = q := by
    have hqne : q ≠ 0 := ne_of_gt hqpos
    field_simp [hqne]
    nlinarith [hq]
  have hbestPow : circleAffineW2 (![(-1 / q), (1 / q)] : Fin 2 → ℝ) 1 ^ n ≤ circleAffineW2 z 1 ^ n := by
    exact hmz disc_middle_candidate
  have hbest : circleAffineW2 (![(-1 / q), (1 / q)] : Fin 2 → ℝ) 1 ≤ circleAffineW2 z 1 :=
    le_of_pow_le_pow_left₀ hn.ne' (affinePosW2 z hz 1).le hbestPow
  have hzval : z 1 - z 0 = q := by
    change (Real.sqrt 2 / 4 + (1 / q - (-1 / q)) / 10) ≤
      (Real.sqrt 2 / 4 + (z 1 - z 0) / 10) at hbest
    rw [hqdiv] at hbest
    have hb := hlinear_bound z hz
    nlinarith
  have hvval : v 1 - v 0 = q := by
    have hbestvPow : circleAffineW2 (![(-1 / q), (1 / q)] : Fin 2 → ℝ) 1 ^ n ≤ circleAffineW2 v 1 ^ n := by
      exact hmv disc_middle_candidate
    have hbestv : circleAffineW2 (![(-1 / q), (1 / q)] : Fin 2 → ℝ) 1 ≤ circleAffineW2 v 1 :=
      le_of_pow_le_pow_left₀ hn.ne' (affinePosW2 v hv 1).le hbestvPow
    change (Real.sqrt 2 / 4 + (1 / q - (-1 / q)) / 10) ≤
      (Real.sqrt 2 / 4 + (v 1 - v 0) / 10) at hbestv
    rw [hqdiv] at hbestv
    have hb := hlinear_bound v hv
    nlinarith
  have hzsum : z 0 + z 1 = 0 := by
    have hd : z 0 ^ 2 + z 1 ^ 2 ≤ 1 := hz
    have hs : (z 1 - z 0) ^ 2 + (z 0 + z 1) ^ 2 =
        2 * (z 0 ^ 2 + z 1 ^ 2) := by ring
    rw [hzval, hq] at hs
    nlinarith [sq_nonneg (z 0 + z 1)]
  have hvsum : v 0 + v 1 = 0 := by
    have hd : v 0 ^ 2 + v 1 ^ 2 ≤ 1 := hv
    have hs : (v 1 - v 0) ^ 2 + (v 0 + v 1) ^ 2 =
        2 * (v 0 ^ 2 + v 1 ^ 2) := by ring
    rw [hvval, hq] at hs
    nlinarith [sq_nonneg (v 0 + v 1)]
  have hz0 : z 0 = -q / 2 := by linarith [hzval, hzsum]
  have hz1 : z 1 = q / 2 := by linarith [hzval, hzsum]
  have hv0 : v 0 = -q / 2 := by linarith [hvval, hvsum]
  have hv1 : v 1 = q / 2 := by linarith [hvval, hvsum]
  ext i
  fin_cases i <;> simp [hz0, hz1, hv0, hv1, q]

private theorem unique_at_y2 {n : ℕ} (hn : 0 < n)
    (z v : Fin 2 → ℝ) (hz : z ∈ circleDiscW2) (hv : v ∈ circleDiscW2)
    (hmz : IsMaxOn (fun a => circleAffineW2 a 2 ^ n) circleDiscW2 z)
    (hmv : IsMaxOn (fun a => circleAffineW2 a 2 ^ n) circleDiscW2 v) : z = v := by
  have hpz : 0 < circleAffineW2 z 2 := affinePosW2 z hz 2
  have hpv : 0 < circleAffineW2 v 2 := affinePosW2 v hv 2
  have hpow : circleAffineW2 z 2 ^ n = circleAffineW2 v 2 ^ n := by
    apply le_antisymm
    · exact hmv hz
    · exact hmz hv
  have hae : circleAffineW2 z 2 = circleAffineW2 v 2 := pow_eq_of_eq hn hpz hpv hpow
  have hbestPow : circleAffineW2 (![0, -1] : Fin 2 → ℝ) 2 ^ n ≤ circleAffineW2 z 2 ^ n := by
    exact hmz disc_right_candidate
  have hbest : circleAffineW2 (![0, -1] : Fin 2 → ℝ) 2 ≤ circleAffineW2 z 2 :=
    le_of_pow_le_pow_left₀ hn.ne' (affinePosW2 z hz 2).le hbestPow
  have hz1 : z 1 = -1 := by
    simp [circleAffineW2] at hbest
    nlinarith [discBoundsW2 z hz]
  have hv1 : v 1 = -1 := by
    have hbestvPow : circleAffineW2 (![0, -1] : Fin 2 → ℝ) 2 ^ n ≤ circleAffineW2 v 2 ^ n := by
      exact hmv disc_right_candidate
    have hbestv : circleAffineW2 (![0, -1] : Fin 2 → ℝ) 2 ≤ circleAffineW2 v 2 :=
      le_of_pow_le_pow_left₀ hn.ne' (affinePosW2 v hv 2).le hbestvPow
    simp [circleAffineW2] at hbestv
    nlinarith [discBoundsW2 v hv]
  have hz0 : z 0 = 0 := by
    have hd := hz
    change z 0 ^ 2 + z 1 ^ 2 ≤ 1 at hd
    rw [hz1] at hd
    nlinarith [sq_nonneg (z 0)]
  have hv0 : v 0 = 0 := by
    have hd := hv
    change v 0 ^ 2 + v 1 ^ 2 ≤ 1 at hd
    rw [hv1] at hd
    nlinarith [sq_nonneg (v 0)]
  ext i
  fin_cases i <;> simp [hz0, hz1, hv0, hv1]

end SAP.P001g.WH.W2.P.T121_L2

open SAP.P001g.WH.W2.P.T121_L2

theorem SAP.P001g.WH.W2.T121_L2_proof : SAP.P001g.WH.W2.T121_L2 := by
  intro n hn y z v hz hv hmz hmv
  fin_cases y
  · exact unique_at_y0 hn z v hz hv hmz hmv
  · exact unique_at_y1 hn z v hz hv hmz hmv
  · exact unique_at_y2 hn z v hz hv hmz hmv
