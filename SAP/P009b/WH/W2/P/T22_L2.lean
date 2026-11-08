import SAP.P009b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology

namespace SAP.P009b.WH.W2.P.T22_L2

private lemma pointwise_bound (N : ℝ) (a : ℝ)
    (hN : 0 < N) (hb : 1 ≤ ⌊a⌋₊) :
    |SAP.P009b.w2CorrectedCenter N ⌊a⌋₊ -
      SAP.P009b.w2RatioCenter (a / Real.sqrt N)| ≤ 5 / Real.sqrt N := by
  let m : ℝ := (⌊a⌋₊ : ℝ) - 1
  let H : ℝ → ℝ := fun x => (N - x ^ 2) / (N + x ^ 2)
  have hm0 : 0 ≤ m := by
    dsimp [m]
    have hfloor : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast hb
    linarith
  have hfloorPos : 0 < ⌊a⌋₊ := by omega
  have ha0 : 0 < a := by
    have := (Nat.floor_pos).mp hfloorPos
    linarith
  have hfloorLe : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le (le_of_lt ha0)
  have hfloorLt : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  have hdeltaLo : 1 ≤ a - m := by
    dsimp [m]
    have hcast : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast hb
    linarith
  have hdeltaHi : a - m ≤ 2 := by
    dsimp [m]
    linarith
  have hma : m ≤ a := by linarith
  have hsqrtPos : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsqrtSq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN.le
  have h2m : 2 * m * Real.sqrt N ≤ N + m ^ 2 := by
    nlinarith [sq_nonneg (m - Real.sqrt N)]
  have h2a : 2 * a * Real.sqrt N ≤ N + a ^ 2 := by
    nlinarith [sq_nonneg (a - Real.sqrt N)]
  have hmden : 0 < N + m ^ 2 := by positivity
  have hadden : 0 < N + m ^ 2 + m := by positivity
  have haddenAlt : 0 < N + m + m ^ 2 := by nlinarith [hadden]
  have haddenA : 0 < N + a ^ 2 := by positivity
  have hbc : (⌊a⌋₊ : ℝ) = m + 1 := by dsimp [m]; ring
  have hfirstEq : SAP.P009b.w2CorrectedCenter N ⌊a⌋₊ - H m =
      ((N - m ^ 2) * (-m)) / ((N + m ^ 2 + m) * (N + m ^ 2)) := by
    dsimp [SAP.P009b.w2CorrectedCenter, H]
    rw [hbc]
    ring_nf
    field_simp [haddenAlt.ne', hmden.ne']
    <;> ring_nf
  have habsN : |N - m ^ 2| ≤ N + m ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg m]
  have hfirst : |SAP.P009b.w2CorrectedCenter N ⌊a⌋₊ - H m| ≤ 1 / Real.sqrt N := by
    rw [hfirstEq, abs_div, abs_mul, abs_neg, abs_of_nonneg hm0,
      abs_of_pos (mul_pos hadden hmden)]
    have hquot : (|N - m ^ 2| * m) / ((N + m ^ 2 + m) * (N + m ^ 2)) ≤
        m / (N + m ^ 2) := by
      apply (div_le_div_iff₀ (mul_pos hadden hmden) hmden).2
      have hnum : |N - m ^ 2| * m ≤ (N + m ^ 2) * m :=
        mul_le_mul_of_nonneg_right habsN hm0
      calc
        |N - m ^ 2| * m * (N + m ^ 2) ≤
            ((N + m ^ 2) * m) * (N + m ^ 2) :=
              mul_le_mul_of_nonneg_right hnum (le_of_lt hmden)
        _ ≤ m * ((N + m ^ 2 + m) * (N + m ^ 2)) := by
              nlinarith [mul_nonneg (sq_nonneg m) (le_of_lt hmden)]
    have hquot' : m / (N + m ^ 2) ≤ 1 / (2 * Real.sqrt N) := by
      apply (div_le_div_iff₀ hmden (by positivity : 0 < 2 * Real.sqrt N)).2
      nlinarith [h2m]
    calc
      (|N - m ^ 2| * m) / ((N + m ^ 2 + m) * (N + m ^ 2)) ≤
          m / (N + m ^ 2) := hquot
      _ ≤ 1 / (2 * Real.sqrt N) := hquot'
      _ ≤ 1 / Real.sqrt N := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt N) hsqrtPos).2
        nlinarith [hsqrtPos]
  have hsecondEq : H m - H a =
      (2 * N * (a - m) * (a + m)) / ((N + m ^ 2) * (N + a ^ 2)) := by
    dsimp [H]
    field_simp [ne_of_gt hmden, ne_of_gt haddenA]
    <;> ring
  have hsecond : |H m - H a| ≤ 4 / Real.sqrt N := by
    have hdelta0 : 0 ≤ a - m := by linarith
    rw [hsecondEq, abs_div, abs_of_nonneg (by positivity :
      0 ≤ 2 * N * (a - m) * (a + m)), abs_of_pos (mul_pos hmden haddenA)]
    apply (div_le_div_iff₀ (mul_pos hmden haddenA) hsqrtPos).2
    have hNumer : 2 * N * (a - m) * (a + m) * Real.sqrt N ≤
        8 * N * a * Real.sqrt N := by
      calc
        2 * N * (a - m) * (a + m) * Real.sqrt N ≤
            2 * N * 2 * (2 * a) * Real.sqrt N := by
              have hδ : 0 ≤ a - m := by linarith
              have hsum : 0 ≤ a + m := by linarith
              have hδ' : a - m ≤ 2 := hdeltaHi
              have hsum' : a + m ≤ 2 * a := by linarith
              gcongr
        _ = 8 * N * a * Real.sqrt N := by ring
    have hdenLower : 4 * N * (N + a ^ 2) ≤
        4 * (N + m ^ 2) * (N + a ^ 2) := by
      have hmSq : 0 ≤ m ^ 2 := sq_nonneg m
      have hfac : 0 ≤ 4 * (N + a ^ 2) := by positivity
      nlinarith [mul_nonneg hfac hmSq]
    have hAM : 8 * N * a * Real.sqrt N ≤ 4 * N * (N + a ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left h2a (show 0 ≤ 4 * N by positivity)
      nlinarith
    nlinarith [hNumer, hdenLower, hAM]
  have hratio : SAP.P009b.w2RatioCenter (a / Real.sqrt N) =
      (N - a ^ 2) / (N + a ^ 2) := by
    dsimp [SAP.P009b.w2RatioCenter]
    rw [div_pow, hsqrtSq]
    field_simp
    <;> ring
  have htriangle : |SAP.P009b.w2CorrectedCenter N ⌊a⌋₊ -
      SAP.P009b.w2RatioCenter (a / Real.sqrt N)| ≤
      |SAP.P009b.w2CorrectedCenter N ⌊a⌋₊ - H m| + |H m - H a| := by
    rw [hratio]
    calc
      |SAP.P009b.w2CorrectedCenter N ⌊a⌋₊ - (N - a ^ 2) / (N + a ^ 2)| =
          |(SAP.P009b.w2CorrectedCenter N ⌊a⌋₊ - H m) + (H m - H a)| := by
            congr 1
            dsimp [H]
            ring
      _ ≤ _ := abs_add_le _ _
  have hsqrtSmall : 0 < Real.sqrt N := hsqrtPos
  calc
    |SAP.P009b.w2CorrectedCenter N ⌊a⌋₊ -
        SAP.P009b.w2RatioCenter (a / Real.sqrt N)| ≤
        |SAP.P009b.w2CorrectedCenter N ⌊a⌋₊ - H m| + |H m - H a| := htriangle
    _ ≤ 1 / Real.sqrt N + 4 / Real.sqrt N := add_le_add hfirst hsecond
    _ = 5 / Real.sqrt N := by ring

end SAP.P009b.WH.W2.P.T22_L2

theorem SAP.P009b.WH.W2.T22_L2_proof : SAP.P009b.WH.W2.T22_L2 := by
  intro N hN hNgrows a ha
  have hNreal : Tendsto (fun t => (N t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hNgrows
  have hsqrt : Tendsto (fun t => Real.sqrt (N t : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hNreal
  have hvanish : Tendsto (fun t => 5 / Real.sqrt (N t : ℝ)) atTop (nhds 0) :=
    hsqrt.const_div_atTop 5
  have habs : Tendsto (fun t => |SAP.P009b.w2CorrectedCenter (N t : ℝ) ⌊a t⌋₊ -
      SAP.P009b.w2RatioCenter (a t / Real.sqrt (N t : ℝ))|) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) _ hvanish
    intro t
    exact SAP.P009b.WH.W2.P.T22_L2.pointwise_bound (N t : ℝ) (a t)
      (by exact_mod_cast hN t) (ha t).1
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact habs
