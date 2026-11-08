import SAP.P009b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b.WH.W1.P.T27_L2

noncomputable section
attribute [local instance] Classical.propDecidable

def distinguished (b : ℕ) : SAP.P009b.Assignment b := fun _ => false

theorem mass_as_correction (b : ℕ) (z : SAP.P009b.Assignment b) :
    SAP.P009b.wholeHeavyMass b z =
      ((4 : ℝ)^b)⁻¹ +
        (if z = distinguished b then 1 - (2 : ℝ)^b * ((4 : ℝ)^b)⁻¹ else 0) := by
  unfold SAP.P009b.wholeHeavyMass distinguished
  by_cases h : z = fun _ => false
  · simp [h]
    ring
  · simp [h]

theorem power_two_le_power_four (b : ℕ) :
    (2 : ℝ)^b ≤ (4 : ℝ)^b := by
  have hpow : (4 : ℝ)^b = (2 : ℝ)^b * (2 : ℝ)^b := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hbase : 1 ≤ (2 : ℝ)^b := one_le_pow₀ (by norm_num)
  rw [hpow]
  nlinarith [sq_nonneg ((2 : ℝ)^b - 1)]

theorem outside_nonneg (b : ℕ) :
    0 ≤ ((2 : ℝ)^b - 1) * ((4 : ℝ)^b)⁻¹ := by
  have hpow : 1 ≤ (2 : ℝ)^b := one_le_pow₀ (by norm_num)
  have hden : 0 ≤ ((4 : ℝ)^b)⁻¹ := inv_nonneg.mpr (pow_nonneg (by norm_num) _)
  exact mul_nonneg (by linarith) hden

theorem outside_le_geometric (b : ℕ) :
    ((2 : ℝ)^b - 1) * ((4 : ℝ)^b)⁻¹ ≤ (1 / 2 : ℝ)^b := by
  let x : ℝ := (2 : ℝ)^b
  let y : ℝ := (4 : ℝ)^b
  have hx : 1 ≤ x := by
    dsimp [x]
    exact one_le_pow₀ (by norm_num)
  have hy : y = x * x := by
    dsimp [x, y]
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  calc
    (x - 1) * y⁻¹ ≤ x * y⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact inv_nonneg.mpr (le_of_lt (pow_pos (by norm_num) _))
    _ = (1 / 2 : ℝ)^b := by
      rw [hy]
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hx)
      calc
        x * (x * x)⁻¹ = x⁻¹ := by field_simp [hx0]
        _ = (1 / 2 : ℝ)^b := by
          symm
          rw [one_div_pow]
          simp [x]

theorem constant_sum (b : ℕ) :
    (∑ z : SAP.P009b.Assignment b, ((4 : ℝ)^b)⁻¹) =
      (2 : ℝ)^b * ((4 : ℝ)^b)⁻¹ := by
  rw [Finset.sum_const, Finset.card_univ]
  simp [SAP.P009b.Assignment, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul]

theorem correction_sum (b : ℕ) :
    (∑ z : SAP.P009b.Assignment b,
      (if z = distinguished b then 1 - (2 : ℝ)^b * ((4 : ℝ)^b)⁻¹ else 0)) =
      1 - (2 : ℝ)^b * ((4 : ℝ)^b)⁻¹ := by
  rw [Finset.sum_ite_eq']
  simp

end
end SAP.P009b.WH.W1.P.T27_L2

theorem SAP.P009b.WH.W1.T27_L2_proof : SAP.P009b.WH.W1.T27_L2 := by
  constructor
  · intro b
    constructor
    · intro z
      by_cases h : z = SAP.P009b.WH.W1.P.T27_L2.distinguished b
      · rw [SAP.P009b.WH.W1.P.T27_L2.mass_as_correction]
        simp [h, SAP.P009b.WH.W1.P.T27_L2.distinguished]
        have hp := SAP.P009b.WH.W1.P.T27_L2.power_two_le_power_four b
        have hden : 0 < (4 : ℝ)^b := pow_pos (by norm_num) _
        have hid : (2 : ℝ)^b * ((4 : ℝ)^b)⁻¹ ≤ 1 := by
          calc
            (2 : ℝ)^b * ((4 : ℝ)^b)⁻¹ ≤ (4 : ℝ)^b * ((4 : ℝ)^b)⁻¹ :=
              mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr hden.le)
            _ = 1 := by field_simp [ne_of_gt hden]
        nlinarith [hid]
      · rw [SAP.P009b.WH.W1.P.T27_L2.mass_as_correction]
        simp [h, SAP.P009b.WH.W1.P.T27_L2.distinguished]
    · have hrepr : ∀ z : SAP.P009b.Assignment b,
          SAP.P009b.wholeHeavyMass b z = ((4 : ℝ)^b)⁻¹ +
            (if z = SAP.P009b.WH.W1.P.T27_L2.distinguished b then
              1 - (2 : ℝ)^b * ((4 : ℝ)^b)⁻¹ else 0) :=
          fun z => SAP.P009b.WH.W1.P.T27_L2.mass_as_correction b z
      simp_rw [hrepr]
      rw [Finset.sum_add_distrib,
        SAP.P009b.WH.W1.P.T27_L2.constant_sum,
        SAP.P009b.WH.W1.P.T27_L2.correction_sum]
      ring
  · have hgeom : Tendsto (fun b : ℕ => (1 / 2 : ℝ)^b) atTop (nhds 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hout : Tendsto
        (fun b : ℕ => ((2 : ℝ)^b - 1) * ((4 : ℝ)^b)⁻¹) atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds hgeom
      · exact fun b => SAP.P009b.WH.W1.P.T27_L2.outside_nonneg b
      · exact fun b => SAP.P009b.WH.W1.P.T27_L2.outside_le_geometric b
    simpa [SAP.P009b.wholeHeavyMass] using (tendsto_const_nhds.sub hout)
