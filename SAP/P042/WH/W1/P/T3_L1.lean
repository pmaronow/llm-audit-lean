import SAP.P042.WH.W1.Leaves
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem SAP.P042.WH.W1.T3_L1_proof : SAP.P042.WH.W1.T3_L1 := by
  change SAP.P042.EndpointSquareLaw
  intro μ L U z V hL hU hz hV
  let r : ℝ := z * Real.sqrt V
  have hr : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg hz (Real.sqrt_nonneg V)
  have hgapL : 0 ≤ μ - L := le_of_lt (sub_pos.mpr hL)
  have hgapU : 0 ≤ U - μ := le_of_lt (sub_pos.mpr hU)
  have hsq : r ^ 2 = z ^ 2 * V := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt hV]
  have hLlt : L < μ - r ↔ r < μ - L := by
    constructor <;> intro h <;> linarith
  have hLle : L ≤ μ - r ↔ r ≤ μ - L := by
    constructor <;> intro h <;> linarith
  have hLrevlt : μ - r < L ↔ μ - L < r := by
    constructor <;> intro h <;> linarith
  have hLrevle : μ - r ≤ L ↔ μ - L ≤ r := by
    constructor <;> intro h <;> linarith
  have hUlt : μ + r < U ↔ r < U - μ := by
    constructor <;> intro h <;> linarith
  have hUle : μ + r ≤ U ↔ r ≤ U - μ := by
    constructor <;> intro h <;> linarith
  have hUrevlt : U < μ + r ↔ U - μ < r := by
    constructor <;> intro h <;> linarith
  have hUrevle : U ≤ μ + r ↔ U - μ ≤ r := by
    constructor <;> intro h <;> linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change L < μ - r ↔ z ^ 2 * V < (μ - L) ^ 2
    rw [← hsq]
    exact hLlt.trans (sq_lt_sq₀ hr hgapL).symm
  · change L ≤ μ - r ↔ z ^ 2 * V ≤ (μ - L) ^ 2
    rw [← hsq]
    exact hLle.trans (sq_le_sq₀ hr hgapL).symm
  · change μ - r < L ↔ (μ - L) ^ 2 < z ^ 2 * V
    rw [← hsq]
    exact hLrevlt.trans (sq_lt_sq₀ hgapL hr).symm
  · change μ - r ≤ L ↔ (μ - L) ^ 2 ≤ z ^ 2 * V
    rw [← hsq]
    exact hLrevle.trans (sq_le_sq₀ hgapL hr).symm
  · change μ + r < U ↔ z ^ 2 * V < (U - μ) ^ 2
    rw [← hsq]
    exact hUlt.trans (sq_lt_sq₀ hr hgapU).symm
  · change μ + r ≤ U ↔ z ^ 2 * V ≤ (U - μ) ^ 2
    rw [← hsq]
    exact hUle.trans (sq_le_sq₀ hr hgapU).symm
  · change U < μ + r ↔ (U - μ) ^ 2 < z ^ 2 * V
    rw [← hsq]
    exact hUrevlt.trans (sq_lt_sq₀ hgapU hr).symm
  · change U ≤ μ + r ↔ (U - μ) ^ 2 ≤ z ^ 2 * V
    rw [← hsq]
    exact hUrevle.trans (sq_le_sq₀ hgapU hr).symm

