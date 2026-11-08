import SAP.P001a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

namespace SAP.P001a.WH.W2.P.T17_L2

open SAP.P001a

lemma structural_uniform : W2PlaceboStructuralLaw =
    (1/24 : ℝ≥0∞) • Measure.count := by
  apply Measure.ext_of_singleton
  intro v
  change (((1/6 : ℝ≥0∞) • Measure.count).prod
      ((1/4 : ℝ≥0∞) • Measure.count)) {(v.1, v.2)}
      = ((1/24 : ℝ≥0∞) • Measure.count) {(v.1, v.2)}
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [Measure.smul_apply]
  have ha : (6 : ℝ≥0∞) ≠ 0 ∨ (4 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hb : (6 : ℝ≥0∞) ≠ ∞ ∨ (4 : ℝ≥0∞) ≠ 0 := by norm_num
  rw [← ENNReal.mul_inv ha hb]
  norm_num

lemma structural_atom_fiber_card (j : Fin 12) :
    Fintype.card {v : (Fin 3 × Bool) × Fin 4 // W2PlaceboStructuralAtom v = j} =
      (if j.val / 4 = 1 then (if j.val % 2 = 1 then 1 else 3)
       else (if j.val % 2 = 1 then 3 else 1)) := by
  classical
  fin_cases j <;> decide

@[simp] lemma ofReal_one_div (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (1 / (n : ℝ)) = (1 / (n : ℝ≥0∞)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn)]
  simp

lemma inv24_mul_three : (1/24 : ℝ≥0∞) * 3 = 1/8 := by
  simp only [ENNReal.div_eq_inv_mul, mul_one]
  calc
    (24 : ℝ≥0∞)⁻¹ * 3 = (3 * 8 : ℝ≥0∞)⁻¹ * 3 := by congr 1 <;> norm_num
    _ = (3 : ℝ≥0∞)⁻¹ * (8 : ℝ≥0∞)⁻¹ * 3 := by
      rw [ENNReal.mul_inv (by norm_num) (by norm_num)]
    _ = (3 : ℝ≥0∞)⁻¹ * 3 * (8 : ℝ≥0∞)⁻¹ := by ac_rfl
    _ = (8 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end SAP.P001a.WH.W2.P.T17_L2

theorem SAP.P001a.WH.W2.T17_L2_proof : SAP.P001a.WH.W2.T17_L2 := by
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply (measurable_of_finite W2PlaceboStructuralAtom)
    (measurableSet_singleton j)]
  rw [SAP.P001a.WH.W2.P.T17_L2.structural_uniform]
  let S : Set ((Fin 3 × Bool) × Fin 4) :=
    W2PlaceboStructuralAtom ⁻¹' ({j} : Set (Fin 12))
  change ((1/24 : ℝ≥0∞) • Measure.count) S = finiteLawMeasure placeboLaw {j}
  have hS : S.Finite := Set.toFinite S
  letI : Fintype S := hS.fintype
  rw [Measure.smul_apply, Measure.count_apply
    (measurableSet_preimage (measurable_of_finite W2PlaceboStructuralAtom)
      (measurableSet_singleton j))]
  simp only [Set.encard, ENat.card_eq_coe_fintype_card, Set.fintypeCard_eq_ncard]
  have hcardS : S.ncard =
      (if j.val / 4 = 1 then (if j.val % 2 = 1 then 1 else 3)
       else (if j.val % 2 = 1 then 3 else 1)) := by
    have hto : hS.toFinset = Finset.univ.filter
        (fun v : (Fin 3 × Bool) × Fin 4 => W2PlaceboStructuralAtom v = j) := by
      ext v
      simp [S]
    rw [Set.ncard_eq_toFinset_card S hS, hto, ← Fintype.card_subtype]
    exact SAP.P001a.WH.W2.P.T17_L2.structural_atom_fiber_card j
  rw [hcardS]
  have hrhs : finiteLawMeasure placeboLaw {j} =
      ENNReal.ofReal (placeboLaw.weight j) := by
    simp [finiteLawMeasure, Pi.single_apply]
  rw [hrhs]
  fin_cases j <;> simp [placeboLaw]
  all_goals simpa only [ENNReal.div_eq_inv_mul, mul_one] using
    SAP.P001a.WH.W2.P.T17_L2.inv24_mul_three
