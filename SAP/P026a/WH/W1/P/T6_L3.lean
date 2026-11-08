import SAP.P026a.WH.W1.Leaves
import AronowAudit.P026.P026_FiniteDesign

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.WH.W1.P.T6_L3

open Finset
open scoped BigOperators

lemma prediction_eq (w : Fin 6 × Fin 15) (i : Fin 16) :
    w1Predict (w1FeDesign w) (w1FeCoefficients w) i = (paperFeFitted w i : ℝ) := by
  by_cases h : i.val < 6
  · have hb : decide (6 ≤ i.val) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    simp [w1Predict, Fin.sum_univ_succ, w1FeDesign, w1FeCoefficients, paperFeFitted,
      paperTableCenteredT, paperTableCenteredX, h, hb]
    ring_nf
  · have hb : decide (6 ≤ i.val) = true := by
      simp only [decide_eq_true_eq]
      omega
    simp [w1Predict, Fin.sum_univ_succ, w1FeDesign, w1FeCoefficients, paperFeFitted,
      paperTableCenteredT, paperTableCenteredX, h, hb]
    ring_nf

lemma intercept_residual_cast (w : Fin 6 × Fin 15) :
    (∑ i : Fin 16, ((paperTableY i : ℝ) - (paperFeFitted w i : ℝ))) = 0 := by
  have h := (AronowAudit.P026.fe_normal_equations w).2.1
  exact_mod_cast h

lemma treated_residual_cast (w : Fin 6 × Fin 15) :
    (∑ i : Fin 16, ((armIndicator paperTableUnitDesign true w i : ℚ) : ℝ) *
      ((paperTableY i : ℝ) - (paperFeFitted w i : ℝ))) = 0 := by
  have h := (AronowAudit.P026.fe_normal_equations w).2.2.1
  exact_mod_cast h

lemma x_residual_cast (w : Fin 6 × Fin 15) :
    (∑ i : Fin 16, (paperTableX i : ℝ) *
      ((paperTableY i : ℝ) - (paperFeFitted w i : ℝ))) = 0 := by
  have h := (AronowAudit.P026.fe_normal_equations w).2.2.2.2
  exact_mod_cast h

lemma block_residual_cast (w : Fin 6 × Fin 15) :
    (∑ i ∈ (Finset.univ : Finset (Fin 16)).filter (fun i => 6 ≤ i.val),
      ((paperTableY i : ℝ) - (paperFeFitted w i : ℝ))) = 0 := by
  have h := (AronowAudit.P026.fe_normal_equations w).2.2.2.1
  exact_mod_cast h

end SAP.P026a.WH.W1.P.T6_L3

theorem SAP.P026a.WH.W1.T6_L3_proof : SAP.P026a.WH.W1.T6_L3 := by
  intro w
  unfold w1Normal
  intro j
  have hp : ∀ i : Fin 16,
      w1Predict (w1FeDesign w) (w1FeCoefficients w) i = (paperFeFitted w i : ℝ) :=
    SAP.P026a.WH.W1.P.T6_L3.prediction_eq w
  simp_rw [hp]
  fin_cases j
  · simpa [w1FeDesign] using SAP.P026a.WH.W1.P.T6_L3.intercept_residual_cast w
  · simpa [w1FeDesign] using SAP.P026a.WH.W1.P.T6_L3.treated_residual_cast w
  · calc
      (∑ i : Fin 16, (if i.val < 6 then (0 : ℝ) else 1) *
          ((paperTableY i : ℝ) - (paperFeFitted w i : ℝ)))
          = ∑ i : Fin 16, if 6 ≤ i.val then
              ((paperTableY i : ℝ) - (paperFeFitted w i : ℝ)) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h : i.val < 6
            · have h6 : ¬ 6 ≤ i.val := by omega
              simp [h, h6]
            · have h6 : 6 ≤ i.val := by omega
              simp [h, h6]
      _ = ∑ i ∈ (Finset.univ : Finset (Fin 16)).filter (fun i => 6 ≤ i.val),
            ((paperTableY i : ℝ) - (paperFeFitted w i : ℝ)) := by
            simp only [Finset.sum_filter]
      _ = 0 := SAP.P026a.WH.W1.P.T6_L3.block_residual_cast w
  · simpa [w1FeDesign] using SAP.P026a.WH.W1.P.T6_L3.x_residual_cast w
