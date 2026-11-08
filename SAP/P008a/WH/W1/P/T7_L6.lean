import SAP.P008a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P008a.WH.W1.P.T7_L6

open scoped BigOperators Classical

theorem fintype_sum_div {α : Type*} [Fintype α] (g : α → ℝ) (a : ℝ) :
    (∑ x, g x) / a = ∑ x, g x / a := by
  exact Finset.sum_div Finset.univ g a

theorem point_injective (hem : Function.Injective SAP.P008a.wholeRiskEmbedding) :
    Function.Injective
      (fun t : SAP.P008a.WholeRiskTriple =>
        SAP.P008a.wholeRiskPoint t.1 t.2.1 t.2.2) := by
    intro a b hab
    have he : SAP.P008a.wholeRiskEmbedding (Sum.inr a) =
        SAP.P008a.wholeRiskEmbedding (Sum.inr b) := by
      change SAP.P008a.wholeRiskPoint a.1 a.2.1 a.2.2 =
        SAP.P008a.wholeRiskPoint b.1 b.2.1 b.2.2
      exact hab
    exact Sum.inr.inj (hem he)

end SAP.P008a.WH.W1.P.T7_L6

theorem SAP.P008a.WH.W1.T7_L6_proof : SAP.P008a.WH.W1.T7_L6 := by
  intro hem
  have hpoint := SAP.P008a.WH.W1.P.T7_L6.point_injective hem
  refine ⟨?_, ?_, ?_⟩
  · unfold SAP.P008a.wholeRiskCirclePoints
    rw [Finset.card_image_of_injective _ hpoint]
    norm_num [SAP.P008a.WholeRiskTriple, SAP.P008a.RiskCell]
  · intro i j k
    change Function.extend
      (fun t : SAP.P008a.WholeRiskTriple =>
        SAP.P008a.wholeRiskPoint t.1 t.2.1 t.2.2)
      (fun t => t.1) (fun _ => 0)
      (SAP.P008a.wholeRiskPoint i j k) = i
    simpa using hpoint.extend_apply (fun t => t.1) (fun _ => 0) (i, j, k)
  · intro f
    have hsum : (∑ x ∈ SAP.P008a.wholeRiskCirclePoints, f x) =
        ∑ t : SAP.P008a.WholeRiskTriple,
          f (SAP.P008a.wholeRiskPoint t.1 t.2.1 t.2.2) := by
      unfold SAP.P008a.wholeRiskCirclePoints
      rw [Finset.sum_image (Set.injOn_of_injective hpoint)]
    have hprod : (∑ t : SAP.P008a.WholeRiskTriple,
          f (SAP.P008a.wholeRiskPoint t.1 t.2.1 t.2.2)) =
        ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : SAP.P008a.RiskCell,
          f (SAP.P008a.wholeRiskPoint i j k) := by
      simp only [SAP.P008a.WholeRiskTriple, Fintype.sum_prod_type]
    -- The count follows from injectivity of the triple-to-point map.
    have hcircle : SAP.P008a.wholeRiskCirclePoints.card = 640000 := by
      unfold SAP.P008a.wholeRiskCirclePoints
      rw [Finset.card_image_of_injective _ hpoint]
      norm_num [SAP.P008a.WholeRiskTriple, SAP.P008a.RiskCell]
    have hscale :
        (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : SAP.P008a.RiskCell,
          f (SAP.P008a.wholeRiskPoint i j k)) / (40000 : ℝ) =
        ∑ i : Fin 4, ∑ j : Fin 4,
          ((∑ k : SAP.P008a.RiskCell,
            f (SAP.P008a.wholeRiskPoint i j k)) / (40000 : ℝ)) := by
      calc
        _ = ∑ i : Fin 4,
            ((∑ j : Fin 4, ∑ k : SAP.P008a.RiskCell,
              f (SAP.P008a.wholeRiskPoint i j k)) / (40000 : ℝ)) :=
          SAP.P008a.WH.W1.P.T7_L6.fintype_sum_div _ _
        _ = ∑ i : Fin 4, ∑ j : Fin 4,
            ((∑ k : SAP.P008a.RiskCell,
              f (SAP.P008a.wholeRiskPoint i j k)) / (40000 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact SAP.P008a.WH.W1.P.T7_L6.fintype_sum_div _ _
    change (∑ x ∈ SAP.P008a.wholeRiskCirclePoints, f x) /
          SAP.P008a.wholeRiskCirclePoints.card =
        (16 : ℝ)⁻¹ * ∑ i : Fin 4, ∑ j : Fin 4,
          ((∑ k : SAP.P008a.RiskCell,
            f (SAP.P008a.wholeRiskPoint i j k)) /
            (Finset.univ.card : ℝ))
    rw [hsum, hprod, hcircle]
    simp only [Finset.card_univ, Fintype.card_fin]
    conv_lhs => rw [div_eq_mul_inv]
    norm_num
    calc
      (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : SAP.P008a.RiskCell,
          f (SAP.P008a.wholeRiskPoint i j k)) * (1 / 640000 : ℝ) =
        (1 / 16 : ℝ) *
          ((∑ i : Fin 4, ∑ j : Fin 4, ∑ k : SAP.P008a.RiskCell,
            f (SAP.P008a.wholeRiskPoint i j k)) / 40000) := by
          ring
      _ = (1 / 16 : ℝ) *
          (∑ i : Fin 4, ∑ j : Fin 4,
            ((∑ k : SAP.P008a.RiskCell,
              f (SAP.P008a.wholeRiskPoint i j k)) / (40000 : ℝ))) := by
          rw [hscale]
