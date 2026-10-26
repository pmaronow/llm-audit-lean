import AronowAudit.P018.Wave1.WeightedConsistencyBlueprint

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem m1_proof : M1.{u} := by
  classical
  intro U _ k R X Y dir v C H hS
  have hR := hS.1
  letI instUnitProbability : IsProbabilityMeasure R.μ := hR.1
  let d : Dyad 2 := ⟨Finset.univ, by simp [dyads]⟩
  let t : Fin (R.T 2 d) := ⟨0, hR.2.1 2 le_rfl d⟩
  obtain ⟨B, hB, hb⟩ := hR.2.2.2.1
  obtain ⟨j, hj⟩ := hR.2.2.2.2
  have hX := (hR.2.2.1 2 d t).1
  have hY := (hR.2.2.1 2 d t).2
  have hcommon := hS.2.2.1 2 d t
  cases hd : dir 2 d t with
  | false =>
    have hx : (fun uv : U × U => R.X 2 d t uv.1 uv.2) =
        (fun uv => X uv.1 uv.2) := by
      funext uv
      simpa only [hd, Bool.false_eq_true, ↓reduceIte] using (hcommon uv.1 uv.2).1
    have hy : (fun uv : U × U => R.Y 2 d t uv.1 uv.2) =
        (fun uv => Y uv.1 uv.2) := by
      funext uv
      simpa only [hd, Bool.false_eq_true, ↓reduceIte] using (hcommon uv.1 uv.2).2
    refine ⟨hx ▸ hX, hy ▸ hY, ⟨B, hB, ?_⟩, j, ?_⟩
    · filter_upwards [hb 2 d t] with uv huv
      rw [← congrFun hx uv, ← congrFun hy uv]
      exact huv
    · intro u₁ u₂
      have h := hj 2 d t u₁ u₂
      have hx' := congrFun hx (u₁, u₂)
      simpa only [hx'] using h
  | true =>
    have hx : (fun uv : U × U => R.X 2 d t uv.2 uv.1) =
        (fun uv => X uv.1 uv.2) := by
      funext uv
      simpa only [hd, ↓reduceIte] using (hcommon uv.2 uv.1).1
    have hy : (fun uv : U × U => R.Y 2 d t uv.2 uv.1) =
        (fun uv => Y uv.1 uv.2) := by
      funext uv
      simpa only [hd, ↓reduceIte] using (hcommon uv.2 uv.1).2
    refine ⟨hx ▸ hX.comp measurable_swap, hy ▸ hY.comp measurable_swap,
      ⟨B, hB, ?_⟩, j, ?_⟩
    · have hb' := hb 2 d t
      rw [← Measure.prod_swap] at hb'
      have ht := ae_of_ae_map measurable_swap.aemeasurable hb'
      filter_upwards [ht] with uv huv
      rw [← congrFun hx uv, ← congrFun hy uv]
      exact huv
    · intro u₁ u₂
      have h := hj 2 d t u₂ u₁
      have hx' := congrFun hx (u₁, u₂)
      simpa only [hx'] using h

end
end AronowAudit.P018.Wave1.WeightedConsistency
