import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

theorem SAP.P001e.WH.W2.T94_L2_proof : SAP.P001e.WH.W2.T94_L2 := by
  intro Ω E _ _ μ hμ X hX D Y hD F hm d hi
  let S : Set Ω := {ω | D ω = d}
  have hS : MeasurableSet S := hD (measurableSet_singleton d)
  refine ⟨?_, hm.2.1.restrict, hi.restrict, ?_⟩
  · exact hm.1.comp (by fun_prop : Measurable (fun x : E => (d, x)))
  · intro A hA
    let T : Set Ω := X ⁻¹' A
    have hT : MeasurableSet T := hX hA
    have hrect : MeasurableSet ({d} ×ˢ A) :=
      (measurableSet_singleton d).prod hA
    have hpre : (fun ω => (D ω, X ω)) ⁻¹' ({d} ×ˢ A) = S ∩ T := by
      ext ω
      simp [S, T]
    have hjoint := hm.2.2.2 ({d} ×ˢ A) hrect
    have hreplace :
        (∫ ω in S ∩ T, F (D ω, X ω) ∂μ) =
          ∫ ω in S ∩ T, F (d, X ω) ∂μ := by
      apply setIntegral_congr_fun (hS.inter hT)
      intro ω hω
      have hDω : D ω = d := hω.1
      change D ω = d at hDω
      change F (D ω, X ω) = F (d, X ω)
      rw [hDω]
    change (∫ ω, Y ω ∂((μ.restrict S).restrict T)) =
      ∫ ω, F (d, X ω) ∂((μ.restrict S).restrict T)
    rw [Measure.restrict_restrict hT]
    rw [Set.inter_comm T S]
    rw [hpre] at hjoint
    exact hjoint.trans hreplace
