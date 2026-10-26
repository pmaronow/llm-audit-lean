import AronowAudit.P018.Wave1.WeightedConsistencyBlueprint
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

theorem g2_proof : G2.{u} := by
  classical
  intro U _ μ _ N S T Z W hST hZ hW hZS hWT hZ2 hW2
  obtain ⟨u₀⟩ := nonempty_of_isProbabilityMeasure μ
  let ext (S : Finset (Fin N)) (x : S → U) : Fin N → U :=
    fun i => if hi : i ∈ S then x ⟨i, hi⟩ else u₀
  have hext (S : Finset (Fin N)) : Measurable (ext S) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ S
    · simpa only [ext, dif_pos hi] using (measurable_pi_apply (⟨i, hi⟩ : S))
    · simpa only [ext, dif_neg hi] using (measurable_const : Measurable (fun _ : S → U => u₀))
  have hfactorZ : (fun ω : Fin N → U => Z (ext S (fun i : S => ω i))) = Z := by
    funext ω
    apply hZS
    intro i hi
    simp only [ext, dif_pos hi]
  have hfactorW : (fun ω : Fin N → U => W (ext T (fun i : T => ω i))) = W := by
    funext ω
    apply hWT
    intro i hi
    simp only [ext, dif_pos hi]
  have hi : iIndepFun (fun i : Fin N => fun ω : Fin N → U => ω i)
      (Measure.pi (fun _ : Fin N => μ)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hind := (hi.indepFun_finset S T hST (fun i => measurable_pi_apply i)).comp
    (hZ.comp (hext S)) (hW.comp (hext T))
  change IndepFun (fun ω : Fin N → U => Z (ext S (fun i : S => ω i)))
    (fun ω : Fin N → U => W (ext T (fun i : T => ω i))) _ at hind
  rw [hfactorZ, hfactorW] at hind
  exact hind.covariance_eq_zero hZ2 hW2

end
end AronowAudit.P018.Wave1.WeightedConsistency
