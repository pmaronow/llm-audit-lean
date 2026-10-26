import AronowAudit.P005.Wave1.InteractedExpansionBlueprint

set_option autoImplicit false
namespace AronowAudit.P005.Wave1.InteractedExpansion
open AronowAudit.P005 Finset Filter
open scoped BigOperators Topology
noncomputable section

theorem n4_proof : N4 := by
  intro n P a c s hs hx A y hv
  have hA : A.Nonempty := by
    by_contra h
    have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he, sampleCov, mean] at hv
  have hshift : sampleCov A (fun i => a i - c) (fun i => a i - c) =
      sampleCov A a a := covariance_location_invariant A hA a a c c
  have hshiftY : sampleCov A (fun i => a i - c) y = sampleCov A a y := by
    simpa only [sub_zero] using covariance_location_invariant A hA a y c 0
  have hxf (k : Fin 1) : (fun i => P.x i k) = fun i => s⁻¹ * (a i - c) := by
    funext i
    rw [hx]
    ring
  have hL : (armL P A) 0 0 = s⁻¹ ^ 2 * sampleCov A a a := by
    change sampleCov A (fun i => P.x i 0) (fun i => P.x i 0) = _
    rw [hxf, sampleCov_scale_both, hshift]
  have hdet : (armL P A).det ≠ 0 := by
    rw [Matrix.det_fin_one, hL]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hs)) hv
  have hN : armN P A y 0 = s⁻¹ * sampleCov A a y := by
    have hcomm : (fun i => y i * P.x i 0) = (fun i => P.x i 0 * y i) := by
      funext i; ring
    change mean A (fun i => y i * P.x i 0) - mean A y * mean A (fun i => P.x i 0) = _
    rw [hcomm, mul_comm (mean A y)]
    change sampleCov A (fun i => P.x i 0) y = _
    rw [hxf, sampleCov_scale_left, hshiftY]
  have hM : xMean P A 0 = s⁻¹ * (mean A a - c) := by
    change mean A (fun i => P.x i 0) = _
    rw [hxf, mean_mul, mean_sub, mean_const A hA]
  have hInv : ((armL P A)⁻¹) 0 0 = (s⁻¹ ^ 2 * sampleCov A a a)⁻¹ := by
    rw [Matrix.inv_subsingleton]
    simp [Ring.inverse_eq_inv, hL]
  refine ⟨hdet, ?_⟩
  simp only [dot, armBetaHat, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  rw [hM, hInv, hN]
  field_simp [hs, hv]
  <;> ring

end
end AronowAudit.P005.Wave1.InteractedExpansion
