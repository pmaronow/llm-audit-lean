import SAP.P022.Bridge.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.Bridge
open SAP.P022

theorem cdf_quarter_eq_iff (d : Design) (y : Fin d.N → ℝ) (x : ℝ) :
    (designVariance d (fun π => empiricalCDF (observedTreatment d y π) x) =
      ((d.N : ℝ) - d.m) / (4 * ((d.N : ℝ) - 1) * d.m)) ↔
      empiricalCDF y x = 1 / 2 := by
  have hv := (cdf_variance_corrected_proof d y y x).2.2.1
  have hm : (0 : ℝ) < d.m := by exact_mod_cast (show 0 < d.m by have := d.treatment_min; omega)
  have hN1 : (0 : ℝ) < (d.N : ℝ) - 1 := by
    have hN : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
    linarith
  have hmN : (d.m : ℝ) < d.N := by
    exact_mod_cast (show d.m < d.N by have := d.sample_le; have := d.control_min; omega)
  let a : ℝ := ((d.N : ℝ) - d.m) / (((d.N : ℝ) - 1) * d.m)
  have ha : 0 < a := div_pos (sub_pos.mpr hmN) (mul_pos hN1 hm)
  have hquarter : ((d.N : ℝ) - d.m) / (4 * ((d.N : ℝ) - 1) * d.m) = a * (1 / 4) := by
    dsimp [a]
    field_simp
  rw [hv, hquarter]
  change a * empiricalCDF y x * (1 - empiricalCDF y x) = a * (1 / 4) ↔ _
  constructor
  · intro he
    have hg : empiricalCDF y x * (1 - empiricalCDF y x) = 1 / 4 :=
      mul_left_cancel₀ ha.ne' (by simpa only [mul_assoc] using he)
    nlinarith [sq_nonneg (empiricalCDF y x - 1 / 2)]
  · intro he
    rw [he]
    ring

end SAP.P022.Bridge
