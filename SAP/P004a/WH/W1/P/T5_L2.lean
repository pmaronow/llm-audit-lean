import SAP.P004a.WH.W1.Leaves
import AronowAudit.P004.Wave1.AreaSum.A5
import AronowAudit.P004.Wave1.AreaSum.A6

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace SAP.P004a.WH.W1.P.T5_L2

open MeasureTheory
open scoped ENNReal

theorem area_bin_sector_volume (c : EuclideanSpace ℝ (Fin 2))
    (j : Fin 6) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    volume (w1AreaBin c j.val ∩ {x | SAP.P004a.angularFraction c x < q}) =
      ENNReal.ofReal (q * Real.pi * (2 * (j : ℝ) + 1)) := by
  by_cases hj : j = 0
  · subst j
    simpa [w1AreaBin, SAP.P004a.angularFraction, AronowAudit.P004.angularFraction] using
      AronowAudit.P004.Wave1.AreaSum.a5_proof.2 c q hq0 hq
  · have hjNat : j.val ≠ 0 := by
      intro h
      apply hj
      exact Fin.ext h
    rw [w1AreaBin, if_neg hjNat]
    have hsector := AronowAudit.P004.Wave1.AreaSum.a4_proof c
      (j : ℝ) ((j : ℝ) + 1) q (by positivity) (by linarith) hq0 hq
    have hsquare : ((j : ℝ) + 1) ^ 2 - (j : ℝ) ^ 2 = 2 * (j : ℝ) + 1 := by ring
    simpa only [hsquare, SAP.P004a.angularFraction, AronowAudit.P004.angularFraction] using hsector

end SAP.P004a.WH.W1.P.T5_L2

theorem SAP.P004a.WH.W1.T5_L2_proof : SAP.P004a.WH.W1.T5_L2 := by
  intro q hq hgeom j i z
  let P := w1AreaPopulation q
  rcases hgeom with ⟨_hbinary, hmeas, hon, _houtside, hwd, _hwd6,
    hregion, _hunion, _hdisjoint, hmass, _hmass6⟩
  have hsectorMeas : MeasurableSet
      {x : EuclideanSpace ℝ (Fin 2) | SAP.P004a.angularFraction (areaBinaryCenter i) x < q j (z i)} := by
    simpa [SAP.P004a.angularFraction, AronowAudit.P004.angularFraction] using
      (measurableSet_lt
        (AronowAudit.P004.Wave1.AreaSum.a6_proof.2.2 (areaBinaryCenter i)) measurable_const)
  have harea : 0 < Real.pi * (2 * (j : ℝ) + 1) := by positivity
  have hnum :
      (∫ x in region P i j, P.outcome x z ∂volume) =
        q j (z i) * Real.pi * (2 * (j : ℝ) + 1) := by
    calc
      _ = ∫ x in region P i j,
          ({y | SAP.P004a.angularFraction (areaBinaryCenter i) y < q j (z i)}).indicator
            (fun _ => (1 : ℝ)) x ∂volume := by
        apply setIntegral_congr_fun (hwd j i).1
        intro x hx
        have honx := hon i j x z hx
        change P.outcome x z = _ at honx
        simpa [Set.indicator] using honx
      _ = (volume (region P i j ∩
          {x | SAP.P004a.angularFraction (areaBinaryCenter i) x < q j (z i)})).toReal := by
        rw [setIntegral_indicator hsectorMeas, setIntegral_const]
        simp only [Measure.real, smul_eq_mul, mul_one]
      _ = q j (z i) * Real.pi * (2 * (j : ℝ) + 1) := by
        rw [hregion i j]
        rw [SAP.P004a.WH.W1.P.T5_L2.area_bin_sector_volume (areaBinaryCenter i) j (q j (z i))
          (hq j (z i)).1 (hq j (z i)).2,
          ENNReal.toReal_ofReal
            (mul_nonneg (mul_nonneg (hq j (z i)).1 Real.pi_nonneg) (by positivity))]
  change (∫ x in region P i j, P.outcome x z ∂volume) /
      (P.zeta (region P i j)).toReal = q j (z i)
  rw [hnum, hmass i j, ENNReal.toReal_ofReal (le_of_lt harea)]
  apply (div_eq_iff harea.ne').2
  ring
