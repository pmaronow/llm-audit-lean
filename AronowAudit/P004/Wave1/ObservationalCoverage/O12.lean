import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import AronowAudit.P004.Wave1.ObservationalCoverage.O7
import AronowAudit.P004.Wave1.ObservationalCoverage.O10
import AronowAudit.P004.Wave1.LinePopulation.N3
import AronowAudit.P004.Wave1.DesignLimits.DL9

/-! Continuous mapping for the actual printed, double-weighted fitted-residual statistic.
The information-inverse identity O7 is used only for N ≥ 3. -/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

theorem oc_armCount_true (N : ℕ) (z : Assignment N) :
    armCount z true = KAct N z + JAct N z := by
  unfold armCount KAct JAct
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : activeGroup N i <;> cases hzi : z i <;> simp [hi, hzi, bit]

theorem oc_RAct_expansion (N : ℕ) (z : Assignment N) :
    RAct N z = KAct N z - 2 * (SAct N z / (nH N * pHatH N z)) * SAct N z +
      KAct N z * (SAct N z / (nH N * pHatH N z))^2 := by
  let b : ℝ := SAct N z / (nH N * pHatH N z)
  have hterm (i : Fin N) :
      (if activeGroup N i then bit (z i) * (activeSign N i - b)^2 else 0) =
        (if activeGroup N i then bit (z i) else 0) - 2 * b * (activeSign N i * bit (z i)) +
          (if activeGroup N i then bit (z i) else 0) * b^2 := by
    by_cases hi : activeGroup N i
    · have hs : (activeSign N i)^2 = 1 := by rw [oc_sign_sq, if_pos hi]
      simp only [if_pos hi]
      calc
        bit (z i) * (activeSign N i - b)^2 =
            bit (z i) * (activeSign N i)^2 - 2 * b * (activeSign N i * bit (z i)) +
              bit (z i) * b^2 := by ring
        _ = bit (z i) - 2 * b * (activeSign N i * bit (z i)) + bit (z i) * b^2 := by
          rw [hs]
          ring
    · simp only [if_neg hi, oc_sign_eq_zero N i hi, zero_mul, mul_zero, sub_zero,
        zero_add]
  change (∑ i, if activeGroup N i then bit (z i) * (activeSign N i - b)^2 else 0) =
    KAct N z - 2 * b * SAct N z + KAct N z * b^2
  simp_rw [hterm]
  simp only [KAct, SAct, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]

/-- Coordinates are (K/N, J/N, S/N, p̂_H, n_H/N). -/
def oc_sahMap (x : Fin 5 → ℝ) : ℝ :=
  let b := x 2 / (x 4 * x 3)
  (x 0 + x 1)^2 * (x 0 - 2 * b * x 2 + x 0 * b^2) / (x 3)^4

def oc_sahPoint : Fin 5 → ℝ := ![1 / 8, 3 / 40, 0, 1 / 2, 1 / 4]

theorem oc_sahMap_continuous : ContinuousAt oc_sahMap oc_sahPoint := by
  have hx (k : Fin 5) : ContinuousAt (fun x : Fin 5 → ℝ => x k) oc_sahPoint :=
    (continuous_apply k).continuousAt
  have htwo : ContinuousAt (fun _ : Fin 5 → ℝ => (2 : ℝ)) oc_sahPoint :=
    continuousAt_const
  have hb : ContinuousAt (fun x : Fin 5 → ℝ => x 2 / (x 4 * x 3)) oc_sahPoint := by
    apply (hx 2).div ((hx 4).mul (hx 3))
    norm_num [oc_sahPoint]
  have hnum : ContinuousAt (fun x : Fin 5 → ℝ =>
      (x 0 + x 1)^2 *
        (x 0 - 2 * (x 2 / (x 4 * x 3)) * x 2 + x 0 * (x 2 / (x 4 * x 3))^2))
      oc_sahPoint :=
    (((hx 0).add (hx 1)).pow 2).mul
      (((hx 0).sub ((htwo.mul hb).mul (hx 2))).add ((hx 0).mul (hb.pow 2)))
  change ContinuousAt (fun x : Fin 5 → ℝ =>
    (x 0 + x 1)^2 *
      (x 0 - 2 * (x 2 / (x 4 * x 3)) * x 2 + x 0 * (x 2 / (x 4 * x 3))^2) /
        (x 3)^4) oc_sahPoint
  apply hnum.div ((hx 3).pow 4)
  norm_num [oc_sahPoint]

theorem oc_sahMap_value : oc_sahMap oc_sahPoint = (2 / 25 : ℝ) := by
  norm_num [oc_sahMap, oc_sahPoint]

theorem oc_sahMap_identity (N : ℕ) (hN : 3 ≤ N) (z : Assignment N) :
    oc_sahMap ![KAct N z / N, JAct N z / N, SAct N z / N, pHatH N z, nH N / N] =
      (N : ℝ) * printedSAH (propensities (activeO N) (activeMLE N z))
        (circleAverage (activePopulation N) 0) (spatialNeighborhoods activePopulation 0 N)
        (fun i a => dot (activeO N i) (fittedBeta (propensities (activeO N) (activeMLE N z))
          (circleAverage (activePopulation N) 0) (activeO N) a z)) z := by
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hHne : nH N ≠ 0 := ne_of_gt (oc_nH_pos N hNp)
  have hph : (1 : ℝ) / 20 ≤ pHatH N z := (oc_clip_bounds _).1
  have hphne : pHatH N z ≠ 0 := ne_of_gt (by linarith : 0 < pHatH N z)
  have hR : circleAverage (activePopulation N) 0 = activeTable N :=
    AronowAudit.P004.Wave1.LinePopulation.n3_proof (activeTable N)
  rw [hR, o7_proof N hN z, oc_armCount_true, oc_RAct_expansion]
  norm_num only [oc_sahMap, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
  try simp only [Matrix.cons_val]
  field_simp [ne_of_gt hNr, hHne, hphne] <;> ring

theorem o12_proof : O12 := by
  let p : ∀ N, Fin N → ℝ := fun N => propensities (activeO N) activeTheta
  let U : Fin 5 → ∀ N, Assignment N → ℝ :=
    ![fun N z => KAct N z / N,
      fun N z => JAct N z / N,
      fun N z => SAct N z / N,
      fun N z => pHatH N z,
      fun N _ => nH N / N]
  obtain ⟨hK, hJ, hS, hph, hH⟩ := o10_proof
  have hH0 : InProb p (fun N _ => nH N / N - 1 / 4) := by
    apply (dl4_proof p oc_admissible).2.2
    convert hH.sub (tendsto_const_nhds (x := (1 / 4 : ℝ))) using 1 <;> norm_num
  have hU : ∀ k, InProb p (fun N z => U k N z - oc_sahPoint k) := by
    intro k
    fin_cases k
    · change InProb p (fun N z => KAct N z / N - 1 / 8)
      exact hK
    · change InProb p (fun N z => JAct N z / N - 3 / 40)
      exact hJ
    · change InProb p (fun N z => SAct N z / N - 0)
      exact hS
    · change InProb p (fun N z => pHatH N z - 1 / 2)
      exact hph
    · change InProb p (fun N _ => nH N / N - 1 / 4)
      exact hH0
  have hmap : InProb p (fun N z => oc_sahMap (fun k => U k N z) - 2 / 25) := by
    simpa only [oc_sahMap_value] using
      dl9_proof p oc_admissible U oc_sahPoint oc_sahMap oc_sahMap_continuous hU
  apply oc_inProb_congr (U := fun N z => oc_sahMap (fun k => U k N z) - 2 / 25) _ hmap
  filter_upwards [eventually_ge_atTop 3] with N hN
  intro z
  have hvec : (fun k => U k N z) =
      ![KAct N z / N, JAct N z / N, SAct N z / N, pHatH N z, nH N / N] := by
    funext k
    fin_cases k <;> rfl
  rw [hvec, oc_sahMap_identity N hN z]

end
end AronowAudit.P004.Wave1.ObservationalCoverage
