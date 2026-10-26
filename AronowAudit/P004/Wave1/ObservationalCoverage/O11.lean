import AronowAudit.P004.Wave1.ObservationalCoverageBlueprint
import AronowAudit.P004.Wave1.ObservationalCoverage.O6
import AronowAudit.P004.Wave1.ObservationalCoverage.O8
import AronowAudit.P004.Wave1.ObservationalCoverage.O10
import AronowAudit.P004.Wave1.LinePopulation.N3
import AronowAudit.P004.Wave1.DesignLimits.DL5
import AronowAudit.P004.Wave1.DesignLimits.DL7
import AronowAudit.P004.Wave1.FiniteConditioning.FC7

/-! The standardized limit of the actual fitted IPW estimator.  The error is controlled
in L¹ by O9 and finite-design Cauchy--Schwarz; no independence of fitted quantities is used. -/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

def oc_ipwRemainder (N : ℕ) (z : Assignment N) : ℝ :=
  (2 / Real.sqrt N) * SAct N z * (1 - 2 * pHatH N z) / pHatH N z

theorem oc_ipwRemainder_bound (N : ℕ) (hN : 0 < N) (z : Assignment N) :
    |oc_ipwRemainder N z| ≤
      (40 / Real.sqrt N) * (|SAct N z| * |1 - 2 * pHatH N z|) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hph : (1 : ℝ) / 20 ≤ pHatH N z := (oc_clip_bounds _).1
  have hphpos : 0 < pHatH N z := by linarith
  have hinv : 1 / pHatH N z ≤ 20 := by
    apply (div_le_iff₀ hphpos).mpr
    linarith
  calc
    |oc_ipwRemainder N z| =
        ((2 / Real.sqrt N) * (|SAct N z| * |1 - 2 * pHatH N z|)) *
          (1 / pHatH N z) := by
      dsimp only [oc_ipwRemainder]
      simp only [abs_div, abs_mul, abs_of_pos hsN, abs_of_pos hphpos, Nat.abs_ofNat]
      ring
    _ ≤ ((2 / Real.sqrt N) * (|SAct N z| * |1 - 2 * pHatH N z|)) * 20 := by
      apply mul_le_mul_of_nonneg_left hinv
      positivity
    _ = (40 / Real.sqrt N) * (|SAct N z| * |1 - 2 * pHatH N z|) := by ring

theorem oc_ipwRemainder_mean_bound (N : ℕ) (hN : 0 < N) :
    expect (propensities (activeO N) activeTheta) (fun z => |oc_ipwRemainder N z|) ≤
      40 * Real.sqrt (1 / nH N) := by
  let p : Fin N → ℝ := propensities (activeO N) activeTheta
  have hp : ∀ i, 0 < p i ∧ p i < 1 := oc_admissible N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  obtain ⟨hL0, _, _, _, _, _, _, hCS, _, _⟩ :=
    AronowAudit.P004.Wave1.FiniteConditioning.fc7_proof p hp
  have hS : l2Norm p (fun z => |SAct N z|) ≤ Real.sqrt N := by
    simp only [l2Norm, sq_abs]
    exact Real.sqrt_le_sqrt (o9_proof N hN).1
  have hD : l2Norm p (fun z => |1 - 2 * pHatH N z|) ≤ Real.sqrt (1 / nH N) := by
    simp only [l2Norm, sq_abs]
    exact Real.sqrt_le_sqrt (o9_proof N hN).2
  have hprod : expect p (fun z => |SAct N z| * |1 - 2 * pHatH N z|) ≤
      Real.sqrt N * Real.sqrt (1 / nH N) := by
    calc
      expect p (fun z => |SAct N z| * |1 - 2 * pHatH N z|) ≤
          |expect p (fun z => |SAct N z| * |1 - 2 * pHatH N z|)| := le_abs_self _
      _ ≤ l2Norm p (fun z => |SAct N z|) *
          l2Norm p (fun z => |1 - 2 * pHatH N z|) := hCS _ _
      _ ≤ Real.sqrt N * Real.sqrt (1 / nH N) :=
        mul_le_mul hS hD (hL0 _) (Real.sqrt_nonneg _)
  calc
    expect p (fun z => |oc_ipwRemainder N z|) ≤
        (40 / Real.sqrt N) *
          expect p (fun z => |SAct N z| * |1 - 2 * pHatH N z|) := by
      simpa only [expect_mul] using expect_mono p hp _ _ (oc_ipwRemainder_bound N hN)
    _ ≤ (40 / Real.sqrt N) * (Real.sqrt N * Real.sqrt (1 / nH N)) := by
      apply mul_le_mul_of_nonneg_left hprod
      positivity
    _ = 40 * Real.sqrt (1 / nH N) := by
      field_simp [ne_of_gt hsN] <;> ring

theorem oc_ipwRemainder_inProb :
    InProb (fun N => propensities (activeO N) activeTheta) oc_ipwRemainder := by
  apply (dl2_proof _ oc_admissible oc_ipwRemainder).1
  have hupper : Tendsto (fun N => 40 * Real.sqrt (1 / nH N)) atTop (nhds (0 : ℝ)) := by
    simpa only [Real.sqrt_zero, mul_zero] using
      oc_nH_inv_tendsto.sqrt.const_mul (40 : ℝ)
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun N => oc_expect_nonneg N _ (fun z => abs_nonneg _))
    ?_ hupper
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact oc_ipwRemainder_mean_bound N hN

theorem o11_proof : O11 := by
  let p : ∀ N, Fin N → ℝ := fun N => propensities (activeO N) activeTheta
  let Z : ∀ N, Assignment N → ℝ :=
    fun N z => (SAct N z - sAct N / 2) / Real.sqrt (nH N / 4)
  let a : ℕ → ℝ := fun N => 4 * Real.sqrt (nH N / 4) / Real.sqrt N
  have hZ : NormalLimit p Z := o8_proof
  have ha_eq (N : ℕ) : a N = 2 * Real.sqrt (nH N / N) := by
    dsimp only [a]
    rw [Real.sqrt_div (oc_nH_nonneg N) (4 : ℝ),
      Real.sqrt_div (oc_nH_nonneg N) (N : ℝ)]
    norm_num <;> ring
  have ha : Tendsto a atTop (nhds (1 : ℝ)) := by
    have hratio := o10_proof.2.2.2.2
    have hb : Tendsto (fun N => 2 * Real.sqrt (nH N / N)) atTop (nhds (1 : ℝ)) := by
      convert hratio.sqrt.const_mul (2 : ℝ) using 1 <;> norm_num
    exact hb.congr' (Filter.Eventually.of_forall fun N => (ha_eq N).symm)
  have hmain : NormalLimit p (fun N z => a N * Z N z) :=
    dl7_proof p oc_admissible Z a hZ ha
  have hsum : NormalLimit p (fun N z => a N * Z N z + oc_ipwRemainder N z) :=
    dl5_proof p oc_admissible _ _ hmain oc_ipwRemainder_inProb
  apply oc_normalLimit_congr (U := fun N z => a N * Z N z + oc_ipwRemainder N z) _ hsum
  filter_upwards [eventually_gt_atTop 0] with N hN
  intro z
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hnH : 0 < nH N := oc_nH_pos N hN
  have hden : Real.sqrt (nH N / 4) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    positivity
  have hph : (1 : ℝ) / 20 ≤ pHatH N z := (oc_clip_bounds _).1
  have hphne : pHatH N z ≠ 0 := ne_of_gt (by linarith : 0 < pHatH N z)
  have hR : circleAverage (activePopulation N) 0 = activeTable N :=
    AronowAudit.P004.Wave1.LinePopulation.n3_proof (activeTable N)
  rw [hR, o6_proof.1 N hN z, o6_proof.2 N]
  calc
    a N * Z N z + oc_ipwRemainder N z =
        (2 / Real.sqrt N) * (SAct N z / pHatH N z - sAct N) := by
      dsimp only [a, Z, oc_ipwRemainder]
      field_simp [hden, ne_of_gt hsN, hphne] <;> ring
    _ = 2 * (Real.sqrt N / (N : ℝ)) * (SAct N z / pHatH N z - sAct N) := by
      rw [Real.sqrt_div_self']
      ring
    _ = Real.sqrt N * (SAct N z / (N * pHatH N z) - sAct N / N) / (1 / 2) := by
      field_simp [ne_of_gt hNr, hphne] <;> ring

end
end AronowAudit.P004.Wave1.ObservationalCoverage
