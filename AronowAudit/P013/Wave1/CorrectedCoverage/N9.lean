import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.CorrectedCoverage

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- The finite Wald inclusion and the Gaussian interval limit yield the coverage bound. -/
theorem n9_proof : N9 := by
  intro h6 h7 L instL P X Vhat target V hclt hV htail α hα hα1
  classical
  obtain ⟨hz, hquant⟩ := h6.2.2.2 α hα hα1
  let C : ℕ → ℝ := fun n => probability (P n) (fun z => 0 ≤ Vhat n z ∧
    |X n z - target n| ≤ normalCritical α * Real.sqrt (Vhat n z))
  have hbelow : IsBoundedUnder (· ≥ ·) atTop C :=
    isBoundedUnder_of ⟨0, fun n => probability_nonneg _ _⟩
  have habove : IsBoundedUnder (· ≤ ·) atTop C := by
    refine isBoundedUnder_of ⟨1, fun n => ?_⟩
    calc
      C n ≤ probability (P n) (fun _ => True) := probability_mono (P n) _ _ (by
        intro z _
        trivial)
      _ = 1 := by simp only [probability, if_true, (P n).total]
  have hfixed (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
      2 * normalCDF (normalCritical α * Real.sqrt (1 - η)) - 1 ≤ liminf C atTop := by
    have hwidth : 0 < normalCritical α * Real.sqrt (1 - η) :=
      mul_pos hz (Real.sqrt_pos.mpr (by linarith))
    have hmain : Tendsto (fun n => probability (P n)
        (fun z => |(X n z - target n) / Real.sqrt (V n)| ≤
          normalCritical α * Real.sqrt (1 - η))) atTop
        (𝓝 (2 * normalCDF (normalCritical α * Real.sqrt (1 - η)) - 1)) :=
      h7 h6 P (fun n z => (X n z - target n) / Real.sqrt (V n))
        (fun _ => normalCritical α * Real.sqrt (1 - η))
        (normalCritical α * Real.sqrt (1 - η)) hclt hwidth tendsto_const_nhds
    have hdiff : Tendsto (fun n => probability (P n)
        (fun z => |(X n z - target n) / Real.sqrt (V n)| ≤
          normalCritical α * Real.sqrt (1 - η)) -
        probability (P n) (fun z => Vhat n z < (1 - η) * V n)) atTop
        (𝓝 (2 * normalCDF (normalCritical α * Real.sqrt (1 - η)) - 1)) := by
      simpa only [sub_zero] using hmain.sub (htail η hη hη1)
    apply (le_liminf_iff habove.isCoboundedUnder_flip hbelow).mpr
    intro y hy
    have hevent := hdiff.eventually (lt_mem_nhds hy)
    filter_upwards [hV, hevent] with n hn hyn
    exact hyn.trans_le
      (finite_wald_coverage_bound (P n) (X n) (Vhat n) (target n) (V n) η
        (normalCritical α) hn hη hη1 hz.le)
  -- A concrete sequence of shrinkage parameters avoids imposing a ratio limit.
  let η : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2)
  have hηpos (k : ℕ) : 0 < η k := by dsimp [η]; positivity
  have hηlt (k : ℕ) : η k < 1 := by
    dsimp [η]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 2)).mpr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hηzero : Tendsto η atTop (𝓝 0) := by
    simpa only [η, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 2)
  have harg : Tendsto (fun k => normalCritical α * Real.sqrt (1 - η k)) atTop
      (𝓝 (normalCritical α)) := by
    have hs : Tendsto (fun k => Real.sqrt (1 - η k)) atTop (𝓝 (Real.sqrt (1 - 0))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hηzero)
    simpa only [sub_zero, Real.sqrt_one, mul_one] using
      (tendsto_const_nhds (x := normalCritical α)).mul hs
  have hlimit : Tendsto (fun k => 2 * normalCDF (normalCritical α * Real.sqrt (1 - η k)) - 1)
      atTop (𝓝 (1 - α)) := by
    have hΦ : Tendsto
        (fun k => normalCDF (normalCritical α * Real.sqrt (1 - η k))) atTop
        (𝓝 (normalCDF (normalCritical α))) := h6.1.continuousAt.tendsto.comp harg
    have ht := ((tendsto_const_nhds (x := (2 : ℝ))).mul hΦ).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
    have heq : 2 * normalCDF (normalCritical α) - 1 = 1 - α := by
      rw [hquant]
      ring
    rwa [heq] at ht
  exact le_of_tendsto hlimit (Eventually.of_forall (fun k => hfixed (η k) (hηpos k) (hηlt k)))

end

end AronowAudit.P013.Wave1.CorrectedCoverage
