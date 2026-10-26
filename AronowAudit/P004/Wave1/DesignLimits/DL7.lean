import AronowAudit.P004.Wave1.DesignLimits.DL9
import AronowAudit.P053.P053_NormalQuantiles
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-!
Deterministic rescaling by fixed-threshold CDF sandwiches.
The argument uses continuity of the Gaussian CDF. Strict-threshold probability
limits follow without assuming that the finite distributions have no atoms.
-/

namespace AronowAudit.P004.Wave1.DesignLimits

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

namespace DLbSupport

theorem normalCDF_eq_cdf (x : ℝ) :
    normalCDF x = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x := by
  exact (ProbabilityTheory.cdf_eq_real
    (μ := ProbabilityTheory.gaussianReal 0 1) x).symm

theorem normalCDF_continuous : Continuous normalCDF := by
  letI : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have he : normalCDF = ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) :=
    funext normalCDF_eq_cdf
  rw [he]
  exact continuous_iff_continuousAt.mpr
    (fun x => AronowAudit.P053.NormalCompletion.cdf_continuousAt
      (ProbabilityTheory.gaussianReal 0 1) x)

theorem normalCDF_neg (x : ℝ) : normalCDF (-x) = 1 - normalCDF x := by
  simpa only [normalCDF_eq_cdf] using
    AronowAudit.P053.NormalCompletion.normal_cdf_neg x

/-- Continuity supplies a strictly smaller threshold with CDF above any
strict lower bound on the CDF at `x`. -/
theorem cdf_left (x b : ℝ) (hb : b < normalCDF x) :
    ∃ y : ℝ, y < x ∧ b < normalCDF y := by
  have hc : Tendsto normalCDF (nhds x) (nhds (normalCDF x)) :=
    normalCDF_continuous.continuousAt.tendsto
  have he : ∀ᶠ y in nhds x, b < normalCDF y := (tendsto_order.mp hc).1 b hb
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨x - δ / 2, by linarith, hnear ?_⟩
  rw [Real.dist_eq, abs_of_neg (by linarith : x - δ / 2 - x < 0)]
  linarith

/-- The corresponding strictly larger threshold for an upper CDF bound. -/
theorem cdf_right (x b : ℝ) (hb : normalCDF x < b) :
    ∃ y : ℝ, x < y ∧ normalCDF y < b := by
  have hc : Tendsto normalCDF (nhds x) (nhds (normalCDF x)) :=
    normalCDF_continuous.continuousAt.tendsto
  have he : ∀ᶠ y in nhds x, normalCDF y < b := (tendsto_order.mp hc).2 b hb
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨x + δ / 2, by linarith, hnear ?_⟩
  rw [Real.dist_eq, abs_of_pos (by linarith : 0 < x + δ / 2 - x)]
  linarith

/-- If every strictly smaller/larger fixed CDF threshold eventually bounds
`q`, continuity identifies its limit. There is no common threshold in `N`. -/
theorem normal_sandwich (p : ∀ N, Fin N → ℝ)
    (Z : ∀ N, Assignment N → ℝ) (hZ : NormalLimit p Z) (x : ℝ) (q : ℕ → ℝ)
    (hlo : ∀ y : ℝ, y < x →
      ∀ᶠ N in atTop, prob (p N) (fun z => Z N z ≤ y) ≤ q N)
    (hhi : ∀ y : ℝ, x < y →
      ∀ᶠ N in atTop, q N ≤ prob (p N) (fun z => Z N z ≤ y)) :
    Tendsto q atTop (nhds (normalCDF x)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨y, hy, hby⟩ := cdf_left x b hb
    filter_upwards [hlo y hy, (tendsto_order.mp (hZ y)).1 b hby] with N hN hbN
    exact lt_of_lt_of_le hbN hN
  · intro b hb
    obtain ⟨y, hy, hyb⟩ := cdf_right x b hb
    filter_upwards [hhi y hy, (tendsto_order.mp (hZ y)).2 b hyb] with N hN hbN
    exact lt_of_le_of_lt hN hbN

/-- Strict threshold probabilities have the same normal limit. This avoids
assuming the finite distributions themselves have no atoms. -/
theorem normalLimit_lt (p : ∀ N, Fin N → ℝ) (hp : AdmissibleSeq p)
    (Z : ∀ N, Assignment N → ℝ) (hZ : NormalLimit p Z) (x : ℝ) :
    Tendsto (fun N => prob (p N) (fun z => Z N z < x)) atTop
      (nhds (normalCDF x)) := by
  apply normal_sandwich p Z hZ x
  · intro y hy
    exact Eventually.of_forall (fun N => prob_mono (p N) (hp N) _ _
      (fun z hz => lt_of_le_of_lt hz hy))
  · intro y hy
    exact Eventually.of_forall (fun N => prob_mono (p N) (hp N) _ _
      (fun z hz => (lt_trans hz hy).le))

end DLbSupport

/-- Rescaling by a deterministic sequence converging to one preserves the CLT. -/
theorem dl7_proof : DL7 := by
  classical
  intro p hp Z a hZ ha x
  have hpos : ∀ᶠ N in atTop, 0 < a N :=
    (tendsto_order.mp ha).1 0 (by norm_num)
  have hquot : Tendsto (fun N => x / a N) atTop (nhds x) := by
    have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => x) atTop (nhds x)).div ha (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at h
    exact h
  apply DLbSupport.normal_sandwich p Z hZ x
  · intro y hy
    filter_upwards [hpos, (tendsto_order.mp hquot).1 y hy] with N haN hyN
    apply DLbSupport.prob_mono (p N) (hp N)
    intro z hz
    have hdiv : Z N z ≤ x / a N := le_trans hz hyN.le
    have hmul : Z N z * a N ≤ x := (le_div_iff₀ haN).mp hdiv
    simpa only [mul_comm] using hmul
  · intro y hy
    filter_upwards [hpos, (tendsto_order.mp hquot).2 y hy] with N haN hyN
    apply DLbSupport.prob_mono (p N) (hp N)
    intro z hz
    have hmul : Z N z * a N ≤ x := by simpa only [mul_comm] using hz
    have hdiv : Z N z ≤ x / a N := (le_div_iff₀ haN).mpr hmul
    exact le_trans hdiv hyN.le

end
end AronowAudit.P004.Wave1.DesignLimits
