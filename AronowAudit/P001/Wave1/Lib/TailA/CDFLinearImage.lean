import AronowAudit.P001.Wave1.Lib.TailA.CDFFiniteApprox
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Finite-coordinate approximation and centered Gaussian closure for CDF bridges. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace AronowAudit.P001.Wave1.TailA

set_option maxHeartbeats 800000

/-- A convenient real form of the centered Gaussian characteristic function. -/
theorem ta18_gaussian_charFun (v : ℝ≥0) (t : ℝ) :
    charFun (gaussianReal 0 v) t = (Real.exp (-(v : ℝ) * t ^ 2 / 2) : ℂ) := by
  rw [charFun_gaussianReal, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Centered real Gaussian laws are closed under pointwise characteristic-function
convergence to a probability law. A nonzero frequency near zero recovers the
variance through the real logarithm. No convergence of moments is assumed. -/
theorem ta18_centered_gaussian_closed (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (v : ℕ → ℝ≥0)
    (hc : ∀ t : ℝ, Tendsto (fun n => charFun (gaussianReal 0 (v n)) t)
      atTop (𝓝 (charFun ρ t))) :
    ∃ w : ℝ≥0, ρ = gaussianReal 0 w := by
  have hzero : 0 < (charFun ρ 0).re := by simp
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (charFun ρ t).re :=
    (Complex.continuous_re.comp continuous_charFun).continuousAt.eventually
      (lt_mem_nhds hzero)
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hevent
  let t : ℝ := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hp : 0 < (charFun ρ t).re := hd (by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith)
  let d : ℝ := -2 * Real.log (charFun ρ t).re / t ^ 2
  have hl : Tendsto (fun n => Real.log (charFun (gaussianReal 0 (v n)) t).re)
      atTop (𝓝 (Real.log (charFun ρ t).re)) :=
    (Real.continuousAt_log hp.ne').tendsto.comp (Complex.continuous_re.tendsto _ |>.comp (hc t))
  have hn (n : ℕ) :
      -2 * Real.log (charFun (gaussianReal 0 (v n)) t).re / t ^ 2 = (v n : ℝ) := by
    rw [ta18_gaussian_charFun, Complex.ofReal_re, Real.log_exp]
    field_simp
    <;> ring
  have hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 d) := by
    have h := ((tendsto_const_nhds (x := (-2 : ℝ))).mul hl).div_const (t ^ 2)
    exact h.congr' (Eventually.of_forall hn)
  have hd0 : 0 ≤ d := ge_of_tendsto hv (Eventually.of_forall fun n => (v n).coe_nonneg)
  let w : ℝ≥0 := ⟨d, hd0⟩
  refine ⟨w, ?_⟩
  apply Measure.ext_of_charFun
  funext s
  have hs : Tendsto (fun n => (Real.exp (-(v n : ℝ) * s ^ 2 / 2) : ℂ))
      atTop (𝓝 (Real.exp (-d * s ^ 2 / 2) : ℂ)) := by
    exact Complex.continuous_ofReal.tendsto _ |>.comp
      (Real.continuous_exp.tendsto _ |>.comp ((hv.neg.mul_const (s ^ 2)).div_const 2))
  calc
    charFun ρ s = (Real.exp (-d * s ^ 2 / 2) : ℂ) :=
      tendsto_nhds_unique (by simpa only [ta18_gaussian_charFun] using hc s) hs
    _ = charFun (gaussianReal 0 w) s := (ta18_gaussian_charFun w s).symm


/-- Almost-sure scalar convergence of centered Gaussians gives a centered
Gaussian law. The characteristic integrands have the constant bound one. -/
theorem ta18_centered_gaussian_ae_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n, AEMeasurable (Y n) μ) (hZ : AEMeasurable Z μ)
    (v : ℕ → ℝ≥0) (hlaw : ∀ n, μ.map (Y n) = gaussianReal 0 (v n))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    ∃ w : ℝ≥0, μ.map Z = gaussianReal 0 w := by
  apply ta18_centered_gaussian_closed (μ.map Z) v
  intro t
  have hcf (W : Ω → ℝ) (hW : AEMeasurable W μ) :
      charFun (μ.map W) t = ∫ ω, Complex.exp (↑(t * W ω) * Complex.I) ∂μ := by
    rw [charFun_apply_real, integral_map hW (by fun_prop)]
    push_cast
    rfl
  simp_rw [← hlaw, hcf _ (hY _), hcf _ hZ]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact ((show Continuous (fun y : ℝ => Complex.exp (↑(t * y) * Complex.I)) by
      fun_prop).measurable.comp_aemeasurable (hY n)).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact Eventually.of_forall fun ω => by simp [Complex.norm_exp]
  · filter_upwards [hlim] with ω hω
    exact Complex.continuous_exp.tendsto _ |>.comp
      ((Complex.continuous_ofReal.tendsto _ |>.comp (hω.const_mul t)).mul_const Complex.I)

/-- Every continuous linear image of a supplied CDF bridge is centered Gaussian.
Finite nets approximate each tangent path in uniform norm; almost-sure scalar
convergence and the proved closure theorem then identify the image law. -/
theorem cdf_bridge_linear_gaussian [MeasurableSpace KolmogorovSpace]
    [BorelSpace KolmogorovSpace] (P : Measure ℝ) [IsProbabilityMeasure P]
    (ν : Measure KolmogorovSpace) [IsProbabilityMeasure ν]
    (hbridge : IsCDFBridge (cdf P id) ν) (L : KolmogorovSpace →L[ℝ] ℝ)
    (hL2 : MemLp (fun h => L h) 2 ν) :
    ν.map L = gaussianReal 0 (var ν (fun h => L h)).toNNReal := by
  classical
  obtain ⟨Y, hfin, hlim⟩ :=
    ta18_cdf_linear_approx (cdf P id) (cdf_value_totallyBounded P) L
  have hex (n : ℕ) : ∃ v : ℝ≥0, ν.map (Y n) = gaussianReal 0 v := by
    obtain ⟨r, x, a, hY⟩ := hfin n
    refine ⟨⟨max (∑ j, ∑ k, a j *
      (min (cdf P id (x j)) (cdf P id (x k)) - cdf P id (x j) * cdf P id (x k)) * a k) 0,
      le_max_right _ _⟩, ?_⟩
    rw [show (Y n : KolmogorovSpace → ℝ) = (fun h => ∑ j, a j * h (x j)) from funext hY]
    exact (hbridge.2 r x a).2
  choose v hv using hex
  have hae : ∀ᵐ h ∂ν, Tendsto (fun n => Y n h) atTop (𝓝 (L h)) := by
    filter_upwards [ae_iff.mpr hbridge.1] with h hh
    exact hlim h hh
  obtain ⟨w, hw⟩ := ta18_centered_gaussian_ae_limit ν (fun n h => Y n h) (fun h => L h)
    (fun n => (Y n).continuous.aemeasurable) hL2.aestronglyMeasurable.aemeasurable v hv hae
  have hvar : var ν (fun h => L h) = (w : ℝ) := by
    change variance (fun h => L h) ν = _
    rw [← variance_id_map L.continuous.aemeasurable, hw, variance_id_gaussianReal]
  rw [hvar, Real.toNNReal_coe]
  exact hw

end AronowAudit.P001.Wave1.TailA
