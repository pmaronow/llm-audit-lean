import SAP.P001d.Defs.WholeW2
import SAP.P001d.Bridge
import AronowAudit.P001.Wave1.Gap.TailA.HeavyMedian

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
namespace SAP.P001d.WH.W2

theorem whole_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] : WholeCDF (cdf ν id) := by
  have he : cdf ν id = fun x => ProbabilityTheory.cdf ν x := by
    funext x
    exact (ProbabilityTheory.cdf_eq_real ν x).symm
  rw [he]
  exact ⟨fun x => ⟨cdf_nonneg ν x, cdf_le_one ν x⟩, monotone_cdf ν,
    fun x => (ProbabilityTheory.cdf ν).right_continuous x,
    tendsto_cdf_atBot ν, tendsto_cdf_atTop ν⟩

theorem heavy_probability : IsProbabilityMeasure heavyBootstrapLaw := by
  have hu : uniformLaw (-1) 1 Set.univ = 1 := by
    change AronowAudit.P001.uniformLaw (-1) 1 Set.univ = 1
    rw [AronowAudit.P001.Wave1.regular_uniform_symmetric_eq, Measure.smul_apply,
      Measure.restrict_apply MeasurableSet.univ]
    norm_num [Real.volume_Icc]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hu0 : uniformLaw 0 1 Set.univ = 1 :=
    AronowAudit.P001.Wave1.regular_uniform_zero_one_mass
  have hm := AronowAudit.P001.Wave1.regular_heavy_transform_measurable
  constructor
  rw [heavyBootstrapLaw, Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply hm MeasurableSet.univ,
    Measure.map_apply (show Measurable (fun u : ℝ => -((2 : ℝ)^(1/u^2))) from hm.neg)
      MeasurableSet.univ]
  simp only [Set.preimage_univ, hu, hu0, smul_eq_mul, mul_one]
  norm_num
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]

theorem heavy_unique_median : cdf heavyBootstrapLaw id 0 = 1/2 ∧
    (∀ x : ℝ, x < 0 → cdf heavyBootstrapLaw id x < 1/2) ∧
    (∀ x : ℝ, 0 < x → 1/2 < cdf heavyBootstrapLaw id x) := by
  haveI := heavy_probability
  have h := AronowAudit.P001.Wave1.TailA.heavyMedian_local_data heavyBootstrapLaw
    (fun _ : ℕ => id) measurable_id (by simpa using Bridge.heavyBootstrapLaw_eq)
  obtain ⟨δ, hδ, hf, hfn, hfm, hc, hp, hz, hl, hr⟩ := h
  exact ⟨hz, hl, hr⟩

/-- The local linear branch proves the derivative on every bounded uniform direction. -/
theorem local_hadamard (F : ℝ → ℝ) (hF : F 0 = 1/2) :
    WholeHadamardEvaluation regularHeavyFunctional F := by
  intro h _ t v ht ht0 _ hv
  have hv0 := hv.tendsto_at 0
  have hm : Tendsto (fun n => t n * v n 0) atTop (nhds 0) := by
    simpa only [zero_mul] using ht0.mul hv0
  have he : ∀ᶠ n in atTop, |t n*v n 0| < 1/4 := by
    have hh := (tendsto_order.mp hm.abs).2 (1/4 : ℝ) (by norm_num)
    simpa only [abs_zero] using hh
  have hfbranch : regularHeavyFunctional F = F 0 - 1/2 := by
    apply ite_eq_left
    rw [hF]
    constructor <;> norm_num
  apply hv0.congr'
  filter_upwards [he] with n hn
  have hg : (F 0 + t n*v n 0) ∈ Set.Icc (1/4 : ℝ) (3/4) := by
    rw [hF]
    have ha := abs_lt.mp hn
    constructor <;> linarith
  rw [regularHeavyFunctional, ite_eq_left hg, hfbranch]
  field_simp [(ht n).ne']
  ring

end SAP.P001d.WH.W2
