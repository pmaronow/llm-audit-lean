import SAP.P018b.Defs.WholeW2
import SAP.P018b.Bridge
import AronowAudit.P018.Wave1.Gap.GLP0181B5

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.WH.W2

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise ENNReal

/-- T22, transfer of the Gaussian simulation error law to an arbitrary realization.
Use `AronowAudit.P018.Wave1.simulation_design_correction_proof` on the canonical product.
The `HasLaw` premise identifies the joint input law, so `Measure.map_map` transfers joint
Gaussianity. Transfer independence by `indepFun_iff_map_prod_eq_prod_map_map` and the same
map identity, and transfer the mean and covariance by `HasLaw.integral_comp` and
`HasLaw.covariance_fun_comp`. Coordinate L2 membership follows from
`memLp_id_gaussianReal`, `measurePreserving_eval` and `HasLaw.memLp_comp`; finite sums
give error L2 membership. All maps here are measurable finite sums or coordinate projections.
This is a finite-dimensional law-transport lemma, not an extra stochastic assumption. -/
def T22_L1 : Prop :=
  ∀ N T : ℕ, 2 ≤ N → 1 ≤ T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → SimulationIndex N T → ℝ), Measurable Z →
    HasLaw Z (simulationLaw N T) μ → simulationErrorFacts μ Z

private theorem error_measurable {N T : ℕ} (d : Dyad N) (t : Fin T) :
    Measurable (fun ω : SimulationIndex N T → ℝ => simulationError ω d t) := by
  exact (Finset.measurable_sum (members d) (fun i _ =>
    measurable_pi_apply (Sum.inr (Sum.inl i) : SimulationIndex N T))).add
    (measurable_pi_apply (Sum.inr (Sum.inr (d,t)) : SimulationIndex N T))

/-- The tower property and conditional-expectation linearity give the response mean
on any smaller sigma algebra on which its predictor is measurable. -/
private theorem mean_from_zero_error {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M m : MeasurableSpace Ω)
    (hM : M ≤ m₀) (hm : m ≤ M) (F E : Ω → ℝ)
    (hF : Integrable F μ) (hE : Integrable E μ)
    (hFm : StronglyMeasurable[m] F)
    (hz : MeasureTheory.condExp M μ E =ᵐ[μ] 0) :
    MeasureTheory.condExp m μ (F + E) =ᵐ[μ] F := by
  have hz' : MeasureTheory.condExp m μ E =ᵐ[μ] 0 := by
    calc
      _ =ᵐ[μ] MeasureTheory.condExp m μ (MeasureTheory.condExp M μ E) :=
        (MeasureTheory.condExp_condExp_of_le hm hM).symm
      _ =ᵐ[μ] MeasureTheory.condExp m μ (0 : Ω → ℝ) :=
        MeasureTheory.condExp_congr_ae hz
      _ =ᵐ[μ] 0 := by simp
  have hfix := MeasureTheory.condExp_of_stronglyMeasurable (hm.trans hM) hFm hF
  filter_upwards [MeasureTheory.condExp_add hF hE m, hz'] with ω hω hzω
  simpa only [hfix, Pi.add_apply, hzω, Pi.zero_apply, add_zero] using hω

/-- The error-law leaf and the proved conditional-expectation glue give the whole design. -/
theorem T22_assembly (h1 : T22_L1) : T22WholeStatement := by
  intro N T hN hT Ω mΩ μ hμ Z hZ hNormal hIndependent
  have hLaw : HasLaw Z (simulationLaw N T) μ := hIndependent.hasLaw_pi hNormal
  have hFacts := h1 N T hN hT μ Z hZ hLaw
  let X : Ω → Fin N → ℝ := fun ω i => simulationX (Z ω) i
  let M : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hX : Measurable[mΩ] X :=
    Measurable.of_eval (fun i => (measurable_pi_apply (Sum.inl i)).comp hZ)
  have hM : M ≤ mΩ := hX.comap_le
  have hz (d : Dyad N) (t : Fin T) :
      MeasureTheory.condExp M μ (fun ω => simulationError (Z ω) d t) =ᵐ[μ] 0 := by
    let E : Ω → ℝ := fun ω => simulationError (Z ω) d t
    have hE : Measurable[mΩ] E := (error_measurable d t).comp hZ
    have hind : IndepFun E X μ :=
      hFacts.2.1.comp (measurable_pi_apply (d,t)) measurable_id
    have hc := MeasureTheory.condExp_indep_eq hE.comap_le hM
      (comap_measurable E).stronglyMeasurable hind
    filter_upwards [hc] with ω hω
    exact hω.trans (hFacts.2.2.2.1 d t)
  refine ⟨hFacts, hz, ?_⟩
  intro β₀ β₁ d t
  let F : Ω → ℝ := fun ω => simulationMean β₀ β₁ (Z ω) d
  let E : Ω → ℝ := fun ω => simulationError (Z ω) d t
  have hCoord (a : SimulationIndex N T) : Integrable (fun ω => Z ω a) μ :=
    (hNormal a).integrable ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable
      (by norm_num))
  have hF : Integrable F μ :=
    (integrable_const β₀).add
      (((hCoord (Sum.inl (firstUnit d))).sub
        (hCoord (Sum.inl (secondUnit d)))).abs.const_mul β₁)
  have hE : Integrable E μ := (hFacts.2.2.1 d t).integrable (by norm_num)
  let P : Ω → ℝ × ℝ := fun ω =>
    (simulationX (Z ω) (firstUnit d), simulationX (Z ω) (secondUnit d))
  let R : Ω → ℝ × ℝ := fun ω => ((1 : ℝ), simulationPredictor (Z ω) d)
  have hPM : MeasurableSpace.comap P inferInstance ≤ M := by
    apply MeasurableSpace.comap_le_comap_of_eq_comp
      (fun x : Fin N → ℝ => (x (firstUnit d), x (secondUnit d)))
      ((measurable_pi_apply (firstUnit d)).prodMk (measurable_pi_apply (secondUnit d)))
    rfl
  have hRM : MeasurableSpace.comap R inferInstance ≤ M := by
    apply MeasurableSpace.comap_le_comap_of_eq_comp
      (fun x : Fin N → ℝ => ((1 : ℝ), |x (firstUnit d) - x (secondUnit d)|))
      (measurable_const.prodMk (((measurable_pi_apply (firstUnit d)).sub
        (measurable_pi_apply (secondUnit d))).abs))
    rfl
  have hFP : StronglyMeasurable[MeasurableSpace.comap P inferInstance] F := by
    have hp : Measurable (fun p : ℝ × ℝ => β₀ + β₁ * |p.1 - p.2|) :=
      measurable_const.add (measurable_const.mul ((measurable_fst.sub measurable_snd).abs))
    exact hp.stronglyMeasurable.comp_measurable (comap_measurable P)
  have hFR : StronglyMeasurable[MeasurableSpace.comap R inferInstance] F := by
    have hr : Measurable (fun p : ℝ × ℝ => β₀ + β₁ * p.2) :=
      measurable_const.add (measurable_const.mul measurable_snd)
    exact hr.stronglyMeasurable.comp_measurable (comap_measurable R)
  exact ⟨mean_from_zero_error μ M _ hM hPM F E hF hE hFP (hz d t),
    mean_from_zero_error μ M _ hM hRM F E hF hE hFR (hz d t)⟩

/-- Existing exact arithmetic already proves the full domains; no new leaf is needed. -/
theorem T24_assembly : T24WholeStatement := by
  have hmag : tableMagnitudeFacts := AronowAudit.P018.table_magnitude_correction
  refine ⟨AronowAudit.P018.table_exact_ratios, hmag, ?_,
    AronowAudit.P018.table_rounding_constraints, ?_, ?_, by norm_num, by norm_num,
    by norm_num⟩
  · intro r hr
    exact (hmag.2.2.1 r hr).2.2.1.trans (by norm_num)
  · intro b se
    exact (AronowAudit.P018.significance_rounding_positive b se).1
  · intro b se
    exact (AronowAudit.P018.significance_rounding_positive b se).2

/-- The explicit fair-sign donor gives the counterexample; limit uniqueness refutes zero. -/
theorem T27_assembly : T27WholeStatement := by
  have hd := AronowAudit.P018.Wave1.appendixB_counterexample_proof
  have hprob (N : ℕ) : IsProbabilityMeasure (unitSampleLaw signKernel N) :=
    AronowAudit.P018.Wave1.printed_sign_probability N
  have hi (N : ℕ) : Integrable (fun ω =>
      (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 -
        (trueTarget signKernel N) 0 0) (unitSampleLaw signKernel N) := by
    letI := hprob N
    exact Integrable.of_finite
  have hlim : Tendsto (fun N : ℕ => ∫ ω,
      (sampleVariance members (design signKernel ω) (response signKernel ω)) 0 0 -
        (trueTarget signKernel N) 0 0 ∂ unitSampleLaw signKernel N) atTop (𝓝 (-4)) := by
    apply hd.2.2.2.2.2.1.congr'
    filter_upwards [eventually_ge_atTop 4] with N hN
    letI := hprob N
    have hTarget : trueTarget signKernel N = !![4] := (hd.2.2.2.2.1 N hN).1
    rw [integral_sub Integrable.of_finite (integrable_const _), integral_const,
      hTarget]
    simp
    rfl
  refine ⟨hd.1, hd.2.1, hd.2.2.1,
    AronowAudit.P018.Wave1.appendixB_populationGram, hd.2.2.2.1, hi, ?_, hlim, ?_⟩
  · intro N hN
    exact ⟨(hd.2.2.2.2.1 N hN).1, (hd.2.2.2.2.1 N hN).2.2⟩
  · intro hzero
    have heq := tendsto_nhds_unique hlim hzero
    norm_num at heq

end SAP.P018b.WH.W2
