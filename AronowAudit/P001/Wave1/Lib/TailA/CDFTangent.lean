import AronowAudit.P001.P001_Foundations
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.TightCoordinateUniqueness
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! Closed separable CDF tangent paths, tight supported laws, and bridge uniqueness. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace AronowAudit.P001.Wave1.TailA

set_option maxHeartbeats 800000

/-- Evaluation is bounded by the uniform distance. -/
theorem cdf_tangent_eval_dist (h g : KolmogorovSpace) (x : ℝ) :
    |h x - g x| ≤ dist h g := by
  simpa only [dist_eq_norm, lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] using
    lp.norm_apply_le_norm ENNReal.top_ne_zero (h - g) x

/-- Uniform limits preserve CDF-uniform continuity and the endpoint zeros. -/
theorem cdf_tangent_closed (F : ℝ → ℝ) : IsClosed (CDFTangent F) := by
  apply isClosed_of_closure_subset
  intro h hh
  constructor
  · intro ε hε
    obtain ⟨g, hg, hgh⟩ := Metric.mem_closure_iff.mp hh (ε / 3) (by positivity)
    obtain ⟨δ, hδ, hgδ⟩ := hg.1 (ε / 3) (by positivity)
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy
    have hx := cdf_tangent_eval_dist h g x
    have hy := cdf_tangent_eval_dist g h y
    rw [dist_comm g h] at hy
    have hm := hgδ x y hxy
    calc
      |h x - h y| = |(h x - g x) + (g x - g y) + (g y - h y)| := by congr 1; ring
      _ ≤ |h x - g x| + |g x - g y| + |g y - h y| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ < ε := by linarith
  · intro x hx
    have hc : IsClosed {g : KolmogorovSpace | g x = 0} :=
      isClosed_eq (lp.evalCLM ℝ (fun _ : ℝ => ℝ) ∞ x).continuous continuous_const
    exact (closure_minimal (fun g hg => hg.2 x hx) hc) hh

/-- CDF-uniform continuity forces paths to be constant on every CDF fiber. -/
theorem cdf_tangent_fiber (F : ℝ → ℝ) {h : KolmogorovSpace}
    (hh : h ∈ CDFTangent F) {x y : ℝ} (hxy : F x = F y) : h x = h y := by
  by_contra hne
  have hε : 0 < |h x - h y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δ, hδ, hd⟩ := hh.1 _ hε
  exact (lt_irrefl _ (hd x y (by simpa [hxy] using hδ)))

/-- Every tangent path extends continuously from the CDF range to its closure. -/
theorem cdf_tangent_extension (F : ℝ → ℝ) {h : KolmogorovSpace}
    (hh : h ∈ CDFTangent F) :
    ∃ g : C(closure (range F), ℝ), ∀ x,
      g ⟨F x, subset_closure (mem_range_self x)⟩ = h x := by
  classical
  let f : range F → ℝ := fun y => h y.property.choose
  have hfval (x : ℝ) : f ⟨F x, mem_range_self x⟩ = h x := by
    exact cdf_tangent_fiber F hh (Exists.choose_spec (show ∃ y, F y = F x from ⟨x, rfl⟩))
  have hf : UniformContinuous f := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := hh.1 ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy
    change |h x.property.choose - h y.property.choose| < ε
    change |x.val - y.val| < δ at hxy
    apply hd
    simpa only [x.property.choose_spec, y.property.choose_spec, Real.dist_eq] using hxy
  let e : range F → closure (range F) := inclusion subset_closure
  have he : IsUniformInducing e :=
    (isUniformEmbedding_set_inclusion (subset_closure : range F ⊆ closure (range F))).isUniformInducing
  have hd : DenseRange e := (denseRange_inclusion_iff subset_closure).2 subset_rfl
  let g : C(closure (range F), ℝ) :=
    ⟨(he.isDenseInducing hd).extend f,
      (uniformContinuous_uniformly_extend he hd hf).continuous⟩
  refine ⟨g, ?_⟩
  intro x
  exact (uniformly_extend_of_ind he hd hf ⟨F x, mem_range_self x⟩).trans (hfval x)

/-- Pull continuous functions on the compact CDF range back to bounded paths. -/
def cdf_value_pullback (F : ℝ → ℝ) [CompactSpace (closure (range F))] :
    C(closure (range F), ℝ) →L[ℝ] KolmogorovSpace := by
  let L : C(closure (range F), ℝ) →ₗ[ℝ] KolmogorovSpace :=
    { toFun := fun g => ⟨fun x => g ⟨F x, subset_closure (mem_range_self x)⟩,
        memℓp_infty ⟨‖g‖, by
          rintro r ⟨x, rfl⟩
          exact g.norm_coe_le_norm _⟩⟩
      map_add' := by intro f g; apply lp.ext; funext x; rfl
      map_smul' := by intro a g; apply lp.ext; funext x; rfl }
  exact L.mkContinuous 1 fun g => by
    simp only [one_mul]
    apply lp.norm_le_of_forall_le (norm_nonneg g)
    intro x
    exact g.norm_coe_le_norm _

/-- Compactness of the CDF-value closure gives separability in uniform norm. -/
theorem cdf_tangent_separable (F : ℝ → ℝ)
    (hF : TotallyBounded (Set.range F)) : TopologicalSpace.IsSeparable (CDFTangent F) := by
  have hK : IsCompact (closure (range F)) :=
    isCompact_iff_totallyBounded_isComplete.mpr ⟨hF.closure, isClosed_closure.isComplete⟩
  let instCompactCDFValueClosure : CompactSpace (closure (range F)) :=
    isCompact_iff_compactSpace.mp hK
  apply (isSeparable_range (cdf_value_pullback F).continuous).mono
  intro h hh
  obtain ⟨g, hg⟩ := cdf_tangent_extension F hh
  refine ⟨g, ?_⟩
  apply lp.ext
  funext x
  exact hg x


/-- A finite law carried by the closed separable tangent is tight in the full path space. -/
theorem cdf_tangent_tight [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (F : ℝ → ℝ) (hF : TotallyBounded (range F))
    (ν : Measure KolmogorovSpace) [IsFiniteMeasure ν]
    (hsupport : ν (CDFTangent F)ᶜ = 0) :
    IsTightMeasureSet ({ν} : Set (Measure KolmogorovSpace)) := by
  let instClosedCDFTangent : IsClosed (CDFTangent F) := cdf_tangent_closed F
  let instSeparableCDFTangent : SeparableSpace (CDFTangent F) :=
    (cdf_tangent_separable F hF).separableSpace
  let ρ : Measure (CDFTangent F) := ν.comap Subtype.val
  have hpush : ρ.map (Subtype.val : CDFTangent F → KolmogorovSpace) = ν := by
    rw [show ρ = ν.comap Subtype.val from rfl,
      map_comap_subtype_coe (cdf_tangent_closed F).measurableSet,
      Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport)]
  have ht : IsTightMeasureSet ({ρ} : Set (Measure (CDFTangent F))) :=
    isTightMeasureSet_singleton
  simpa only [image_singleton, hpush] using ht.map continuous_subtype_val

/-- The values of an arbitrary probability CDF lie in the compact unit interval. -/
theorem cdf_value_totallyBounded (P : Measure ℝ) [IsProbabilityMeasure P] :
    TotallyBounded (range (cdf P id)) := by
  apply isCompact_Icc.totallyBounded.subset
  rintro r ⟨x, rfl⟩
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  change (P {ω | id ω ≤ x}).toReal ≤ 1
  have hm : P {ω | id ω ≤ x} ≤ 1 := prob_le_one
  simpa using ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hm

/-- Tightness of a supplied CDF bridge follows from its tangent-support clause. -/
theorem cdf_bridge_tight [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (ν : Measure KolmogorovSpace) [IsProbabilityMeasure ν]
    (hν : IsCDFBridge (cdf P id) ν) :
    IsTightMeasureSet ({ν} : Set (Measure KolmogorovSpace)) :=
  cdf_tangent_tight (cdf P id) (cdf_value_totallyBounded P) ν hν.1

/-- Threshold evaluation is a continuous linear coordinate on the path space. -/
def cdf_evaluation (x : ℝ) : KolmogorovSpace →L[ℝ] ℝ :=
  lp.evalCLM ℝ (fun _ : ℝ => ℝ) ∞ x

/-- All threshold evaluations together separate bounded paths. -/
theorem cdf_evaluation_separates (h g : KolmogorovSpace)
    (heq : ∀ x, cdf_evaluation x h = cdf_evaluation x g) : h = g := by
  apply lp.ext
  funext x
  exact heq x

/-- The specified scalar Gaussian projections determine every finite coordinate-vector law. -/
theorem cdf_bridge_finite_laws [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (F : ℝ → ℝ) (ν κ : Measure KolmogorovSpace)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (hν : IsCDFBridge F ν) (hκ : IsCDFBridge F κ)
    (r : ℕ) (x : Fin r → ℝ) :
    ν.map (AsymptoticStatistics.finiteCoordinateCLM cdf_evaluation x) =
      κ.map (AsymptoticStatistics.finiteCoordinateCLM cdf_evaluation x) := by
  let T : KolmogorovSpace →L[ℝ] EuclideanSpace ℝ (Fin r) :=
    AsymptoticStatistics.finiteCoordinateCLM cdf_evaluation x
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_eq_charFun_map_inner_one T.continuous.aemeasurable,
    charFun_map_eq_charFun_map_inner_one T.continuous.aemeasurable]
  have heq : (fun h => inner (𝕜 := ℝ) (T h) t) =
      fun h => ∑ j, t j * h (x j) := by
    funext h
    simp [T, PiLp.inner_apply, AsymptoticStatistics.finiteCoordinateCLM,
      cdf_evaluation, lp.evalCLM, lp.evalₗ]
    rfl
  rw [heq, (hν.2 r x (fun j => t j)).2, (hκ.2 r x (fun j => t j)).2]

/-- Supplied bridges are equal: both tightness premises are derived from tangent support. -/
theorem cdf_bridge_unique [MeasurableSpace KolmogorovSpace] [BorelSpace KolmogorovSpace]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (ν κ : Measure KolmogorovSpace) [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (hν : IsCDFBridge (cdf P id) ν) (hκ : IsCDFBridge (cdf P id) κ) : ν = κ := by
  exact AsymptoticStatistics.tightMeasure_eq_of_finiteCoordinate_laws cdf_evaluation
    cdf_evaluation_separates inferInstance inferInstance
    (cdf_bridge_tight P ν hν) (cdf_bridge_tight P κ hκ)
    (cdf_bridge_finite_laws (cdf P id) ν κ hν hκ)

end AronowAudit.P001.Wave1.TailA
