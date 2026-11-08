import SAP.P001b.Defs.WholeW2
import SAP.P001b.Bridge
import AronowAudit.P001.P001_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001b.WH.W2

universe u

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Recover the planar density representation from the defining iterated CDF
integrals. Tonelli identifies these with the weighted measure on lower-left
rectangles. To prove uniqueness, fix a second-coordinate lower ray, restrict
both measures to its cylinder and push forward by `Prod.fst`; apply
`Measure.ext_of_Iic`. Next fix any measurable first-coordinate set and repeat
with `Prod.snd`; conclude by `Measure.ext_prod`. In both applications only the
restriction of the probability law needs to be finite. Finally read off total
mass one and deduce global integrability. This avoids assumptions on exceptional
slices and avoids a separate generating-system construction. -/
def T30_L1 : Prop :=
  ∀ (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (f : ℝ × ℝ → ℝ),
    JointCDFDensity ν f → JointDensity ν f

/-- Pointwise PMF factorization characterizes independence of countable-range
real random variables. Restrict each variable to its countable range subtype.
For the joint law and product marginal law on the product of these subtypes,
use `Measure.ext_of_singleton`, `Measure.prod_prod`, and `Measure.map_apply`.
Transport independence by the subtype inclusions, or directly apply the
measure-intersection characterization and countable disjoint unions of atoms.
Finite probability masses let `ENNReal.toReal` preserve equality and products.
Points outside either actual range have empty fibers, so their PMF identities
hold too. All real x,y are quantified, including zero-mass atoms. -/
def T30_L2 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ), Measurable X → Measurable Y →
    (Set.range X).Countable → (Set.range Y).Countable →
      (IndepFun X Y μ ↔ ∀ x y : ℝ,
        probability μ {ω | X ω = x ∧ Y ω = y} =
          probability μ {ω | X ω = x} * probability μ {ω | Y ω = y})

/-- The univariate bridge is a short application of half-line measure uniqueness;
the probability law supplies global integrability as a conclusion. -/
theorem cdfDensity_density (ν : Measure ℝ) [IsProbabilityMeasure ν] (f : ℝ → ℝ)
    (hf : CDFDensity ν f) : Density ν f := by
  have hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
    apply Measure.ext_of_Iic
    intro x
    rw [withDensity_apply _ measurableSet_Iic, hf.2.2 x]
  refine ⟨hf.1, hf.2.1, ?_, hν⟩
  apply (lintegral_ofReal_ne_top_iff_integrable hf.1.aestronglyMeasurable
    (ae_of_all _ hf.2.1)).mp
  have hmass := congrArg (fun m : Measure ℝ => m Set.univ) hν
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  rw [← hmass]
  exact ENNReal.one_ne_top

/-- The weighted-measure representation immediately supplies the lower tails. -/
theorem density_cdfDensity (ν : Measure ℝ) (f : ℝ → ℝ) (hf : Density ν f) :
    CDFDensity ν f := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  intro x
  rw [hf.2.2.2, withDensity_apply _ measurableSet_Iic]

/-- Tonelli supplies the iterated lower tails without pointwise slice hypotheses. -/
theorem jointDensity_jointCDFDensity (ν : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ)
    (hf : JointDensity ν f) : JointCDFDensity ν f := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  intro x y
  rw [hf.2.2.2, withDensity_apply _ (measurableSet_Iic.prod measurableSet_Iic)]
  exact (setLIntegral_prod (fun z : ℝ × ℝ => ENNReal.ofReal (f z))
    hf.1.ennreal_ofReal.restrict).symm

/-- The interval length is one, so the restricted Lebesgue law is normalized. -/
theorem unitUniform_probability : IsProbabilityMeasure unitUniformLaw := by
  constructor
  simp [unitUniformLaw, Real.volume_Icc]

/-- Direct interval intersection computes the unit uniform CDF everywhere. -/
theorem unitUniform_cdf (t : ℝ) :
    probability unitUniformLaw (Set.Iic t) = uniformDistributionFunction t := by
  have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 (min t 1) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
    tauto
  simp only [probability, unitUniformLaw, Measure.restrict_apply measurableSet_Iic,
    hset, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal', uniformDistributionFunction,
    min_comm, max_comm]

/-- Product rectangles compute the actual product-law CDF. -/
theorem unitUniform_joint_cdf (x y : ℝ) :
    jointDistributionFunction (unitUniformLaw.prod unitUniformLaw) x y =
      uniformDistributionFunction x * uniformDistributionFunction y := by
  have : IsProbabilityMeasure unitUniformLaw := unitUniform_probability
  rw [jointDistributionFunction, probability, Measure.prod_prod, ENNReal.toReal_mul]
  change probability unitUniformLaw (Set.Iic x) * probability unitUniformLaw (Set.Iic y) = _
  rw [unitUniform_cdf, unitUniform_cdf]

/-- Assembly of the CDF representation bridges, the existing analytic donors,
and the pointwise discrete factorization leaf. -/
theorem T30_assembly (h1 : T30_L1) (h2 : T30_L2.{u}) :
    T30WholeStatement.{u} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, @h2⟩
  · intro ν _ f g hf hg
    have hfd := cdfDensity_density ν f hf
    have hgd := cdfDensity_density ν g hg
    obtain ⟨heq, hder, hnonneg, hnorm⟩ :=
      AronowAudit.P001.pdf_unique_and_derivative_ae ν f g hfd hgd
    have htail := AronowAudit.P001.pdf_version_change ν f f hfd hfd.1 hfd.2.1
      Filter.EventuallyEq.rfl
    exact ⟨heq, hder, hnonneg, hfd.2.2.1, hnorm, htail.2⟩
  · intro ν _ f h hf hnonneg heq
    have hfd := cdfDensity_density ν f hf
    have hh := AronowAudit.P001.pdf_version_change ν f h hfd
      (hfd.1.congr heq.symm) hnonneg heq
    exact ⟨density_cdfDensity ν h hh.1, hh.1.2.2.1, hh.2⟩
  · intro ν _ f g hf hg
    exact AronowAudit.P001.joint_pdf_unique_ae ν f g (h1 ν f hf) (h1 ν g hg)
  · dsimp only
    have : IsProbabilityMeasure unitUniformLaw := unitUniform_probability
    refine ⟨inferInstance, inferInstance, ?_, unitUniform_cdf, unitUniform_joint_cdf, ?_, ?_⟩
    · exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id
    · intro x y hx hy
      rw [unitUniform_joint_cdf]
      simp [uniformDistributionFunction, min_eq_right hx.2, max_eq_right hx.1,
        min_eq_right hy.2, max_eq_right hy.1]
    · intro y hy
      constructor
      · intro u
        have hid : uniformDistributionFunction =ᶠ[𝓝 y] (fun v : ℝ => v) := by
          filter_upwards [eventually_gt_nhds hy.1, eventually_lt_nhds hy.2] with v hv0 hv1
          simp [uniformDistributionFunction, min_eq_right hv1.le, max_eq_right hv0.le]
        have hd : HasDerivAt uniformDistributionFunction 1 y :=
          (hasDerivAt_id y).congr_of_eventuallyEq hid
        simpa only [unitUniform_joint_cdf, mul_one] using
          hd.const_mul (uniformDistributionFunction u)
      · simpa only [unitUniform_joint_cdf, Bridge.uniformDistributionFunction_eq] using
          AronowAudit.P001.joint_cdf_mixed_derivative_boundary y hy
  · intro ν _ f fx fy hf hx hy
    have hfd := h1 ν f hf
    have hxd := cdfDensity_density (ν.map Prod.fst) fx hx
    have hyd := cdfDensity_density (ν.map Prod.snd) fy hy
    refine ⟨AronowAudit.P001.continuous_independence_density_ae ν f fx fy hfd hxd hyd,
      ?_⟩
    constructor
    · intro heq
      apply jointDensity_jointCDFDensity
      refine ⟨hfd.1.congr heq, (fun z => mul_nonneg (hx.2.1 z.1) (hy.2.1 z.2)),
        hfd.2.2.1.congr heq, ?_⟩
      rw [hfd.2.2.2]
      apply withDensity_congr_ae
      exact heq.fun_comp ENNReal.ofReal
    · intro hprod
      exact AronowAudit.P001.joint_pdf_unique_ae ν f _ hfd (h1 ν _ hprod)

end
end SAP.P001b.WH.W2
