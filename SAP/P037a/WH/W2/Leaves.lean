import SAP.P037a.WH.W2.Algebra
import AronowAudit.External.Causalean.Stat.OrderStatistic.Dirichlet
import AronowAudit.External.Causalean.Stat.OrderStatistic.SimplexIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037a.WH.W2

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical Topology

/-- Open-simplex boundary and volume. Prove that the closed-minus-open simplex
is contained in the finite union of coordinate hyperplanes and the hyperplane
sum q=1, each null for coordinate volume. The dimension-zero case is equality
of the two singleton spaces, with volume one. Then use
`Causalean.Stat.OrderStatistic.scaledSpacingSimplex_volume` at radius one and
convert `ofReal (1/m!)` to the inverse natural cast in ENNReal. This is a local
boundary argument, not a new integration of the simplex. -/
def T5_L1 : Prop := simplexVolumeFactsW2

/-- Inverse Jacobian. Differentiate H(q,t)=(tq,t(1-sum q)) coordinatewise.
In the displayed order its derivative has blocks t I, q, -t 1ᵀ, 1-sum q.
For t>0 use the Schur complement: the last scalar complement is one.
Thus det DH=t^m, positive on the domain, including m=0 where det=1.
Use `Matrix.det_fromBlocks₁₁` after reindexing `Fin (m+1)` by `Fin m ⊕ Fin 1`,
or elementary column additions. Derivative identification and determinant
computation belong together; no claim about the forward determinant is assumed. -/
def T5_L2 : Prop := inverseJacobianW2

/-- Forward Jacobian from the inverse Jacobian. The inverse-calculus premise
is exactly L2's conclusion. Positivity makes the total nonzero; differentiate
the rational forward map to obtain differentiability. Use `geometry_proofW2`
and the chain rule on H∘F=id on the open positive orthant. Determinants multiply
to one, and |det DH(F(e))|=(sum e)^m; solve for the reciprocal. The argument
must use local equality on an open domain, not global equality of the totalized
maps. Dimension zero of the free coordinates also satisfies this formula. -/
def T5_L3 : Prop := inverseJacobianW2 → forwardJacobianW2

/-- Product exponential density and support. Each Exp(1) law is Lebesgue
measure with density exp(-x) on x>0, with the endpoint zero null. Prove the
finite-product density by induction using `MeasureTheory.prod_withDensity` and
`volume_preserving_piFinSuccAbove` (or extensionality on measurable rectangles
using `Measure.pi_eq` and Tonelli). The product of exponentials
is exp(-sum e). The density vanishes off the positive orthant, which also gives
the asserted almost-sure strict positivity. There is at least one multiplier;
the case m=0 is the single standard exponential. -/
def T5_L4 : Prop := exponentialProductDensityW2

/-- Change of variables for the complete joint law. The premises are the
inverse Jacobian and the source density, proved in L2 and L4. Apply
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` to the inverse H on
the measurable open normalization domain. `geometry_proofW2` supplies
injectivity and image=positive orthant. Weight by exp(-sum H(z))=exp(-t),
and transport back by F. The resulting factor is |det DH|=t^m. Source and
target densities vanish off their stated domains. Handle restricted measures
and measurable maps explicitly; no gamma-Dirichlet literature premise is used. -/
def T5_L5 : Prop :=
  inverseJacobianW2 → exponentialProductDensityW2 → exponentialJointDensityW2

/-- Marginalize the joint density in t. Split the last coordinate by the
volume-preserving `piFinSuccAbove` equivalence, apply Tonelli on the product,
and use `AronowAudit.P037.simplex_gamma_integral` with exponent m. Convert its
nonnegative Bochner integral to the ENNReal integral, using the already proved
`gamma_integrableW2`. Off the open simplex the marginal is zero, and on it the
density is m!. This statement concerns the explicit joint-density measure and
does not assume that it already has mass one. -/
def T5_L6 : Prop := jointMarginalW2

/-- Complete ordered-uniform spacing construction. Assuming only the boundary
and volume facts of L1, identify the open and closed unit-uniform measures
(their endpoints are null). `Causalean.Stat.OrderStatistic.uniform_firstN_spacings_law`
gives the first m spacings' factorial density on the closed simplex. L1 replaces
it by the open simplex; map `appendSimplex` to include the final gap. Telescoping
shows sum(first spacings)=largest order statistic. Their open-simplex support
gives strict order and both endpoint inequalities almost surely. Prove the
displayed last-gap identity using telescoping, rather than dropping that gap.
All statements are for n=k+2 schools and k+1 independent uniform draws. -/
def T5_L7 : Prop := simplexVolumeFactsW2 → spacingConstructionW2

/-- Positive full-rank WLS is well defined and unique. Expand the weighted
Gram quadratic form as sum_i w_i (Xv)_i². Injectivity of X.mulVec and strictly
positive w make this form positive for v≠0, hence the Gram matrix is positive
definite and has unit determinant (`Matrix.PosDef.isUnit`). Expand WLS as
G.mulVec b=rhs, apply the nonsingular inverse identities, and deduce that its
unique solution is the existing inverse-formula `wlsCoefficient`. Include
empty coefficient index types: the zero-dimensional determinant is one and
the coefficient function is unique. No nonempty coefficient hypothesis is
needed or allowed. -/
def T5_L8 : Prop := wlsUniquenessW2

theorem normalized_exponential_lawW2
    (hp : exponentialProductDensityW2) (hj : exponentialJointDensityW2)
    (hm : jointMarginalW2) (m : ℕ) :
    Measure.map normalizedWeights (exponentialInputW2 (m+1)) = simplexLaw m := by
  have ha : (fun e => appendSimplex m
      (headCoordinatesW2 m (forwardNormalizationW2 m e))) =ᵐ[exponentialInputW2 (m+1)]
      normalizedWeights := by
    filter_upwards [(hp m).2] with e he
    rw [head_forwardW2]
    exact append_headW2 m _ (normalized_factsW2 m e he).2.2
  calc
    Measure.map normalizedWeights (exponentialInputW2 (m+1)) =
        Measure.map (fun e => appendSimplex m
          (headCoordinatesW2 m (forwardNormalizationW2 m e)))
          (exponentialInputW2 (m+1)) := Measure.map_congr ha.symm
    _ = Measure.map (appendSimplex m) (Measure.map (headCoordinatesW2 m)
        (Measure.map (forwardNormalizationW2 m) (exponentialInputW2 (m+1)))) := by
      rw [Measure.map_map (measurable_headW2 m) (measurable_forwardW2 m),
        Measure.map_map (measurable_appendW2 m)
          ((measurable_headW2 m).comp (measurable_forwardW2 m))]
      rfl
    _ = simplexLaw m := by rw [hj m, hm m]; rfl

theorem exponential_construction_proofW2
    (hp : exponentialProductDensityW2) (hj : exponentialJointDensityW2)
    (hm : jointMarginalW2) : exponentialConstructionW2 := by
  intro k Ω _ μ _ E hE hi hl
  have hv : Measurable (fun ω i => E i ω) := Measurable.of_eval hE
  have hin : Measure.map (fun ω i => E i ω) μ = exponentialInputW2 (k+2) :=
    joint_inputW2 E (expMeasure 1) hE hi hl
  have hn := normalized_exponential_lawW2 hp hj hm (k+1)
  constructor
  · rw [← hn, ← hin, Measure.map_map (measurable_normalizedW2 _) hv]
    rfl
  constructor
  · rw [← hj (k+1), ← hin, Measure.map_map (measurable_forwardW2 _) hv]
    rfl
  · have hae : ∀ᵐ e ∂Measure.map (fun ω i => E i ω) μ,
        e ∈ positiveOrthantW2 (k+2) := by rw [hin]; exact (hp (k+1)).2
    filter_upwards [ae_of_ae_map hv.aemeasurable hae] with ω hω
    exact normalized_factsW2 (k+1) _ hω

theorem log_uniform_construction_proofW2 (he : exponentialConstructionW2) :
    logUniformConstructionW2 := by
  intro k Ω _ μ _ V hV hi hl
  have hlog : Measurable (fun v : ℝ => -Real.log v) := Real.measurable_log.neg
  have hE : ∀ i, Measurable (fun ω => -Real.log (V i ω)) :=
    fun i => hlog.comp (hV i)
  have hind : iIndepFun (fun i ω => -Real.log (V i ω)) μ :=
    hi.comp (fun _ v => -Real.log v) (fun _ => hlog)
  have hlaw : ∀ i, Measure.map (fun ω => -Real.log (V i ω)) μ = expMeasure 1 := by
    intro i
    change Measure.map ((fun v : ℝ => -Real.log v) ∘ V i) μ = expMeasure 1
    rw [← Measure.map_map hlog (hV i), hl i]
    exact AronowAudit.P037.uniform_log_gives_exponential
  have h := he k Ω μ (fun i ω => -Real.log (V i ω)) hE hind hlaw
  exact ⟨hind, hlaw, joint_inputW2 _ (expMeasure 1) hE hind hlaw, h.1, h.2.1, h.2.2⟩

theorem direct_uniform_construction_proofW2 : directUniformConstructionW2 := by
  intro k Ω _ μ _ U hU hi hl
  have hv : Measurable (fun ω i => U i ω) := Measurable.of_eval hU
  have hin : Measure.map (fun ω i => U i ω) μ = uniformInputW2 (k+2) :=
    joint_inputW2 U uniformDraw hU hi hl
  have hn : Measure.map (fun ω => normalizedWeights (fun i => U i ω)) μ =
      uniformWeightLaw k := by
    change _ = Measure.map normalizedWeights (uniformInputW2 (k+2))
    rw [← hin, Measure.map_map (measurable_normalizedW2 _) hv]
    rfl
  refine ⟨hn, ?_, ?_⟩
  · rw [hn]
    exact (AronowAudit.P037.Wave1.uniform_weights_not_bayesian_bootstrap_proof k).2.2
  · have hae : ∀ᵐ u ∂Measure.map (fun ω i => U i ω) μ,
        u ∈ positiveOrthantW2 (k+2) := by rw [hin]; exact uniform_input_positiveW2 _
    filter_upwards [ae_of_ae_map hv.aemeasurable hae] with ω hω
    exact ⟨hω, fun d X y hX => normalization_refit_proofW2 k _ X y hω hX⟩

/-- Assembly of the corrected whole P037-T5. Only L1–L8 are unproved mathematical
obligations; the assembly itself is a kernel-checked proof from those propositions. -/
theorem T5_assembly (h1 : T5_L1) (h2 : T5_L2) (h3 : T5_L3) (h4 : T5_L4)
    (h5 : T5_L5) (h6 : T5_L6) (h7 : T5_L7) (h8 : T5_L8) : T5WholeStatement_W2 := by
  have hj : exponentialJointDensityW2 := h5 h2 h4
  have he : exponentialConstructionW2 := exponential_construction_proofW2 h4 hj h6
  exact ⟨simplex_certificationW2 h1, geometry_proofW2, h2, h3 h2, hj, he,
    AronowAudit.P037.uniform_log_gives_exponential, log_uniform_construction_proofW2 he,
    AronowAudit.P037.simplex_gamma_integral, h7 h1,
    AronowAudit.P037.Wave1.uniform_weights_not_bayesian_bootstrap_proof,
    direct_uniform_construction_proofW2, scaling_proofW2, normalization_refit_proofW2, h8⟩

end SAP.P037a.WH.W2
