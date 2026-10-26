

import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
import AronowAudit.External.StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.MeasurableSelectionRandomFunctions
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance

/-!
# Marginal CLTs and empirical-process equicontinuity

`IsMarginalCLT F P` records square integrability and joint Gaussian limits for
finite tuples from `F` under iid sampling. `IsAsymptoticallyEquicontinuous F P`
uses an outer-probability bound on the oscillation over all L²-close pairs.
`IsPDonsker F P` is the working conjunction of these two predicates.

Identifying this conjunction with convergence to a tight ℓ∞-valued Gaussian law
requires total boundedness of the indexing semimetric and the relevant path-space
conditions. The separate theorem `donskerWithBridge_of_finite_bracketing_entropy`
proves the stronger `IsPDonskerWithBridge` conclusion under finite bracketing
entropy in the separate abstract-Donsker development.

The retained API also supplies marginal-CLT proofs, projections from these
predicates, outer-measure monotonicity and a limsup addition bound.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.2 and
Theorem 18.14.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter ProbabilityTheory Matrix
open scoped ENNReal Topology RealInnerProductSpace Matrix

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Marginal covariance entry** of a finite tuple of functions under `P`:
`marginalCovEntry P f i j = P(fᵢ fⱼ) − (P fᵢ)(P fⱼ)`.

This is the `(i,j)` entry of the limiting Gaussian covariance in the
Theorem-18.14(a) marginal CLT: the empirical process `(𝔾ₙ fᵢ)ᵢ` of a P-Donsker
class converges to a centred Gaussian with this covariance (vdV §19.2,
book p.269). -/
noncomputable def marginalCovEntry
    {k : ℕ} (P : Measure Ω) (f : Fin k → (Ω → ℝ)) (i j : Fin k) : ℝ :=
  (∫ x, f i x * f j x ∂P) - (∫ x, f i x ∂P) * (∫ x, f j x ∂P)

/-- **Marginal covariance matrix** of a finite tuple of functions under `P`.
Entry `(i,j)` is `P(fᵢfⱼ) − (Pfᵢ)(Pfⱼ)` (vdV §19.2, book p.269). -/
noncomputable def marginalCovMatrix
    {k : ℕ} (P : Measure Ω) (f : Fin k → (Ω → ℝ)) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => marginalCovEntry P f i j

/-- **Coordinate vector** of a finite tuple `f : Fin k → (Ω → ℝ)` at a point
`ω : Ω`, as an element of `EuclideanSpace ℝ (Fin k)`: the `i`-th coordinate is
`f i ω`. -/
noncomputable def tupleVec
    {k : ℕ} (f : Fin k → (Ω → ℝ)) (ω : Ω) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 _).symm (fun i => f i ω)

/-- **Marginal CLT** — Theorem 18.14(a) form: every finite tuple of
functions from `F` has a joint `√n`-CLT under iid sampling from `P`, with the
Gaussian limit's covariance matrix given by `(Pfᵢfⱼ − Pfᵢ·Pfⱼ)ᵢⱼ`
(`marginalCovMatrix`).

Two conjuncts:

* **`memLp`** — every `f ∈ F` is square-integrable (`MemLp f 2 P`), without
  which the limiting covariance is undefined. It is available separately as
  the projection `IsMarginalCLT.memLp`.
* **`fdd`** — genuine finite-dimensional (marginal) convergence in
  distribution. For every finite tuple `f : Fin k → (Ω → ℝ)` valued in `F` and
  every iid sample `X : ℕ → Ξ → Ω` with law `P`, the empirical-process random
  vector `n ↦ (𝔾ₙ(f₀), …, 𝔾ₙ(f_{k-1}))` (built coordinatewise as the
  standardised sum `(√n)⁻¹ • ∑_{i<n} (tupleVec f (Xᵢ ξ) − E[tupleVec f (X₀)])`)
  converges in distribution to the centred multivariate Gaussian
  `multivariateGaussian 0 (marginalCovMatrix P f)`.

vdV §19.2 + Theorem 18.14(a) (book p.269): finite-dim joint convergence in
distribution to a tight Gaussian limit. -/
def IsMarginalCLT (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  (∀ f ∈ F, MemLp f 2 P) ∧
  (∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
      [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
      (∀ i, Measurable (X i)) →
      ProbabilityTheory.iIndepFun X μ →
      (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
      μ.map (X 0) = P →
      ∀ {k : ℕ} (f : Fin k → (Ω → ℝ)), (∀ i, f i ∈ F) →
        ∃ Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k),
          ProbabilityTheory.HasLaw Y
            (multivariateGaussian 0 (marginalCovMatrix P f))
            (multivariateGaussian 0 (marginalCovMatrix P f)) ∧
          MeasureTheory.TendstoInDistribution
            (fun (n : ℕ) ξ =>
              (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec f (X i ξ)
                - n • μ[fun ξ => tupleVec f (X 0 ξ)]))
            atTop Y (fun _ => μ) (multivariateGaussian 0 (marginalCovMatrix P f)))

/-- **Marginal CLT for an iid empirical process (`fdd` clause).**

From iid sampling `X : ℕ → Ξ → Ω` with law `P` and a finite tuple
`f : Fin k → (Ω → ℝ)` of square-integrable functions, the empirical-process
random vector converges in distribution to the centred Gaussian with covariance
`marginalCovMatrix P f`.

This is the multivariate-CLT content of Theorem 18.14(a). The proof builds the
coordinate vector
`Y i ξ := tupleVec f (X i ξ)`, transports iid / `MemLp 2` from `X` and `f`,
identifies the inner-product variance `Var[⟪t, Y 0⟫]` with the quadratic form of
`marginalCovMatrix P f` (which is positive semidefinite, being a covariance
Gram matrix), and applies the classical multivariate CLT.

vdV §19.2 + Theorem 18.14(a) (book p.269: the empirical process of a Donsker
class has Gaussian finite-dimensional marginals with covariance
`Pfᵢfⱼ − Pfᵢ·Pfⱼ`).

The proof applies the classical multivariate CLT to the iid vectors
`tupleVec f (Xᵢ ·)`, identifies their covariance with `marginalCovMatrix P f`,
and rewrites the standardized sum in empirical-process form. -/
lemma marginalCLT_fdd_of_iid
    {F : Set (Ω → ℝ)} {P : Measure Ω}
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (_hX_meas : ∀ i, Measurable (X i))
    (_hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (_hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (_hX_law : μ.map (X 0) = P)
    {k : ℕ} (f : Fin k → (Ω → ℝ)) (_hf_memLp : ∀ i, MemLp (f i) 2 P) :
    ∃ Y : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k),
      ProbabilityTheory.HasLaw Y
        (multivariateGaussian 0 (marginalCovMatrix P f))
        (multivariateGaussian 0 (marginalCovMatrix P f)) ∧
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) ξ =>
          (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec f (X i ξ)
            - n • μ[fun ξ => tupleVec f (X 0 ξ)]))
        atTop Y (fun _ => μ) (multivariateGaussian 0 (marginalCovMatrix P f)) := by
  classical
  -- The witness for the Gaussian limit is `id`, with law `multivariateGaussian 0 …`.
  refine ⟨id, HasLaw.id, ?_⟩
  -- `μ.map (X j) = P` for every index, via `IdentDistrib` and `_hX_law`.
  have hmap : ∀ j, μ.map (X j) = P := by
    intro j
    rw [(_hX_id j).map_eq, _hX_law]
  -- `P` is a probability measure (pushforward of `μ` by the measurable `X 0`).
  have hP_prob : IsProbabilityMeasure P := by
    rw [← _hX_law]; exact (by infer_instance)
  -- Measurable representatives `f' i =ᵐ[P] f i` of the L²(P) tuple entries.
  set f' : Fin k → (Ω → ℝ) := fun i => (_hf_memLp i).aestronglyMeasurable.mk (f i) with hf'_def
  have hf'_meas : ∀ i, Measurable (f' i) := fun i =>
    (_hf_memLp i).aestronglyMeasurable.measurable_mk
  have hff' : ∀ i, f i =ᵐ[P] f' i := fun i => (_hf_memLp i).aestronglyMeasurable.ae_eq_mk
  have hf'_memLp : ∀ i, MemLp (f' i) 2 P := fun i =>
    (_hf_memLp i).ae_eq (hff' i)
  -- The coordinate map `tupleVec f'` is measurable (each coordinate is).
  have htv_meas : Measurable (tupleVec f') := by
    have hpi : Measurable (fun ω => (fun i => f' i ω) : Ω → (Fin k → ℝ)) :=
      measurable_pi_iff.mpr (fun i => hf'_meas i)
    exact (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.measurable.comp hpi
  -- The (measurable-representative) coordinate iid sequence `Y i ξ = tupleVec f' (X i ξ)`.
  set Y : ℕ → Ξ → EuclideanSpace ℝ (Fin k) := fun i ξ => tupleVec f' (X i ξ) with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := fun i => htv_meas.comp (_hX_meas i)
  have hY_iid : ProbabilityTheory.iIndepFun Y μ :=
    _hX_iindep.comp (fun _ => tupleVec f') (fun _ => htv_meas)
  have hY_id : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ := fun i =>
    (_hX_id i).comp htv_meas
  -- `tupleVec f' = tupleVec f` along the sample, μ-a.e.: each coordinate agrees `P`-a.e.,
  -- pulled back through `X i` (whose law is `P`).
  have hYY' : ∀ i, (fun ξ => tupleVec f (X i ξ)) =ᵐ[μ] Y i := by
    intro i
    have hcoord : ∀ j, (fun ξ => f j (X i ξ)) =ᵐ[μ] (fun ξ => f' j (X i ξ)) := by
      intro j
      exact ae_eq_comp (_hX_meas i).aemeasurable (by rw [hmap i]; exact hff' j)
    -- combine the finitely-many coordinate a.e. equalities
    have hall : ∀ᵐ ξ ∂μ, ∀ j, f j (X i ξ) = f' j (X i ξ) :=
      (ae_all_iff.mpr fun j => hcoord j)
    filter_upwards [hall] with ξ hξ
    change tupleVec f (X i ξ) = tupleVec f' (X i ξ)
    unfold tupleVec
    congr 1
    funext j
    exact hξ j
  -- `MemLp (tupleVec f') 2 P`: every coordinate is in L²(P).
  have htv_memLp : MemLp (tupleVec f') 2 P := by
    refine memLp_piLp_iff.mpr (fun i => ?_)
    have : (fun ω => tupleVec f' ω i) = f' i := rfl
    rw [this]; exact hf'_memLp i
  -- `MemLp (Y 0) 2 μ` by transporting `htv_memLp` along `X 0` (law `P`).
  have hY0_memLp : MemLp (Y 0) 2 μ := by
    have hmp : MemLp (tupleVec f') 2 (μ.map (X 0)) := by rw [hmap 0]; exact htv_memLp
    exact (memLp_map_measure_iff htv_meas.aestronglyMeasurable
      (_hX_meas 0).aemeasurable).1 hmp
  -- The covariance matrix is insensitive to the a.e.-replacement `f ↦ f'`.
  have hcov_eq : marginalCovMatrix P f' = marginalCovMatrix P f := by
    funext i j
    simp only [marginalCovMatrix, marginalCovEntry]
    have h1 : ∫ x, f' i x * f' j x ∂P = ∫ x, f i x * f j x ∂P :=
      integral_congr_ae (by filter_upwards [hff' i, hff' j] with x hi hj; rw [hi, hj])
    have h2 : ∫ x, f' i x ∂P = ∫ x, f i x ∂P :=
      integral_congr_ae ((hff' i).symm)
    have h3 : ∫ x, f' j x ∂P = ∫ x, f j x ∂P :=
      integral_congr_ae ((hff' j).symm)
    rw [h1, h2, h3]
  -- Pointwise inner-product expansion: `⟪t, tupleVec f' ω⟫ = ∑ i, t i * f' i ω`.
  have hinner_eq : ∀ (t : EuclideanSpace ℝ (Fin k)) (ω : Ω),
      ⟪t, tupleVec f' ω⟫ = ∑ i, t i * f' i ω := by
    intro t ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change (f' i ω * t i : ℝ) = t i * f' i ω
    ring
  -- L¹-integrability of products `f' i · f' j` under `P` (Hölder for L²×L²).
  have hf'_int : ∀ i, Integrable (f' i) P := fun i =>
    (hf'_memLp i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hf'_mul_int : ∀ i j, Integrable (fun x => f' i x * f' j x) P := fun i j =>
    (hf'_memLp i).integrable_mul (hf'_memLp j)
  -- Variance identity: `Var[⟪t, Y 0⟫; μ] = t ⬝ᵥ marginalCovMatrix P f *ᵥ t`.
  have hvar : ∀ t : EuclideanSpace ℝ (Fin k),
      Var[fun ξ => ⟪t, Y 0 ξ⟫; μ] = t ⬝ᵥ marginalCovMatrix P f *ᵥ t := by
    intro t
    -- `Z ξ = gt (X 0 ξ)` where `gt ω = ∑ i, t i * f' i ω`.
    set gt : Ω → ℝ := fun ω => ∑ i, t i * f' i ω with hgt_def
    have hgt_meas : Measurable gt :=
      Finset.measurable_sum _ (fun i _ => (measurable_const.mul (hf'_meas i)))
    have hZ_eq : (fun ξ => ⟪t, Y 0 ξ⟫) = (fun ξ => gt (X 0 ξ)) := by
      funext ξ; exact hinner_eq t (X 0 ξ)
    -- `gt` and `gt²` are integrable under `P`.
    have hgt_int : Integrable gt P := by
      rw [hgt_def]
      exact integrable_finsetSum _ (fun i _ => (hf'_int i).const_mul _)
    have hgt_sq_int : Integrable (fun x => gt x ^ 2) P := by
      have hexpand : (fun x => gt x ^ 2)
          = fun x => ∑ i, ∑ j, (t i * t j) * (f' i x * f' j x) := by
        funext x
        rw [hgt_def]
        simp only [sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
      rw [hexpand]
      exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => ((hf'_mul_int i j).const_mul _)))
    have hgt_memLp : MemLp gt 2 P :=
      (memLp_two_iff_integrable_sq hgt_meas.aestronglyMeasurable).mpr hgt_sq_int
    have hZ_memLp : MemLp (fun ξ => ⟪t, Y 0 ξ⟫) 2 μ := by
      rw [hZ_eq]
      have hmp : MemLp gt 2 (μ.map (X 0)) := by rw [hmap 0]; exact hgt_memLp
      exact (memLp_map_measure_iff hgt_meas.aestronglyMeasurable
        (_hX_meas 0).aemeasurable).1 hmp
    -- Push the mean and second moment to integrals under `P`.
    have hmean : μ[fun ξ => ⟪t, Y 0 ξ⟫] = ∫ x, gt x ∂P := by
      rw [hZ_eq, ← hmap 0,
        integral_map (_hX_meas 0).aemeasurable hgt_meas.aestronglyMeasurable]
    have hsq : μ[fun ξ => ⟪t, Y 0 ξ⟫ ^ 2] = ∫ x, gt x ^ 2 ∂P := by
      have hZ_eq_sq : (fun ξ => ⟪t, Y 0 ξ⟫ ^ 2) = (fun ξ => gt (X 0 ξ) ^ 2) := by
        funext ξ; rw [congrFun hZ_eq ξ]
      rw [hZ_eq_sq, ← hmap 0,
        integral_map (_hX_meas 0).aemeasurable
          (hgt_meas.pow_const 2).aestronglyMeasurable]
    -- Expand the two integrals over `P`.
    have hmean_exp : ∫ x, gt x ∂P = ∑ i, t i * ∫ x, f' i x ∂P := by
      rw [hgt_def]
      rw [integral_finsetSum _ (fun i _ => (hf'_int i).const_mul _)]
      exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)
    have hsq_exp : ∫ x, gt x ^ 2 ∂P
        = ∑ i, ∑ j, (t i * t j) * ∫ x, f' i x * f' j x ∂P := by
      have hexpand : (fun x => gt x ^ 2)
          = fun x => ∑ i, ∑ j, (t i * t j) * (f' i x * f' j x) := by
        funext x
        rw [hgt_def]
        simp only [sq, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
      rw [hexpand,
        integral_finsetSum _ (fun i _ => integrable_finsetSum _
          (fun j _ => (hf'_mul_int i j).const_mul _))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum _ (fun j _ => (hf'_mul_int i j).const_mul _)]
      exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
    -- Assemble: `Var = E[Z²] − (E Z)²`.
    rw [variance_eq_sub hZ_memLp]
    simp only [Pi.pow_apply]
    rw [hmean, hsq, hmean_exp, hsq_exp]
    -- RHS as a double sum over `marginalCovEntry P f`.
    have hrhs : t ⬝ᵥ marginalCovMatrix P f *ᵥ t
        = ∑ i, ∑ j, (t i * t j) * marginalCovEntry P f i j := by
      simp only [dotProduct, Matrix.mulVec, marginalCovMatrix]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hrhs]
    -- Expand `(∑ i, t i * ∫ f' i)²` into a double sum.
    rw [sq, Finset.sum_mul_sum]
    -- Merge the two double sums termwise.
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [marginalCovEntry]
    -- `f'`-integrals equal `f`-integrals (a.e.), so substitute.
    have e1 : ∫ x, f' i x * f' j x ∂P = ∫ x, f i x * f j x ∂P :=
      integral_congr_ae (by filter_upwards [hff' i, hff' j] with x hi hj; rw [hi, hj])
    have e2 : ∫ x, f' i x ∂P = ∫ x, f i x ∂P := integral_congr_ae ((hff' i).symm)
    have e3 : ∫ x, f' j x ∂P = ∫ x, f j x ∂P := integral_congr_ae ((hff' j).symm)
    rw [e1, e2, e3]
    ring
  -- Positive-semidefiniteness of the covariance matrix (via the variance form).
  have hpsd : (marginalCovMatrix P f).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
    · -- Hermitian: symmetric real matrix.
      ext i j
      simp only [marginalCovMatrix, marginalCovEntry,
        Matrix.conjTranspose_apply, star_trivial]
      rw [mul_comm (∫ x, f j x ∂P)]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))
    · -- Nonneg quadratic form = variance ≥ 0.
      have hx : (star x : Fin k → ℝ) = (x : Fin k → ℝ) := by
        funext i; exact star_trivial _
      rw [hx]
      have hxv : x ⬝ᵥ marginalCovMatrix P f *ᵥ x
          = Var[fun ξ => ⟪((WithLp.equiv 2 (Fin k → ℝ)).symm x), Y 0 ξ⟫; μ] :=
        (hvar ((WithLp.equiv 2 (Fin k → ℝ)).symm x)).symm
      rw [hxv]
      exact variance_nonneg _ _
  -- Apply the multivariate iid CLT with the identity witness.
  have hYid : ProbabilityTheory.HasLaw
      (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
      (multivariateGaussian 0 (marginalCovMatrix P f))
      (multivariateGaussian 0 (marginalCovMatrix P f)) := ProbabilityTheory.HasLaw.id
  have hTID :
      MeasureTheory.TendstoInDistribution
        (fun (n : ℕ) ξ =>
          (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, Y i ξ - n • μ[fun ξ => Y 0 ξ]))
        atTop (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
        (fun _ => μ) (multivariateGaussian 0 (marginalCovMatrix P f)) :=
    ProbabilityTheory.tendstoInDistribution_multivariate_clt
      (P := μ) (P' := multivariateGaussian 0 (marginalCovMatrix P f))
      (X := Y) (Y := id) (S := marginalCovMatrix P f) hpsd hvar hYid hY0_memLp hY_iid hY_id
  -- Transfer to the original (un-modified) `f` via μ-a.e. equality of the random vectors.
  refine hTID.congr ?_ (Filter.EventuallyEq.refl _ _)
  intro n
  -- `μ[fun ξ => Y 0 ξ] = μ[fun ξ => tupleVec f (X 0 ξ)]` since the integrands are a.e. equal.
  have hcenter : μ[fun ξ => Y 0 ξ] = μ[fun ξ => tupleVec f (X 0 ξ)] :=
    integral_congr_ae (hYY' 0).symm
  rw [hcenter]
  -- Pointwise: the standardised sums agree μ-a.e. (each summand agrees a.e.).
  have hsum : ∀ᵐ ξ ∂μ, ∀ i ∈ Finset.range n, tupleVec f (X i ξ) = Y i ξ :=
    (ae_ball_iff (Finset.range n).countable_toSet).mpr
      (fun i _ => hYY' i)
  filter_upwards [hsum] with ξ hξ
  congr 1
  congr 1
  exact Finset.sum_congr rfl (fun i hi => (hξ i hi).symm)

/-- **Marginal-CLT predicate from tuple-wise L²-membership.** Assembles
`IsMarginalCLT F P` from `∀ f ∈ F, MemLp f 2 P`: the `memLp` conjunct is the
hypothesis itself; the `fdd` conjunct delegates, per finite tuple, to
`marginalCLT_fdd_of_iid` (each tuple entry inherits `MemLp 2` from membership in
`F`). -/
lemma isMarginalCLT_of_memLp {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hmem : ∀ f ∈ F, MemLp f 2 P) : IsMarginalCLT F P := by
  refine ⟨hmem, ?_⟩
  intro Ξ _ μ _ X hX_meas hX_iindep hX_id hX_law k f hf_in
  exact marginalCLT_fdd_of_iid (F := F) μ X hX_meas hX_iindep hX_id hX_law f
    (fun i => hmem (f i) (hf_in i))

/-- **Asymptotic equicontinuity in outer probability.**

For every iid sample with law `P` and every `ε, η > 0`, there is an L²-radius
`δ > 0` such that the limiting upper outer probability of an empirical-process
oscillation greater than `ε` across some pair in `F` at distance less than `δ`
is at most `η`.

The parameters have distinct roles: `ε` bounds the oscillation, `η` bounds its
outer probability, and `δ` bounds the L²-distance between indices. The quantified
sampling space `Ξ` is restricted to `Type 0` in this definition.

Reference: van der Vaart, *Asymptotic Statistics*, Theorem 18.14(ii).
-/
def IsAsymptoticallyEquicontinuous (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
    [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
    (∀ i, Measurable (X i)) →
    ProbabilityTheory.iIndepFun X μ →
    (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
    μ.map (X 0) = P →
    ∀ ε η : ℝ, 0 < ε → 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ limsup (fun n => μ.outerMeasureStar
        {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
          ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|}) atTop
        ≤ ENNReal.ofReal η

/-- Working Donsker predicate: marginal CLTs and L² asymptotic equicontinuity.

This conjunction does not include total boundedness or a tight ℓ∞-valued limit
law. The stronger path-space conclusion is recorded by `IsPDonskerWithBridge`
in the abstract-Donsker development.
-/
def IsPDonsker (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  IsMarginalCLT F P ∧ IsAsymptoticallyEquicontinuous F P

/-- **L²-membership projection of the marginal CLT.** Every
`f ∈ F` is square-integrable. -/
lemma IsMarginalCLT.memLp {F : Set (Ω → ℝ)} {P : Measure Ω}
    (h : IsMarginalCLT F P) : ∀ f ∈ F, MemLp f 2 P := h.1

namespace IsPDonsker

variable {F : Set (Ω → ℝ)} {P : Measure Ω}

lemma marginalCLT (h : IsPDonsker F P) : IsMarginalCLT F P := h.1

lemma asymptoticallyEquicontinuous (h : IsPDonsker F P) :
    IsAsymptoticallyEquicontinuous F P := h.2

end IsPDonsker

/-! ### Outer-measure monotonicity and addition of a vanishing remainder

These helpers bound outer probabilities and control the limsup of a sum when
one nonnegative extended-real sequence tends to zero.
-/

/-- **Monotonicity of the outer measure `P*`.** `A ⊆ B ⟹ P*(A) ≤ P*(B)`
(the indicators satisfy `1_A ≤ 1_B`, and `E*` is monotone). -/
theorem outerMeasureStar_mono {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    {A B : Set Ξ} (hAB : A ⊆ B) :
    μ.outerMeasureStar A ≤ μ.outerMeasureStar B := by
  refine outerExpectation_mono fun ω => ?_
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω, Set.indicator_of_mem (hAB hω), le_refl]
  · simp only [Set.indicator_of_notMem hω, zero_le]


/-- **`limsup (Uf + Vf) ≤ a` when `limsup Uf ≤ a` and `Vf → 0`** (over `atTop`,
`ℝ≥0∞`). For every `b > a` the `limsup`-characterization needs `Uf n + Vf n < b`
eventually: pick `c` with `limsup Uf < c < b`, so eventually `Uf n < c` and (from
`Vf → 0`) `Vf n < b − c`, whence `Uf n + Vf n < c + (b − c) = b`. -/
theorem limsup_add_tendsto_zero_le (Uf Vf : ℕ → ℝ≥0∞) (a : ℝ≥0∞)
    (hU : limsup Uf atTop ≤ a) (hV : Tendsto Vf atTop (𝓝 0)) :
    limsup (fun n => Uf n + Vf n) atTop ≤ a := by
  rw [limsup_le_iff isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)]
  intro b hb
  obtain ⟨c, hac, hcb⟩ := exists_between (lt_of_le_of_lt hU hb)
  have hUev : ∀ᶠ n in atTop, Uf n < c := eventually_lt_of_limsup_lt hac
  have hbc : (0 : ℝ≥0∞) < b - c := tsub_pos_of_lt hcb
  have hVev : ∀ᶠ n in atTop, Vf n < b - c := hV (Iio_mem_nhds hbc)
  filter_upwards [hUev, hVev] with n hUn hVn
  calc Uf n + Vf n < c + (b - c) := ENNReal.add_lt_add hUn hVn
    _ = b := add_tsub_cancel_of_le (le_of_lt hcb)


end AsymptoticStatistics.EmpiricalProcess
