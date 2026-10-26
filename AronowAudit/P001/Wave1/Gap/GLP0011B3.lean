import AronowAudit.P001.Wave1.Gap.GP0011B1b
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix

open MeasureTheory ProbabilityTheory Filter

/-!
Adapted from StatLean/Stat-Lean (Apache-2.0).
See NOTICE at the repository root.
-/

/-! Adapted from StatLean module `AsymptoticStatistics.Core.Hilbert`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source0


/-!
# The mean-zero Hilbert subspace

`L2ZeroMean P` is the kernel of the integral functional on `Lp ℝ 2 P`,
represented by the inner product against the constant function `1`.

Reference: van der Vaart, *Asymptotic Statistics*, §25.2.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.Hilbert

/-! ## The mean-zero `L²(P)` subspace -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The constant function `1` lifted to `Lp ℝ 2 P`. Available whenever `P` is a
finite (in particular probability) measure. -/
noncomputable def oneL2 (P : Measure Ω) [IsFiniteMeasure P] : Lp ℝ 2 P :=
  (memLp_const (1 : ℝ)).toLp _

/-- The integral functional `f ↦ ∫ f ∂P` as a continuous linear functional on
`Lp ℝ 2 P`, realised as the inner product against the constant `1`. The
identity `integralL2 P f = ∫ f ∂P` is proved in
`CandidateIF.integralL2_toLp_eq_integral`. -/
noncomputable def integralL2 (P : Measure Ω) [IsFiniteMeasure P] :
    Lp ℝ 2 P →L[ℝ] ℝ :=
  innerSL ℝ (oneL2 P)

/-- The closed submodule of mean-zero `L²(P)` functions: the kernel of the
integral functional `integralL2 P`. -/
noncomputable def L2ZeroMean (P : Measure Ω) [IsFiniteMeasure P] :
    Submodule ℝ (Lp ℝ 2 P) :=
  LinearMap.ker (integralL2 P).toLinearMap




section Hilbert

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]


variable [CompleteSpace E]


end Hilbert

end AsymptoticStatistics.Core.Hilbert

end GLP0011B3Source0
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.Core.CandidateIF`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source1


/-!
# Candidate influence function (a.e. mean-zero L² representative)

This section packages the mean-zero L² data used by candidate influence
functions. A centered, square-integrable representative belongs to
`L²₀(P)`, the closed subspace of `L²(P)` orthogonal to the constants.
These properties alone do not identify the influence function of a
particular estimator or parameter; that requires a first-order relation
to the estimator or model.

This file packages that data model-agnostically. A *candidate influence
function* bundles a raw a.e. strongly measurable representative $\Omega \to \mathbb{R}$
together with square-integrability under $P$ and the mean-zero
constraint, into a single object that lifts cleanly into $L^2_0(P)$.
Concrete examples specify the influence function pointwise as a raw
function on the observation space; comparing two such formulas as
*almost-everywhere* equalities is much easier than comparing them as
elements of the quotient $L^2(P)$. The `CandidateIF.toL2ZeroMean`
constructor turns a candidate into an element of the target Hilbert
space $L^2_0(P)$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge
Series in Statistical and Probabilistic Mathematics, Cambridge
University Press, 1998. Chapter 25 (Semiparametric Models), §25.3
(Efficient Influence Functions). The structure here packages the necessary
mean-zero and finite-second-moment conditions; it does not assert the
first-order relation for a particular estimator or parameter.

**Bundle and lift.** The bundle has exactly three fields:
`raw` (the raw a.e. strongly measurable representative — without it the object is not
a candidate function); `memLp2` (square-integrability under $P$, which
bundles `AEStronglyMeasurable` via `MemLp.aestronglyMeasurable`, so a
separate measurability field is unnecessary and is intentionally
absent); and `mean_zero` (centering, required to land in the kernel of
the integral functional `integralL2 P`). The lift `toL2ZeroMean` sends a
candidate to `⟨memLp2.toLp raw, _⟩`, where membership in
$L^2_0(P) = \ker(\text{integralL2}\,P)$ is discharged by
`integralL2_toLp_eq_integral` (which identifies the abstract functional
on an L² lift with the ordinary integral, via `L2.inner_def` and the
real inner-product reduction `⟪a,b⟫_ℝ = b * a`) composed with the
`mean_zero` field.

-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core

open AsymptoticStatistics.Core.Hilbert

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A *candidate influence function* on `(Ω, P)` is a raw `Ω → ℝ`
function packaged with the data needed to lift it into `L2ZeroMean P`.

Fields, in order:

- `raw` — the raw pointwise representative, a.e. strongly measurable by `memLp2`.
- `memLp2` — square-integrability under `P`. Bundles
  `AEStronglyMeasurable` via `MemLp.aestronglyMeasurable`, so a separate
  measurability field is unnecessary and is intentionally absent.
- `mean_zero` — mean-zero, required to land in `L2ZeroMean P`
  (the kernel of `integralL2 P`).

Reference: vdV §25.3 (background on influence functions). -/
structure CandidateIF (P : Measure Ω) [IsFiniteMeasure P] where
  /-- The raw pointwise representative `Ω → ℝ` of the candidate influence function. -/
  raw : Ω → ℝ
  memLp2 : MemLp raw 2 P
  mean_zero : ∫ ω, raw ω ∂P = 0

namespace CandidateIF

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- The integral functional `integralL2 P` evaluated on the L² lift of
a `MemLp raw 2 P` function equals the ordinary integral.

Proof: unfold `integralL2 P` to `⟪oneL2 P, ·⟫`, then `L2.inner_def` to
the integral of the pointwise inner product, then identify `oneL2 P`
with `1` and `(hf.toLp).val` with `f` on the AE side. The real inner
product `⟪a, b⟫_ℝ` reduces to `b * a`. -/
private lemma integralL2_toLp_eq_integral
    {f : Ω → ℝ} (hf : MemLp f 2 P) :
    integralL2 P (hf.toLp f) = ∫ ω, f ω ∂P := by
  change ⟪oneL2 P, hf.toLp f⟫_ℝ = _
  rw [MeasureTheory.L2.inner_def]
  have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  have h_f_ae : ((hf.toLp f : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] f :=
    MemLp.coeFn_toLp hf
  apply integral_congr_ae
  filter_upwards [h_one_ae, h_f_ae] with a ha hb
  -- ⟪oneL2 P a, (hf.toLp f) a⟫_ℝ reduces by defeq to (hf.toLp f) a * oneL2 P a
  have hcomm :
      ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
        ((hf.toLp f : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ
        = ((hf.toLp f : Lp ℝ 2 P) : Ω → ℝ) a
            * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
  rw [hcomm, ha, hb]
  ring

/-- Lift a candidate into the mean-zero L² subspace `L2ZeroMean P`. -/
noncomputable def toL2ZeroMean (φ : CandidateIF P) : ↥(L2ZeroMean P) :=
  ⟨φ.memLp2.toLp φ.raw, by
    -- L2ZeroMean P = ker (integralL2 P).toLinearMap
    change φ.memLp2.toLp φ.raw ∈ LinearMap.ker (integralL2 P).toLinearMap
    rw [LinearMap.mem_ker]
    change integralL2 P (φ.memLp2.toLp φ.raw) = 0
    rw [integralL2_toLp_eq_integral]
    exact φ.mean_zero⟩

/-- The underlying `Lp ℝ 2 P` function of `φ.toL2ZeroMean` agrees a.e.
with the raw representative `φ.raw`. -/
@[simp] theorem coeFn_toL2ZeroMean (φ : CandidateIF P) :
    ((φ.toL2ZeroMean : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] φ.raw :=
  MemLp.coeFn_toLp φ.memLp2


end CandidateIF

end AsymptoticStatistics.Core

end GLP0011B3Source1
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.LpSeminorm`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source2

/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/

/-!
# The L² seminorm

For an a.e. strongly measurable function, `eLpNorm f 2 μ` agrees with the
integral seminorm `eLpNorm' f 2 μ`.
-/

namespace MeasureTheory
open scoped ENNReal


variable {α ε : Type*} [MeasurableSpace α] [ENorm ε] [TopologicalSpace ε]
  {μ : Measure α} {f : α → ε}

/-- On a.e. strongly measurable functions, `eLpNorm f 2` is the integral seminorm. -/
theorem eLpNorm_two_eq_eLpNorm' (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = eLpNorm' f 2 μ := by
  simpa only [ENNReal.toReal_ofNat] using
    eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num) hf


end MeasureTheory

end GLP0011B3Source2
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.RnDerivSqrt`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source3


/-!
Square-root density helpers for absolutely continuous measures.

When `ν` is finite, `ν ≪ μ`, and `μ` is σ-finite, the Radon–Nikodym
derivative `p := ν.rnDeriv μ` is `μ`-a.e. finite, and `√p ∈ L²(μ)` with
`‖√p‖²_{L²(μ)} = ν(univ)`. The bridge between `L²(μ)`-membership of
`g · √p` and `L²(ν)`-membership of `g`, plus the integral identity
`∫ g dν = ∫ g · p dμ`, relate the two L² spaces.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib.RnDerivSqrt

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Multiplication by the square-root density transports a.e. strong measurability. -/
theorem aestronglyMeasurable_sqrt_rnDeriv_mul_iff {ν ξ : Measure Ω} [SigmaFinite ν] [SigmaFinite ξ]
    (hνξ : ν ≪ ξ) (h : Ω → ℝ) :
    AEStronglyMeasurable (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal * h ω) ξ ↔
      AEStronglyMeasurable h ν := by
  have hw : Measurable (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal) :=
    (Measure.measurable_rnDeriv ν ξ).ennreal_toReal.sqrt
  constructor
  · rintro ⟨k, hk, heq⟩
    refine ⟨fun ω => (Real.sqrt (ν.rnDeriv ξ ω).toReal)⁻¹ * k ω,
      hw.inv.stronglyMeasurable.mul hk, ?_⟩
    filter_upwards [hνξ.ae_le heq, Measure.rnDeriv_pos hνξ,
      hνξ.ae_le (Measure.rnDeriv_lt_top ν ξ)] with ω hω hp ht
    have hw0 : Real.sqrt (ν.rnDeriv ξ ω).toReal ≠ 0 :=
      (Real.sqrt_pos.2 (ENNReal.toReal_pos hp.ne' ht.ne)).ne'
    rw [← hω, ← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
  · rintro ⟨k, hk, heq⟩
    refine ⟨fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal * k ω,
      hw.stronglyMeasurable.mul hk, ?_⟩
    have heq' : h =ᵐ[ξ.withDensity (ν.rnDeriv ξ)] k := by
      rw [Measure.withDensity_rnDeriv_eq ν ξ hνξ]
      exact heq
    rw [Filter.EventuallyEq, ae_withDensity_iff (Measure.measurable_rnDeriv ν ξ)] at heq'
    filter_upwards [heq'] with ω hω
    by_cases hd : ν.rnDeriv ξ ω = 0
    · simp [hd]
    · rw [hω hd]


/-- Pointwise identity: `√(x.toReal)² = x.toReal` since `x.toReal ≥ 0`. -/
private lemma sqrt_rnDeriv_sq_eq (ν μ : Measure Ω) :
    (fun ω => Real.sqrt ((ν.rnDeriv μ ω).toReal) ^ 2)
      = fun ω => (ν.rnDeriv μ ω).toReal := by
  funext ω; exact Real.sq_sqrt ENNReal.toReal_nonneg

/-- For a finite measure `ν ≪ μ` with `μ` σ-finite, the square-root density
`√(dν/dμ)` is in `L²(μ)`. The norm is computed in `integral_sqrt_rnDeriv_sq`. -/
lemma memLp_sqrt_rnDeriv {ν μ : Measure Ω} [SigmaFinite μ] [IsFiniteMeasure ν]
    (_h_ac : ν ≪ μ) :
    MemLp (fun ω => Real.sqrt (ν.rnDeriv μ ω).toReal) 2 μ := by
  have h_meas : AEStronglyMeasurable
      (fun ω => Real.sqrt ((ν.rnDeriv μ ω).toReal)) μ :=
    ((Measure.measurable_rnDeriv ν μ).ennreal_toReal.sqrt).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq h_meas, sqrt_rnDeriv_sq_eq]
  exact Measure.integrable_toReal_rnDeriv

/-- Hellinger-type identity: the squared `L²(μ)`-norm of `√(dν/dμ)` equals
`ν(univ)`. For `ν` a probability measure this reduces to `1`. -/
lemma integral_sqrt_rnDeriv_sq {ν μ : Measure Ω} [SigmaFinite μ] [IsFiniteMeasure ν]
    (h_ac : ν ≪ μ) :
    ∫ ω, Real.sqrt (ν.rnDeriv μ ω).toReal ^ 2 ∂μ = (ν Set.univ).toReal := by
  rw [sqrt_rnDeriv_sq_eq, Measure.integral_toReal_rnDeriv h_ac, Measure.real_def]

/-- Bridge: if `g · √(dP/dμ) ∈ L²(μ)` and `P ≪ μ` with `μ` σ-finite, then
`g ∈ L²(P)`. -/
lemma memLp_two_of_memLp_two_mul_sqrt_rnDeriv
    {P μ : Measure Ω} [IsFiniteMeasure P] [SigmaFinite μ] (h_ac : P ≪ μ)
    {g : Ω → ℝ} (hg_meas : AEStronglyMeasurable g P)
    (h : MemLp (fun ω => g ω * Real.sqrt (P.rnDeriv μ ω).toReal) 2 μ) :
    MemLp g 2 P := by
  -- Prove `Integrable (g²) P`, then use `memLp_two_iff_integrable_sq`.
  rw [memLp_two_iff_integrable_sq hg_meas]
  -- `P = μ.withDensity (P.rnDeriv μ)` since `P ≪ μ` and both σ-finite.
  have hP : P = μ.withDensity (P.rnDeriv μ) :=
    (Measure.withDensity_rnDeriv_eq P μ h_ac).symm
  rw [hP, MeasureTheory.integrable_withDensity_iff
        (Measure.measurable_rnDeriv P μ) (Measure.rnDeriv_lt_top P μ)]
  -- Goal: `Integrable (fun x => g x ^ 2 * (P.rnDeriv μ x).toReal) μ`.
  -- This equals `Integrable ((g · √p_0)^2) μ` pointwise, which is `MemLp.integrable_sq`
  -- on the hypothesis `h`.
  have h_sq := h.integrable_sq
  -- Pointwise rewrite `(g · √p_0)^2 = g^2 · p_0.toReal`:
  have h_eq : (fun ω => (g ω * Real.sqrt (P.rnDeriv μ ω).toReal) ^ 2)
                = fun ω => g ω ^ 2 * (P.rnDeriv μ ω).toReal := by
    funext ω
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  rwa [h_eq] at h_sq

/-- Integral identity: `∫ g dP = ∫ g · (dP/dμ) dμ` for `P ≪ μ` with `μ`
σ-finite. The integrability of `g` under `P` is not needed for the
equality (both sides are defined as Bochner integrals, which fall back to
`0` when the integrand fails integrability). -/
lemma integral_eq_integral_mul_rnDeriv_of_ac
    {P μ : Measure Ω} [IsFiniteMeasure P] [SigmaFinite μ] (h_ac : P ≪ μ)
    (g : Ω → ℝ) :
    ∫ ω, g ω ∂P = ∫ ω, g ω * (P.rnDeriv μ ω).toReal ∂μ := by
  rw [← MeasureTheory.integral_rnDeriv_smul h_ac]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp [smul_eq_mul, mul_comm]


end AsymptoticStatistics.ForMathlib.RnDerivSqrt

end GLP0011B3Source3
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.L2`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source4


/-!
Asymptotic Statistics — pure L² / integral utility lemmas.

## Contents

* `integral_sq_nonneg`                   — `0 ≤ ∫ f² dμ`.
* `sq_add_le_two_mul_sq`                 — pointwise `(a + b)² ≤ 2a² + 2b²`.
* `abs_integral_mul_le_sqrt_integral_sq` — Cauchy–Schwarz on real integrals.
* `integrable_mul_of_memLp_two`          — `L² × L² → L¹` for real functions.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
open scoped ENNReal

namespace AsymptoticStatistics
namespace L2Utils

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-! ## Pointwise and integral inequalities -/

/-- The integral of a square is non-negative. -/
lemma integral_sq_nonneg (μ : Measure 𝓧) (f : 𝓧 → ℝ) :
    0 ≤ ∫ x, (f x) ^ 2 ∂μ :=
  MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)

/-- Pointwise inequality: `(a + b)² ≤ 2 a² + 2 b²`.  Follows from
`(a − b)² ≥ 0 ⇒ a² + b² ≥ 2ab ⇒ (a+b)² = a² + 2ab + b² ≤ 2(a² + b²)`. -/
lemma sq_add_le_two_mul_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]


/-! ## Cauchy–Schwarz and Hölder specialisations -/

/-- **Cauchy–Schwarz for real-valued integrals**:
`|∫ f·g dμ| ≤ √(∫ f² dμ) · √(∫ g² dμ)` for `f, g ∈ L²(μ)`.

Proof: lift `f, g` to `Lp ℝ 2 μ`, apply the abstract Cauchy–Schwarz
`real_inner_mul_inner_self_le`, and translate the inner products back to
integrals via `MeasureTheory.L2.inner_def`. -/
lemma abs_integral_mul_le_sqrt_integral_sq
    (μ : Measure 𝓧) {f g : 𝓧 → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ|
      ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  set F : Lp ℝ 2 μ := hf.toLp f with hF_def
  set G : Lp ℝ 2 μ := hg.toLp g with hG_def
  have hF_ae : (F : 𝓧 → ℝ) =ᵐ[μ] f := MemLp.coeFn_toLp hf
  have hG_ae : (G : 𝓧 → ℝ) =ᵐ[μ] g := MemLp.coeFn_toLp hg
  have hFG_eq : ∫ x, F x * G x ∂μ = ∫ x, f x * g x ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hF_ae, hG_ae] with x hxF hxG
    rw [hxF, hxG]
  have hFF_eq : ∫ x, (F x) ^ 2 ∂μ = ∫ x, (f x) ^ 2 ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hF_ae] with x hxF
    rw [hxF]
  have hGG_eq : ∫ x, (G x) ^ 2 ∂μ = ∫ x, (g x) ^ 2 ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hG_ae] with x hxG
    rw [hxG]
  have h_cs : ⟪F, G⟫ * ⟪F, G⟫ ≤ ⟪F, F⟫ * ⟪G, G⟫ :=
    real_inner_mul_inner_self_le F G
  have hFG_inner : (⟪F, G⟫ : ℝ) = ∫ x, F x * G x ∂μ := by
    rw [MeasureTheory.L2.inner_def F G]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact mul_comm _ _
  have hFF_inner : (⟪F, F⟫ : ℝ) = ∫ x, (F x) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def F F]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp [sq]
  have hGG_inner : (⟪G, G⟫ : ℝ) = ∫ x, (G x) ^ 2 ∂μ := by
    rw [MeasureTheory.L2.inner_def G G]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp [sq]
  rw [hFG_inner, hFF_inner, hGG_inner, hFG_eq, hFF_eq, hGG_eq] at h_cs
  have h_lhs_sq :
      (∫ x, f x * g x ∂μ) * (∫ x, f x * g x ∂μ) = |∫ x, f x * g x ∂μ| ^ 2 := by
    rw [sq_abs]; ring
  rw [h_lhs_sq] at h_cs
  have hF_sq_nn : 0 ≤ ∫ x, (f x) ^ 2 ∂μ := integral_sq_nonneg μ f
  have h_abs_nn : 0 ≤ |∫ x, f x * g x ∂μ| := abs_nonneg _
  have h_sqrt_le := Real.sqrt_le_sqrt h_cs
  rw [Real.sqrt_sq h_abs_nn, Real.sqrt_mul hF_sq_nn] at h_sqrt_le
  exact h_sqrt_le

/-- Specialised `L² × L² → L¹` for real-valued functions. -/
lemma integrable_mul_of_memLp_two
    (μ : Measure 𝓧) {f g : 𝓧 → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * g x) μ := by
  simpa using! hf.integrable_mul hg

/-- **L² norm-square convergence from L²-difference convergence.**

If `g ∈ L²(μ)`, `f_n − g ∈ L²(μ)` eventually, and `∫(f_n − g)² dμ → 0`,
then `∫f_n² dμ → ∫g² dμ`.

Proof. `f_n² = (f_n − g)² + 2(f_n − g)·g + g²` pointwise. Integrate:
`∫f_n² = ∫(f_n − g)² + 2∫(f_n − g)·g + ∫g²`. The first → 0 by hypothesis;
the second → 0 by Cauchy–Schwarz `|∫(f_n − g)·g| ≤ √(∫(f_n − g)²)·√(∫g²) → 0`;
the third is constant. -/
lemma tendsto_integral_sq_of_tendsto_integral_diff_sq
    (μ : Measure 𝓧) {f : ℕ → 𝓧 → ℝ} {g : 𝓧 → ℝ}
    (hg_memLp : MemLp g 2 μ)
    (hf_diff_memLp : ∀ᶠ n in Filter.atTop, MemLp (fun x => f n x - g x) 2 μ)
    (h_diff_tendsto :
      Filter.Tendsto (fun n : ℕ => ∫ x, (f n x - g x) ^ 2 ∂μ)
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n : ℕ => ∫ x, (f n x) ^ 2 ∂μ)
      Filter.atTop (𝓝 (∫ x, (g x) ^ 2 ∂μ)) := by
  -- Set up integrability ingredients.
  have hg_sq_int : Integrable (fun x => (g x) ^ 2) μ := hg_memLp.integrable_sq
  have hg_sq_nn : 0 ≤ ∫ x, (g x) ^ 2 ∂μ := integral_sq_nonneg μ g
  -- The cross term tends to 0 by Cauchy–Schwarz.
  have h_cross_tendsto :
      Filter.Tendsto (fun n : ℕ => ∫ x, (f n x - g x) * g x ∂μ)
        Filter.atTop (𝓝 0) := by
    -- Bound: `|∫(f_n - g)·g dμ| ≤ √(∫(f_n - g)²) · √(∫g²)`.
    have h_bound : ∀ᶠ n in Filter.atTop,
        |∫ x, (f n x - g x) * g x ∂μ| ≤
          Real.sqrt (∫ x, (f n x - g x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
      filter_upwards [hf_diff_memLp] with n hn_diff_memLp
      exact abs_integral_mul_le_sqrt_integral_sq μ hn_diff_memLp hg_memLp
    -- `√(∫(f_n - g)²) → 0` from `h_diff_tendsto`.
    have h_sqrt_diff : Filter.Tendsto
        (fun n : ℕ => Real.sqrt (∫ x, (f n x - g x) ^ 2 ∂μ))
        Filter.atTop (𝓝 0) := by
      have := h_diff_tendsto
      have h_cont : Continuous Real.sqrt := Real.continuous_sqrt
      have h_at_zero : Real.sqrt 0 = 0 := Real.sqrt_zero
      have := (h_cont.tendsto 0).comp h_diff_tendsto
      simpa [h_at_zero] using! this
    -- Multiply by the constant `√(∫g²)`.
    have h_const : Tendsto (fun _ : ℕ => Real.sqrt (∫ x, (g x) ^ 2 ∂μ))
        atTop (𝓝 (Real.sqrt (∫ x, (g x) ^ 2 ∂μ))) := tendsto_const_nhds
    have h_prod := h_sqrt_diff.mul h_const
    simp only [zero_mul] at h_prod
    -- Sandwich `0 ≤ |∫(f_n - g)·g| ≤ √(...)·√(...) → 0` to get `|∫(f_n - g)·g| → 0`.
    have h_abs_tendsto :
        Filter.Tendsto (fun n : ℕ => |∫ x, (f n x - g x) * g x ∂μ|)
          Filter.atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (b := Filter.atTop)
        (g := fun _ : ℕ => (0 : ℝ)) tendsto_const_nhds h_prod
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) h_bound
    -- Convert `|·| → 0` to `· → 0`.
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h_abs_tendsto
  -- Pointwise expansion: `(f_n)² = (f_n - g)² + 2(f_n - g)·g + g²`.
  have h_pt_expand : ∀ n x, (f n x) ^ 2 =
      (f n x - g x) ^ 2 + 2 * ((f n x - g x) * g x) + (g x) ^ 2 := by
    intro n x; ring
  -- Integrate the expansion (eventually, for n with f_n - g ∈ L²).
  have h_int_eq : ∀ᶠ n in Filter.atTop,
      ∫ x, (f n x) ^ 2 ∂μ =
        (∫ x, (f n x - g x) ^ 2 ∂μ) +
        2 * (∫ x, (f n x - g x) * g x ∂μ) +
        (∫ x, (g x) ^ 2 ∂μ) := by
    filter_upwards [hf_diff_memLp] with n hn_diff_memLp
    have h_diff_sq_int : Integrable (fun x => (f n x - g x) ^ 2) μ :=
      hn_diff_memLp.integrable_sq
    have h_cross_int : Integrable (fun x => (f n x - g x) * g x) μ :=
      integrable_mul_of_memLp_two μ hn_diff_memLp hg_memLp
    have h_2cross_int : Integrable (fun x => 2 * ((f n x - g x) * g x)) μ :=
      h_cross_int.const_mul 2
    calc ∫ x, (f n x) ^ 2 ∂μ
        = ∫ x, ((f n x - g x) ^ 2 + 2 * ((f n x - g x) * g x) + (g x) ^ 2) ∂μ := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro x; exact h_pt_expand n x
      _ = (∫ x, ((f n x - g x) ^ 2 + 2 * ((f n x - g x) * g x)) ∂μ) +
            ∫ x, (g x) ^ 2 ∂μ :=
          MeasureTheory.integral_add (h_diff_sq_int.add h_2cross_int) hg_sq_int
      _ = (∫ x, (f n x - g x) ^ 2 ∂μ) + (∫ x, 2 * ((f n x - g x) * g x) ∂μ) +
            ∫ x, (g x) ^ 2 ∂μ := by
          rw [MeasureTheory.integral_add h_diff_sq_int h_2cross_int]
      _ = (∫ x, (f n x - g x) ^ 2 ∂μ) + 2 * (∫ x, (f n x - g x) * g x ∂μ) +
            ∫ x, (g x) ^ 2 ∂μ := by
          rw [MeasureTheory.integral_const_mul]
  -- Combine: each piece tendsto to its limit.
  have h_combined :
      Filter.Tendsto (fun n : ℕ =>
        (∫ x, (f n x - g x) ^ 2 ∂μ) +
        2 * (∫ x, (f n x - g x) * g x ∂μ) +
        (∫ x, (g x) ^ 2 ∂μ)) Filter.atTop
        (𝓝 (0 + 2 * 0 + ∫ x, (g x) ^ 2 ∂μ)) :=
    ((h_diff_tendsto.add (h_cross_tendsto.const_mul 2)).add tendsto_const_nhds)
  simp only [zero_add, mul_zero] at h_combined
  exact h_combined.congr' (h_int_eq.mono (fun n hn => hn.symm))


end L2Utils
end AsymptoticStatistics

end GLP0011B3Source4
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.QMDAnalytic`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source5


/-!
The identity `sqrt_integral_sq_eq_eLpNorm_toReal` relates the real-valued
`√(∫ f² dμ)` to the L² seminorm of a square-integrable function.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib.QMDAnalytic

variable {Ω : Type*} [MeasurableSpace Ω]


/-- Bridge between the L²(μ) `eLpNorm` and the real-valued
`√(∫ f² dμ)` for `MemLp f 2 μ`. -/
lemma sqrt_integral_sq_eq_eLpNorm_toReal {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Real.sqrt (∫ ω, f ω ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  -- Goal: √(∫ f²) = (ENNReal.ofReal ((∫ ‖f‖^2)^(1/2))).toReal
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  -- Reduce `‖f‖^(2 : ℝ)` to `f^(2 : ℕ)` pointwise.
  have h_int_eq :
      (fun ω => ‖f ω‖ ^ (2 : ℝ≥0∞).toReal) = (fun ω => f ω ^ 2) := by
    funext ω
    rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [h_int_eq]
  have h_int_nn : 0 ≤ ∫ ω, f ω ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h_int_nn _), h2,
      Real.sqrt_eq_rpow]
  norm_num








end AsymptoticStatistics.ForMathlib.QMDAnalytic

end GLP0011B3Source5
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.Core.QMDPath`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source6


/-!
# Quadratic-mean-differentiable paths (dominated case)

A one-parameter curve $t \mapsto Q_t$ of probability measures through $P$
(so $Q_0 = P$), all dominated by a fixed $\sigma$-finite measure $\mu$ with
densities $p_t := \mathrm{d}Q_t/\mathrm{d}\mu$, is *differentiable in
quadratic mean* (QMD) at $t = 0$ with *score function* $g$ when the
square-root densities admit the first-order expansion
$$
  \frac{1}{|t|}\,
  \Bigl\| \sqrt{p_t} - \sqrt{p_0} - \tfrac{t}{2}\, g \sqrt{p_0} \Bigr\|_{L^2(\mu)}
  \;\longrightarrow\; 0
  \qquad (t \to 0).
$$
The score $g$ then lies in $L^2_0(P)$: it has mean zero, $\int g \,\mathrm{d}P = 0$,
and is square-integrable, $\int g^2 \,\mathrm{d}P < \infty$ (the analytic
content of vdV Lemma 25.14).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge
Series in Statistical and Probabilistic Mathematics, Cambridge University
Press, 1998. Chapter 25 (Semiparametric Models), §25.3, Eq (25.13) (the QMD
condition via square-root densities) and Lemma 25.14 (the score has mean
zero and is square-integrable).

**Dominated paths.**
The *dominated specialisation* uses a fixed dominating measure
`μ`, densities `pₜ := dQₜ/dμ`, and the QMD condition stated as L²(μ)
convergence of `√pₜ - √p₀ - (t/2) g √p₀` to zero faster than `t`. vdV
§25.3 explicitly authorizes taking the model dominated "for simplicity";
the canonical nondominated form of Eq (25.13) uses formal `dP^{1/2}`
symbols. The structure `QMDPath` uses densities with respect to a fixed dominator.

The score field is typed `↥(L2ZeroMean P)`, so "mean zero +
square-integrable" (the analytic content of vdV Lemma 25.14) is enforced by
the Lean type system. The QMD limit is stated in `ℝ≥0∞`-quotient form `eLpNorm … / ofReal |t| → 0`
rather than the classical `.toReal²/t² → 0` form: the latter would be
vacuously satisfied whenever the residual leaves `L²(μ)` (since
`(⊤ : ℝ≥0∞).toReal = 0`), whereas the `ℝ≥0∞` form genuinely forces
finiteness of the residual L²-norm near `t = 0`.

-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal



set_option linter.dupNamespace false

namespace AsymptoticStatistics.Core.QMDPath

open AsymptoticStatistics.Core.Hilbert

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A *dominated quadratic-mean-differentiable path* at the probability
measure `P`: a curve `t ↦ curve t : ℝ → Measure Ω` through `P` (at
`t = 0`) that is dominated by a fixed measure `dominating`, with score
function `score : ↥(L2ZeroMean P)`. Writing `p₀ = dP/d(dominating)`,
its square-root-density derivative in `L²(dominating)` is `score * √p₀ / 2`.

Reference: vdV §25.3, `eq:25.13`. This structure is the dominated
specialisation authorized by vdV's "for simplicity" footnote. The canonical
nondominated form, expressed with formal `dP^{1/2}` symbols, lies outside the
scope of this density-based API. -/
structure QMDPath (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- vdV §25.3, eq:25.13: the curve in the space of measures. -/
  curve : ℝ → Measure Ω
  /-- vdV §25.3: the curve passes through `P` at `t = 0`. -/
  curve_at_zero : curve 0 = P
  /-- vdV §25.3: each `curve t` is a probability measure. -/
  curve_isProbability : ∀ t, IsProbabilityMeasure (curve t)
  /-- A fixed dominating measure `μ` (vdV §25.3 footnote authorizes the
  dominated specialisation "for simplicity"). The canonical book form of
  eq 25.13 uses formal `dP^{1/2}` symbols and is *nondominated*;
  this structure specialises to the dominated case because Mathlib's RN-derivative +
  `eLpNorm` machinery operates on densities, not on
  square-roots-of-measures. -/
  dominating : Measure Ω
  /-- Each `curve t` is absolutely continuous w.r.t. `μ`. Vacuous in the
  nondominated form of eq 25.13. -/
  curve_absContinuous : ∀ t, curve t ≪ dominating
  /-- σ-finiteness of `dominating`, required by Mathlib's `Measure.rnDeriv`
  / `lintegral_rnDeriv`. (Probability ⇒ σ-finite, so `dominating := P`
  always satisfies it.) -/
  dominating_sigmaFinite : SigmaFinite dominating
  /-- The *score function* of the path at `P`. The type `↥(L2ZeroMean P)`
  enforces mean zero and square-integrability (the analytic half of vdV
  lem:25.14); the QMD limit below specifies *which* L²₀(P) function is the
  score. -/
  score : ↥(L2ZeroMean P)
  /-- vdV §25.3, eq:25.13: the QMD limit on square-root densities, in
  `ℝ≥0∞`-form. Writing
  `pₜ ω := ((curve t).rnDeriv dominating ω).toReal`, this asserts
    `‖√pₜ - √p₀ - (t/2) · score · √p₀‖_{L²(dominating)} / |t| → 0`
  in `ℝ≥0∞` as `t → 0` along `𝓝[≠] 0`.

  **Why `ℝ≥0∞`-form, not `.toReal`-form**: a `.toReal² / t² → 0`
  formulation would be *vacuously satisfied* whenever the residual lived
  outside `L²(dominating)` (since `(⊤ : ℝ≥0∞).toReal = 0`). The
  `ℝ≥0∞`-quotient form genuinely forces `eLpNorm residual 2 dominating < ⊤`
  for `t` in a punctured neighbourhood of `0`: otherwise the quotient
  evaluates to `⊤` and cannot tend to `0`. -/
  qmd_limit :
    Tendsto
      (fun t : ℝ =>
        eLpNorm (fun ω : Ω =>
          Real.sqrt ((curve t).rnDeriv dominating ω).toReal
            - Real.sqrt ((curve 0).rnDeriv dominating ω).toReal
            - (t / 2) * (score : Ω → ℝ) ω
                * Real.sqrt ((curve 0).rnDeriv dominating ω).toReal)
          2 dominating / ENNReal.ofReal |t|)
      (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞))

/-- Lift the `dominating_sigmaFinite` field of `QMDPath` to a typeclass
instance, so consumers can synthesize
`[SigmaFinite γ.dominating]` automatically. This is the gate that lets
Mathlib's RN-derivative integrability lemmas (`integral_toReal_rnDeriv`,
`lintegral_rnDeriv`, `withDensity_rnDeriv_eq`, ...) fire on `γ.dominating`
without manual instance hand-off. -/
instance {P : Measure Ω} [IsProbabilityMeasure P] (γ : QMDPath P) :
    SigmaFinite γ.dominating := γ.dominating_sigmaFinite

namespace QMDPath

variable {P : Measure Ω} [IsProbabilityMeasure P]


end QMDPath


namespace QMDPath

variable {P : Measure Ω} [IsProbabilityMeasure P]


end QMDPath

end AsymptoticStatistics.Core.QMDPath

end GLP0011B3Source6
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source7


/-!
# One-sided pairwise quadratic-mean differentiability

The square-root comparison is made against the canonical pairwise dominator
`P + Q`; hence no single measure must dominate an entire curve.  This is the
nondominated reading of van der Vaart (25.13).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

open AsymptoticStatistics.Core.Hilbert

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The canonical finite dominator of a pair of measures.  Edge behavior: if
one measure is zero this is the other measure. -/
noncomputable def canonicalDominator (P Q : Measure Ω) : Measure Ω := P + Q

/-- Square-root QMD residual for `P` versus `Q`, represented under `μ`.
The definition is meaningful without domination, but its invariance theorem
assumes both measures are absolutely continuous with respect to `μ`. -/
noncomputable def residualAgainst (P Q μ : Measure Ω) (g : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  fun ω => Real.sqrt (Q.rnDeriv μ ω).toReal
    - Real.sqrt (P.rnDeriv μ ω).toReal
    - (t / 2) * g ω * Real.sqrt (P.rnDeriv μ ω).toReal

/-- Right-sided nondominated QMD at zero, using the canonical pairwise
dominator separately for every `t`.  The ENNReal quotient prevents a
non-`L²` residual from being hidden by `toReal`. -/
def IsRightQMD (P : Measure Ω) (curve : ℝ → Measure Ω) (g : Ω → ℝ) : Prop :=
  Tendsto
    (fun t => eLpNorm'
      (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
      2 (canonicalDominator P (curve t)) / ENNReal.ofReal t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 : ℝ≥0∞))

/-- A baseline-measurable score gives a measurable residual under a dominating measure. -/
lemma residualAgainst_aestronglyMeasurable {P Q μ : Measure Ω} [SigmaFinite P] [SigmaFinite μ]
    (hPμ : P ≪ μ) {g : Ω → ℝ} (hg : AEStronglyMeasurable g P) (t : ℝ) :
    AEStronglyMeasurable (residualAgainst P Q μ g t) μ := by
  have hw := (AsymptoticStatistics.ForMathlib.RnDerivSqrt.aestronglyMeasurable_sqrt_rnDeriv_mul_iff
      hPμ g).2 hg
  have hp := ((Measure.measurable_rnDeriv P μ).ennreal_toReal.sqrt).aestronglyMeasurable (μ := μ)
  have hq := ((Measure.measurable_rnDeriv Q μ).ennreal_toReal.sqrt).aestronglyMeasurable (μ := μ)
  convert! (hq.sub hp).sub (hw.const_mul (t / 2)) using 1
  funext ω
  simp only [residualAgainst, Pi.sub_apply]
  ring

/-- For a baseline-measurable score, right QMD can be stated with `eLpNorm`. -/
lemma isRightQMD_iff_eLpNorm {P : Measure Ω} [IsProbabilityMeasure P]
    (curve : ℝ → Measure Ω) (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t))
    {g : Ω → ℝ} (hg : AEStronglyMeasurable g P) :
    IsRightQMD P curve g ↔
    Tendsto (fun t => eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
      2 (canonicalDominator P (curve t)) / ENNReal.ofReal t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  unfold IsRightQMD
  apply tendsto_congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  let : IsProbabilityMeasure (curve t) := hprob t ht.le
  let μ := canonicalDominator P (curve t)
  let : SigmaFinite μ := by dsimp only [μ, canonicalDominator]; infer_instance
  have hPμ : P ≪ μ := (Measure.le_add_right le_rfl).absolutelyContinuous
  rw [← eLpNorm_two_eq_eLpNorm' (residualAgainst_aestronglyMeasurable hPμ hg t)]

/-- The weighted `L²` change-of-dominator identity used below. -/
private lemma eLpNorm_sqrt_rnDeriv_mul_eq
    {ν ξ : Measure Ω} [SigmaFinite ν] [SigmaFinite ξ]
    (hνξ : ν ≪ ξ) (h : Ω → ℝ) :
    eLpNorm (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal * h ω) 2 ξ =
      eLpNorm h 2 ν := by
  by_cases hh : AEStronglyMeasurable h ν
  · have hw := (RnDerivSqrt.aestronglyMeasurable_sqrt_rnDeriv_mul_iff hνξ h).2 hh
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hw,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hh]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [h2]
    congr 1
    have h_ae : (fun ω => ‖Real.sqrt (ν.rnDeriv ξ ω).toReal * h ω‖ₑ ^ (2 : ℝ))
        =ᵐ[ξ] (fun ω => ν.rnDeriv ξ ω * ‖h ω‖ₑ ^ (2 : ℝ)) := by
      filter_upwards [Measure.rnDeriv_lt_top ν ξ] with ω hω
      rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
        Real.enorm_of_nonneg (Real.sqrt_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two, Real.sq_sqrt ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hω.ne]
    rw [lintegral_congr_ae h_ae]
    calc
      ∫⁻ ω, ν.rnDeriv ξ ω * ‖h ω‖ₑ ^ (2 : ℝ) ∂ξ =
          ∫⁻ ω, ‖h ω‖ₑ ^ (2 : ℝ) ∂ξ.withDensity (ν.rnDeriv ξ) :=
        (lintegral_withDensity_eq_lintegral_mul_non_measurable ξ
          (Measure.measurable_rnDeriv ν ξ) (Measure.rnDeriv_lt_top ν ξ) _).symm
      _ = ∫⁻ ω, ‖h ω‖ₑ ^ (2 : ℝ) ∂ν := by
        rw [Measure.withDensity_rnDeriv_eq ν ξ hνξ]
  · have hw : ¬ AEStronglyMeasurable (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal * h ω) ξ :=
      fun hmeas => hh ((RnDerivSqrt.aestronglyMeasurable_sqrt_rnDeriv_mul_iff hνξ h).1 hmeas)
    rw [eLpNorm_of_not_aestronglyMeasurable hw, eLpNorm_of_not_aestronglyMeasurable hh]


/-- A right-QMD remainder already forces square-integrability of the score. -/
private lemma memLp_score_of_rightQMD
    (P : Measure Ω) [IsProbabilityMeasure P]
    (curve : ℝ → Measure Ω)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t))
    (g : Ω → ℝ) (hg : Measurable g) (hqmd : IsRightQMD P curve g) :
    MemLp g 2 P := by
  have hqmd := (isRightQMD_iff_eLpNorm curve hprob hg.aestronglyMeasurable).1 hqmd
  obtain ⟨t, ht, hlt⟩ : ∃ t : ℝ, 0 < t ∧
      eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
          2 (canonicalDominator P (curve t)) < ENNReal.ofReal t := by
    have hsmall : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
        eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
          2 (canonicalDominator P (curve t)) / ENNReal.ofReal t < 1 :=
      hqmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
    have hboth : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), 0 < t ∧
        eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
          2 (canonicalDominator P (curve t)) < ENNReal.ofReal t := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hlt
      refine ⟨ht, ?_⟩
      calc
        eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
            2 (canonicalDominator P (curve t)) =
            (eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
              2 (canonicalDominator P (curve t)) / ENNReal.ofReal t) * ENNReal.ofReal t := by
                rw [ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top]
        _ < 1 * ENNReal.ofReal t :=
          ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr ht).ne'
            ENNReal.ofReal_ne_top hlt
        _ = ENNReal.ofReal t := one_mul _
    exact hboth.exists
  let ν := canonicalDominator P (curve t)
  let : IsProbabilityMeasure (curve t) := hprob t ht.le
  let : IsFiniteMeasure ν := by
    dsimp [ν, canonicalDominator]
    infer_instance
  have hPν : P ≪ ν :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hQν : curve t ≪ ν :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hp : MemLp (fun ω => Real.sqrt (P.rnDeriv ν ω).toReal) 2 ν :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hPν
  have hq : MemLp (fun ω => Real.sqrt ((curve t).rnDeriv ν ω).toReal) 2 ν :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hQν
  have hr : MemLp (residualAgainst P (curve t) ν g t) 2 ν :=
    lt_trans hlt ENNReal.ofReal_lt_top
  have hscaled : MemLp
      (fun ω => (t / 2) * (g ω * Real.sqrt (P.rnDeriv ν ω).toReal)) 2 ν := by
    convert (hq.sub hp).sub hr using 1
    funext ω
    change (t / 2) * (g ω * Real.sqrt (P.rnDeriv ν ω).toReal) =
      (Real.sqrt ((curve t).rnDeriv ν ω).toReal -
        Real.sqrt (P.rnDeriv ν ω).toReal) - residualAgainst P (curve t) ν g t ω
    simp only [residualAgainst]
    ring
  have hgsqrt : MemLp (fun ω => g ω * Real.sqrt (P.rnDeriv ν ω).toReal) 2 ν := by
    convert hscaled.const_mul (2 / t) using 1
    funext ω
    field_simp
  exact AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_two_of_memLp_two_mul_sqrt_rnDeriv
    hPν hg.aestronglyMeasurable hgsqrt

set_option maxHeartbeats 3000000 in
-- The one-sided unit-norm argument expands several measure-valued L² identities.
/-- Analytic part of Lemma 25.14 for one-sided pairwise QMD: the bare score
has an `L²₀(P)` representative.

Proof idea: obtain `L²` from one positive parameter, then differentiate the
unit-mass identity from the right to prove mean zero.

Joint witness: the constant path with bare score zero. -/
theorem rightQMD_score_in_L2ZeroMean
    (P : Measure Ω) [IsProbabilityMeasure P]
    (curve : ℝ → Measure Ω)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t))
    (hzero : curve 0 = P) (g : Ω → ℝ) (hg : Measurable g)
    (hqmd : IsRightQMD P curve g) :
    ∃ g' : ↥(L2ZeroMean P), g =ᵐ[P] (g' : Ω → ℝ) := by
  let : IsProbabilityMeasure (curve 0) := hprob 0 le_rfl
  have hqmd0 : IsRightQMD (curve 0) curve g := by simpa [hzero] using hqmd
  have hgL20 : MemLp g 2 (curve 0) :=
    memLp_score_of_rightQMD (curve 0) curve hprob g hg hqmd0
  have hgL2 : MemLp g 2 P := by simpa [hzero] using hgL20
  let I : ℝ := ∫ ω, g ω ∂P
  let G : ℝ := (eLpNorm g 2 P).toReal
  let ν : ℝ → Measure Ω := fun t => canonicalDominator P (curve t)
  let r : ℝ → Ω → ℝ := fun t => residualAgainst P (curve t) (ν t) g t
  let R : ℝ → ℝ := fun t => (eLpNorm (r t) 2 (ν t)).toReal
  let H : ℝ → ℝ := fun t => (eLpNorm (fun ω =>
    Real.sqrt ((curve t).rnDeriv (ν t) ω).toReal -
      Real.sqrt (P.rnDeriv (ν t) ω).toReal) 2 (ν t)).toReal
  let C : ℝ → ℝ := fun t => ∫ ω, r t ω *
    Real.sqrt (P.rnDeriv (ν t) ω).toReal ∂(ν t)
  have hqmd := (isRightQMD_iff_eLpNorm curve hprob hg.aestronglyMeasurable).1 hqmd
  have hRratio : Tendsto (fun t => R t / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hreal := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp hqmd
    apply hreal.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change (eLpNorm (residualAgainst P (curve t) (canonicalDominator P (curve t)) g t)
      2 (canonicalDominator P (curve t)) / ENNReal.ofReal t).toReal = _
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal ht.le]
  have ht0 : Tendsto (fun t : ℝ => t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hbound_zero : Tendsto
      (fun t => t / 2 * (G / 2 + R t / t) ^ 2 + R t / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc : Tendsto (fun _ : ℝ => G / 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (G / 2)) := tendsto_const_nhds
    have hsum : Tendsto (fun t => G / 2 + R t / t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (G / 2)) := by
      simpa using hc.add hRratio
    have hprod := (ht0.div_const 2).mul (hsum.pow 2)
    simpa using hprod.add hRratio
  have hsmall : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      eLpNorm (r t) 2 (ν t) / ENNReal.ofReal t < 1 := by
    simpa [IsRightQMD, r, ν] using
      hqmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  have hmain : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      |I| / 2 ≤ t / 2 * (G / 2 + R t / t) ^ 2 + R t / t := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hlt
    have htpos : 0 < t := ht
    let : IsProbabilityMeasure (curve t) := hprob t htpos.le
    let : IsFiniteMeasure (ν t) := by
      dsimp [ν, canonicalDominator]
      infer_instance
    have hPν : P ≪ ν t :=
      Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
    have hQν : curve t ≪ ν t :=
      Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
    let p : Ω → ℝ := fun ω => Real.sqrt (P.rnDeriv (ν t) ω).toReal
    let q : Ω → ℝ := fun ω => Real.sqrt ((curve t).rnDeriv (ν t) ω).toReal
    have hp : MemLp p 2 (ν t) :=
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hPν
    have hq : MemLp q 2 (ν t) :=
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hQν
    have hrlt : eLpNorm (r t) 2 (ν t) < ENNReal.ofReal t := by
      calc
        eLpNorm (r t) 2 (ν t) =
            (eLpNorm (r t) 2 (ν t) / ENNReal.ofReal t) * ENNReal.ofReal t := by
              rw [ENNReal.div_mul_cancel (ENNReal.ofReal_pos.mpr ht).ne'
                ENNReal.ofReal_ne_top]
        _ < 1 * ENNReal.ofReal t := ENNReal.mul_lt_mul_left
          (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top hlt
        _ = ENNReal.ofReal t := one_mul _
    have hr : MemLp (r t) 2 (ν t) := lt_trans hrlt ENNReal.ofReal_lt_top
    have hgp : MemLp (fun ω => g ω * p ω) 2 (ν t) := by
      change eLpNorm (fun ω => g ω * p ω) 2 (ν t) < ∞
      rw [show (fun ω => g ω * p ω) = fun ω => p ω * g ω by
        funext ω; ring]
      rw [eLpNorm_sqrt_rnDeriv_mul_eq hPν g]
      exact hgL2
    have hgpNorm : eLpNorm (fun ω => g ω * p ω) 2 (ν t) = eLpNorm g 2 P := by
      rw [show (fun ω => g ω * p ω) = fun ω => p ω * g ω by
        funext ω; ring]
      exact eLpNorm_sqrt_rnDeriv_mul_eq hPν g
    have hdiff : MemLp (fun ω => q ω - p ω) 2 (ν t) := hq.sub hp
    have hfun : (fun ω => q ω - p ω) =
        (t / 2) • (fun ω => g ω * p ω) + r t := by
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, p, q, r, residualAgainst]
      ring
    have htriE : eLpNorm (fun ω => q ω - p ω) 2 (ν t) ≤
        ‖t / 2‖ₑ * eLpNorm (fun ω => g ω * p ω) 2 (ν t) +
          eLpNorm (r t) 2 (ν t) := by
      calc
        eLpNorm (fun ω => q ω - p ω) 2 (ν t) =
            eLpNorm ((t / 2) • (fun ω => g ω * p ω) + r t) 2 (ν t) :=
          congrArg (fun f => eLpNorm f 2 (ν t)) hfun
        _ ≤ eLpNorm ((t / 2) • (fun ω => g ω * p ω)) 2 (ν t) +
            eLpNorm (r t) 2 (ν t) :=
          eLpNorm_add_le  (by norm_num)
        _ = ‖t / 2‖ₑ * eLpNorm (fun ω => g ω * p ω) 2 (ν t) +
            eLpNorm (r t) 2 (ν t) := by rw [eLpNorm_const_smul]
    have htri : H t ≤ t / 2 * G + R t := by
      have ha : ‖t / 2‖ₑ * eLpNorm (fun ω => g ω * p ω) 2 (ν t) ≠ ∞ :=
        ENNReal.mul_ne_top (by simp) hgp.ne
      have htop : ‖t / 2‖ₑ * eLpNorm (fun ω => g ω * p ω) 2 (ν t) +
          eLpNorm (r t) 2 (ν t) ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ha, hr.ne⟩
      have hle := ENNReal.toReal_mono htop htriE
      rw [ENNReal.toReal_add ha hr.ne, ENNReal.toReal_mul, hgpNorm] at hle
      simpa [H, p, q, G, R, Real.enorm_eq_ofReal, abs_of_pos htpos]
        using hle
    have hpSq : ∫ ω, p ω ^ 2 ∂(ν t) = 1 := by
      simpa [p] using
        (AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_sqrt_rnDeriv_sq hPν)
    have hqSq : ∫ ω, q ω ^ 2 ∂(ν t) = 1 := by
      simpa [q] using
        (AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_sqrt_rnDeriv_sq hQν)
    have hCbound : |C t| ≤ R t := by
      have hcs := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
        (ν t) hr hp
      rw [AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal hr,
        hpSq, Real.sqrt_one, mul_one] at hcs
      simpa [C, R, p] using hcs
    let A : ℝ := ∫ ω, q ω * p ω ∂(ν t)
    have hgpSq : ∫ ω, g ω * p ω ^ 2 ∂(ν t) = I := by
      have hpoint : (fun ω => g ω * p ω ^ 2) =
          fun ω => g ω * (P.rnDeriv (ν t) ω).toReal := by
        funext ω
        simp only [p, Real.sq_sqrt ENNReal.toReal_nonneg]
      rw [hpoint,
        ← AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
          hPν g]
    have hCeq : C t = A - 1 - (t / 2) * I := by
      have hqp := AsymptoticStatistics.L2Utils.integrable_mul_of_memLp_two (ν t) hq hp
      have hp2 := hp.integrable_sq
      have hgpp := AsymptoticStatistics.L2Utils.integrable_mul_of_memLp_two (ν t) hgp hp
      have hgp2 : Integrable (fun ω => g ω * p ω ^ 2) (ν t) := by
        convert hgpp using 1
        funext ω
        ring
      change ∫ ω, r t ω * p ω ∂(ν t) = _
      have heq : (fun ω => r t ω * p ω) =
          (fun ω => q ω * p ω) -
            ((fun ω => p ω ^ 2) + fun ω => (t / 2) * (g ω * p ω ^ 2)) := by
        funext ω
        simp only [Pi.sub_apply, Pi.add_apply, r, residualAgainst, p, q]
        ring
      rw [heq]
      calc
        integral (ν t) ((fun ω => q ω * p ω) -
            ((fun ω => p ω ^ 2) + fun ω => (t / 2) * (g ω * p ω ^ 2))) =
            ∫ ω, q ω * p ω ∂(ν t) -
              ∫ ω, p ω ^ 2 + (t / 2) * (g ω * p ω ^ 2) ∂(ν t) :=
          integral_sub hqp (hp2.add (hgp2.const_mul _))
        _ = A - 1 - (t / 2) * I := by
          rw [integral_add hp2 (hgp2.const_mul _), integral_const_mul, hpSq, hgpSq]
          dsimp [A]
          ring
    have hHsq : H t ^ 2 = 2 - 2 * A := by
      have hdiffSq := hdiff.integrable_sq
      have hqp := AsymptoticStatistics.L2Utils.integrable_mul_of_memLp_two (ν t) hq hp
      have hq2 := hq.integrable_sq
      have hp2 := hp.integrable_sq
      have heq : (fun ω => (q ω - p ω) ^ 2) =
          ((fun ω => q ω ^ 2) + fun ω => p ω ^ 2) -
            fun ω => 2 * (q ω * p ω) := by
        funext ω
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      have hint : ∫ ω, (q ω - p ω) ^ 2 ∂(ν t) = 2 - 2 * A := by
        rw [heq]
        calc
          integral (ν t) (((fun ω => q ω ^ 2) + fun ω => p ω ^ 2) -
              fun ω => 2 * (q ω * p ω)) =
              ∫ ω, q ω ^ 2 + p ω ^ 2 ∂(ν t) -
                ∫ ω, 2 * (q ω * p ω) ∂(ν t) :=
            integral_sub (hq2.add hp2) (hqp.const_mul _)
          _ = 2 - 2 * A := by
            rw [integral_add hq2 hp2, integral_const_mul, hqSq, hpSq]
            dsimp [A]
            ring
      have hsqrt :=
        AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal hdiff
      have hnn : 0 ≤ ∫ ω, (q ω - p ω) ^ 2 ∂(ν t) :=
        integral_nonneg fun _ => sq_nonneg _
      have hsquare : H t ^ 2 = ∫ ω, (q ω - p ω) ^ 2 ∂(ν t) := by
        change (eLpNorm (fun ω => q ω - p ω) 2 (ν t)).toReal ^ 2 = _
        rw [← hsqrt, Real.sq_sqrt hnn]
      rw [hsquare, hint]
    have hid : (t / 2) * I = -(H t ^ 2) / 2 - C t := by
      rw [hCeq, hHsq]
      ring
    have hraw : |I| / 2 ≤ H t ^ 2 / (2 * t) + |C t| / t := by
      have habs : |(t / 2) * I| ≤ H t ^ 2 / 2 + |C t| := by
        rw [hid]
        calc
          |-(H t ^ 2) / 2 - C t| ≤ |-(H t ^ 2) / 2| + |C t| := abs_sub _ _
          _ = H t ^ 2 / 2 + |C t| := by
            rw [abs_div, abs_neg, abs_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have := (div_le_div_iff_of_pos_right ht).mpr habs
      have hleft : |(t / 2) * I| / t = |I| / 2 := by
        rw [abs_mul, abs_of_pos (half_pos htpos)]
        field_simp [htpos.ne']
      have hright : (H t ^ 2 / 2 + |C t|) / t =
          H t ^ 2 / (2 * t) + |C t| / t := by ring
      rwa [hleft, hright] at this
    have hHnonneg : 0 ≤ H t := ENNReal.toReal_nonneg
    have hRnonneg : 0 ≤ R t := ENNReal.toReal_nonneg
    have hGnonneg : 0 ≤ G := ENNReal.toReal_nonneg
    calc
      |I| / 2 ≤ H t ^ 2 / (2 * t) + |C t| / t := hraw
      _ ≤ (t / 2 * G + R t) ^ 2 / (2 * t) + R t / t := by
        gcongr
      _ = t / 2 * (G / 2 + R t / t) ^ 2 + R t / t := by
        field_simp [htpos.ne']
  have hIle : |I| / 2 ≤ 0 := ge_of_tendsto hbound_zero hmain
  have hI : I = 0 := by
    have : |I| = 0 := by linarith [abs_nonneg I]
    exact abs_eq_zero.mp this
  have hmeanP : ∫ ω, g ω ∂P = 0 := by simpa [I] using hI
  let F : Lp ℝ 2 P := hgL2.toLp g
  have hF : F ∈ L2ZeroMean P := by
    change integralL2 P F = 0
    change @inner ℝ (Lp ℝ 2 P) _ (oneL2 P) F = 0
    rw [MeasureTheory.L2.inner_def]
    have h_one : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have h_g : (F : Ω → ℝ) =ᵐ[P] g := MemLp.coeFn_toLp hgL2
    calc
      ∫ ω, @inner ℝ ℝ _ (((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω)
          ((F : Ω → ℝ) ω) ∂P =
          ∫ ω, g ω ∂P := by
        apply integral_congr_ae
        filter_upwards [h_one, h_g] with ω h1 hg'
        rw [h1, hg']
        change g ω * 1 = g ω
        exact mul_one _
      _ = 0 := hmeanP
  exact ⟨⟨F, hF⟩, (MemLp.coeFn_toLp hgL2).symm⟩

end AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

end GLP0011B3Source7
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.Core.NondominatedQMDPath`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source8


/-! # Nondominated one-sided QMD paths -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.Core.NondominatedQMDPath

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

set_option linter.dupNamespace false

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A one-sided QMD path at `P` in the canonical pairwise sense of (25.13).

Constitutive (vdV §25.3 pp.362--363): a path consists of probability laws through
`P`, its `L²₀(P)` score, and the right-sided quadratic-mean derivative.  No
fixed common dominator is part of the object. -/
structure NondominatedQMDPath (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- Constitutive (vdV §25.3 p.362): the one-sided measure-valued path. -/
  curve : ℝ → Measure Ω
  /-- Constitutive (vdV §25.3 p.362): the path passes through `P`. -/
  curve_at_zero : curve 0 = P
  /-- Constitutive (vdV §25.3 p.362): every nonnegative point of the
  one-sided path is a probability law in the model. The definition imposes no
  condition at negative parameters. -/
  curve_isProbability : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t)
  /-- Constitutive (vdV §25.3 p.362): the QMD score, after Lemma 25.14's
  analytic conclusion has placed it in `L²₀(P)`. -/
  score : ↥(L2ZeroMean P)
  /-- Constitutive (vdV §25.3 eq.25.13): right pairwise QMD at zero. -/
  qmd_limit : IsRightQMD P curve (score : Ω → ℝ)


/-- Package bare one-sided QMD data after the analytic score theorem.

The construction applies `rightQMD_score_in_L2ZeroMean` and transports the QMD
residual across its `P`-a.e. score representative. -/
theorem exists_nondominatedQMDPath_of_bare_qmd
    (P : Measure Ω) [IsProbabilityMeasure P]
    (curve : ℝ → Measure Ω)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t))
    (hzero : curve 0 = P) (g : Ω → ℝ) (hg : Measurable g)
    (hqmd : IsRightQMD P curve g) :
    ∃ γ : NondominatedQMDPath P,
      γ.curve = curve ∧ g =ᵐ[P] (γ.score : Ω → ℝ) := by
  obtain ⟨g', hgg'⟩ := rightQMD_score_in_L2ZeroMean P curve hprob hzero g hg hqmd
  have hqmd' : IsRightQMD P curve (g' : Ω → ℝ) := by
    apply hqmd.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    let ν := canonicalDominator P (curve t)
    let : IsProbabilityMeasure (curve t) := hprob t ht.le
    let : IsFiniteMeasure ν := by
      dsimp [ν, canonicalDominator]
      infer_instance
    have hPν : P ≪ ν :=
      Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
    have hwith : g =ᵐ[ν.withDensity (P.rnDeriv ν)] (g' : Ω → ℝ) := by
      rw [Measure.withDensity_rnDeriv_eq P ν hPν]
      exact hgg'
    have hae : residualAgainst P (curve t) ν g t =ᵐ[ν]
        residualAgainst P (curve t) ν (g' : Ω → ℝ) t := by
      have hon := (ae_withDensity_iff (Measure.measurable_rnDeriv P ν)).mp hwith
      filter_upwards [hon] with ω hω
      by_cases hz : P.rnDeriv ν ω = 0
      · simp [residualAgainst, hz]
      · simp [residualAgainst, hω hz]
    change eLpNorm' (residualAgainst P (curve t) ν g t) 2 ν / ENNReal.ofReal t = _
    rw [eLpNorm'_congr_ae hae]
  exact ⟨{
    curve := curve
    curve_at_zero := hzero
    curve_isProbability := hprob
    score := g'
    qmd_limit := hqmd' }, rfl, hgg'⟩

namespace QMDPath


end QMDPath
end AsymptoticStatistics.Core.NondominatedQMDPath

end GLP0011B3Source8
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.Contiguity`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source9


/-!
# Contiguity of sequences of probability measures

Contiguity (van der Vaart §6.3-§6.7) and Le Cam's first and third lemmas as
general probability-theoretic results.

Main declarations:
* `WeakConverges` — test-function-based weak convergence of measures.
* `Contiguous` — contiguity along a filter.
* `uniform_integrability_exp_L_of_integral_tendsto_one` — uniform integrability
  under asymptotic normalization, using vdV Example 6.5.
* `weak_limit_under_Q_of_lecam_third_of_integral_comparison` — Le Cam's third
  lemma under asymptotic integral comparison (vdV Theorem 6.6).
-/

set_option linter.style.longFile 3800

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- Weak convergence of a sequence of probability measures (convergence in law).

Test-function characterization: for every bounded continuous real-valued `f`, the
`f`-integrals converge. Equivalent to convergence in the weak topology on
`MeasureTheory.ProbabilityMeasure E`, but given in unpacked form for convenience. -/
def WeakConverges {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))

/-- **Continuous mapping theorem for weak convergence**: if `μ_n` weakly converges to
`ν` on `E` and `f : E → F` is continuous and measurable, then the pushforwards by `f`
weakly converge to the pushforward of the limit. Standard application of
`BoundedContinuousFunction.compContinuous` + `integral_map`. -/
lemma WeakConverges.map {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSpace F] [TopologicalSpace F] [PseudoMetricSpace F]
    [OpensMeasurableSpace F]
    {μ : ℕ → Measure E} {ν : Measure E}
    (hμν : WeakConverges μ ν) {f : E → F}
    (hf_cont : Continuous f) (hf_meas : Measurable f) :
    WeakConverges (fun n => (μ n).map f) (ν.map f) := by
  intro g
  -- `g ∘ f` is a bounded continuous function on `E`.
  let g_comp_f : E →ᵇ ℝ := g.compContinuous ⟨f, hf_cont⟩
  -- Both `∫ g d(μ.map f)` and `∫ g d(ν.map f)` rewrite to `∫ (g ∘ f) dμ` / `∫ (g ∘ f) dν`.
  have h_rewrite : ∀ ρ : Measure E,
      ∫ y, g y ∂(ρ.map f) = ∫ x, g_comp_f x ∂ρ := by
    intro ρ
    rw [MeasureTheory.integral_map hf_meas.aemeasurable
      g.continuous.aestronglyMeasurable]
    rfl
  simp_rw [h_rewrite]
  exact hμν g_comp_f

/-- **Subsequence preservation** of weak convergence. If `μ_n ⇝ ν` and `φ : ℕ → ℕ`
is strictly monotone, then `μ_{φ k} ⇝ ν`. -/
lemma WeakConverges.comp {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    {μ : ℕ → Measure E} {ν : Measure E}
    (h : WeakConverges μ ν) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeakConverges (fun k => μ (φ k)) ν :=
  fun f => (h f).comp hφ.tendsto_atTop

/-- **Weak-limit uniqueness** on a Polish-adjacent Borel space. If a sequence of
measures weakly converges to two finite measures, they agree. Pure consequence of
`ext_of_forall_integral_eq_of_IsFiniteMeasure` + `tendsto_nhds_unique`. -/
lemma WeakConverges.unique
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    [HasOuterApproxClosed E]
    {μ : ℕ → Measure E} {ν ν' : Measure E}
    [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h₁ : WeakConverges μ ν) (h₂ : WeakConverges μ ν') :
    ν = ν' :=
  MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
    (fun f => tendsto_nhds_unique (h₁ f) (h₂ f))

/-- **Marginal weak-limit identification**. If `μ_n ⇝ π` jointly on `E × F` and
`(μ_n.map snd) ⇝ ν` on `F`, then `π.map Prod.snd = ν`. Proof: continuous-mapping
gives `(μ_n.map snd) ⇝ π.map snd`, then apply weak-limit uniqueness. -/
lemma WeakConverges.snd_eq
    {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSpace F] [TopologicalSpace F] [PseudoMetricSpace F]
    [BorelSpace F] [HasOuterApproxClosed F]
    {μ : ℕ → Measure (E × F)} {π : Measure (E × F)} [IsFiniteMeasure π]
    {ν : Measure F} [IsFiniteMeasure ν]
    (hπ : WeakConverges μ π)
    (hν : WeakConverges (fun n => (μ n).map Prod.snd) ν) :
    π.map Prod.snd = ν :=
  have : IsFiniteMeasure (π.map Prod.snd) :=
    MeasureTheory.Measure.isFiniteMeasure_map π Prod.snd
  WeakConverges.unique (hπ.map continuous_snd measurable_snd) hν


/-- **Commuting `withDensity` past `Measure.map`**:
`(μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ`, for measurable `φ` and `h`.

Useful for pushing a density through a measurable pushforward — e.g., when a joint
law `π_tilted = π.map φ` is `withDensity`-ed against a function `h` that factors
through `φ`, the calculation can be pulled back to `π` under the composed density. -/
lemma Measure.withDensity_map_eq_map_withDensity
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : MeasureTheory.Measure α) (φ : α → β) (hφ : Measurable φ)
    (h : β → ℝ≥0∞) (hh : Measurable h) :
    (μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ := by
  refine MeasureTheory.Measure.ext (fun A hA => ?_)
  rw [MeasureTheory.withDensity_apply _ hA,
      MeasureTheory.Measure.map_apply hφ hA,
      MeasureTheory.withDensity_apply _ (hφ hA),
      MeasureTheory.setLIntegral_map hA hh hφ]
  rfl


namespace Contiguity

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- **Contiguity** (van der Vaart §6.3). A family `Q` is contiguous with respect to `P`
along filter `l` (written informally `Q ⊲ P`) if any sequence of measurable events whose
`P`-probabilities tend to 0 also has `Q`-probabilities tending to 0. -/
def Contiguous (l : Filter ι) (P Q : ∀ i, Measure (Ω i)) : Prop :=
  ∀ A : ∀ i, Set (Ω i), (∀ i, MeasurableSet (A i)) →
    Tendsto (fun i => (P i) (A i)) l (𝓝 0) →
    Tendsto (fun i => (Q i) (A i)) l (𝓝 0)

/-- **Mutual contiguity**: both directions. -/
def MutuallyContiguous (l : Filter ι) (P Q : ∀ i, Measure (Ω i)) : Prop :=
  Contiguous l P Q ∧ Contiguous l Q P


lemma Contiguous.trans {l : Filter ι} {P Q R : ∀ i, Measure (Ω i)}
    (h₁ : Contiguous l P Q) (h₂ : Contiguous l Q R) :
    Contiguous l P R := fun A hA hP => h₂ A hA (h₁ A hA hP)

lemma MutuallyContiguous.symm {l : Filter ι} {P Q : ∀ i, Measure (Ω i)}
    (h : MutuallyContiguous l P Q) : MutuallyContiguous l Q P :=
  ⟨h.2, h.1⟩




/-! ## Le Cam's first lemma — asymptotic log normality criterion

vdV Example 6.5. If the log-likelihood ratio `log dQ_n/dP_n` is asymptotically normal
under `P_n` with mean `-σ²/2` and variance `σ²`, then `P_n ⊲⊳ Q_n`.

The Gaussian exponential normalization and truncation estimates below
are ingredients in the uniform-integrability argument for this criterion.
-/

section LeCamFirst

/-- **Gaussian mgf at 1**: `∫ exp(x) dN(-v/2, v) = 1`. This is the multiplicative
normalization underlying Le Cam 1 — if `W ~ N(-v/2, v)`, then `E[exp W] = 1`, which is
exactly what keeps the likelihood ratio's mass normalized. -/
private lemma integral_exp_gaussianReal_neg_half_var (v : NNReal) :
    ∫ x, Real.exp x ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) = 1 := by
  have hX :
      Measure.map (id : ℝ → ℝ) (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)
        = ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v :=
    Measure.map_id
  have h := ProbabilityTheory.mgf_gaussianReal ⟨aemeasurable_id, hX⟩ 1
  rw [ProbabilityTheory.mgf] at h
  simp only [one_mul, id_eq] at h
  rw [show (-(v : ℝ) / 2 * 1 + (v : ℝ) * 1 ^ 2 / 2 : ℝ) = 0 by ring, Real.exp_zero] at h
  exact h

/-- Truncated exponential `min(exp x, M)` as a bounded continuous function, for `M ≥ 0`. -/
private noncomputable def truncExpBCF (M : ℝ) (hM : 0 ≤ M) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (Real.exp x) M)
    (Real.continuous_exp.min continuous_const)
    M
    (fun x => by
      rw [Real.norm_eq_abs]
      have h_nonneg : 0 ≤ min (Real.exp x) M :=
        le_min (Real.exp_pos x).le hM
      rw [abs_of_nonneg h_nonneg]
      exact min_le_right _ _)

@[simp] private lemma truncExpBCF_apply (M : ℝ) (hM : 0 ≤ M) (x : ℝ) :
    truncExpBCF M hM x = min (Real.exp x) M := rfl

/-- As `M → ∞` (over naturals), `∫ min(exp x, M) dN(-v/2, v) → 1`.

Dominated convergence: `min(exp x, M) ↑ exp x` pointwise, dominated by `exp x` which is
integrable under the log-normal-tilt Gaussian (mgf exists at 1). The limit equals
`∫ exp = 1` by the Gaussian mgf. -/
private lemma tendsto_integral_truncExp_gaussianReal (v : NNReal) :
    Tendsto
      (fun M : ℕ =>
        ∫ x, min (Real.exp x) (M : ℝ) ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))
      atTop (𝓝 1) := by
  set ν : Measure ℝ := ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v with hν_def
  have h_exp_int : Integrable (fun x => Real.exp x) ν := by
    have := ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := -(v : ℝ) / 2) (v := v) 1
    simpa using this
  have h_lim : ∀ᵐ x ∂ν,
      Tendsto (fun M : ℕ => min (Real.exp x) (M : ℝ)) atTop (𝓝 (Real.exp x)) := by
    refine Eventually.of_forall (fun x => ?_)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈Real.exp x⌉₊] with M hM
    have : Real.exp x ≤ (M : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hM)
    exact (min_eq_left this).symm
  have h_dom : ∀ M : ℕ, ∀ᵐ x ∂ν, ‖min (Real.exp x) (M : ℝ)‖ ≤ Real.exp x := by
    intro M
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    have h_nonneg : 0 ≤ min (Real.exp x) (M : ℝ) :=
      le_min (Real.exp_pos x).le (Nat.cast_nonneg _)
    rw [abs_of_nonneg h_nonneg]
    exact min_le_left _ _
  have h_meas : ∀ M : ℕ, AEStronglyMeasurable (fun x => min (Real.exp x) (M : ℝ)) ν :=
    fun M => (Real.continuous_exp.min continuous_const).aestronglyMeasurable
  have h_tendsto :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (F := fun M x =>
      min (Real.exp x) (M : ℝ)) (f := fun x => Real.exp x) (bound := fun x => Real.exp x)
      h_meas h_exp_int h_dom h_lim
  rw [integral_exp_gaussianReal_neg_half_var] at h_tendsto
  exact h_tendsto


/-- **For fixed `M ≥ 0`, weak convergence transfers to integrals of the truncated
exponential**: `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN(-v/2, v)` as `n → ∞`.

Follows from `WeakConverges` applied to `truncExpBCF M`, after rewriting the map-integral
via `MeasureTheory.integral_map`. -/
private lemma tendsto_integral_truncExp_L
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))
    (M : ℝ) (hM : 0 ≤ M) :
    Tendsto
      (fun n => ∫ ω, min (Real.exp (L n ω)) M ∂(P n)) atTop
      (𝓝 (∫ x, min (Real.exp x) M ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))) := by
  have h_bcf := h_weak (truncExpBCF M hM)
  -- Use `integral_map` to swap `(P n).map (L n)` integrals back to integrals in `P n`.
  have h_map_n : ∀ n,
      ∫ x, truncExpBCF M hM x ∂((P n).map (L n))
        = ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    intro n
    rw [MeasureTheory.integral_map (hL_meas n).aemeasurable
        (truncExpBCF M hM).continuous.aestronglyMeasurable]
    simp
  simp only [h_map_n] at h_bcf
  simpa using h_bcf


end LeCamFirst

section ReverseDirection





end ReverseDirection





/-! ## Le Cam variants under asymptotic density comparison

The results below use asymptotic normalization and an integral-comparison
bound with vanishing slack in place of an exact density identity. Such a
bound permits a vanishing singular component without common support.
-/

/-- **Uniform-integrability of `exp(L n)` from `∫ exp(L n) dP_n → 1`.**

The hypotheses include integrability of `exp(L n)`, asymptotic normalization
`∫ exp(L n) dP_n → 1`, and weak convergence of the laws of `L n` to
`gaussianReal (-(v : ℝ) / 2) v`.

In the Gaussian truncation argument, the exact term `1 − ∫min` becomes
`(∫ exp(L n) dP_n) − ∫min = (1 + δₙ) − ∫min`. Split ε across the `δₙ` slack and the
truncation gap; `δₙ = o(1)` is absorbable but must be carried explicitly (UI only needs
`≤ ε` eventually). -/
lemma uniform_integrability_exp_L_of_integral_tendsto_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    -- Integrability makes the exponentially tilted measure finite.
    (h_exp_int : ∀ n, Integrable (fun ω => Real.exp (L n ω)) (P n))
    -- The exponentially tilted masses converge to one.
    (h_mass : Tendsto (fun n => ∫ ω, Real.exp (L n ω) ∂(P n)) atTop (𝓝 1))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε := by
  intro ε hε
  -- Step 1: pick a natural M₀ with `∫ min(exp, M₀) dN ≥ 1 - ε/4`.
  have h_gaussian := tendsto_integral_truncExp_gaussianReal v
  have h_ev :
      ∀ᶠ M : ℕ in atTop,
        1 - ε / 4 ≤
          ∫ x, min (Real.exp x) (M : ℝ)
            ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
    have h_mem : Set.Ici (1 - ε / 4) ∈ 𝓝 (1 : ℝ) :=
      Ici_mem_nhds (by linarith)
    exact h_gaussian h_mem
  obtain ⟨M₀, hM₀⟩ := h_ev.exists
  set M : ℝ := (M₀ : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨M, hM_nonneg, ?_⟩
  -- Step 2: for fixed M, get `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN`.
  have h_trunc_tendsto :=
    tendsto_integral_truncExp_L P L hL_meas v h_weak M hM_nonneg
  -- Step 3a: pick N₁ so that for n ≥ N₁, `∫ min(exp(L n), M) dP_n ≥ 1 - ε/2`.
  have h_target :
      ∀ᶠ n : ℕ in atTop,
        1 - ε / 2 ≤ ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    have h_mem : Set.Ioi (1 - ε / 2) ∈ 𝓝 (∫ x, min (Real.exp x) M
        ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) := by
      apply Ioi_mem_nhds
      linarith [hM₀]
    filter_upwards [h_trunc_tendsto h_mem] with n hn
    exact le_of_lt (Set.mem_Ioi.mp hn)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_target
  -- Step 3b: from `h_mass`, pick N₂ so that for n ≥ N₂, `∫ exp(L n) dP_n ≤ 1 + ε/2`.
  have h_mass_ub :
      ∀ᶠ n : ℕ in atTop,
        ∫ ω, Real.exp (L n ω) ∂(P n) ≤ 1 + ε / 2 := by
    have h_mem : Set.Iic (1 + ε / 2) ∈ 𝓝 (1 : ℝ) :=
      Iic_mem_nhds (by linarith)
    filter_upwards [h_mass h_mem] with n hn
    exact Set.mem_Iic.mp hn
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp h_mass_ub
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  -- Step 4: rearrange using `∫ exp(L n) dP_n ≤ 1 + ε/2` and `∫min ≥ 1 - ε/2`.
  have h_exp_int_n := h_exp_int n
  have h_trunc_int : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int_n.mono' ?_ ?_
    · exact ((Real.continuous_exp.measurable.comp
        (hL_meas n)).min measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact min_le_left _ _
      · exact le_min (Real.exp_pos _).le hM_nonneg
  have h_diff_eq :
      ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        = (∫ ω, Real.exp (L n ω) ∂(P n))
          - ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    rw [MeasureTheory.integral_sub h_exp_int_n h_trunc_int]
  rw [h_diff_eq]
  linarith [hN₁ n hn₁, hN₂ n hn₂]

/-- **Le Cam's third lemma from an integral-comparison bound.**

Assume the integral-comparison hypothesis `h_integral_comparison`:
for some `ρ → 0` and every bounded continuous `f`,
`|∫ f(X n) dQ_n − ∫ f(X n)·exp(L n) dP_n| ≤ ‖f‖·ρ_n`. The vanishing
slack does not affect the weak limit.

The proof combines bounded-continuous truncation, the residue estimate, the
target-side dominated-convergence argument, and an ε/4 bound for the
integral-comparison error. -/
theorem weak_limit_under_Q_of_lecam_third_of_integral_comparison
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (X : ∀ n, Ω n → E) (L : ∀ n, Ω n → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) (hL_meas : ∀ n, Measurable (L n))
    -- Asymptotic integral comparison without a common-support assumption.
    (h_integral_comparison :
      ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
        ∀ (f : E →ᵇ ℝ) (n : ℕ),
          |∫ ω, f (X n ω) ∂(Q n)
            - ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)| ≤ ‖f‖ * ρ n)
    (π : Measure (E × ℝ)) [IsProbabilityMeasure π]
    (h_joint_weak :
      WeakConverges (fun n => (P n).map (fun ω => (X n ω, L n ω))) π)
    (h_UI : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε)
    (h_exp_int_π : Integrable (fun p : E × ℝ => Real.exp p.2) π)
    (h_exp_int_π_eq_one : ∫ p, Real.exp p.2 ∂π = 1) :
    WeakConverges (fun n => (Q n).map (X n))
      ((π.withDensity (fun p => ENNReal.ofReal (Real.exp p.2))).map Prod.fst) := by
  intro f
  -- Rewrite RHS (target integral over tilted marginal) as ∫ f(p.1)·exp(p.2) dπ.
  have h_target_rewrite : ∫ x, f x ∂((π.withDensity
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2))).map Prod.fst)
      = ∫ p, f p.1 * Real.exp p.2 ∂π := by
    have h_exp_meas_snd : Measurable (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2)) :=
      (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
    have h_exp_lt_top : ∀ᵐ p ∂π, ENNReal.ofReal (Real.exp p.2) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable
        f.continuous.aestronglyMeasurable]
    rw [integral_withDensity_eq_integral_toReal_smul h_exp_meas_snd h_exp_lt_top
        (fun p => f p.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    change (ENNReal.ofReal (Real.exp p.2)).toReal • f p.1 = f p.1 * Real.exp p.2
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
  rw [h_target_rewrite]
  -- Map-integral identities: `bₙ` (under `Q n`) and `aₙ` (under `P n`, tilted).
  have h_bn_map : ∀ n, ∫ x, f x ∂((Q n).map (X n)) = ∫ ω, f (X n ω) ∂(Q n) := fun n =>
    MeasureTheory.integral_map (hX_meas n).aemeasurable f.continuous.aestronglyMeasurable
  have h_an_map : ∀ n,
      ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
        = ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n) := by
    intro n
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : E × ℝ => f p.1 * Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      ((f.continuous.comp continuous_fst).mul
        (Real.continuous_exp.comp continuous_snd)).aestronglyMeasurable
    rw [MeasureTheory.integral_map h_joint_meas.aemeasurable h_integrand_meas]
  -- ── Slack data from the integral comparison. ─────────────────────────────────────────
  obtain ⟨ρ, hρ_tendsto, hρ_bound⟩ := h_integral_comparison
  -- Eventual integrability of `exp(L n)` under `P n`, recovered from the comparison applied
  -- to the constant `1` BCF: `|1 - ∫ exp(L n) dP_n| ≤ ‖(1 : E →ᵇ ℝ)‖ · ρ n`, and the RHS → 0.
  have h_eventually_int :
      ∀ᶠ n in atTop, Integrable (fun ω => Real.exp (L n ω)) (P n) := by
    have hg1_bound := hρ_bound (1 : E →ᵇ ℝ)
    -- `∫ (1 : E →ᵇ ℝ)(X n) dQ_n = 1` and `(1 : E →ᵇ ℝ)(X n ω)·exp(L n ω) = exp(L n ω)`.
    have h_one_apply : ∀ n ω, ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) = 1 := by
      intro n ω; rw [BoundedContinuousFunction.coe_one]; rfl
    have hg1_simp : ∀ n,
        |(1 : ℝ) - ∫ ω, Real.exp (L n ω) ∂(P n)| ≤ ‖(1 : E →ᵇ ℝ)‖ * ρ n := by
      intro n
      have hb := hg1_bound n
      have h1 : ∫ ω, ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) ∂(Q n) = 1 := by
        simp only [h_one_apply, integral_const, smul_eq_mul, mul_one, probReal_univ]
      have h2 : (fun ω => ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) * Real.exp (L n ω))
          = fun ω => Real.exp (L n ω) := by
        funext ω; rw [h_one_apply]; ring
      rw [h1, h2] at hb
      exact hb
    -- `‖(1 : E →ᵇ ℝ)‖ · ρ n → 0`, so eventually `< 1`.
    have h_slack_zero : Tendsto (fun n => ‖(1 : E →ᵇ ℝ)‖ * ρ n) atTop (𝓝 0) := by
      have := hρ_tendsto.const_mul ‖(1 : E →ᵇ ℝ)‖
      simpa using this
    have h_ev_lt_one : ∀ᶠ n in atTop, ‖(1 : E →ᵇ ℝ)‖ * ρ n < 1 := by
      have h_mem : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
      filter_upwards [h_slack_zero h_mem] with n hn using Set.mem_Iio.mp hn
    filter_upwards [h_ev_lt_one] with n hn
    by_contra h_not_int
    have h_zero : ∫ ω, Real.exp (L n ω) ∂(P n) = 0 := integral_undef h_not_int
    have hb := hg1_simp n
    rw [h_zero, sub_zero, abs_one] at hb
    linarith
  -- The residue estimate applies after enlarging the threshold so that
  -- `exp(L n)` is integrable under `P n`.
  have h_map_tendsto : Tendsto
      (fun n => ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω))))
      atTop (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂π)) := by
    -- Residue bound on both sides via BCF truncation + triangle inequality.
    have hfbound : ∀ p : E × ℝ, |f p.1| ≤ ‖f‖ := fun p => f.norm_coe_le_norm _
    have h_exp_nonneg : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos _).le
    have h_residue_EℝR :
        ∀ (μ : Measure (E × ℝ)) (M : ℝ), 0 ≤ M →
          Integrable (fun p : E × ℝ => Real.exp p.2) μ →
          |∫ p, f p.1 * Real.exp p.2 ∂μ - ∫ p, f p.1 * min (Real.exp p.2) M ∂μ|
            ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
      intro μ M hM h_exp_int
      have h_min_nn : ∀ p : E × ℝ, 0 ≤ min (Real.exp p.2) M := fun p =>
        le_min (h_exp_nonneg _) hM
      have h_min_le : ∀ p : E × ℝ, min (Real.exp p.2) M ≤ Real.exp p.2 :=
        fun p => min_le_left _ _
      have h_min_meas : Measurable (fun p : E × ℝ => min (Real.exp p.2) M) :=
        (Real.continuous_exp.measurable.comp measurable_snd).min measurable_const
      have h_min_int : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) μ := by
        refine h_exp_int.mono' h_min_meas.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Real.norm_eq_abs, abs_of_nonneg (h_min_nn p)]
        exact h_min_le p
      have hf_ae :
          AEStronglyMeasurable (fun p : E × ℝ => f p.1) μ :=
        (f.continuous.comp continuous_fst).aestronglyMeasurable
      have hf_bound_ae : ∀ᵐ p ∂μ, ‖f p.1‖ ≤ ‖f‖ :=
        Filter.Eventually.of_forall (fun p => f.norm_coe_le_norm _)
      have h_fexp_int : Integrable (fun p : E × ℝ => f p.1 * Real.exp p.2) μ :=
        h_exp_int.bdd_mul hf_ae hf_bound_ae
      have h_fmin_int :
          Integrable (fun p : E × ℝ => f p.1 * min (Real.exp p.2) M) μ :=
        h_min_int.bdd_mul hf_ae hf_bound_ae
      rw [← integral_sub h_fexp_int h_fmin_int]
      have h_diff_eq :
          (fun p : E × ℝ => f p.1 * Real.exp p.2 - f p.1 * min (Real.exp p.2) M)
            = fun p => f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) := by
        funext p; ring
      rw [h_diff_eq]
      calc |∫ p, f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ|
          ≤ ∫ p, |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)| ∂μ :=
            abs_integral_le_integral_abs
        _ = ∫ p, |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
            change |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)|
              = |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M)
            rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (h_min_le p))]
        _ ≤ ∫ p, ‖f‖ * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun p => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (h_min_le p))))
              ((h_exp_int.sub h_min_int).const_mul ‖f‖)
              (Filter.Eventually.of_forall (fun p => ?_))
            refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (h_min_le p))
            exact hfbound p
        _ = ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ :=
            integral_const_mul _ _
    -- Target-side tendsto: as M → ∞, ∫ min(exp p.2, M) dπ → ∫ exp p.2 dπ = 1 (DCT under π).
    have h_target_tendsto : Tendsto
        (fun M : ℕ => ∫ p, min (Real.exp p.2) (M : ℝ) ∂π) atTop (𝓝 1) := by
      have h_lim : ∀ᵐ p ∂π,
          Tendsto (fun M : ℕ => min (Real.exp p.2) (M : ℝ)) atTop (𝓝 (Real.exp p.2)) := by
        refine Filter.Eventually.of_forall (fun p => ?_)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈Real.exp p.2⌉₊] with M hM
        have : Real.exp p.2 ≤ (M : ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast hM)
        exact (min_eq_left this).symm
      have h_dom : ∀ M : ℕ, ∀ᵐ p ∂π,
          ‖min (Real.exp p.2) (M : ℝ)‖ ≤ Real.exp p.2 := by
        intro M
        refine Filter.Eventually.of_forall (fun p => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) (Nat.cast_nonneg _))]
        exact min_le_left _ _
      have h_meas : ∀ M : ℕ,
          AEStronglyMeasurable (fun p : E × ℝ => min (Real.exp p.2) (M : ℝ)) π :=
        fun M => ((Real.continuous_exp.comp continuous_snd).min
          continuous_const).aestronglyMeasurable
      have h_conv := MeasureTheory.tendsto_integral_of_dominated_convergence
        (F := fun (M : ℕ) (p : E × ℝ) => min (Real.exp p.2) (M : ℝ))
        (f := fun p : E × ℝ => Real.exp p.2) (bound := fun p : E × ℝ => Real.exp p.2)
        h_meas h_exp_int_π h_dom h_lim
      rw [h_exp_int_π_eq_one] at h_conv
      exact h_conv
    -- Start ε argument.
    rw [Metric.tendsto_nhds]
    intro ε hε
    set C : ℝ := ‖f‖ + 1 with hC_def
    have hC_pos : 0 < C := by positivity
    have hnorm_le_C : ‖f‖ ≤ C := by simp [hC_def]
    have hthresh_pos : 0 < ε / (3 * C) := by positivity
    -- UI threshold on sequence side.
    obtain ⟨M_UI, hM_UI_nonneg, N_UI, hN_UI⟩ :=
      h_UI (ε / (3 * C)) hthresh_pos
    -- Target-side pick M_target so `1 - ε/(3C) < ∫ min(exp, M_target) dπ`.
    have h_ev_target : ∀ᶠ M : ℕ in atTop,
        (1 : ℝ) - ε / (3 * C) < ∫ p, min (Real.exp p.2) (M : ℝ) ∂π := by
      have h_mem : Set.Ioi ((1 : ℝ) - ε / (3 * C)) ∈ 𝓝 (1 : ℝ) :=
        Ioi_mem_nhds (by linarith)
      exact h_target_tendsto h_mem
    obtain ⟨M_target, hM_target⟩ := h_ev_target.exists
    -- Take M := max M_UI (M_target : ℝ).
    set M : ℝ := max M_UI (M_target : ℝ) with hM_def
    have hM_nonneg : 0 ≤ M := le_max_of_le_left hM_UI_nonneg
    have hM_ge_UI : M_UI ≤ M := le_max_left _ _
    have hM_ge_target : (M_target : ℝ) ≤ M := le_max_right _ _
    -- BCF `g_M(p) := f(p.1) · min(exp(p.2), M)`, norm ≤ ‖f‖ · M.
    let g_M : E × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p => f p.1 * min (Real.exp p.2) M)
      ((f.continuous.comp continuous_fst).mul
        ((Real.continuous_exp.comp continuous_snd).min continuous_const))
      (‖f‖ * M)
      (fun p => by
        rw [Real.norm_eq_abs, abs_mul]
        have h2 : 0 ≤ min (Real.exp p.2) M :=
          le_min (h_exp_nonneg _) hM_nonneg
        rw [abs_of_nonneg h2]
        refine mul_le_mul ?_ (min_le_right _ _) h2 (norm_nonneg _)
        exact hfbound p)
    have hg_M_apply : ∀ p, g_M p = f p.1 * min (Real.exp p.2) M := fun _ => rfl
    -- Weak convergence at g_M.
    have h_weak_gM := h_joint_weak g_M
    rw [Metric.tendsto_nhds] at h_weak_gM
    have hε3_pos : (0 : ℝ) < ε / 3 := by linarith
    obtain ⟨N_weak, hN_weak⟩ :=
      Filter.eventually_atTop.mp (h_weak_gM (ε / 3) hε3_pos)
    -- Eventual-integrability threshold.
    obtain ⟨N_int, hN_int⟩ := Filter.eventually_atTop.mp h_eventually_int
    rw [Filter.eventually_atTop]
    refine ⟨max (max N_UI N_weak) N_int, fun n hn => ?_⟩
    have hn_UI : N_UI ≤ n := le_of_max_le_left (le_of_max_le_left hn)
    have hn_weak : N_weak ≤ n := le_of_max_le_right (le_of_max_le_left hn)
    have hn_int : N_int ≤ n := le_of_max_le_right hn
    -- Sequence-side: `exp` integrable under `P n` (eventual) and under `(P n).map (X_n, L_n)`.
    have h_exp_int_Pn : Integrable (fun ω => Real.exp (L n ω)) (P n) := hN_int n hn_int
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_exp_int_map_n :
        Integrable (fun p : E × ℝ => Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      (MeasureTheory.integrable_map_measure
        (Real.continuous_exp.comp continuous_snd).aestronglyMeasurable
        h_joint_meas.aemeasurable).mpr h_exp_int_Pn
    -- UI bound at enlarged M: monotonicity of min(exp, ·) in M.
    have h_min_mono_M : ∀ ω,
        min (Real.exp (L n ω)) M_UI ≤ min (Real.exp (L n ω)) M :=
      fun ω => min_le_min_left _ hM_ge_UI
    have h_int_trunc_UI : Integrable
        (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI) (P n) := by
      refine h_exp_int_Pn.sub ?_
      refine h_exp_int_Pn.mono'
        ((Real.continuous_exp.measurable.comp (hL_meas n)).min
          measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (le_min (h_exp_nonneg _) hM_UI_nonneg)]
      exact min_le_left _ _
    have h_UI_bound_Pn :
        ∫ ω, (Real.exp (L n ω) - min (Real.exp (L n ω)) M) ∂(P n) ≤ ε / (3 * C) :=
      calc ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
          ≤ ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI ∂(P n) :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun ω => sub_nonneg.mpr (min_le_left _ _)))
              h_int_trunc_UI
              (Filter.Eventually.of_forall
                (fun ω => by linarith [h_min_mono_M ω]))
        _ ≤ ε / (3 * C) := hN_UI n hn_UI
    have h_UI_bound_map_n :
        ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
            ∂((P n).map (fun ω => (X n ω, L n ω)))
          ≤ ε / (3 * C) := by
      rw [MeasureTheory.integral_map h_joint_meas.aemeasurable]
      · exact h_UI_bound_Pn
      · exact ((Real.continuous_exp.comp continuous_snd).sub
          ((Real.continuous_exp.comp continuous_snd).min
            continuous_const)).aestronglyMeasurable
    -- Target-side residue bound:
    have h_trunc_int_π : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) π := by
      refine h_exp_int_π.mono'
        ((Real.continuous_exp.comp continuous_snd).min
          continuous_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
      exact min_le_left _ _
    have h_target_trunc_M_lb :
        (1 : ℝ) - ε / (3 * C) ≤ ∫ p, min (Real.exp p.2) M ∂π := by
      have h_mono :
          ∫ p, min (Real.exp p.2) (M_target : ℝ) ∂π
            ≤ ∫ p, min (Real.exp p.2) M ∂π := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall
            (fun p => le_min (h_exp_nonneg _) (Nat.cast_nonneg _)))
          h_trunc_int_π
          (Filter.Eventually.of_forall (fun p => min_le_min_left _ hM_ge_target))
      linarith [hM_target]
    have h_target_bound_π :
        ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π ≤ ε / (3 * C) := by
      rw [integral_sub h_exp_int_π h_trunc_int_π, h_exp_int_π_eq_one]
      linarith [h_target_trunc_M_lb]
    -- Apply residue bound on both sides.
    have h_res_map_n := h_residue_EℝR ((P n).map (fun ω => (X n ω, L n ω))) M hM_nonneg
      h_exp_int_map_n
    have h_res_π := h_residue_EℝR π M hM_nonneg h_exp_int_π
    -- Triangle inequality.
    rw [Real.dist_eq]
    have h_weak_bound :
        |∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω))) - ∫ p, g_M p ∂π| < ε / 3 := by
      have := hN_weak n hn_weak
      rwa [Real.dist_eq] at this
    have h_res_nonneg : 0 ≤ ‖f‖ := norm_nonneg _
    have h_seq_piece :
        |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
          - ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))| ≤ ε / 3 := by
      have h_gM_eq :
          ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
            = ∫ p, f p.1 * min (Real.exp p.2) M
                ∂((P n).map (fun ω => (X n ω, L n ω))) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
      rw [h_gM_eq]
      calc |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
              - ∫ p, f p.1 * min (Real.exp p.2) M
                  ∂((P n).map (fun ω => (X n ω, L n ω)))|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
                ∂((P n).map (fun ω => (X n ω, L n ω))) := h_res_map_n
        _ ≤ ‖f‖ * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_left h_UI_bound_map_n h_res_nonneg
        _ ≤ C * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
        _ = ε / 3 := by field_simp
    have h_target_piece :
        |∫ p, g_M p ∂π - ∫ p, f p.1 * Real.exp p.2 ∂π| ≤ ε / 3 := by
      have h_gM_eq :
          ∫ p, g_M p ∂π = ∫ p, f p.1 * min (Real.exp p.2) M ∂π :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
      rw [h_gM_eq, abs_sub_comm]
      calc |∫ p, f p.1 * Real.exp p.2 ∂π - ∫ p, f p.1 * min (Real.exp p.2) M ∂π|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π := h_res_π
        _ ≤ ‖f‖ * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_left h_target_bound_π h_res_nonneg
        _ ≤ C * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
        _ = ε / 3 := by field_simp
    set A := ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
    set B := ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
    set D := ∫ p, g_M p ∂π
    set E' := ∫ p, f p.1 * Real.exp p.2 ∂π
    have h_split : A - E' = (A - B) + (B - D) + (D - E') := by ring
    rw [h_split]
    calc |(A - B) + (B - D) + (D - E')|
        ≤ |(A - B) + (B - D)| + |D - E'| := abs_add_le _ _
      _ ≤ |A - B| + |B - D| + |D - E'| := by linarith [abs_add_le (A - B) (B - D)]
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h_seq_piece, h_weak_bound, h_target_piece]
      _ = ε := by ring
  -- ── Bridge `aₙ` (map form → `P n` form) to `bₙ = ∫ f d((Q n).map X)` via the slack. ───
  have h_a_tendsto : Tendsto
      (fun n => ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)) atTop
      (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂π)) :=
    h_map_tendsto.congr h_an_map
  -- Slack `bₙ - aₙ → 0` from `|bₙ - aₙ| ≤ ‖f‖·ρ n` and `‖f‖·ρ n → 0`.
  have h_slack_tendsto : Tendsto
      (fun n => (∫ ω, f (X n ω) ∂(Q n))
        - ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)) atTop (𝓝 0) := by
    have h_norm_zero : Tendsto (fun n => ‖f‖ * ρ n) atTop (𝓝 0) := by
      have := hρ_tendsto.const_mul ‖f‖
      simpa using this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h_norm_zero
    rw [Real.norm_eq_abs]
    exact hρ_bound f n
  -- Conclude: `bₙ = aₙ + (bₙ - aₙ) → target + 0 = target`.
  have h_sum := h_a_tendsto.add h_slack_tendsto
  rw [add_zero] at h_sum
  refine (h_sum.congr (fun n => ?_)).congr (fun n => (h_bn_map n).symm)
  ring

/-! ## Le Cam's first lemma — full four-way equivalence (vdV Lemma 6.4)

The four equivalent characterizations of contiguity are from van der Vaart
Lemma 6.4. The notion `Contiguous atTop P Q` (`Q ⊲ P`) is the book's statement (i)
in event form; its statistic form is statement (iv). Statements (ii) and (iii)
concern the weak limit points of the likelihood ratios `dPₙ/dQₙ` (under `Qₙ`) and
`dQₙ/dPₙ` (under `Pₙ`).

Throughout, `Measure.rnDeriv (P n) (Q n)` is `dPₙ/dQₙ`, mapped to `ℝ` via `.toReal`
and pushed forward to its law via `.map`.
-/

section LeCamFirstEquivalence

/-- **(i) ⟺ (iv): event form ⟺ statistic form** (vdV Lemma 6.4, equivalence of (i) and
(iv)).

The event-form contiguity `Contiguous atTop P Q` (`Q ⊲ P`: events with vanishing
`P`-probability have vanishing `Q`-probability) is equivalent to the statistic form: for
every sequence of measurable real-valued statistics `T n : Ω n → ℝ` that converges to `0`
in `P`-probability (`∀ ε > 0, (P n) {|T n| ≥ ε} → 0`), it also converges to `0` in
`Q`-probability.

Book reduction: events `Aₙ = {|Tₙ| ≥ ε}` (event form ⟹ statistic form), and
statistics `Tₙ = 1_{Aₙ}` (statistic form ⟹ event form). Pure measure theory. -/
theorem contiguous_iff_tendsto_zero_statistics
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n)) :
    Contiguous (ι := ℕ) (Ω := Ω) atTop P Q ↔
      ∀ (T : ∀ n, Ω n → ℝ), (∀ n, Measurable (T n)) →
        (∀ ε : ℝ, 0 < ε →
          Tendsto (fun n => (P n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0)) →
        ∀ ε : ℝ, 0 < ε →
          Tendsto (fun n => (Q n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0) := by
  constructor
  · -- (i) ⟹ (iv): events `Aₙ = {|Tₙ| ≥ ε}`.
    intro hcont T hT_meas hTP ε hε
    refine hcont (fun n => {ω | ε ≤ |T n ω|}) (fun n => ?_) (hTP ε hε)
    exact measurableSet_le measurable_const (hT_meas n).norm
  · -- (iv) ⟹ (i): statistics `Tₙ = 1_{Aₙ}`.
    intro h A hA_meas hP_A
    -- Use `T n = (A n).indicator (fun _ => (1 : ℝ))` and threshold `ε = 1/2`.
    set T : ∀ n, Ω n → ℝ := fun n => (A n).indicator (fun _ => (1 : ℝ)) with hT_def
    have hT_meas : ∀ n, Measurable (T n) := fun n =>
      (measurable_const.indicator (hA_meas n))
    -- `{ω | (1/2 : ℝ) ≤ |T n ω|} = A n`.
    have h_event : ∀ n, {ω | (1 / 2 : ℝ) ≤ |T n ω|} = A n := by
      intro n
      ext ω
      simp only [Set.mem_ofPred_eq, hT_def]
      by_cases hω : ω ∈ A n
      · rw [Set.indicator_of_mem hω, abs_one]
        simp only [hω, iff_true]; norm_num
      · rw [Set.indicator_of_notMem hω, abs_zero]
        simp only [hω, iff_false, not_le]; norm_num
    have h_half : (0 : ℝ) < 1 / 2 := by norm_num
    -- Statistic form: `P{|T|≥ε} → 0` for all ε, since `{|T|≥ε} ⊆ A n` and `P(A)→0`.
    have hTP : ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => (P n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0) := by
      intro ε hε
      -- `{ω | ε ≤ |T n ω|} ⊆ A n` for any `ε > 0`.
      have h_sub : ∀ n, {ω | ε ≤ |T n ω|} ⊆ A n := by
        intro n ω hω
        simp only [Set.mem_ofPred_eq, hT_def] at hω
        by_contra hωA
        rw [Set.indicator_of_notMem hωA] at hω
        simp only [abs_zero] at hω
        linarith
      -- Squeeze: `0 ≤ P{|T|≥ε} ≤ P(A) → 0` (ENNReal-valued).
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hP_A
        (Eventually.of_forall (fun n => zero_le))
        (Eventually.of_forall (fun n => measure_mono (h_sub n)))
    have hTQ := h (fun n => T n) hT_meas hTP (1 / 2) h_half
    -- Rewrite the `Q`-events back to `A n`.
    have h_eq : (fun n => (Q n) {ω | (1 / 2 : ℝ) ≤ |T n ω|}) = fun n => (Q n) (A n) := by
      funext n; rw [h_event n]
    rwa [h_eq] at hTQ

/-- **(i) ⟹ (ii)**: contiguity forces the weak limit points of `dPₙ/dQₙ` (under `Qₙ`)
to give mass `0` to `0` (vdV Lemma 6.4, (i) ⟹ (ii)).

If `Contiguous atTop P Q` (`Q ⊲ P`) and `U` is a weak limit (along a subsequence `φ`) of
the laws of `(dP_{φk}/dQ_{φk})` under `Q_{φk}`, then `U {x | 0 < x} = 1`.

Book: `gₙ(c) = Qₙ(dPₙ/dQₙ < c) − U(< c)`; portmanteau `liminf gₙ(c) ≥ 0` on the open
set `{· < c}`; a slowly decreasing `εₙ ↓ 0`; contiguity kills `Qₙ(dPₙ/dQₙ < εₙ) → 0`.

The hypothesis `hac : ∀ k, P (φ k) ≪ Q (φ k)` makes the real-valued density
`(dPₙ/dQₙ).toReal` a density capturing all of `Pₙ`.
This is van der Vaart's implicit likelihood-ratio convention. -/
theorem contiguous_imp_limit_pos
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hcont : Contiguous (ι := ℕ) (Ω := Ω) atTop P Q)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hac : ∀ k, (P (φ k)).AbsolutelyContinuous (Q (φ k)))
    (U : Measure ℝ) [IsProbabilityMeasure U]
    (hU : WeakConverges
      (fun k => (Q (φ k)).map (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal)) U) :
    U {x : ℝ | 0 < x} = 1 := by
  -- Abbreviations: real-valued density `r k`, its law `μ' k` under `Q (φ k)`.
  set r : ∀ k, Ω (φ k) → ℝ := fun k ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal with hr_def
  have hr_meas : ∀ k, Measurable (r k) := fun k =>
    ((P (φ k)).measurable_rnDeriv (Q (φ k))).ennreal_toReal
  have hr_nonneg : ∀ k ω, 0 ≤ r k ω := fun k ω => ENNReal.toReal_nonneg
  -- The pushforward law as a `ProbabilityMeasure`, and `Tendsto` in the weak topology.
  set μ' : ℕ → ProbabilityMeasure ℝ :=
    fun k => ⟨(Q (φ k)).map (r k), by
      have : IsProbabilityMeasure ((Q (φ k)).map (r k)) :=
        (by infer_instance)
      exact this⟩ with hμ'_def
  set U' : ProbabilityMeasure ℝ := ⟨U, inferInstance⟩ with hU'_def
  have h_tendsto : Tendsto μ' atTop (𝓝 U') :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hU
  -- Measure-level value of `μ' k` on a measurable set: `μ' k s = Q(φk) (r k ⁻¹' s)`.
  have hμ'_coe : ∀ k, ((μ' k : Measure ℝ)) = (Q (φ k)).map (r k) := fun k => rfl
  have hU'_coe : ((U' : Measure ℝ)) = U := rfl
  have hμ'_apply : ∀ k {s : Set ℝ}, MeasurableSet s →
      ((μ' k : Measure ℝ)) s = (Q (φ k)) (r k ⁻¹' s) := by
    intro k s hs
    rw [hμ'_coe k, Measure.map_apply (hr_meas k) hs]
  -- ── Crux pointwise bound: `P(φk){r k < c} ≤ ofReal c` for `c > 0`. ──────────────────────
  have h_crux : ∀ (k : ℕ) (c : ℝ), 0 < c →
      (P (φ k)) {ω | r k ω < c} ≤ ENNReal.ofReal c := by
    intro k c hc
    set ν := Q (φ k) with hν
    set μ := P (φ k) with hμ
    set C : Set (Ω (φ k)) := {ω | r k ω < c} with hC
    have hC_meas : MeasurableSet C :=
      measurableSet_lt (hr_meas k) measurable_const
    -- `μ = ν.withDensity (rnDeriv μ ν)` via absolute continuity.
    have h_wd : ν.withDensity (μ.rnDeriv ν) = μ :=
      Measure.withDensity_rnDeriv_eq μ ν (hac k)
    -- `μ C = ∫⁻ ω in C, rnDeriv μ ν ω ∂ν`.
    have h_μC : μ C = ∫⁻ ω in C, μ.rnDeriv ν ω ∂ν := by
      conv_lhs => rw [← h_wd]
      rw [withDensity_apply _ hC_meas]
    rw [h_μC]
    -- On `C`, `ν`-a.e. `rnDeriv μ ν ω ≤ ofReal c`.
    have h_rn_lt_top : ∀ᵐ ω ∂ν, μ.rnDeriv ν ω < ⊤ := Measure.rnDeriv_lt_top μ ν
    have h_bound_ae : ∀ᵐ ω ∂(ν.restrict C), μ.rnDeriv ν ω ≤ ENNReal.ofReal c := by
      rw [ae_restrict_iff' hC_meas]
      filter_upwards [h_rn_lt_top] with ω hω_lt_top hω_in
      -- `ω ∈ C` means `(rnDeriv μ ν ω).toReal < c`; with finiteness, `rnDeriv < ofReal c`.
      have hω_mem : (μ.rnDeriv ν ω).toReal < c := hω_in
      rw [← ENNReal.ofReal_toReal hω_lt_top.ne]
      exact ENNReal.ofReal_le_ofReal hω_mem.le
    calc ∫⁻ ω in C, μ.rnDeriv ν ω ∂ν
        ≤ ∫⁻ _ in C, ENNReal.ofReal c ∂ν := lintegral_mono_ae h_bound_ae
      _ = ENNReal.ofReal c * ν C := by rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal c * 1 := by
          gcongr; exact prob_le_one
      _ = ENNReal.ofReal c := mul_one _
  -- ── Step A: `U` puts no mass below 0. ───────────────────────────────────────────────────
  -- The open set `{x < 0}` has `μ' k`-mass 0 (densities are `≥ 0`), so by portmanteau
  -- `U {x < 0} ≤ liminf 0 = 0`.
  have h_neg_open : IsOpen {x : ℝ | x < 0} := isOpen_lt continuous_id continuous_const
  have h_below_zero : U {x : ℝ | x < 0} = 0 := by
    -- Portmanteau (Measure/ENNReal form): `U {x<0} ≤ liminf (μ' k {x<0})`.
    have h_le := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      h_tendsto h_neg_open
    rw [hU'_coe] at h_le
    -- Each `(μ' k : Measure ℝ) {x < 0} = 0` since densities are `≥ 0`.
    have h_each : ∀ k, ((μ' k : Measure ℝ)) {x : ℝ | x < 0} = 0 := by
      intro k
      have h_pre : r k ⁻¹' {x : ℝ | x < 0} = (∅ : Set (Ω (φ k))) := by
        ext ω; simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_lt]
        exact hr_nonneg k ω
      rw [hμ'_apply k h_neg_open.measurableSet, h_pre, measure_empty]
    simp only [h_each, Filter.liminf_const] at h_le
    exact le_antisymm h_le (zero_le)
  -- ── Step B: `U {x ≤ 0} = 0` via slow-threshold contiguity. ──────────────────────────────
  have h_at_zero : U {x : ℝ | x ≤ 0} = 0 := by
    by_contra h_ne
    -- `δ := U {x ≤ 0} > 0` (in ℝ≥0∞).
    set δ : ℝ≥0∞ := U {x : ℝ | x ≤ 0} with hδ_def
    have hδ_pos : 0 < δ := pos_iff_ne_zero.mpr h_ne
    have hδ_lt_top : δ < ⊤ := lt_of_le_of_lt prob_le_one ENNReal.one_lt_top
    have hδ2_lt : δ / 2 < δ := ENNReal.half_lt_self hδ_pos.ne' hδ_lt_top.ne
    -- For each `m`, the open set `Gₘ = {x < 1/(m+1)}` contains `{x ≤ 0}`, and portmanteau gives
    -- `δ ≤ U Gₘ ≤ liminf_k μ'ₖ Gₘ`, hence `∀ᶠ k, δ/2 < μ'ₖ Gₘ = Q(φk){r k < 1/(m+1)}`.
    have h_event_each : ∀ m : ℕ, ∀ᶠ k in atTop,
        δ / 2 < (Q (φ k)) {ω | r k ω < 1 / (m + 1 : ℝ)} := by
      intro m
      have hc_pos : (0 : ℝ) < 1 / (m + 1 : ℝ) := by positivity
      set G : Set ℝ := {x : ℝ | x < 1 / (m + 1 : ℝ)} with hG_def
      have hG_open : IsOpen G := isOpen_lt continuous_id continuous_const
      have h_subset : {x : ℝ | x ≤ 0} ⊆ G := by
        intro x hx; simp only [hG_def, Set.mem_ofPred_eq]; exact lt_of_le_of_lt hx hc_pos
      have h_portmanteau :=
        MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto h_tendsto hG_open
      rw [hU'_coe] at h_portmanteau
      have h_δ_le : δ ≤ U G := by rw [hδ_def]; exact measure_mono h_subset
      have h_δ_le_liminf : δ ≤ Filter.liminf (fun k => ((μ' k : Measure ℝ)) G) atTop :=
        le_trans h_δ_le h_portmanteau
      have h_lt_liminf : δ / 2 < Filter.liminf (fun k => ((μ' k : Measure ℝ)) G) atTop :=
        lt_of_lt_of_le hδ2_lt h_δ_le_liminf
      have h_ev := Filter.eventually_lt_of_lt_liminf h_lt_liminf
      filter_upwards [h_ev] with k hk
      have h_μ'G : ((μ' k : Measure ℝ)) G = (Q (φ k)) {ω | r k ω < 1 / (m + 1 : ℝ)} := by
        rw [hμ'_apply k hG_open.measurableSet]; rfl
      rwa [h_μ'G] at hk
    -- Extract a strictly increasing threshold-index `N : ℕ → ℕ`.
    choose N₀ hN₀ using fun m => Filter.eventually_atTop.mp (h_event_each m)
    -- Strictly monotone version: `N m := (running max of N₀) + m`.
    set N : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup N₀ + m with hN_def
    have hN_ge : ∀ m, N₀ m ≤ N m := by
      intro m
      have : N₀ m ≤ (Finset.range (m + 1)).sup N₀ :=
        Finset.le_sup (Finset.self_mem_range_succ m)
      simp only [hN_def]; omega
    have hN_strictMono : StrictMono N := by
      intro a b hab
      have hab1 : a + 1 ≤ b + 1 := by omega
      have h_sup_mono : (Finset.range (a + 1)).sup N₀ ≤ (Finset.range (b + 1)).sup N₀ :=
        Finset.sup_mono (Finset.range_mono hab1)
      simp only [hN_def]
      omega
    have hN_ge_self : ∀ m, m ≤ N m := fun m => hN_strictMono.le_apply
    -- The guarantee at the monotone threshold: `∀ k ≥ N m, δ/2 < Q(φk){r k < 1/(m+1)}`.
    have hN_guar : ∀ m, ∀ k, N m ≤ k → δ / 2 < (Q (φ k)) {ω | r k ω < 1 / (m + 1 : ℝ)} :=
      fun m k hk => hN₀ m k (le_trans (hN_ge m) hk)
    -- Slow threshold: `g k = largest m ≤ k with N m ≤ k`; `c k = 1/(g k + 1)`.
    set g : ℕ → ℕ := fun k => Nat.findGreatest (fun m => N m ≤ k) k with hg_def
    set c : ℕ → ℝ := fun k => 1 / (g k + 1 : ℝ) with hc_def
    have hc_pos : ∀ k, 0 < c k := fun k => by simp only [hc_def]; positivity
    -- `g k → ∞`: for any `m`, once `k ≥ N m`, `g k ≥ m`.
    have hg_tendsto : Tendsto g atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro m
      refine ⟨N m, fun k hk => ?_⟩
      have hm_le_k : m ≤ k := le_trans (hN_ge_self m) hk
      exact Nat.le_findGreatest hm_le_k hk
    -- hence `c k → 0`.
    have hc_tendsto : Tendsto c atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => (g k : ℝ) + 1) atTop atTop := by
        have := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hg_tendsto
        exact this.atTop_add tendsto_const_nhds
      simpa [hc_def, one_div] using! h1.inv_tendsto_atTop
    -- For `k` with a witness (i.e. `N 0 ≤ k`), `N (g k) ≤ k`, giving the mass lower bound.
    have h_mass_lb : ∀ k, N 0 ≤ k →
        δ / 2 < (Q (φ k)) {ω | r k ω < c k} := by
      intro k hk
      have h_spec : N (g k) ≤ k :=
        Nat.findGreatest_spec (m := 0) (P := fun m => N m ≤ k) (Nat.zero_le k) hk
      have := hN_guar (g k) k h_spec
      -- `1/(g k + 1) = c k`.
      simpa [hc_def] using! this
    -- ── Build the contiguity event family along the full index. ──────────────────────────
    -- `A i := {ω | (dPᵢ/dQᵢ).toReal < c (φ⁻¹ i)}` for `i ∈ range φ`, else `∅`.
    classical
    set A : ∀ i : ℕ, Set (Ω i) := fun i =>
      if h : ∃ k, φ k = i then
        {ω | ((P i).rnDeriv (Q i) ω).toReal < c (Classical.choose h)}
      else ∅ with hA_def
    have hA_meas : ∀ i, MeasurableSet (A i) := by
      intro i
      simp only [hA_def]
      by_cases h : ∃ k, φ k = i
      · rw [dite_eq_left h]
        exact measurableSet_lt
          (((P i).measurable_rnDeriv (Q i)).ennreal_toReal) measurable_const
      · rw [dite_eq_right h]; exact MeasurableSet.empty
    -- At `i = φ k`, `A (φ k) = {ω | r k ω < c k}` (uses injectivity of `φ`).
    have hA_at_φ : ∀ k, A (φ k) = {ω | r k ω < c k} := by
      intro k
      have h_ex : ∃ j, φ j = φ k := ⟨k, rfl⟩
      simp only [hA_def, dite_eq_left h_ex]
      have h_choose : Classical.choose h_ex = k :=
        hφ.injective (Classical.choose_spec h_ex)
      rw [h_choose]
    -- `P i (A i) → 0` over all `i`.
    have hP_tendsto : Tendsto (fun i => (P i) (A i)) atTop (𝓝 0) := by
      -- For `ε > 0`, pick `K` with `c k < ε` for `k ≥ K`; then for `i ≥ φ K`, `P i (A i) ≤ ε`.
      rw [ENNReal.tendsto_atTop_zero]
      intro ε hε
      -- choose real threshold `ε' > 0` with `ofReal ε' ≤ ε`.
      obtain ⟨ε', hε'_pos, hε'_le⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ENNReal.ofReal ε' ≤ ε := by
        rcases eq_or_lt_of_le (le_top (a := ε)) with h | h
        · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
        · refine ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h.ne, ?_⟩
          rw [ENNReal.ofReal_toReal h.ne]
      have hc_lt : ∀ᶠ k in atTop, c k < ε' := by
        have := hc_tendsto
        rw [Metric.tendsto_nhds] at this
        filter_upwards [this ε' hε'_pos] with k hk
        rw [Real.dist_eq, sub_zero, abs_of_pos (hc_pos k)] at hk
        exact hk
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hc_lt
      refine ⟨φ K, fun i hi => ?_⟩
      by_cases h_ex : ∃ k, φ k = i
      · obtain ⟨k, hk_eq⟩ := h_ex
        subst hk_eq
        -- `φ K ≤ φ k ⟹ K ≤ k` (φ mono).
        have hKk : K ≤ k := by
          by_contra hlt
          push Not at hlt
          exact absurd (hφ hlt) (not_lt.mpr hi)
        rw [hA_at_φ k]
        calc (P (φ k)) {ω | r k ω < c k}
            ≤ ENNReal.ofReal (c k) := h_crux k (c k) (hc_pos k)
          _ ≤ ENNReal.ofReal ε' := ENNReal.ofReal_le_ofReal (hK k hKk).le
          _ ≤ ε := hε'_le
      · have hAi : A i = ∅ := by simp only [hA_def, dite_eq_right h_ex]
        rw [hAi, measure_empty]; exact zero_le (a := ε)
    -- Contiguity ⟹ `Q i (A i) → 0`.
    have hQ_tendsto : Tendsto (fun i => (Q i) (A i)) atTop (𝓝 0) :=
      hcont A hA_meas hP_tendsto
    -- But along `φ`, `Q (φ k)(A (φ k)) = Q(φk){r k < c k} > δ/2` eventually — contradiction.
    have hQ_sub : Tendsto (fun k => (Q (φ k)) (A (φ k))) atTop (𝓝 0) :=
      hQ_tendsto.comp hφ.tendsto_atTop
    -- Lower bound `δ/2 < Q(φk)(A(φk))` for `k ≥ N 0`.
    have h_contra : ∀ᶠ k in atTop, δ / 2 < (Q (φ k)) (A (φ k)) := by
      refine Filter.eventually_atTop.mpr ⟨N 0, fun k hk => ?_⟩
      rw [hA_at_φ k]
      exact h_mass_lb k hk
    -- Upper bound `Q(φk)(A(φk)) < δ/2` eventually, from convergence to 0.
    have h_ev_lt : ∀ᶠ k in atTop, (Q (φ k)) (A (φ k)) < δ / 2 := by
      have h_mem : Set.Iio (δ / 2) ∈ 𝓝 (0 : ℝ≥0∞) :=
        Iio_mem_nhds (ENNReal.half_pos hδ_pos.ne')
      filter_upwards [hQ_sub h_mem] with k hk using Set.mem_Iio.mp hk
    obtain ⟨k, hk1, hk2⟩ := (h_contra.and h_ev_lt).exists
    exact absurd hk1 (not_lt.mpr hk2.le)
  -- ── Step C: conclude `U {0 < x} = 1`. ───────────────────────────────────────────────────
  have h_compl : {x : ℝ | 0 < x}ᶜ = {x : ℝ | x ≤ 0} := by
    ext x; simp [not_lt]
  have h_meas_pos : MeasurableSet {x : ℝ | (0 : ℝ) < x} :=
    measurableSet_lt measurable_const measurable_id
  have h_compl_zero : U {x : ℝ | 0 < x}ᶜ = 0 := by rw [h_compl]; exact h_at_zero
  have h_eq := prob_compl_eq_one_sub (μ := U) h_meas_pos
  rw [h_compl_zero] at h_eq
  -- `0 = 1 - U {0<x}`, and `U {0<x} ≤ 1`, so `U {0<x} = 1`.
  have h_le_one : U {x : ℝ | 0 < x} ≤ 1 := prob_le_one
  rw [eq_comm, tsub_eq_zero_iff_le] at h_eq
  exact le_antisymm h_le_one h_eq

/-- **Marginal tightness implies joint tightness.** -/
private theorem tight_prod_of_tight_marginals_local
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (S : Set (Measure (X × Y)))
    (hX : IsTightMeasureSet ((fun μ : Measure (X × Y) => μ.map Prod.fst) '' S))
    (hY : IsTightMeasureSet ((fun μ : Measure (X × Y) => μ.map Prod.snd) '' S)) :
    IsTightMeasureSet S := by
  rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hX hY ⊢
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := by
    rw [ENNReal.div_pos_iff]; exact ⟨hε.ne', by norm_num⟩
  obtain ⟨K_X, hK_X_compact, hK_X⟩ := hX (ε / 2) hε2
  obtain ⟨K_Y, hK_Y_compact, hK_Y⟩ := hY (ε / 2) hε2
  refine ⟨K_X ×ˢ K_Y, hK_X_compact.prod hK_Y_compact, ?_⟩
  intro μ hμ
  rw [Set.compl_prod_eq_union]
  calc μ ((K_X)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (K_Y)ᶜ)
      ≤ μ ((K_X)ᶜ ×ˢ Set.univ) + μ (Set.univ ×ˢ (K_Y)ᶜ) := measure_union_le _ _
    _ = (μ.map Prod.fst) (K_X)ᶜ + (μ.map Prod.snd) (K_Y)ᶜ := by
        rw [Set.prod_univ, Set.univ_prod,
            Measure.map_apply measurable_fst hK_X_compact.measurableSet.compl,
            Measure.map_apply measurable_snd hK_Y_compact.measurableSet.compl]
    _ ≤ ε / 2 + ε / 2 :=
        add_le_add (hK_X _ ⟨μ, hμ, rfl⟩) (hK_Y _ ⟨μ, hμ, rfl⟩)
    _ = ε := ENNReal.add_halves _

/-- **A tight sequence of probability measures has a weakly convergent subsequence.** -/
private theorem extract_weak_subseq_local
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (h_tight : IsTightMeasureSet (Set.range μ)) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (μ_lim : Measure E) (_ : IsProbabilityMeasure μ_lim),
      WeakConverges (fun k => μ (φ k)) μ_lim := by
  set P : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩ with hP_def
  have h_tight_P :
      IsTightMeasureSet {(↑(ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range P} := by
    have : {(↑(ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range P} = Set.range μ := by
      ext ρ
      constructor
      · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩; exact ⟨P n, ⟨n, rfl⟩, rfl⟩
    rw [this]; exact h_tight
  have h_compact : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet h_tight_P
  have h_P_in : ∀ n, P n ∈ closure (Set.range P) := fun n => subset_closure ⟨n, rfl⟩
  have h_seqcompact : IsSeqCompact (closure (Set.range P)) := h_compact.isSeqCompact
  obtain ⟨P_lim, _hP_lim_in, φ, hφ_mono, hφ_conv⟩ := h_seqcompact h_P_in
  refine ⟨φ, hφ_mono, (P_lim : Measure E), inferInstance, ?_⟩
  intro f
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hφ_conv) f

/-- **(iii) ⟹ (i)**: if every subsequential weak limit `V` of `dQₙ/dPₙ` (under `Pₙ`) has
mean `1`, then `Q ⊲ P` (vdV Lemma 6.4, (iii) ⟹ (i)).

Book: to show `Pₙ(Aₙ) → 0 ⟹ Qₙ(Aₙ) → 0`, pass to a subsequence along which
`(dQₙ/dPₙ, 1_{Aₙᶜ}) ⇝ (V, 1)` jointly under `Pₙ` (Prohorov), then portmanteau on the
continuous nonnegative `(v, t) ↦ v·t` gives `liminf Qₙ(Aₙᶜ) ≥ EV = 1`, so `Qₙ(Aₙ) → 0`.

The hypothesis `hac : ∀ n, Q n ≪ P n` makes `(dQₙ/dPₙ).toReal` honest as the `Pₙ`-density
of `Qₙ`, so `Qₙ(B) = ∫_B (dQₙ/dPₙ) dPₙ`; this is van der Vaart's likelihood-ratio
convention. -/
theorem mean_one_imp_contiguous
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hac : ∀ n, (Q n).AbsolutelyContinuous (P n))
    (hV : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (V : Measure ℝ), IsProbabilityMeasure V →
      WeakConverges
        (fun k => (P (φ k)).map (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal)) V →
      ∫ x, x ∂V = 1) :
    Contiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  -- Real-valued density of `Q n` w.r.t. `P n`, and the change-of-measure identity.
  set q : ∀ n, Ω n → ℝ := fun n ω => ((Q n).rnDeriv (P n) ω).toReal with hq_def
  have hq_meas : ∀ n, Measurable (q n) := fun n =>
    ((Q n).measurable_rnDeriv (P n)).ennreal_toReal
  have hq_nonneg : ∀ n ω, 0 ≤ q n ω := fun n ω => ENNReal.toReal_nonneg
  -- `Q n B = ∫⁻ ω in B, (Q n).rnDeriv (P n) ω ∂(P n)` (change of measure, `Q n ≪ P n`).
  have hQ_change : ∀ n {B : Set (Ω n)}, MeasurableSet B →
      (Q n) B = ∫⁻ ω in B, (Q n).rnDeriv (P n) ω ∂(P n) :=
    fun n {B} hB => (Measure.setLIntegral_rnDeriv' (hac n) hB).symm
  -- `∫⁻ (Q n).rnDeriv (P n) ∂(P n) = 1`.
  have hQ_total : ∀ n, ∫⁻ ω, (Q n).rnDeriv (P n) ω ∂(P n) = 1 := by
    intro n; rw [Measure.lintegral_rnDeriv (hac n)]; simp
  classical
  -- Suppose, for contradiction, that `Q n (A n)` does not tend to 0.
  intro A hA_meas hPA
  by_contra h_not
  -- Extract `δ > 0` and a strictly monotone subsequence with `δ ≤ Q (ψ m) (A (ψ m))`.
  -- Since `Q n (A n) ∈ [0, 1]`, failure of convergence gives a frequently-`≥ δ` event.
  obtain ⟨δ, hδ_pos, hψ_freq⟩ :
      ∃ δ : ℝ≥0∞, 0 < δ ∧ ∃ᶠ n in atTop, δ ≤ (Q n) (A n) := by
    by_contra h_all
    push Not at h_all
    -- `∀ δ > 0, ∀ᶠ n, Q n (A n) < δ`, i.e. `Q n (A n) → 0`.
    apply h_not
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    rcases eq_or_lt_of_le (le_top (a := ε)) with hε_top | hε_lt
    · exact ⟨0, fun n _ => hε_top ▸ le_top⟩
    · have hε2_pos : (0 : ℝ≥0∞) < ε := hε
      obtain ⟨N, hN⟩ := (h_all ε hε2_pos).exists_forall_of_atTop
      exact ⟨N, fun n hn => (hN n hn).le⟩
  obtain ⟨ψ, hψ_mono, hψ_ge⟩ := extraction_of_frequently_atTop hψ_freq
  -- ── Joint laws of `(q, 1_{Aᶜ})` under `P` along `ψ`. ───────────────────────────────────
  -- Indicator of the complement of the event.
  set s : ∀ n, Ω n → ℝ := fun n => (A n)ᶜ.indicator (fun _ => (1 : ℝ)) with hs_def
  have hs_meas : ∀ n, Measurable (s n) := fun n =>
    (measurable_const.indicator (hA_meas n).compl)
  have hs01 : ∀ n ω, s n ω = 0 ∨ s n ω = 1 := by
    intro n ω; by_cases h : ω ∈ (A n)ᶜ
    · right; simp only [hs_def, Set.indicator_of_mem h]
    · left; simp only [hs_def, Set.indicator_of_notMem h]
  have hs_nonneg : ∀ n ω, 0 ≤ s n ω := by
    intro n ω; rcases hs01 n ω with h | h
    · rw [h]
    · rw [h]; exact zero_le_one
  -- Joint map `ω ↦ (q (ψ m) ω, s (ψ m) ω)` and its pushforward under `P (ψ m)`.
  set pair : ∀ m, Ω (ψ m) → ℝ × ℝ := fun m ω => (q (ψ m) ω, s (ψ m) ω) with hpair_def
  have hpair_meas : ∀ m, Measurable (pair m) := fun m =>
    (hq_meas (ψ m)).prodMk (hs_meas (ψ m))
  set J : ℕ → Measure (ℝ × ℝ) := fun m => (P (ψ m)).map (pair m) with hJ_def
  have hJ_prob : ∀ m, IsProbabilityMeasure (J m) := fun m =>
    (by infer_instance)
  -- ── Tightness of the joint laws (via tight marginals). ──────────────────────────────────
  -- First marginal: law of `q (ψ m)` under `P (ψ m)`.
  have hcomp_fst : ∀ m, Prod.fst ∘ pair m = q (ψ m) := fun m => by
    funext ω; simp only [hpair_def, Function.comp_apply]
  have hcomp_snd : ∀ m, Prod.snd ∘ pair m = s (ψ m) := fun m => by
    funext ω; simp only [hpair_def, Function.comp_apply]
  have hJ_fst : ∀ m, (J m).map Prod.fst = (P (ψ m)).map (q (ψ m)) := by
    intro m
    rw [hJ_def, Measure.map_map measurable_fst (hpair_meas m), hcomp_fst m]
  have hJ_snd : ∀ m, (J m).map Prod.snd = (P (ψ m)).map (s (ψ m)) := by
    intro m
    rw [hJ_def, Measure.map_map measurable_snd (hpair_meas m), hcomp_snd m]
  -- Tightness of the first marginals via Markov on the uniform first-moment bound.
  have h_tight_fst : IsTightMeasureSet (Set.range (fun m => (J m).map Prod.fst)) := by
    refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
    -- Uniform Markov bound: `⨆ m, ((J m).map fst) {x | r < |x|} ≤ ofReal (1 / r)` for `r > 0`.
    have h_bound : ∀ r : ℝ, 0 < r →
        (⨆ μ' ∈ Set.range (fun m => (J m).map Prod.fst), μ' {x : ℝ | r < ‖x‖})
          ≤ (ENNReal.ofReal r)⁻¹ := by
      intro r hr
      refine iSup₂_le ?_
      rintro μ' ⟨m, rfl⟩
      simp only [hJ_fst m]
      -- Pull back: `{x | r < |x|}` under `q (ψ m)` is `{ω | r < q (ψ m) ω}` (since `q ≥ 0`).
      rw [Measure.map_apply (hq_meas (ψ m))
        (measurableSet_lt measurable_const measurable_norm)]
      have h_sub : (q (ψ m)) ⁻¹' {x : ℝ | r < ‖x‖}
          ⊆ {ω | ENNReal.ofReal r ≤ (Q (ψ m)).rnDeriv (P (ψ m)) ω} := by
        intro ω hω
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Real.norm_eq_abs,
          abs_of_nonneg (hq_nonneg (ψ m) ω)] at hω
        simp only [Set.mem_ofPred_eq, hq_def] at hω ⊢
        -- `r < (rnDeriv ω).toReal` with `r > 0` forces `rnDeriv ω ≠ ∞`.
        have h_ne_top : (Q (ψ m)).rnDeriv (P (ψ m)) ω ≠ ∞ := by
          intro h_top; rw [h_top, ENNReal.toReal_top] at hω; linarith
        rw [← ENNReal.ofReal_toReal h_ne_top]
        exact ENNReal.ofReal_le_ofReal hω.le
      calc (P (ψ m)) ((q (ψ m)) ⁻¹' {x : ℝ | r < ‖x‖})
          ≤ (P (ψ m)) {ω | ENNReal.ofReal r ≤ (Q (ψ m)).rnDeriv (P (ψ m)) ω} :=
            measure_mono h_sub
        _ ≤ (∫⁻ ω, (Q (ψ m)).rnDeriv (P (ψ m)) ω ∂(P (ψ m))) / ENNReal.ofReal r :=
            meas_ge_le_lintegral_div ((Q (ψ m)).measurable_rnDeriv (P (ψ m))).aemeasurable
              (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
        _ = (ENNReal.ofReal r)⁻¹ := by rw [hQ_total (ψ m), one_div]
    -- `(ofReal r)⁻¹ → 0`, and the iSup is squeezed below it.
    have h_lim : Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹) atTop (𝓝 0) := by
      have h := tendsto_inv_iff.2 ENNReal.tendsto_ofReal_atTop
      rw [ENNReal.inv_top] at h
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr using h_bound r hr
  -- Tightness of the second marginals (they live in `[0,1]`, hence in a compact set).
  have h_tight_snd : IsTightMeasureSet (Set.range (fun m => (J m).map Prod.snd)) := by
    refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
    -- For `r ≥ 1`, `{x | r < |x|}` has zero mass (`s ∈ {0,1}`, so `|s| ≤ 1`).
    have h_zero : ∀ r : ℝ, 1 ≤ r →
        (⨆ μ' ∈ Set.range (fun m => (J m).map Prod.snd), μ' {x : ℝ | r < ‖x‖}) = 0 := by
      intro r hr
      refine le_antisymm (iSup₂_le ?_) (zero_le)
      rintro μ' ⟨m, rfl⟩
      simp only [hJ_snd m]
      rw [Measure.map_apply (hs_meas (ψ m))
        (measurableSet_lt measurable_const measurable_norm)]
      have h_empty : (s (ψ m)) ⁻¹' {x : ℝ | r < ‖x‖} = (∅ : Set (Ω (ψ m))) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        rcases hs01 (ψ m) ω with h | h <;> rw [h] <;> simp only [Real.norm_eq_abs] <;>
          [(rw [abs_zero]; linarith); (rw [abs_one]; exact hr)]
      rw [h_empty, measure_empty]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_const_nhds
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr using (h_zero r hr).le
  -- Joint tightness.
  have h_tight_J : IsTightMeasureSet (Set.range J) := by
    apply tight_prod_of_tight_marginals_local (Set.range J)
    · convert! h_tight_fst using 2
      ext ρ; constructor
      · rintro ⟨_, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
      · rintro ⟨m, rfl⟩; exact ⟨J m, ⟨m, rfl⟩, rfl⟩
    · convert! h_tight_snd using 2
      ext ρ; constructor
      · rintro ⟨_, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
      · rintro ⟨m, rfl⟩; exact ⟨J m, ⟨m, rfl⟩, rfl⟩
  -- ── Extract a further weakly-convergent subsequence of the joints. ──────────────────────
  obtain ⟨φ, hφ_mono, Jlim, hJlim_prob, hJlim_conv⟩ :=
    extract_weak_subseq_local J h_tight_J
  -- The composite subsequence index into the original `P, Q`.
  set χ : ℕ → ℕ := fun k => ψ (φ k) with hχ_def
  have hχ_mono : StrictMono χ := hψ_mono.comp hφ_mono
  -- ── First marginal weak-limit: feed `hV` to get its mean is 1. ──────────────────────────
  set V : Measure ℝ := Jlim.map Prod.fst with hV_def
  have hV_prob : IsProbabilityMeasure V := by
    rw [hV_def]; exact (by infer_instance)
  -- `(J (φ k)).map fst ⇝ V` (continuous mapping on the joint convergence).
  have hfst_conv : WeakConverges (fun k => (J (φ k)).map Prod.fst) V :=
    hJlim_conv.map continuous_fst measurable_fst
  -- Rewrite the first marginals as the `hV`-shaped sequence (law of `q (χ k)` under `P (χ k)`).
  have hfst_eq : (fun k => (J (φ k)).map Prod.fst)
      = fun k => (P (χ k)).map (fun ω => ((Q (χ k)).rnDeriv (P (χ k)) ω).toReal) := by
    funext k
    rw [hJ_fst (φ k)]
  rw [hfst_eq] at hfst_conv
  have hV_mean : ∫ x, x ∂V = 1 := hV (fun k => χ k) hχ_mono V hV_prob hfst_conv
  -- ── Second marginal weak-limit is `δ₁` (since `1_{Aᶜ} → 1` in `P`-probability). ─────────
  have hP_A_χ : Tendsto (fun k => (P (χ k)) (A (χ k))) atTop (𝓝 0) :=
    hPA.comp hχ_mono.tendsto_atTop
  have hsnd_dirac : WeakConverges (fun k => (P (χ k)).map (s (χ k))) (Measure.dirac 1) := by
    intro g
    -- `∫ g d((P).map s) = g 1 + (g 0 - g 1) · (P (A (χ k))).toReal`.
    have h_int_eq : ∀ k, ∫ x, g x ∂((P (χ k)).map (s (χ k)))
        = g 1 + (g 0 - g 1) * ((P (χ k)) (A (χ k))).toReal := by
      intro k
      rw [MeasureTheory.integral_map (hs_meas (χ k)).aemeasurable
        g.continuous.aestronglyMeasurable]
      -- `g (s ω) = g 1 + (g 0 - g 1) · 1_{A} ω`.
      have h_pt : (fun ω => g (s (χ k) ω))
          = fun ω => g 1 + (g 0 - g 1) * (A (χ k)).indicator (fun _ => (1 : ℝ)) ω := by
        funext ω
        by_cases hω : ω ∈ A (χ k)
        · have hs0 : s (χ k) ω = 0 := by
            have : ω ∉ (A (χ k))ᶜ := fun hc => hc hω
            simp only [hs_def, Set.indicator_of_notMem this]
          rw [hs0, Set.indicator_of_mem hω]
          change g 0 = g 1 + (g 0 - g 1) * 1
          ring
        · have hs1 : s (χ k) ω = 1 := by
            have : ω ∈ (A (χ k))ᶜ := hω
            simp only [hs_def, Set.indicator_of_mem this]
          rw [hs1, Set.indicator_of_notMem hω]
          change g 1 = g 1 + (g 0 - g 1) * 0
          ring
      rw [h_pt]
      rw [MeasureTheory.integral_add (integrable_const _)
        (((integrable_const (1 : ℝ)).indicator (hA_meas (χ k))).const_mul (g 0 - g 1))]
      rw [MeasureTheory.integral_const, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator (hA_meas (χ k))]
      simp only [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, measure_univ, ENNReal.toReal_one]
      ring
    -- `∫ g d(dirac 1) = g 1`.
    rw [show (∫ x, g x ∂(Measure.dirac (1 : ℝ))) = g 1 from by
      rw [MeasureTheory.integral_dirac]]
    simp_rw [h_int_eq]
    -- The added term tends to `0`.
    have h_tendsto0 : Tendsto (fun k => (g 0 - g 1) * ((P (χ k)) (A (χ k))).toReal)
        atTop (𝓝 0) := by
      have h_toReal : Tendsto (fun k => ((P (χ k)) (A (χ k))).toReal) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal (by simp)).comp hP_A_χ
        simpa using! this
      simpa using! h_toReal.const_mul (g 0 - g 1)
    simpa using (tendsto_const_nhds (x := g 1)).add h_tendsto0
  -- Identify `Jlim.map snd = δ₁`.
  have hJlim_snd_eq : Jlim.map Prod.snd = Measure.dirac (1 : ℝ) := by
    have hsnd_conv : WeakConverges (fun k => (J (φ k)).map Prod.snd) (Measure.dirac 1) := by
      have : (fun k => (J (φ k)).map Prod.snd)
          = fun k => (P (χ k)).map (s (χ k)) := by
        funext k; rw [hJ_snd (φ k)]
      rw [this]; exact hsnd_dirac
    exact WeakConverges.snd_eq hJlim_conv hsnd_conv
  -- ── Portmanteau lower bound on the nonnegative continuous `(v, t) ↦ max v 0 * max t 0`. ──
  -- Nonnegative continuous test function on `ℝ × ℝ` agreeing with `v · t` on the support.
  set F : ℝ × ℝ → ℝ := fun p => max p.1 0 * max p.2 0 with hF_def
  have hF_cont : Continuous F :=
    (continuous_fst.max continuous_const).mul (continuous_snd.max continuous_const)
  have hF_nonneg : 0 ≤ F := fun p => mul_nonneg (le_max_right _ _) (le_max_right _ _)
  -- On each joint law, `∫⁻ ofReal (F p) ∂(J m) = Q (ψ m) (A (ψ m))ᶜ`.
  have hF_on_J : ∀ m, ∫⁻ p, ENNReal.ofReal (F p) ∂(J m)
      = (Q (ψ m)) (A (ψ m))ᶜ := by
    intro m
    -- Pull back through the pushforward `pair m`.
    rw [hJ_def, lintegral_map (by
      exact (ENNReal.measurable_ofReal.comp (hF_cont.measurable))) (hpair_meas m)]
    -- `ofReal (F (pair m ω)) = 1_{Aᶜ} ω · rnDeriv ω` `P (ψ m)`-a.e. (rnDeriv finite a.e.).
    have h_int_eq : (fun ω => ENNReal.ofReal (F (pair m ω)))
        =ᵐ[P (ψ m)] fun ω => (A (ψ m))ᶜ.indicator
          (fun ω' => (Q (ψ m)).rnDeriv (P (ψ m)) ω') ω := by
      filter_upwards [Measure.rnDeriv_ne_top (Q (ψ m)) (P (ψ m))] with ω hω_fin
      simp only [hF_def, hpair_def]
      rw [max_eq_left (hq_nonneg (ψ m) ω), max_eq_left (hs_nonneg (ψ m) ω)]
      by_cases hω : ω ∈ (A (ψ m))ᶜ
      · have hs1 : s (ψ m) ω = 1 := by simp only [hs_def, Set.indicator_of_mem hω]
        rw [hs1, Set.indicator_of_mem hω]
        simp only [mul_one, hq_def]
        rw [ENNReal.ofReal_toReal hω_fin]
      · have hs0 : s (ψ m) ω = 0 := by simp only [hs_def, Set.indicator_of_notMem hω]
        rw [hs0, Set.indicator_of_notMem hω]
        simp only [mul_zero, ENNReal.ofReal_zero]
    rw [lintegral_congr_ae h_int_eq, lintegral_indicator (hA_meas (ψ m)).compl,
        ← hQ_change (ψ m) (hA_meas (ψ m)).compl]
  -- `V` is supported on `[0, ∞)` (weak limit of laws of nonnegative `q`).
  have hV_supp : V {x : ℝ | x < 0} = 0 := by
    have h_neg_open : IsOpen {x : ℝ | x < 0} := isOpen_lt continuous_id continuous_const
    -- Bundle the first-marginal laws as probability measures.
    have hfst_prob : ∀ k, IsProbabilityMeasure
        ((P (χ k)).map (fun ω => ((Q (χ k)).rnDeriv (P (χ k)) ω).toReal)) :=
      fun k => (by infer_instance)
    set PM : ℕ → ProbabilityMeasure ℝ := fun k =>
      ⟨(P (χ k)).map (fun ω => ((Q (χ k)).rnDeriv (P (χ k)) ω).toReal), hfst_prob k⟩ with hPM_def
    have h_tendsto_V : Tendsto PM atTop (𝓝 (⟨V, hV_prob⟩ : ProbabilityMeasure ℝ)) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hfst_conv
    have h_le := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      h_tendsto_V h_neg_open
    have h_each : ∀ k, ((PM k : Measure ℝ)) {x : ℝ | x < 0} = 0 := by
      intro k
      have hcoe : (PM k : Measure ℝ)
          = (P (χ k)).map (fun ω => ((Q (χ k)).rnDeriv (P (χ k)) ω).toReal) := rfl
      rw [hcoe, Measure.map_apply (hq_meas (χ k)) h_neg_open.measurableSet]
      convert! measure_empty (μ := P (χ k))
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hq_nonneg (χ k) ω
    simp only [h_each, Filter.liminf_const] at h_le
    exact le_antisymm h_le (zero_le)
  -- On the limit, `∫⁻ ofReal (F p) ∂Jlim = ∫ x ∂V = 1`.
  have hF_on_Jlim : ∫⁻ p, ENNReal.ofReal (F p) ∂Jlim = 1 := by
    -- `snd = 1` `Jlim`-a.e. (from `Jlim.map snd = dirac 1`).
    have h_snd_ae : ∀ᵐ p ∂Jlim, p.2 = 1 := by
      have h_map_ae : ∀ᵐ y ∂(Jlim.map Prod.snd), y = 1 := by
        rw [hJlim_snd_eq]
        rw [MeasureTheory.ae_dirac_iff
          (show MeasurableSet {y : ℝ | y = 1} from measurableSet_singleton (1 : ℝ))]
      exact (MeasureTheory.ae_map_iff measurable_snd.aemeasurable
        (p := fun y : ℝ => y = 1) (measurableSet_singleton (1 : ℝ))).mp h_map_ae
    -- Replace `F p` by `max p.1 0` `Jlim`-a.e.
    have h_ae_eq : (fun p : ℝ × ℝ => ENNReal.ofReal (F p))
        =ᵐ[Jlim] fun p => ENNReal.ofReal (max p.1 0) := by
      filter_upwards [h_snd_ae] with p hp
      simp only [hF_def, hp]; norm_num
    rw [MeasureTheory.lintegral_congr_ae h_ae_eq]
    -- Push to first marginal `V`.
    have h_map : ∫⁻ p, ENNReal.ofReal (max p.1 0) ∂Jlim
        = ∫⁻ x, ENNReal.ofReal (max x 0) ∂V := by
      rw [hV_def]
      exact (lintegral_map
        (ENNReal.measurable_ofReal.comp (continuous_id.max continuous_const).measurable)
        measurable_fst).symm
    rw [h_map]
    -- `ofReal (max x 0) = ofReal x` pointwise.
    have h_ofReal : (fun x : ℝ => ENNReal.ofReal (max x 0)) = fun x => ENNReal.ofReal x := by
      funext x; rcases le_total 0 x with hx | hx
      · rw [max_eq_left hx]
      · rw [max_eq_right hx, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hx]
    rw [h_ofReal]
    -- `(∫⁻ ofReal x dV).toReal = ∫ x dV = 1`, and `1 ≠ 0` forces the value to be `1`.
    have h_nonneg_ae : 0 ≤ᵐ[V] (fun x : ℝ => x) := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
      simp only [Pi.zero_apply, not_le]
      exact hV_supp
    have h_bridge := MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg_ae
      (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
    rw [hV_mean] at h_bridge
    -- `h_bridge : 1 = (∫⁻ x, ofReal x ∂V).toReal`.
    have h_ne_top : (∫⁻ x, ENNReal.ofReal x ∂V) ≠ ⊤ := by
      intro h_top; rw [h_top, ENNReal.toReal_top] at h_bridge; exact one_ne_zero h_bridge
    rw [← ENNReal.ofReal_toReal h_ne_top, ← h_bridge, ENNReal.ofReal_one]
  -- Portmanteau (open-set liminf) for the joint convergence `J (φ k) ⇝ Jlim`.
  set PMJ : ℕ → ProbabilityMeasure (ℝ × ℝ) :=
    fun k => ⟨J (φ k), hJ_prob (φ k)⟩ with hPMJ_def
  set PMlim : ProbabilityMeasure (ℝ × ℝ) := ⟨Jlim, hJlim_prob⟩ with hPMlim_def
  have hPMJ_tendsto : Tendsto PMJ atTop (𝓝 PMlim) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hJlim_conv
  have h_open_liminf : ∀ G : Set (ℝ × ℝ), IsOpen G →
      Jlim G ≤ Filter.liminf (fun k => (J (φ k)) G) atTop := fun G hG =>
    MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto hPMJ_tendsto hG
  -- Apply the nonneg-continuous portmanteau liminf integral bound.
  have h_liminf_int :
      ∫⁻ p, ENNReal.ofReal (F p) ∂Jlim
        ≤ Filter.liminf (fun k => ∫⁻ p, ENNReal.ofReal (F p) ∂(J (φ k))) atTop :=
    MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      hF_cont hF_nonneg h_open_liminf
  -- Rewrite both sides: LHS = 1, RHS-integrands = `Q (χ k) (A (χ k))ᶜ`.
  rw [hF_on_Jlim] at h_liminf_int
  have h_rhs_eq : (fun k => ∫⁻ p, ENNReal.ofReal (F p) ∂(J (φ k)))
      = fun k => (Q (χ k)) (A (χ k))ᶜ := by
    funext k; rw [hF_on_J (φ k)]
  rw [h_rhs_eq] at h_liminf_int
  -- `Q (χ k) (A (χ k))ᶜ = 1 - Q (χ k) (A (χ k)) ≤ 1 - δ`
  -- eventually (since `δ ≤ Q (χ k) (A (χ k))`).
  have hχ_ge : ∀ k, δ ≤ (Q (χ k)) (A (χ k)) := fun k => hψ_ge (φ k)
  have hcompl_le : ∀ k, (Q (χ k)) (A (χ k))ᶜ ≤ 1 - δ := by
    intro k
    have h_eq : (Q (χ k)) (A (χ k))ᶜ = 1 - (Q (χ k)) (A (χ k)) := by
      rw [measure_compl (hA_meas (χ k)) (measure_ne_top _ _), measure_univ]
    rw [h_eq]; exact tsub_le_tsub_left (hχ_ge k) 1
  -- Hence `liminf ≤ 1 - δ`, contradicting `1 ≤ liminf`.
  have h_liminf_le : Filter.liminf (fun k => (Q (χ k)) (A (χ k))ᶜ) atTop ≤ 1 - δ := by
    calc Filter.liminf (fun k => (Q (χ k)) (A (χ k))ᶜ) atTop
        ≤ Filter.liminf (fun _ : ℕ => (1 : ℝ≥0∞) - δ) atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hcompl_le)
      _ = 1 - δ := Filter.liminf_const _
  have h_one_le : (1 : ℝ≥0∞) ≤ 1 - δ := le_trans h_liminf_int h_liminf_le
  -- `1 ≤ 1 - δ` with `δ > 0` is a contradiction.
  have hδ_le_one : δ ≤ 1 := le_trans (hχ_ge 0) prob_le_one
  have hδ_ne_top : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hδ_le_one
  rw [ENNReal.le_sub_iff_add_le_left hδ_ne_top hδ_le_one] at h_one_le
  -- `δ + 1 ≤ 1` contradicts `1 < δ + 1` (since `δ > 0`).
  have h_lt : (1 : ℝ≥0∞) < δ + 1 := by
    rw [add_comm]; exact ENNReal.lt_add_right ENNReal.one_ne_top hδ_pos.ne'
  exact absurd h_one_le (not_le.mpr h_lt)

/-- **Mixture-dominating-measure densities** (foundation for vdV Lemma 6.4, (ii) ⟹ (iii)).

For probability measures `P Q` on `α`, the half-sum `μ = ½P + ½Q` dominates both, and the
real densities `W := (dP/dμ).toReal`, `2 - W = (dQ/dμ).toReal` take values in `[0, 2]`.
This packages the four facts needed by the book proof: absolute continuity of `P` and `Q`
to `μ`, the bound `W ∈ [0, 2]` (`μ`-a.e.), and the complementary identity
`(dQ/dμ).toReal = 2 - (dP/dμ).toReal` (`μ`-a.e.).

The key brick is `Measure.rnDeriv_self` for `μ = ½P + ½Q`: `dμ/dμ = 1` `μ`-a.e., and the
linearity `d(½P+½Q)/dμ = ½ dP/dμ + ½ dQ/dμ`, giving `dP/dμ + dQ/dμ = 2`. -/
private lemma mixture_rnDeriv_facts {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    letI μ := ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • P + ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • Q
    (P.AbsolutelyContinuous μ) ∧ (Q.AbsolutelyContinuous μ) ∧
      IsProbabilityMeasure μ ∧
      (∀ᵐ x ∂μ, (Q.rnDeriv μ x).toReal = 2 - (P.rnDeriv μ x).toReal) ∧
      (∀ᵐ x ∂μ, (P.rnDeriv μ x).toReal ≤ 2) := by
  set c : ℝ≥0∞ := ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) with hc_def
  have hc_ne : c ≠ 0 := by simp [hc_def]
  have hc_ne_top : c ≠ ∞ := by simp [hc_def]
  have hc_eq : c = (2 : ℝ≥0∞)⁻¹ := by simp [hc_def]
  set μ : Measure α := c • P + c • Q with hμ_def
  have hPμ : P.AbsolutelyContinuous μ :=
    (Measure.absolutelyContinuous_smul hc_ne).add_right _
  have hQμ : Q.AbsolutelyContinuous μ :=
    (Measure.absolutelyContinuous_smul hc_ne).add_right' _
  -- `μ` is a probability measure: `μ univ = c·1 + c·1 = 2c = 1`.
  have hμ_prob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_def]
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    rw [hc_eq, ← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hcP_fin : IsFiniteMeasure (c • P) := by
    constructor; rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]; exact hc_ne_top.lt_top
  have hcQ_fin : IsFiniteMeasure (c • Q) := by
    constructor; rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]; exact hc_ne_top.lt_top
  -- Linearity of the RN derivative: `dμ/dμ = c·dP/dμ + c·dQ/dμ`, and `dμ/dμ = 1` μ-a.e.
  have h_lin : μ.rnDeriv μ =ᵐ[μ] fun x => c * P.rnDeriv μ x + c * Q.rnDeriv μ x := by
    have h1 : (c • P).rnDeriv μ =ᵐ[μ] c • P.rnDeriv μ :=
      Measure.rnDeriv_smul_left_of_ne_top' P μ hc_ne_top
    have h2 : (c • Q).rnDeriv μ =ᵐ[μ] c • Q.rnDeriv μ :=
      Measure.rnDeriv_smul_left_of_ne_top' Q μ hc_ne_top
    have h_add : (c • P + c • Q).rnDeriv μ =ᵐ[μ] (c • P).rnDeriv μ + (c • Q).rnDeriv μ :=
      Measure.rnDeriv_add' (c • P) (c • Q) μ
    filter_upwards [h_add, h1, h2] with x hx hx1 hx2
    rw [hμ_def] at hx ⊢
    rw [hx, Pi.add_apply, hx1, hx2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  have h_self : μ.rnDeriv μ =ᵐ[μ] 1 := μ.rnDeriv_self
  -- Hence `c·(dP/dμ + dQ/dμ) = 1`, i.e. `dP/dμ + dQ/dμ = 2` μ-a.e.
  have h_sum : ∀ᵐ x ∂μ, P.rnDeriv μ x + Q.rnDeriv μ x = 2 := by
    filter_upwards [h_lin, h_self, P.rnDeriv_lt_top μ, Q.rnDeriv_lt_top μ]
      with x hx hx_self hP_top hQ_top
    rw [hx] at hx_self
    simp only [Pi.one_apply] at hx_self
    -- `c·a + c·b = 1` with `c = 2⁻¹`, so `a + b = 2`.
    have hmul : c * (P.rnDeriv μ x + Q.rnDeriv μ x) = 1 := by
      rw [mul_add]; exact hx_self
    have hsum_eq : P.rnDeriv μ x + Q.rnDeriv μ x = c⁻¹ * 1 := by
      rw [← hmul, ← mul_assoc, ENNReal.inv_mul_cancel hc_ne hc_ne_top, one_mul]
    rw [hsum_eq, mul_one, hc_eq, inv_inv]
  refine ⟨hPμ, hQμ, hμ_prob, ?_, ?_⟩
  · -- `(dQ/dμ).toReal = 2 - (dP/dμ).toReal`.
    filter_upwards [h_sum, P.rnDeriv_lt_top μ, Q.rnDeriv_lt_top μ]
      with x hx hP_top hQ_top
    have hQ_eq : Q.rnDeriv μ x = 2 - P.rnDeriv μ x := by
      rw [← hx, ENNReal.add_sub_cancel_left hP_top.ne]
    rw [hQ_eq, ENNReal.toReal_sub_of_le (by rw [← hx]; exact le_add_right le_rfl) (by simp)]
    norm_num
  · -- `(dP/dμ).toReal ≤ 2`.
    filter_upwards [h_sum, P.rnDeriv_lt_top μ] with x hx hP_top
    have hle : P.rnDeriv μ x ≤ 2 := by rw [← hx]; exact le_add_right le_rfl
    calc (P.rnDeriv μ x).toReal ≤ ((2 : ℝ≥0∞)).toReal :=
          ENNReal.toReal_mono (by simp) hle
      _ = 2 := by simp

/-- **Change-of-variable bridge** (foundation for vdV Lemma 6.4, (ii) ⟹ (iii)).

For probability measures `R S` on `α`, set `μ = ½R + ½S` and `W ω = (R.rnDeriv μ ω).toReal`,
the `μ`-density of `R` (taking values in `[0, 2]`, with `(S.rnDeriv μ).toReal = 2 - W`).
Along `R`, the likelihood ratio is `(S.rnDeriv R).toReal = (2 - W)/W`; hence for a bounded
continuous `g`,
`∫ g((S.rnDeriv R ω).toReal) ∂R = ∫ w, (w * g ((2 - w)/w)) ∂(μ.map W)`,
the integrand on the right understood as `0` at `w = 0` (which it is, since the factor `w`
vanishes there). This is the engine for both the `V`-side (`R = P, S = Q`) and the
`U`-side (`R = Q, S = P`) change-of-variables in the book proof.

The function `g` is bounded and continuous, as expressed by the bounded-continuous bundle. -/
private lemma cov_ratio_integral {α : Type*} [MeasurableSpace α]
    (R S : Measure α) [IsProbabilityMeasure R] [IsProbabilityMeasure S]
    (g : ℝ →ᵇ ℝ) :
    letI μ := ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • R + ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • S
    ∫ ω, g ((S.rnDeriv R ω).toReal) ∂R
      = ∫ w, (w * g ((2 - w) / w))
          ∂(μ.map (fun ω => (R.rnDeriv μ ω).toReal)) := by
  classical
  set c : ℝ≥0∞ := ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) with hc_def
  set μ : Measure α := c • R + c • S with hμ_def
  -- The packaged mixture facts (apply with `P := R, Q := S`).
  obtain ⟨hRμ, hSμ, hμ_prob, h2W, _hW2⟩ := mixture_rnDeriv_facts R S
  -- `W` is the real `μ`-density of `R`; it is measurable.
  set W : α → ℝ := fun ω => (R.rnDeriv μ ω).toReal with hW_def
  have hW_meas : Measurable W := (R.measurable_rnDeriv μ).ennreal_toReal
  -- The function `Ψ w = w * g ((2 - w)/w)`.
  set Ψ : ℝ → ℝ := fun w => w * g ((2 - w) / w) with hΨ_def
  have hratio_meas : Measurable fun w : ℝ => (2 - w) / w :=
    (measurable_const.sub measurable_id).div measurable_id
  have hΨ_meas : Measurable Ψ :=
    measurable_id.mul (g.continuous.measurable.comp hratio_meas)
  -- ── RHS: push the law `μ.map W` back to `μ`. ──
  have hRHS : ∫ w, Ψ w ∂(μ.map W) = ∫ ω, Ψ (W ω) ∂μ := by
    rw [MeasureTheory.integral_map hW_meas.aemeasurable hΨ_meas.aestronglyMeasurable]
  -- ── LHS: change of measure `∫ · ∂R = ∫ W · · ∂μ`. ──
  have hLHS : ∫ ω, g ((S.rnDeriv R ω).toReal) ∂R
      = ∫ ω, W ω * g ((S.rnDeriv R ω).toReal) ∂μ := by
    rw [← integral_toReal_rnDeriv_mul hRμ (f := fun ω => g ((S.rnDeriv R ω).toReal))]
  -- ── R-a.e. chain rule: `(dS/dR).toReal = (2 - W)/W`. ──
  -- `W > 0` `R`-a.e. and the ennreal chain rule `(dS/dR)·(dR/dμ) = dS/dμ` `R`-a.e.
  have hW_pos_R : ∀ᵐ ω ∂R, 0 < W ω := by
    filter_upwards [Measure.rnDeriv_pos hRμ, hRμ.ae_le (R.rnDeriv_lt_top μ)]
      with ω hpos hlt
    simpa [hW_def] using! ENNReal.toReal_pos hpos.ne' hlt.ne
  have h2W_R : ∀ᵐ ω ∂R, (S.rnDeriv μ ω).toReal = 2 - W ω := hRμ.ae_le h2W
  have h_chain_ennR : S.rnDeriv R * R.rnDeriv μ =ᵐ[R] S.rnDeriv μ :=
    Measure.rnDeriv_mul_rnDeriv' hRμ
  have h_ratio_R : ∀ᵐ ω ∂R, (S.rnDeriv R ω).toReal = (2 - W ω) / W ω := by
    filter_upwards [hW_pos_R, h2W_R, h_chain_ennR, S.rnDeriv_lt_top R,
      hRμ.ae_le (R.rnDeriv_lt_top μ)] with ω hWpos h2 hchain hSR_lt hR_lt
    -- toReal of the ennreal chain rule: `(dS/dR).toReal * W ω = (dS/dμ).toReal = 2 - W ω`.
    have hmul : (S.rnDeriv R ω).toReal * W ω = 2 - W ω := by
      have hc := congrArg ENNReal.toReal hchain
      simp only [Pi.mul_apply, ENNReal.toReal_mul] at hc
      change (S.rnDeriv R ω).toReal * (R.rnDeriv μ ω).toReal = 2 - W ω
      rw [hc, h2]
    -- divide by `W ω > 0`.
    rw [eq_div_iff hWpos.ne', hmul]
  -- Transfer to `μ`-a.e. on `{W ≠ 0}`.
  have h_ratio_μ : ∀ᵐ ω ∂μ, R.rnDeriv μ ω ≠ 0 →
      (S.rnDeriv R ω).toReal = (2 - W ω) / W ω :=
    Measure.ae_rnDeriv_ne_zero_imp_of_ae (μ := R) (ν := μ) h_ratio_R
  -- ── Integrands agree `μ`-a.e. ──
  have h_integrand : (fun ω => W ω * g ((S.rnDeriv R ω).toReal)) =ᵐ[μ] fun ω => Ψ (W ω) := by
    filter_upwards [h_ratio_μ] with ω hω
    by_cases hW0 : W ω = 0
    · simp [hΨ_def, hW0]
    · have hne : R.rnDeriv μ ω ≠ 0 := by
        intro h; apply hW0; simp [hW_def, h]
      rw [hΨ_def]
      simp only []
      rw [hω hne]
  calc ∫ ω, g ((S.rnDeriv R ω).toReal) ∂R
      = ∫ ω, W ω * g ((S.rnDeriv R ω).toReal) ∂μ := hLHS
    _ = ∫ ω, Ψ (W ω) ∂μ := integral_congr_ae h_integrand
    _ = ∫ w, Ψ w ∂(μ.map W) := hRHS.symm

/-- **(ii) ⟹ (iii)** (vdV Lemma 6.4, (ii) ⟹ (iii)).

If every subsequential weak limit `U` of `dPₙ/dQₙ` (under `Qₙ`) gives mass `0` to `0`,
then every subsequential weak limit `V` of `dQₙ/dPₙ` (under `Pₙ`) has mean `1`.

Book proof: dominate `Pₙ, Qₙ` by `μₙ = ½(Pₙ + Qₙ)`; the density `Wₙ = (dPₙ/dμₙ).toReal`
takes values in `[0, 2]`, with `(dQₙ/dμₙ).toReal = 2 − Wₙ`. Along the given subsequence
`φ`, extract (Prohorov, twice) a sub-subsequence `χ = φ ∘ ρ` along which the law of
`dPₙ/dQₙ` under `Qₙ` weakly converges to some `U` (Markov-tight) **and** the law `LWₙ` of
`Wₙ` under `μₙ` weakly converges to `LW` (compact-support tight). The change-of-variables
bridge `cov_ratio_integral` (with `g(w) = w·f((2−w)/w)`) turns `dPₙ/dQₙ`- and
`dQₙ/dPₙ`-integrals into `LWₙ`-integrals of explicit bounded continuous test functions:
- `EV = ∫ (2−w) dLW = 2 − ∫ w dLW = 1` (Fact C: `∫ w dLW = 1` from `EWₙ = 1`), using
- `LW{0} = 0` (Fact B: `U{0} = 2·LW{0}` and `U{0} = 0` from (ii)).
The monotone/antitone Bochner convergence theorems supply the truncation limits. -/
theorem limit_pos_imp_mean_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hU : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (U : Measure ℝ), IsProbabilityMeasure U →
      WeakConverges
        (fun k => (Q (φ k)).map (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal)) U →
      U {x : ℝ | 0 < x} = 1)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (V : Measure ℝ) [IsProbabilityMeasure V]
    (hVconv : WeakConverges
      (fun k => (P (φ k)).map (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal)) V) :
    ∫ x, x ∂V = 1 := by
  classical
  -- ══ Setup along the given subsequence `φ`. ══
  -- Mixture `μ k = ½ P(φk) + ½ Q(φk)`, real density `W k = (dP(φk)/dμk).toReal ∈ [0,2]`.
  set μ : ∀ k, Measure (Ω (φ k)) := fun k =>
    ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • P (φ k) + ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • Q (φ k) with hμ_def
  set W : ∀ k, Ω (φ k) → ℝ := fun k ω => ((P (φ k)).rnDeriv (μ k) ω).toReal with hW_def
  have hW_meas : ∀ k, Measurable (W k) := fun k =>
    ((P (φ k)).measurable_rnDeriv (μ k)).ennreal_toReal
  -- Mixture facts for each `k`.
  have hmix : ∀ k, (P (φ k)).AbsolutelyContinuous (μ k) ∧
      (Q (φ k)).AbsolutelyContinuous (μ k) ∧ IsProbabilityMeasure (μ k) ∧
      (∀ᵐ x ∂(μ k), ((Q (φ k)).rnDeriv (μ k) x).toReal = 2 - W k x) ∧
      (∀ᵐ x ∂(μ k), W k x ≤ 2) := fun k => mixture_rnDeriv_facts (P (φ k)) (Q (φ k))
  have hμ_prob : ∀ k, IsProbabilityMeasure (μ k) := fun k => (hmix k).2.2.1
  have hPμ : ∀ k, (P (φ k)).AbsolutelyContinuous (μ k) := fun k => (hmix k).1
  have hQμ : ∀ k, (Q (φ k)).AbsolutelyContinuous (μ k) := fun k => (hmix k).2.1
  have hW_le2 : ∀ k, ∀ᵐ x ∂(μ k), W k x ≤ 2 := fun k => (hmix k).2.2.2.2
  have hW_nonneg : ∀ k ω, 0 ≤ W k ω := fun k ω => ENNReal.toReal_nonneg
  -- Law of `W k` under `μ k`, a probability measure on `ℝ` supported in `[0,2]`.
  set LW : ℕ → Measure ℝ := fun k => (μ k).map (W k) with hLW_def
  have hLW_prob : ∀ k, IsProbabilityMeasure (LW k) := fun k => by
    have := hμ_prob k
    exact (by infer_instance)
  -- `LW k` is supported in `[0,2]`.
  have hLW_supp : ∀ k, (LW k) {x : ℝ | x < 0 ∨ 2 < x} = 0 := by
    intro k
    have hSmeas : MeasurableSet {x : ℝ | x < 0 ∨ 2 < x} :=
      (measurableSet_lt measurable_id measurable_const).union
        (measurableSet_lt measurable_const measurable_id)
    rw [hLW_def, Measure.map_apply (hW_meas k) hSmeas]
    have : (∀ᵐ ω ∂(μ k), ω ∉ W k ⁻¹' {x : ℝ | x < 0 ∨ 2 < x}) := by
      filter_upwards [hW_le2 k] with ω hω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_lt]
      exact ⟨hW_nonneg k ω, hω⟩
    rw [ae_iff] at this
    simpa only [not_not] using! this
  -- ══ Extraction 1: weak limit `U` of `dP/dQ`-laws under `Q` (Markov-tight). ══
  set LdPdQ : ℕ → Measure ℝ :=
    fun k => (Q (φ k)).map (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal) with hLdPdQ_def
  have hdPdQ_meas : ∀ k, Measurable (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal) :=
    fun k => ((P (φ k)).measurable_rnDeriv (Q (φ k))).ennreal_toReal
  have hLdPdQ_prob : ∀ k, IsProbabilityMeasure (LdPdQ k) := fun k =>
    (by infer_instance)
  -- `∫⁻ dP/dQ dQ ≤ 1` (it is `P_a(univ) ≤ 1`).
  have hdPdQ_total : ∀ k, ∫⁻ ω, (P (φ k)).rnDeriv (Q (φ k)) ω ∂(Q (φ k)) ≤ 1 := by
    intro k
    calc ∫⁻ ω, (P (φ k)).rnDeriv (Q (φ k)) ω ∂(Q (φ k))
        ≤ (P (φ k)) Set.univ := Measure.lintegral_rnDeriv_le
      _ = 1 := by simp
  have h_tight_LdPdQ : IsTightMeasureSet (Set.range LdPdQ) := by
    refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
    have h_bound : ∀ r : ℝ, 0 < r →
        (⨆ μ' ∈ Set.range LdPdQ, μ' {x : ℝ | r < ‖x‖}) ≤ (ENNReal.ofReal r)⁻¹ := by
      intro r hr
      refine iSup₂_le ?_
      rintro μ' ⟨k, rfl⟩
      rw [hLdPdQ_def, Measure.map_apply (hdPdQ_meas k)
        (measurableSet_lt measurable_const measurable_norm)]
      have h_sub : (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal) ⁻¹' {x : ℝ | r < ‖x‖}
          ⊆ {ω | ENNReal.ofReal r ≤ (P (φ k)).rnDeriv (Q (φ k)) ω} := by
        intro ω hω
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg] at hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        have h_ne_top : (P (φ k)).rnDeriv (Q (φ k)) ω ≠ ∞ := by
          intro h_top; rw [h_top, ENNReal.toReal_top] at hω; linarith
        rw [← ENNReal.ofReal_toReal h_ne_top]
        exact ENNReal.ofReal_le_ofReal hω.le
      calc (Q (φ k)) ((fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal) ⁻¹' {x : ℝ | r < ‖x‖})
          ≤ (Q (φ k)) {ω | ENNReal.ofReal r ≤ (P (φ k)).rnDeriv (Q (φ k)) ω} :=
            measure_mono h_sub
        _ ≤ (∫⁻ ω, (P (φ k)).rnDeriv (Q (φ k)) ω ∂(Q (φ k))) / ENNReal.ofReal r :=
            meas_ge_le_lintegral_div ((P (φ k)).measurable_rnDeriv (Q (φ k))).aemeasurable
              (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
        _ ≤ (1 : ℝ≥0∞) / ENNReal.ofReal r :=
            ENNReal.div_le_div_right (hdPdQ_total k) _
        _ = (ENNReal.ofReal r)⁻¹ := by rw [one_div]
    have h_lim : Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹) atTop (𝓝 0) := by
      have h := tendsto_inv_iff.2 ENNReal.tendsto_ofReal_atTop
      rw [ENNReal.inv_top] at h
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr using h_bound r hr
  obtain ⟨σ₁, hσ₁_mono, U, hU_prob, hU_conv⟩ := extract_weak_subseq_local LdPdQ h_tight_LdPdQ
  -- ══ Extraction 2: weak limit `LW_lim` of the bounded `LW ∘ σ₁` (compact support tight). ══
  have hLWσ₁_prob : ∀ k, IsProbabilityMeasure ((LW ∘ σ₁) k) := fun k => hLW_prob (σ₁ k)
  have h_tight_LW : IsTightMeasureSet (Set.range (LW ∘ σ₁)) := by
    refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
    -- For `r ≥ 2`, `{|x| > r}` has zero `LW`-mass (support ⊆ [0,2]).
    have h_zero : ∀ r : ℝ, 2 ≤ r →
        (⨆ μ' ∈ Set.range (LW ∘ σ₁), μ' {x : ℝ | r < ‖x‖}) = 0 := by
      intro r hr
      refine le_antisymm (iSup₂_le ?_) (zero_le)
      rintro μ' ⟨k, rfl⟩
      refine le_of_eq ?_
      refine measure_mono_null ?_ (hLW_supp (σ₁ k))
      intro x hx
      simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hx ⊢
      rcases lt_or_ge x 0 with hx0 | hx0
      · left; rw [abs_of_neg hx0] at hx; linarith
      · right; rw [abs_of_nonneg hx0] at hx; linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_const_nhds
      (Filter.Eventually.of_forall (fun _ => zero_le)) ?_
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr using (h_zero r hr).le
  obtain ⟨σ₂, hσ₂_mono, LW_lim, hLW_lim_prob, hLW_lim_conv⟩ :=
    extract_weak_subseq_local (LW ∘ σ₁) h_tight_LW
  -- ══ Combined subsequence. ══
  set ρ : ℕ → ℕ := σ₁ ∘ σ₂ with hρ_def
  have hρ_mono : StrictMono ρ := hσ₁_mono.comp hσ₂_mono
  set χ : ℕ → ℕ := φ ∘ ρ with hχ_def
  have hχ_mono : StrictMono χ := hφ.comp hρ_mono
  -- `LW (ρ ·) ⇝ LW_lim`.
  have hLW_conv : WeakConverges (fun j => LW (ρ j)) LW_lim := by
    intro f
    have := hLW_lim_conv f
    simpa only [Function.comp_apply, hρ_def] using this
  -- `LdPdQ (ρ ·) ⇝ U` (subsequence of the `σ₁`-convergence).
  have hU_conv' : WeakConverges (fun j => LdPdQ (ρ j)) U := by
    intro f
    have := (hU_conv f).comp hσ₂_mono.tendsto_atTop
    simpa only [Function.comp_apply, hρ_def] using! this
  -- `hU` applies along `χ = φ ∘ ρ`: `U {0 < x} = 1`.
  have hU_pos : U {x : ℝ | 0 < x} = 1 := by
    refine hU χ hχ_mono U hU_prob ?_
    intro f
    have := hU_conv' f
    simpa only [hLdPdQ_def, hχ_def, Function.comp_apply] using! this
  -- `V`-law convergence along `ρ` (subsequence of the given `hVconv`).
  set LdQdP : ℕ → Measure ℝ :=
    fun k => (P (φ k)).map (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal) with hLdQdP_def
  have hdQdP_meas : ∀ k, Measurable (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal) :=
    fun k => ((Q (φ k)).measurable_rnDeriv (P (φ k))).ennreal_toReal
  have hLdQdP_prob : ∀ k, IsProbabilityMeasure (LdQdP k) := fun k =>
    (by infer_instance)
  have hV_conv : WeakConverges (fun j => LdQdP (ρ j)) V := by
    intro f; exact (hVconv f).comp hρ_mono.tendsto_atTop
  -- ── `LW_lim` is supported in `[0,2]`; `V` is supported in `[0,∞)`. ──
  have hLW_lim_supp : LW_lim {x : ℝ | x < 0 ∨ 2 < x} = 0 := by
    have hSopen : IsOpen {x : ℝ | x < 0 ∨ 2 < x} :=
      (isOpen_lt continuous_id continuous_const).union (isOpen_lt continuous_const continuous_id)
    set PMW : ℕ → ProbabilityMeasure ℝ := fun j => ⟨LW (ρ j), hLW_prob (ρ j)⟩ with hPMW_def
    have h_tend : Tendsto PMW atTop (𝓝 (⟨LW_lim, hLW_lim_prob⟩ : ProbabilityMeasure ℝ)) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hLW_conv
    have h_le := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto h_tend hSopen
    have h_each : ∀ j, ((PMW j : Measure ℝ)) {x : ℝ | x < 0 ∨ 2 < x} = 0 := fun j => hLW_supp (ρ j)
    simp only [h_each, Filter.liminf_const] at h_le
    exact le_antisymm h_le (zero_le)
  have hV_supp : V {x : ℝ | x < 0} = 0 := by
    have h_neg_open : IsOpen {x : ℝ | x < 0} := isOpen_lt continuous_id continuous_const
    set PMV : ℕ → ProbabilityMeasure ℝ := fun j => ⟨LdQdP (ρ j), hLdQdP_prob (ρ j)⟩ with hPMV_def
    have h_tend : Tendsto PMV atTop (𝓝 (⟨V, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hV_conv
    have h_le := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      h_tend h_neg_open
    have h_each : ∀ j, ((PMV j : Measure ℝ)) {x : ℝ | x < 0} = 0 := by
      intro j
      change (LdQdP (ρ j)) {x : ℝ | x < 0} = 0
      rw [hLdQdP_def, Measure.map_apply (hdQdP_meas (ρ j)) h_neg_open.measurableSet]
      have : (fun ω => ((Q (φ (ρ j))).rnDeriv (P (φ (ρ j))) ω).toReal) ⁻¹' {x : ℝ | x < 0}
          = (∅ : Set (Ω (φ (ρ j)))) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact ENNReal.toReal_nonneg
      rw [this, measure_empty]
    simp only [h_each, Filter.liminf_const] at h_le
    exact le_antisymm h_le (zero_le)
  -- ── Bounded-continuous clamp `cl w = min (max w 0) 2 ∈ [0,2]`, equal to `id` on `[0,2]`. ──
  set clampBdd : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun w => min (max w 0) 2)
    ((continuous_id.max continuous_const).min continuous_const) 2
    (fun w => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have : (0 : ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
        linarith
      · exact min_le_right _ _) with hclamp_def
  have hclamp_apply : ∀ w, clampBdd w = min (max w 0) 2 := fun _ => rfl
  -- On `[0,2]`, `clampBdd = id`.
  have hclamp_id : ∀ w : ℝ, 0 ≤ w → w ≤ 2 → clampBdd w = w := by
    intro w hw0 hw2
    rw [hclamp_apply, max_eq_left hw0, min_eq_left hw2]
  -- ── Fact C: `∫ w ∂LW_lim = 1`. ──
  have hFactC : ∫ w, w ∂LW_lim = 1 := by
    -- Replace `id` by `clampBdd` under `LW_lim` (supported in `[0,2]`).
    have hC_lim : ∫ w, w ∂LW_lim = ∫ w, clampBdd w ∂LW_lim := by
      refine integral_congr_ae ?_
      have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
        rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
      filter_upwards [h_compl] with w hw
      simp only [not_or, not_lt] at hw
      exact (hclamp_id w hw.1 hw.2).symm
    -- Each `∫ clampBdd ∂LW (ρ j) = 1` exactly.
    have hC_each : ∀ j, ∫ w, clampBdd w ∂(LW (ρ j)) = 1 := by
      intro j
      have := hμ_prob (ρ j)
      -- Push to `μ (ρ j)` via `integral_map`, then `clampBdd (W) = W` `μ`-a.e.
      rw [hLW_def, MeasureTheory.integral_map (hW_meas (ρ j)).aemeasurable
        clampBdd.continuous.aestronglyMeasurable]
      have h_clW : (fun ω => clampBdd (W (ρ j) ω)) =ᵐ[μ (ρ j)] fun ω => W (ρ j) ω := by
        filter_upwards [hW_le2 (ρ j)] with ω hω
        exact hclamp_id (W (ρ j) ω) (hW_nonneg (ρ j) ω) hω
      rw [integral_congr_ae h_clW]
      -- `∫ W ∂μ = ∫ (dP/dμ).toReal ∂μ = P(univ) = 1`.
      have : ∫ ω, W (ρ j) ω ∂(μ (ρ j)) = ∫ ω, (1 : ℝ) ∂(P (φ (ρ j))) := by
        rw [hW_def]
        rw [← integral_toReal_rnDeriv_mul (hPμ (ρ j)) (f := fun _ => (1 : ℝ))]
        simp
      rw [this]
      simp
    -- `∫ clampBdd ∂LW (ρ j) → ∫ clampBdd ∂LW_lim` by weak convergence; the LHS is constant 1.
    have h_tendsto : Tendsto (fun j => ∫ w, clampBdd w ∂(LW (ρ j))) atTop
        (𝓝 (∫ w, clampBdd w ∂LW_lim)) := hLW_conv clampBdd
    rw [hC_lim]
    have h_const : Tendsto (fun j => ∫ w, clampBdd w ∂(LW (ρ j))) atTop (𝓝 (1 : ℝ)) := by
      simp only [hC_each]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h_tendsto h_const
  -- ── Portmanteau transfer helpers: equal `j`-integrals ⟹ equal limit integrals. ──
  -- `U`-side: `dP/dQ`-law `⇝ U`, so equality with `LW`-integrals lifts to the limits.
  have transfer_U : ∀ (b cc : ℝ →ᵇ ℝ),
      (∀ j, ∫ x, b x ∂(LdPdQ (ρ j)) = ∫ x, cc x ∂(LW (ρ j))) →
      ∫ x, b x ∂U = ∫ x, cc x ∂LW_lim := by
    intro b cc hbc
    have hb := hU_conv' b
    have hc := hLW_conv cc
    have : (fun j => ∫ x, b x ∂(LdPdQ (ρ j))) = fun j => ∫ x, cc x ∂(LW (ρ j)) := funext hbc
    rw [this] at hb
    exact tendsto_nhds_unique hb hc
  -- `V`-side: `dQ/dP`-law `⇝ V`.
  have transfer_V : ∀ (b cc : ℝ →ᵇ ℝ),
      (∀ j, ∫ x, b x ∂(LdQdP (ρ j)) = ∫ x, cc x ∂(LW (ρ j))) →
      ∫ x, b x ∂V = ∫ x, cc x ∂LW_lim := by
    intro b cc hbc
    have hb := hV_conv b
    have hc := hLW_conv cc
    have : (fun j => ∫ x, b x ∂(LdQdP (ρ j))) = fun j => ∫ x, cc x ∂(LW (ρ j)) := funext hbc
    rw [this] at hb
    exact tendsto_nhds_unique hb hc
  -- ── Per-`j` change-of-variable identity, `V`-side (`R = P, S = Q`). ──
  -- `∫ g ∂LdQdP(ρj) = ∫ cc ∂LW(ρj)` when `cc` agrees with `w ↦ w·g((2-w)/w)` on `[0,2]`.
  have vIdent : ∀ (g cc : ℝ →ᵇ ℝ),
      (∀ w, 0 ≤ w → w ≤ 2 → w * g ((2 - w) / w) = cc w) →
      ∀ j, ∫ x, g x ∂(LdQdP (ρ j)) = ∫ x, cc x ∂(LW (ρ j)) := by
    intro g cc hagree j
    -- LHS = `∫ g((dQ/dP).toReal) ∂P(φ(ρj))`.
    rw [hLdQdP_def, MeasureTheory.integral_map (hdQdP_meas (ρ j)).aemeasurable
      g.continuous.aestronglyMeasurable]
    -- bridge: `= ∫ w·g((2-w)/w) ∂(μ(ρj).map W(ρj)) = ∫ w·g((2-w)/w) ∂LW(ρj)`.
    rw [cov_ratio_integral (P (φ (ρ j))) (Q (φ (ρ j))) g]
    -- The pushforward law is `LW (ρ j)` (defeq); replace `Ψ_g` by `cc` on the support `[0,2]`.
    have h_meas_eq : (μ (ρ j)).map (fun ω => ((P (φ (ρ j))).rnDeriv (μ (ρ j)) ω).toReal)
        = LW (ρ j) := rfl
    rw [h_meas_eq]
    refine integral_congr_ae ?_
    have h_compl : ∀ᵐ w ∂(LW (ρ j)), w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_supp (ρ j)
    filter_upwards [h_compl] with w hw
    simp only [not_or, not_lt] at hw
    exact hagree w hw.1 hw.2
  -- ── Per-`j` change-of-variable identity, `U`-side (`R = Q, S = P`). ──
  -- `∫ g ∂LdPdQ(ρj) = ∫ cc ∂LW(ρj)` when `cc` agrees with `(2-w)·g(w/(2-w))` on `[0,2]`.
  have uIdent : ∀ (g cc : ℝ →ᵇ ℝ),
      (∀ w, 0 ≤ w → w ≤ 2 → (2 - w) * g (w / (2 - w)) = cc w) →
      ∀ j, ∫ x, g x ∂(LdPdQ (ρ j)) = ∫ x, cc x ∂(LW (ρ j)) := by
    intro g cc hagree j
    rw [hLdPdQ_def, MeasureTheory.integral_map (hdPdQ_meas (ρ j)).aemeasurable
      g.continuous.aestronglyMeasurable]
    -- bridge with `R = Q, S = P`: `= ∫ v·g((2-v)/v) ∂(μ(ρj).map ((Q.rnDeriv μ).toReal))`.
    rw [cov_ratio_integral (Q (φ (ρ j))) (P (φ (ρ j))) g]
    -- Identify the lemma's mixture with `μ (ρ j)` (sum is commutative).
    rw [show (((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • Q (φ (ρ j)) + ((2 : ℝ≥0)⁻¹ : ℝ≥0∞) • P (φ (ρ j)))
        = μ (ρ j) from by rw [hμ_def]; exact add_comm _ _]
    -- Push the law `μ.map K` back to `μ` (`K = (Q.rnDeriv μ).toReal`).
    set K : Ω (φ (ρ j)) → ℝ := fun ω => ((Q (φ (ρ j))).rnDeriv (μ (ρ j)) ω).toReal with hK_def
    have hK_meas : Measurable K := ((Q (φ (ρ j))).measurable_rnDeriv (μ (ρ j))).ennreal_toReal
    have hΨg_meas : Measurable (fun w : ℝ => w * g ((2 - w) / w)) :=
      measurable_id.mul (g.continuous.measurable.comp
        ((measurable_const.sub measurable_id).div measurable_id))
    rw [MeasureTheory.integral_map (f := fun w : ℝ => w * g ((2 - w) / w))
      hK_meas.aemeasurable hΨg_meas.aestronglyMeasurable]
    -- `∫ ω, K ω·g((2-Kω)/Kω) ∂μ`. Replace `K` by `2 - W` `μ`-a.e., giving `Hbc(W)`.
    -- Then push `Hbc(W)` to `LW(ρj)` and replace `Hbc` by `cc` on `[0,2]`.
    have hHbc_meas : Measurable (fun w : ℝ => (2 - w) * g (w / (2 - w))) :=
      (measurable_const.sub measurable_id).mul (g.continuous.measurable.comp
        (measurable_id.div (measurable_const.sub measurable_id)))
    rw [show (∫ w, cc w ∂(LW (ρ j))) = ∫ ω, (fun w : ℝ => (2 - w) * g (w / (2 - w))) (W (ρ j) ω)
        ∂(μ (ρ j)) from ?_]
    · refine integral_congr_ae ?_
      filter_upwards [(hmix (ρ j)).2.2.2.1, hW_le2 (ρ j)] with ω hKeq hW2
      simp only [hK_def] at hKeq ⊢
      rw [hKeq]
      -- `(2 - (2-W))/(2-W) = W/(2-W)`.
      have : (2 - (2 - W (ρ j) ω)) / (2 - W (ρ j) ω) = W (ρ j) ω / (2 - W (ρ j) ω) := by ring_nf
      rw [this]
    · -- `∫ cc ∂LW = ∫ cc(W) ∂μ = ∫ Hbc(W) ∂μ` (`W ∈ [0,2]` `μ`-a.e. and `hagree`).
      change ∫ w, cc w ∂((μ (ρ j)).map (W (ρ j))) = _
      rw [MeasureTheory.integral_map (f := fun w : ℝ => cc w)
        (hW_meas (ρ j)).aemeasurable cc.continuous.aestronglyMeasurable]
      refine integral_congr_ae ?_
      filter_upwards [hW_le2 (ρ j)] with ω hW2
      exact (hagree (W (ρ j) ω) (hW_nonneg (ρ j) ω) hW2).symm
  -- ══ Fact B: `LW_lim {0} = 0` (from `hU_pos` via the `U`-side change of variable). ══
  -- `U {0} = 0`: `U` is a probability measure with `U {0 < x} = 1`.
  have hU_zero : U {(0 : ℝ)} = 0 := by
    have hmeas : MeasurableSet {x : ℝ | 0 < x} := measurableSet_lt measurable_const measurable_id
    have h1 : U {x : ℝ | 0 < x}ᶜ = 0 := by
      have := prob_compl_eq_one_sub (μ := U) hmeas
      rw [hU_pos, tsub_self] at this
      exact this
    refine measure_mono_null ?_ h1
    intro x hx; simp only [Set.mem_singleton_iff] at hx
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt, hx, le_refl]
  -- `f_m(x) = max 0 (1 - (m+1)|x|)`, bounded continuous in `[0,1]`, `↓ 1_{x=0}`.
  set fB : ℕ → (ℝ →ᵇ ℝ) := fun m => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max 0 (1 - (m + 1 : ℝ) * |x|))
    (continuous_const.max (continuous_const.sub (continuous_const.mul continuous_abs))) 1
    (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      refine ⟨by have : (0 : ℝ) ≤ max 0 (1 - (m + 1 : ℝ) * |x|) := le_max_left _ _; linarith, ?_⟩
      rw [max_le_iff]
      refine ⟨by norm_num, ?_⟩
      have : (0 : ℝ) ≤ (m + 1 : ℝ) * |x| := by positivity
      linarith) with hfB_def
  have hfB_apply : ∀ m x, fB m x = max 0 (1 - (m + 1 : ℝ) * |x|) := fun _ _ => rfl
  -- `ccB_m(w) = max 0 (2 - (m+2)·w)`, bounded continuous (`[0,2]` on the support), `↓ 2·1_{0}`.
  set ccB : ℕ → (ℝ →ᵇ ℝ) := fun m => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun w => max 0 (min (2 - (m + 2 : ℝ) * w) 2))
    (continuous_const.max ((continuous_const.sub (continuous_const.mul continuous_id)).min
      continuous_const)) 2
    (fun w => by
      rw [Real.norm_eq_abs, abs_le]
      have h0 : (0 : ℝ) ≤ max 0 (min (2 - (m + 2 : ℝ) * w) 2) := le_max_left _ _
      refine ⟨by linarith, ?_⟩
      rw [max_le_iff]
      exact ⟨by norm_num, min_le_right _ _⟩) with hccB_def
  have hccB_apply : ∀ m w, ccB m w = max 0 (min (2 - (m + 2 : ℝ) * w) 2) := fun _ _ => rfl
  -- Agreement on `[0,2]`: `(2-w)·fB m (w/(2-w)) = ccB m w`.
  have hB_agree : ∀ m w, 0 ≤ w → w ≤ 2 → (2 - w) * fB m (w / (2 - w)) = ccB m w := by
    intro m w hw0 hw2
    rw [hfB_apply, hccB_apply]
    have hmin : min (2 - (m + 2 : ℝ) * w) 2 = 2 - (m + 2 : ℝ) * w := by
      apply min_eq_left; nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (m + 2 : ℝ)) hw0]
    rw [hmin]
    rcases eq_or_lt_of_le hw2 with hw | hw
    · -- `w = 2`: both sides `0`.
      subst hw
      rw [sub_self, zero_mul, max_eq_left]
      have : (2 : ℝ) - (m + 2 : ℝ) * 2 ≤ 0 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith
      linarith
    · -- `w < 2`: `2 - w > 0`, `w/(2-w) ≥ 0`.
      have h2w : (0 : ℝ) < 2 - w := by linarith
      have hratio : (0 : ℝ) ≤ w / (2 - w) := div_nonneg hw0 h2w.le
      rw [abs_of_nonneg hratio]
      rw [mul_max_of_nonneg _ _ h2w.le, mul_zero]
      congr 1
      field_simp
      ring
  -- Per-`m` identity: `∫ fB m ∂U = ∫ ccB m ∂LW_lim`.
  have hB_ident : ∀ m, ∫ x, fB m x ∂U = ∫ w, ccB m w ∂LW_lim := fun m =>
    transfer_U (fB m) (ccB m) (uIdent (fB m) (ccB m) (hB_agree m))
  -- Antitone limits (`m → ∞`).
  have hfB_int : ∀ m, Integrable (fun x => fB m x) U := fun m => (fB m).integrable U
  have hccB_int : ∀ m, Integrable (fun w => ccB m w) LW_lim := fun m => (ccB m).integrable LW_lim
  -- `fB m x ↓ 1_{x=0}`.
  have hfB_anti : ∀ x : ℝ, Antitone (fun m => fB m x) := by
    intro x m n hmn
    simp only [hfB_apply]
    apply max_le_max le_rfl
    have : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hmn 1
    nlinarith [abs_nonneg x]
  have hfB_tendsto : ∀ x : ℝ,
      Tendsto (fun m => fB m x) atTop (𝓝 (Set.indicator {(0 : ℝ)} (fun _ => (1 : ℝ)) x)) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [Set.indicator_of_mem (Set.mem_singleton 0)]
      have : (fun m => fB m (0 : ℝ)) = fun _ => (1 : ℝ) := by
        funext m; rw [hfB_apply]; simp
      rw [this]; exact tendsto_const_nhds
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      -- Eventually zero: once `(m+1)|x| ≥ 1`, `fB m x = 0`.
      have habs : (0 : ℝ) < |x| := abs_pos.mpr hx
      have h_ev : (fun m => fB m x) =ᶠ[atTop] fun _ => (0 : ℝ) := by
        filter_upwards [Filter.eventually_atTop.mpr ⟨Nat.ceil (1 / |x|), fun m hm => hm⟩]
          with m hm
        rw [hfB_apply, max_eq_left]
        have h1 : (1 : ℝ) / |x| ≤ m := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
        rw [div_le_iff₀ habs] at h1
        nlinarith [habs]
      rw [tendsto_congr' h_ev]
      exact tendsto_const_nhds
  -- `∫ fB m ∂U → (U {0}).toReal = 0`.
  have hfB_lim : Tendsto (fun m => ∫ x, fB m x ∂U) atTop (𝓝 (0 : ℝ)) := by
    have hint_ind : Integrable (Set.indicator {(0 : ℝ)} (fun _ => (1 : ℝ))) U :=
      (integrable_const (1 : ℝ)).indicator (measurableSet_singleton (0 : ℝ))
    have h := integral_tendsto_of_tendsto_of_antitone hfB_int hint_ind
      (Filter.Eventually.of_forall hfB_anti) (Filter.Eventually.of_forall hfB_tendsto)
    rwa [MeasureTheory.integral_indicator (measurableSet_singleton (0 : ℝ)),
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def, hU_zero, ENNReal.toReal_zero] at h
  -- `ccB m w ↓ 2·1_{w=0}` `LW_lim`-a.e. (support `[0,2]`); hence `∫ ccB m → 2·(LW_lim{0}).toReal`.
  have hccB_anti : ∀ᵐ w ∂LW_lim, Antitone (fun m => ccB m w) := by
    have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
    filter_upwards [h_compl] with w hw
    simp only [not_or, not_lt] at hw
    intro m n hmn
    simp only [hccB_apply]
    apply max_le_max le_rfl
    apply min_le_min _ le_rfl
    have hmn' : (m + 2 : ℝ) ≤ (n + 2 : ℝ) := by exact_mod_cast Nat.add_le_add_right hmn 2
    nlinarith [hw.1]
  have hccB_tendsto : ∀ᵐ w ∂LW_lim,
      Tendsto (fun m => ccB m w) atTop (𝓝 (Set.indicator {(0 : ℝ)} (fun _ => (2 : ℝ)) w)) := by
    have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
    filter_upwards [h_compl] with w hw
    simp only [not_or, not_lt] at hw
    by_cases hw0 : w = 0
    · subst hw0
      rw [Set.indicator_of_mem (Set.mem_singleton 0)]
      have : (fun m => ccB m (0 : ℝ)) = fun _ => (2 : ℝ) := by
        funext m; rw [hccB_apply]; simp
      rw [this]; exact tendsto_const_nhds
    · rw [Set.indicator_of_notMem (by simpa using! hw0)]
      have hwpos : 0 < w := lt_of_le_of_ne hw.1 (Ne.symm hw0)
      have h_ev : (fun m => ccB m w) =ᶠ[atTop] fun _ => (0 : ℝ) := by
        filter_upwards [Filter.eventually_atTop.mpr ⟨Nat.ceil (2 / w), fun m hm => hm⟩] with m hm
        rw [hccB_apply, max_eq_left]
        apply min_le_of_left_le
        have h1 : (2 : ℝ) / w ≤ m := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
        rw [div_le_iff₀ hwpos] at h1
        nlinarith [hwpos]
      rw [tendsto_congr' h_ev]; exact tendsto_const_nhds
  have hccB_lim : Tendsto (fun m => ∫ w, ccB m w ∂LW_lim) atTop
      (𝓝 (2 * (LW_lim {(0 : ℝ)}).toReal)) := by
    have hint_ind : Integrable (Set.indicator {(0 : ℝ)} (fun _ => (2 : ℝ))) LW_lim :=
      (integrable_const (2 : ℝ)).indicator (measurableSet_singleton (0 : ℝ))
    have h := integral_tendsto_of_tendsto_of_antitone hccB_int hint_ind
      hccB_anti hccB_tendsto
    rw [MeasureTheory.integral_indicator (measurableSet_singleton (0 : ℝ)),
      MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def] at h
    rwa [mul_comm] at h
  -- Combine: `2·(LW_lim{0}).toReal = 0`, hence `LW_lim {0} = 0`.
  have hFactB : LW_lim {(0 : ℝ)} = 0 := by
    have heq : Tendsto (fun m => ∫ w, ccB m w ∂LW_lim) atTop (𝓝 (0 : ℝ)) := by
      have : (fun m => ∫ w, ccB m w ∂LW_lim) = fun m => ∫ x, fB m x ∂U := by
        funext m; exact (hB_ident m).symm
      rw [this]; exact hfB_lim
    have h2 : 2 * (LW_lim {(0 : ℝ)}).toReal = 0 := tendsto_nhds_unique hccB_lim heq
    have h3 : (LW_lim {(0 : ℝ)}).toReal = 0 := by linarith
    exact (ENNReal.toReal_eq_zero_iff _).mp h3 |>.resolve_right (measure_ne_top _ _)
  -- ══ Fact A: `∫ x ∂V = ∫ (2-w)·1_{0<w} ∂LW_lim = 1`. ══
  -- `hA m(x) = min (max x 0) m`, bounded continuous, `↑ max x 0`.
  set hA : ℕ → (ℝ →ᵇ ℝ) := fun m => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (max x 0) (m : ℝ))
    ((continuous_id.max continuous_const).min continuous_const) (m : ℝ)
    (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      have h0 : (0 : ℝ) ≤ min (max x 0) (m : ℝ) := le_min (le_max_right _ _) (by positivity)
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      exact ⟨by linarith, min_le_right _ _⟩) with hA_def
  have hA_apply : ∀ m x, hA m x = min (max x 0) (m : ℝ) := fun _ _ => rfl
  -- `ccA m(w) = min (2 - cl w) (m · cl w)`, `cl = clamp [0,2]`; bdd-cont, `↑ (2-w)1_{0<w}`.
  set ccA : ℕ → (ℝ →ᵇ ℝ) := fun m => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun w => min (2 - min (max w 0) 2) ((m : ℝ) * min (max w 0) 2))
    ((continuous_const.sub ((continuous_id.max continuous_const).min continuous_const)).min
      (continuous_const.mul ((continuous_id.max continuous_const).min continuous_const))) 2
    (fun w => by
      have hcl0 : (0 : ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
      have hcl2 : min (max w 0) 2 ≤ 2 := min_le_right _ _
      rw [Real.norm_eq_abs, abs_le]
      refine ⟨?_, ?_⟩
      · have : (0 : ℝ) ≤ min (2 - min (max w 0) 2) ((m : ℝ) * min (max w 0) 2) :=
          le_min (by linarith) (by positivity)
        linarith
      · exact le_trans (min_le_left _ _) (by linarith)) with hccA_def
  have hccA_apply : ∀ m w, ccA m w = min (2 - min (max w 0) 2) ((m : ℝ) * min (max w 0) 2) :=
    fun _ _ => rfl
  -- Agreement on `[0,2]`: `w·hA m ((2-w)/w) = ccA m w`.
  have hA_agree : ∀ m w, 0 ≤ w → w ≤ 2 → w * hA m ((2 - w) / w) = ccA m w := by
    intro m w hw0 hw2
    rw [hA_apply, hccA_apply, max_eq_left hw0, min_eq_left hw2]
    rcases eq_or_lt_of_le hw0 with hw | hw
    · -- `w = 0`: both `0`.
      rw [← hw]; simp
    · -- `w > 0`: `(2-w)/w ≥ 0`.
      have hratio : (0 : ℝ) ≤ (2 - w) / w := div_nonneg (by linarith) hw.le
      rw [max_eq_left hratio, mul_min_of_nonneg _ _ hw.le]
      congr 1
      · field_simp
      · ring
  -- Per-`m` identity: `∫ hA m ∂V = ∫ ccA m ∂LW_lim`.
  have hA_ident : ∀ m, ∫ x, hA m x ∂V = ∫ w, ccA m w ∂LW_lim := fun m =>
    transfer_V (hA m) (ccA m) (vIdent (hA m) (ccA m) (hA_agree m))
  -- Uniform bound: `∫ ccA m ∂LW_lim ≤ 2` (since `ccA m ≤ 2`); hence `∫ hA m ∂V ≤ 2`.
  have hccA_le2 : ∀ m w, ccA m w ≤ 2 := by
    intro m w
    rw [hccA_apply]
    have hcl0 : (0 : ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
    exact le_trans (min_le_left _ _) (by linarith)
  have hccA_nonneg : ∀ m w, 0 ≤ ccA m w := by
    intro m w
    rw [hccA_apply]
    have hcl0 : (0 : ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
    have hcl2 : min (max w 0) 2 ≤ 2 := min_le_right _ _
    exact le_min (by linarith) (by positivity)
  have hA_le2 : ∀ m, ∫ x, hA m x ∂V ≤ 2 := by
    intro m
    rw [hA_ident m]
    calc ∫ w, ccA m w ∂LW_lim ≤ ∫ _, (2 : ℝ) ∂LW_lim :=
          integral_mono ((ccA m).integrable LW_lim) (integrable_const _)
            (fun w => hccA_le2 m w)
      _ = 2 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  -- `max · 0` is `V`-integrable (uniform bound on the truncations + monotone convergence).
  have hA_apply_nonneg : ∀ m x, 0 ≤ hA m x := by
    intro m x; rw [hA_apply]; exact le_min (le_max_right _ _) (by positivity)
  -- pointwise sup `ofReal (max x 0) = ⨆ m, ofReal (hA m x)`.
  have hA_iSup : ∀ x : ℝ, ⨆ m, ENNReal.ofReal (hA m x) = ENNReal.ofReal (max x 0) := by
    intro x
    refine le_antisymm (iSup_le (fun m => ENNReal.ofReal_le_ofReal ?_)) ?_
    · rw [hA_apply]; exact min_le_left _ _
    · -- pick `m ≥ max x 0`; then `ofReal (hA m x) = ofReal (max x 0)`.
      obtain ⟨m, hm⟩ := exists_nat_ge (max x 0)
      refine le_iSup_of_le m ?_
      rw [hA_apply, min_eq_left hm]
  have hVmax_int : Integrable (fun x => max x 0) V := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => max x 0) V :=
      (continuous_id.max continuous_const).aestronglyMeasurable
    have h0 : 0 ≤ᵐ[V] fun x : ℝ => max x 0 :=
      Filter.Eventually.of_forall (fun x => le_max_right _ _)
    refine ⟨hmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal h0]
    have hmono : Monotone (fun m => fun x => ENNReal.ofReal (hA m x)) := by
      intro m n hmn x
      exact ENNReal.ofReal_le_ofReal (by
        rw [hA_apply, hA_apply]; exact min_le_min le_rfl (by exact_mod_cast hmn))
    have hmeas_m : ∀ m, Measurable (fun x => ENNReal.ofReal (hA m x)) :=
      fun m => (hA m).continuous.measurable.ennreal_ofReal
    calc ∫⁻ x, ENNReal.ofReal (max x 0) ∂V
        = ∫⁻ x, ⨆ m, ENNReal.ofReal (hA m x) ∂V := by
          simp_rw [hA_iSup]
      _ = ⨆ m, ∫⁻ x, ENNReal.ofReal (hA m x) ∂V :=
          lintegral_iSup hmeas_m hmono
      _ ≤ 2 := by
          refine iSup_le (fun m => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal ((hA m).integrable V)
            (Filter.Eventually.of_forall (fun x => hA_apply_nonneg m x))]
          exact le_trans (ENNReal.ofReal_le_ofReal (hA_le2 m)) (by norm_num)
      _ < ⊤ := by norm_num
  -- Monotone limits (`m → ∞`).
  have hA_mono : ∀ x : ℝ, Monotone (fun m => hA m x) := by
    intro x m n hmn
    change hA m x ≤ hA n x
    rw [hA_apply, hA_apply]; exact min_le_min le_rfl (by exact_mod_cast hmn)
  have hA_tendsto : ∀ x : ℝ, Tendsto (fun m => hA m x) atTop (𝓝 (max x 0)) := by
    intro x
    have h_ev : (fun m => hA m x) =ᶠ[atTop] fun _ => max x 0 := by
      obtain ⟨M, hM⟩ := exists_nat_ge (max x 0)
      filter_upwards [Filter.eventually_atTop.mpr ⟨M, fun m hm => hm⟩] with m hm
      rw [hA_apply, min_eq_left (le_trans hM (by exact_mod_cast hm))]
    rw [tendsto_congr' h_ev]; exact tendsto_const_nhds
  have hA_lim : Tendsto (fun m => ∫ x, hA m x ∂V) atTop (𝓝 (∫ x, max x 0 ∂V)) :=
    integral_tendsto_of_tendsto_of_monotone (fun m => (hA m).integrable V) hVmax_int
      (Filter.Eventually.of_forall hA_mono) (Filter.Eventually.of_forall hA_tendsto)
  -- `ccA m w ↑ 2 - w` `LW_lim`-a.e. (`w ∈ (0,2]` a.e.).
  have hccA_mono : ∀ᵐ w ∂LW_lim, Monotone (fun m => ccA m w) := by
    have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
    filter_upwards [h_compl] with w hw
    simp only [not_or, not_lt] at hw
    intro m n hmn
    change ccA m w ≤ ccA n w
    rw [hccA_apply, hccA_apply]
    apply min_le_min le_rfl
    have hcl0 : (0 : ℝ) ≤ min (max w 0) 2 := le_min (le_max_right _ _) (by norm_num)
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    nlinarith
  have hccA_tendsto : ∀ᵐ w ∂LW_lim,
      Tendsto (fun m => ccA m w) atTop (𝓝 (2 - w)) := by
    have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
      rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
    have h_zero : ∀ᵐ w ∂LW_lim, w ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, Decidable.not_not]
      have : {w : ℝ | w = 0} = {(0 : ℝ)} := by ext w; simp
      rw [this]; exact hFactB
    filter_upwards [h_compl, h_zero] with w hw hw0
    simp only [not_or, not_lt] at hw
    have hwpos : 0 < w := lt_of_le_of_ne hw.1 (Ne.symm hw0)
    -- For `m` large, `ccA m w = 2 - w` (since `m·w ≥ 2 - w`).
    have h_ev : (fun m => ccA m w) =ᶠ[atTop] fun _ => 2 - w := by
      obtain ⟨M, hM⟩ := exists_nat_ge ((2 - w) / w)
      filter_upwards [Filter.eventually_atTop.mpr ⟨M, fun m hm => hm⟩] with m hm
      rw [hccA_apply, max_eq_left hw.1, min_eq_left hw.2, min_eq_left]
      have h1 : (2 - w) / w ≤ m := le_trans hM (by exact_mod_cast hm)
      rw [div_le_iff₀ hwpos] at h1; linarith
    rw [tendsto_congr' h_ev]; exact tendsto_const_nhds
  have hF_int : Integrable (fun w => 2 - w) LW_lim := by
    have : Integrable (fun w : ℝ => w) LW_lim := by
      have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
        rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
      refine (integrable_const (2 : ℝ)).mono' measurable_id.aestronglyMeasurable ?_
      filter_upwards [h_compl] with w hw
      simp only [not_or, not_lt] at hw
      rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2
    exact (integrable_const (2 : ℝ)).sub this
  have hccA_lim : Tendsto (fun m => ∫ w, ccA m w ∂LW_lim) atTop (𝓝 (∫ w, (2 - w) ∂LW_lim)) :=
    integral_tendsto_of_tendsto_of_monotone (fun m => (ccA m).integrable LW_lim) hF_int
      hccA_mono hccA_tendsto
  -- Combine: `∫ max x 0 ∂V = ∫ (2 - w) ∂LW_lim`.
  have hA_combine : ∫ x, max x 0 ∂V = ∫ w, (2 - w) ∂LW_lim := by
    have heq : (fun m => ∫ x, hA m x ∂V) = fun m => ∫ w, ccA m w ∂LW_lim := funext hA_ident
    rw [heq] at hA_lim
    exact tendsto_nhds_unique hA_lim hccA_lim
  -- `∫ x ∂V = ∫ max x 0 ∂V` (`V` supported in `[0,∞)`).
  have hV_id_eq : ∫ x, x ∂V = ∫ x, max x 0 ∂V := by
    refine integral_congr_ae ?_
    have h_compl : ∀ᵐ x ∂V, x ∉ {y : ℝ | y < 0} := by
      rw [ae_iff]; simpa only [not_not] using! hV_supp
    filter_upwards [h_compl] with x hx
    simp only [not_lt] at hx
    rw [max_eq_left hx]
  -- `∫ (2 - w) ∂LW_lim = 2 - 1 = 1` (probability + Fact C).
  have hF_eval : ∫ w, (2 - w) ∂LW_lim = 1 := by
    rw [integral_sub (integrable_const _) (by
      -- `id` is integrable because the measure is supported on `[0,2]`.
      have h_compl : ∀ᵐ w ∂LW_lim, w ∉ {x : ℝ | x < 0 ∨ 2 < x} := by
        rw [ae_iff]; simpa only [not_not] using! hLW_lim_supp
      refine (integrable_const (2 : ℝ)).mono' measurable_id.aestronglyMeasurable ?_
      filter_upwards [h_compl] with w hw
      simp only [not_or, not_lt] at hw
      rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2)]
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul, hFactC]
    norm_num
  rw [hV_id_eq, hA_combine, hF_eval]

/-- **Le Cam's first lemma** (vdV Lemma 6.4): the four-way equivalence packaged as a
`TFAE`, in the order (i) [`Contiguous`, event form], (iv) [statistic form], (ii) [limit
points of `dPₙ/dQₙ` give mass `0` to `0`], (iii) [limit points of `dQₙ/dPₙ` have mean
`1`].

The hypotheses `hac_PQ : ∀ n, P n ≪ Q n` and `hac_QP : ∀ n, Q n ≪ P n`
ensure that the likelihood ratios capture the full measures, following
van der Vaart's likelihood-ratio convention. -/
theorem leCam_first_tfae
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (hac_PQ : ∀ n, (P n).AbsolutelyContinuous (Q n))
    (hac_QP : ∀ n, (Q n).AbsolutelyContinuous (P n)) :
    List.TFAE
      [ Contiguous (ι := ℕ) (Ω := Ω) atTop P Q,
        ∀ (T : ∀ n, Ω n → ℝ), (∀ n, Measurable (T n)) →
          (∀ ε : ℝ, 0 < ε →
            Tendsto (fun n => (P n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun n => (Q n) {ω | ε ≤ |T n ω|}) atTop (𝓝 0),
        ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (U : Measure ℝ), IsProbabilityMeasure U →
          WeakConverges
            (fun k => (Q (φ k)).map (fun ω => ((P (φ k)).rnDeriv (Q (φ k)) ω).toReal)) U →
          U {x : ℝ | 0 < x} = 1,
        ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (V : Measure ℝ), IsProbabilityMeasure V →
          WeakConverges
            (fun k => (P (φ k)).map (fun ω => ((Q (φ k)).rnDeriv (P (φ k)) ω).toReal)) V →
          ∫ x, x ∂V = 1 ] := by
  tfae_have 1 ↔ 2 := contiguous_iff_tendsto_zero_statistics P Q
  tfae_have 1 → 3 := by
    intro hcont φ hφ U _ hU
    exact contiguous_imp_limit_pos P Q hcont φ hφ (fun k => hac_PQ (φ k)) U hU
  tfae_have 3 → 4 := by
    intro hU φ hφ V _ hV
    exact limit_pos_imp_mean_one P Q hU φ hφ V hV
  tfae_have 4 → 1 := mean_one_imp_contiguous P Q hac_QP
  tfae_finish

end LeCamFirstEquivalence

end Contiguity
end AsymptoticStatistics

end GLP0011B3Source9
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.PiWithDensity`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source10


/-!
# Pi measure under withDensity

A pi-measure tilted by a product density decomposes componentwise into the product
of individually-tilted measures:
```
(Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
  = Measure.pi (fun i => (μ i).withDensity (f i))
```

For the multivariate Girsanov argument in van der Vaart's Theorem 7.10,
the 1D Girsanov identity `(gaussianReal 0 1).withDensity (exp-shift) = gaussianReal a 1`
and `map_pi_eq_stdGaussian` combine with this theorem to give the finite-product identity.

The proof goes through an ENNReal version of
`MeasureTheory.integral_fintype_prod_eq_prod`. The ENNReal analogue follows
by induction on `Fin n` using `measurePreserving_piFinSuccAbove` + `lintegral_prod_mul`, then lift to a
general `Fintype` via `measurePreserving_piCongrLeft`, and finally apply
`Measure.pi_eq` on rectangles.
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

section LintegralProd

variable {ι : Type*} [Fintype ι]

set_option backward.isDefEq.respectTransparency.types false in
/-- **ENNReal Fubini on `Fin n`**: the `lintegral` of a product of per-coordinate
functions over `Measure.pi μ` factors as a product of per-coordinate lintegrals.

ENNReal analogue of `MeasureTheory.integral_fin_nat_prod_eq_prod`. Proved by induction
on `n` using `measurePreserving_piFinSuccAbove` + `lintegral_prod_mul`. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : Fin n) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi μ
      = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have mp := measurePreserving_piFinSuccAbove μ 0
      have h_prod_meas : Measurable fun x : (i : Fin (n + 1)) → E i => ∏ i, f i (x i) :=
        Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
      have hf0_ae : AEMeasurable (f 0) (μ 0) := (hf 0).aemeasurable
      have h_tail_ae :
          AEMeasurable (fun y : (i : Fin n) → E i.succ => ∏ i, f i.succ (y i))
            (Measure.pi (fun i => μ i.succ)) :=
        (Finset.measurable_prod _ (fun i _ =>
          (hf _).comp (measurable_pi_apply i))).aemeasurable
      have ih' : ∫⁻ y : (i : Fin n) → E i.succ, ∏ i, f i.succ (y i)
                   ∂Measure.pi (fun i : Fin n => μ i.succ)
                 = ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ :=
        ih (E := fun i : Fin n => E i.succ) (μ := fun i : Fin n => μ i.succ)
           (f := fun i : Fin n => f i.succ) (fun i => hf _)
      calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂Measure.pi μ
          = ∫⁻ z : E 0 × ((i : Fin n) → E i.succ),
              f 0 z.1 * ∏ i, f i.succ (z.2 i)
              ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
            rw [← mp.symm.lintegral_comp h_prod_meas]
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
            rfl
        _ = (∫⁻ x, f 0 x ∂μ 0)
              * ∫⁻ y : (i : Fin n) → E i.succ,
                  (∏ i : Fin n, f i.succ (y i)) ∂Measure.pi (fun i : Fin n => μ i.succ) :=
            lintegral_prod_mul hf0_ae h_tail_ae
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by rw [ih']
        _ = ∏ i, ∫⁻ x, f i x ∂μ i := by
            rw [← Fin.prod_univ_succ (fun i : Fin (n + 1) => ∫⁻ x, f i x ∂μ i)]

/-- **ENNReal Fubini on a general `Fintype`**: same factorisation as
`lintegral_fin_nat_prod_eq_prod`, but with variables indexed by any finite type.
Lifts the `Fin n` case through `measurePreserving_piCongrLeft`. -/
theorem lintegral_fintype_prod_eq_prod {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : ι) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂Measure.pi μ
      = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  have mp := measurePreserving_piCongrLeft (fun i => μ i) e
  have h_meas : Measurable fun x : (i : ι) → E i => ∏ i, f i (x i) :=
    Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  rw [← mp.lintegral_comp h_meas]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => hf _)

end LintegralProd

section PiWithDensity

variable {ι : Type*} [Fintype ι]

/-- **Pi measure tilted by a product density**. A product of per-coordinate densities
applied to the product measure equals the product of per-coordinate tilted measures:
```
(Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
  = Measure.pi (fun i => (μ i).withDensity (f i))
```

Proof: compare both sides on rectangles using `Measure.pi_eq`. On a rectangle
`Set.univ.pi s`, the left side becomes `∫⁻ x in pi s, ∏ f i (x i) ∂pi μ`, and the
rectangle indicator factors as a product of indicators; `lintegral_fintype_prod_eq_prod`
then splits the integral into `∏ i, ∫⁻ (s i).indicator (f i)`, each of which is
`(μ i).withDensity (f i) (s i)` by `withDensity_apply`.

Second step of the multivariate Girsanov chain (van der Vaart's Theorem 7.10); combines with
`gaussianReal_withDensity_exp_shift` and `map_pi_eq_stdGaussian` to give the standard
multivariate Gaussian Girsanov identity on `EuclideanSpace ℝ (Fin k)`. -/
theorem pi_withDensity_prod {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : ι) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))
      = Measure.pi (fun i => (μ i).withDensity (f i)) := by
  classical
  refine (Measure.pi_eq (μ := fun i => (μ i).withDensity (f i)) fun s hs => ?_).symm
  -- LHS on the rectangle `∏ᵢ sᵢ`.
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  -- Rewrite indicator of a rectangle as a product of indicators.
  have h_indic : ∀ x : (i : ι) → E i,
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x
        = ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Set.indicator_of_mem (hx i (Set.mem_univ _))]
    · rw [Set.indicator_of_notMem hx]
      rw [Set.mem_univ_pi] at hx
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)).symm
  simp_rw [h_indic]
  -- Apply the ENNReal Fubini factorisation.
  rw [lintegral_fintype_prod_eq_prod (fun i => (hf i).indicator (hs i))]
  -- Reassemble each factor as `(μ i).withDensity (f i) (s i)`.
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [lintegral_indicator (hs i), ← withDensity_apply _ (hs i)]

end PiWithDensity

end MeasureTheory

end GLP0011B3Source10
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.HellingerProduct`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source11


/-!
# Product-Hellinger inequality for iid products

For two probability measures dominated by a common σ-finite measure with densities
`p, q : Ω → ℝ≥0∞` (typed via `ENNReal` to match `Measure.rnDeriv`), the squared
Hellinger residual

```
‖√p.toReal - √q.toReal‖²_{L²(μ)}
```

and its `n`-fold-product counterpart

```
‖√(∏ⱼ pⱼ).toReal - √(∏ⱼ qⱼ).toReal‖²_{L²(μ^n)}
```

are related by

```
‖√∏p.toReal - √∏q.toReal‖²_{L²(μ^n)} ≤ n · ‖√p.toReal - √q.toReal‖²_{L²(μ)}
```

## Mathematical content

Define the *Hellinger affinity* `A := ∫ √(p · q).toReal dμ`. Then for probability
densities `p, q`:

1. `‖√p.toReal - √q.toReal‖²_{L²(μ)} = ∫ p.toReal + ∫ q.toReal - 2A = 2 - 2A`.
2. The affinity multiplies under iid products:
   `A(μ^n, ν^n, μ_dom^n) = A(μ, ν, μ_dom)^n` (via `lintegral_fintype_prod_eq_prod`
   applied to `∏ⱼ √(pⱼ qⱼ)`).
3. Bernoulli inequality `1 - A^n ≤ n · (1 - A)` for `0 ≤ A ≤ 1` (Cauchy-Schwarz).
4. Combining gives the squared `L²`-form, and `√n` after square-rooting.

The analytic core is product-affinity multiplicativity, expressed below in
`lintegral` and Bochner-integral forms. Together with the one-sample Hellinger
identity and Bernoulli's inequality, it yields the squared residual bound and
the headline square-root estimate
`hellinger_product_eLpNorm_le_sqrt_n_per_sample`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib.HellingerProduct

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Pointwise / numerical lemma: Bernoulli `1 - x^n ≤ n(1-x)` for `x ∈ [0,1]`. -/

/-- Bernoulli-style inequality: `1 - x^n ≤ n(1-x)` for `x ∈ [0,1]`.

Proof: induction on `n`. The step uses
`1 - x^{n+1} = (1 - x^n) + x^n · (1 - x) ≤ n(1-x) + 1·(1-x) = (n+1)(1-x)`. -/
lemma one_sub_pow_le_nsmul_one_sub
    {x : ℝ} (hx_nn : 0 ≤ x) (hx_le : x ≤ 1) (n : ℕ) :
    1 - x ^ n ≤ n * (1 - x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx_n_nn : 0 ≤ x ^ n := pow_nonneg hx_nn n
      have hx_n_le : x ^ n ≤ 1 := pow_le_one₀ hx_nn hx_le
      have h_id : 1 - x ^ (n + 1) = (1 - x ^ n) + x ^ n * (1 - x) := by ring
      have h_term2 : x ^ n * (1 - x) ≤ 1 * (1 - x) :=
        mul_le_mul_of_nonneg_right hx_n_le (by linarith)
      have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [h_id, h_cast]
      have h_rhs : ((n : ℝ) + 1) * (1 - x) = (n : ℝ) * (1 - x) + 1 * (1 - x) := by
        ring
      rw [h_rhs]
      linarith

/-! ## Product affinity multiplicativity (toReal form).

For iid product measures with densities `p, q : Ω → ℝ≥0∞`, the Hellinger affinity
factors as a power:

```
∫ Real.sqrt ((∏ⱼ p(X j)).toReal * (∏ⱼ q(X j)).toReal) d(μ^n)
  = (∫ Real.sqrt (p ω . toReal * q ω . toReal) dμ) ^ n
```

(when both `p, q` are finite-valued so `.toReal` commutes with products).

The cleanest framing uses `ℝ≥0∞`-valued integrals of `√(p · q)` via
`ENNReal.toReal` and a finiteness side-condition. The unwrapped form is stated
on the `lintegral` side (with the ENNReal product) and a `.toReal` wrapper. -/


/-- For iid product measures, the lintegral of `∏ⱼ f(X j)` factors as `(∫ f dμ)^n`,
when `f` is the same function at each coordinate.

This is `lintegral_fin_nat_prod_eq_prod` specialised to the iid case. -/
lemma lintegral_prod_iid_eq_pow
    {n : ℕ} (μ : Measure Ω) [SigmaFinite μ]
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ X : Fin n → Ω, ∏ _j : Fin n, f (X _j)
        ∂Measure.pi (fun _ : Fin n => μ)
      = (∫⁻ ω, f ω ∂μ) ^ n := by
  have h_fact := MeasureTheory.lintegral_fin_nat_prod_eq_prod
    (μ := fun _ : Fin n => μ)
    (f := fun _ : Fin n => f) (fun _ => hf)
  rw [h_fact, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## Hellinger affinity and the iid product inequality

The tensorisation inequality is
`(eLpNorm (√(∏p) − √(∏q)) 2 (ξ^n)).toReal ≤ √n · (eLpNorm (√p − √q) 2 ξ).toReal`
proved via the **Hellinger affinity** `A := ∫ √p · √q dξ ∈ [0, 1]`, with the canonical
chain
  per-sample residual sq = `2 − 2A`,
  product residual sq    = `2 − 2 Aⁿ`,
  Bernoulli `1 − Aⁿ ≤ n(1 − A)`,
take sqrt.
-/

open AsymptoticStatistics.ForMathlib.RnDerivSqrt

omit [MeasurableSpace Ω] in
/-- Pointwise rewrite `(∏ⱼ √pⱼ.toReal) = √((∏ⱼ pⱼ).toReal)`. -/
lemma prod_sqrt_eq_sqrt_prod_toReal {n : ℕ} (p : Ω → ℝ≥0∞) (X : Fin n → Ω) :
    ∏ j, Real.sqrt ((p (X j)).toReal)
      = Real.sqrt ((∏ j, p (X j)).toReal) := by
  rw [ENNReal.toReal_prod]
  exact (Real.sqrt_prod _ (fun _ _ => ENNReal.toReal_nonneg)).symm

/-- `A := ∫ √p · √q dξ ≥ 0`. -/
lemma integral_sqrt_mul_sqrt_nonneg (μ ν ξ : Measure Ω) :
    0 ≤ ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
          * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ :=
  integral_nonneg (fun _ =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- `A ≤ 1`. By Cauchy-Schwarz `|∫ √p · √q|² ≤ (∫ p)(∫ q) = 1`. -/
lemma integral_sqrt_mul_sqrt_le_one
    {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
          * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ ≤ 1 := by
  have hf_mem : MemLp (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal) 2 ξ :=
    memLp_sqrt_rnDeriv hμ
  have hg_mem : MemLp (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal) 2 ξ :=
    memLp_sqrt_rnDeriv hν
  have hf_sq_int :
      ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal ^ 2 ∂ξ = 1 := by
    have := integral_sqrt_rnDeriv_sq (ν := μ) (μ := ξ) hμ
    simpa using this
  have hg_sq_int :
      ∫ ω, Real.sqrt (ν.rnDeriv ξ ω).toReal ^ 2 ∂ξ = 1 := by
    have := integral_sqrt_rnDeriv_sq (ν := ν) (μ := ξ) hν
    simpa using this
  have h_cs : |∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
                    * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ|
              ≤ Real.sqrt (∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal ^ 2 ∂ξ)
                  * Real.sqrt (∫ ω, Real.sqrt (ν.rnDeriv ξ ω).toReal ^ 2 ∂ξ) :=
    AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq ξ hf_mem hg_mem
  rw [hf_sq_int, hg_sq_int] at h_cs
  simp only [Real.sqrt_one, mul_one] at h_cs
  exact le_of_abs_le h_cs

/-- `∫ (∏ⱼ pⱼ(Xⱼ)).toReal d(ξ^n) = 1` for prob μ ≪ ξ. -/
lemma integral_prod_rnDeriv_toReal_eq_one
    {n : ℕ} {μ ξ : Measure Ω} [SigmaFinite ξ] [IsProbabilityMeasure μ]
    (hμ : μ ≪ ξ) :
    ∫ X : Fin n → Ω, (∏ j, (μ.rnDeriv ξ (X j)).toReal)
        ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := by
  have h_prod_nn : ∀ X : Fin n → Ω, 0 ≤ ∏ j, (μ.rnDeriv ξ (X j)).toReal :=
    fun X => Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have h_meas_p : Measurable (fun ω => (μ.rnDeriv ξ ω).toReal) :=
    (Measure.measurable_rnDeriv μ ξ).ennreal_toReal
  have h_prod_meas : Measurable
      (fun X : Fin n → Ω => ∏ j, (μ.rnDeriv ξ (X j)).toReal) :=
    Finset.measurable_prod _ (fun j _ => h_meas_p.comp (measurable_pi_apply j))
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall h_prod_nn) h_prod_meas.aestronglyMeasurable]
  have h_ofReal_prod : ∀ X : Fin n → Ω,
      ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal)
        = ∏ j, ENNReal.ofReal ((μ.rnDeriv ξ (X j)).toReal) :=
    fun _ => ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  rw [show (fun X : Fin n → Ω => ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal))
        = (fun X : Fin n → Ω => ∏ j, ENNReal.ofReal ((μ.rnDeriv ξ (X j)).toReal))
        from funext h_ofReal_prod]
  rw [lintegral_prod_iid_eq_pow (μ := ξ) (n := n)
      (f := fun ω => ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal))
      (ENNReal.measurable_ofReal.comp h_meas_p)]
  have h_ae_finite : ∀ᵐ ω ∂ξ, μ.rnDeriv ξ ω ≠ ⊤ :=
    (Measure.rnDeriv_lt_top μ ξ).mono (fun _ => ne_of_lt)
  have h_ofReal_toReal : ∀ᵐ ω ∂ξ,
      ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal) = μ.rnDeriv ξ ω :=
    h_ae_finite.mono (fun _ h => ENNReal.ofReal_toReal h)
  rw [lintegral_congr_ae h_ofReal_toReal]
  rw [MeasureTheory.Measure.lintegral_rnDeriv hμ]
  simp [measure_univ]

/-- Integrability of `(∏ⱼ pⱼ(Xⱼ)).toReal` under `ξ^n`. -/
lemma integrable_prod_rnDeriv_toReal
    {n : ℕ} {μ ξ : Measure Ω} [SigmaFinite ξ] [IsProbabilityMeasure μ]
    (hμ : μ ≪ ξ) :
    Integrable (fun X : Fin n → Ω => ∏ j, (μ.rnDeriv ξ (X j)).toReal)
      (Measure.pi (fun _ : Fin n => ξ)) := by
  have h_prod_nn : ∀ X : Fin n → Ω, 0 ≤ ∏ j, (μ.rnDeriv ξ (X j)).toReal :=
    fun _ => Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have h_meas_p : Measurable (fun ω => (μ.rnDeriv ξ ω).toReal) :=
    (Measure.measurable_rnDeriv μ ξ).ennreal_toReal
  have h_prod_meas : Measurable
      (fun X : Fin n → Ω => ∏ j, (μ.rnDeriv ξ (X j)).toReal) :=
    Finset.measurable_prod _ (fun j _ => h_meas_p.comp (measurable_pi_apply j))
  refine ⟨h_prod_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp_rw [Real.norm_of_nonneg (h_prod_nn _)]
  have h_eq : ∫⁻ X : Fin n → Ω,
      ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal)
        ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := by
    have h_ofReal_prod : ∀ X : Fin n → Ω,
        ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal)
          = ∏ j, ENNReal.ofReal ((μ.rnDeriv ξ (X j)).toReal) :=
      fun _ => ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    rw [show (fun X : Fin n → Ω => ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal))
          = (fun X : Fin n → Ω => ∏ j, ENNReal.ofReal ((μ.rnDeriv ξ (X j)).toReal))
          from funext h_ofReal_prod]
    rw [lintegral_prod_iid_eq_pow (μ := ξ) (n := n)
        (f := fun ω => ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal))
        (ENNReal.measurable_ofReal.comp h_meas_p)]
    have h_ae_finite : ∀ᵐ ω ∂ξ, μ.rnDeriv ξ ω ≠ ⊤ :=
      (Measure.rnDeriv_lt_top μ ξ).mono (fun _ => ne_of_lt)
    have h_ofReal_toReal : ∀ᵐ ω ∂ξ,
        ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal) = μ.rnDeriv ξ ω :=
      h_ae_finite.mono (fun _ h => ENNReal.ofReal_toReal h)
    rw [lintegral_congr_ae h_ofReal_toReal]
    rw [MeasureTheory.Measure.lintegral_rnDeriv hμ]
    simp [measure_univ]
  rw [h_eq]; exact ENNReal.one_lt_top

/-- *Product affinity multiplicativity (Bochner form)*:
  `∫ (∏ⱼ √p(Xⱼ)) · (∏ⱼ √q(Xⱼ)) d(ξ^n) = (∫ √p · √q dξ)^n`. -/
lemma integral_prod_sqrt_mul_prod_sqrt_eq_pow
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫ X : Fin n → Ω,
        (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          * (∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal)
        ∂(Measure.pi (fun _ : Fin n => ξ))
      = (∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
              * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ) ^ n := by
  set h : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
                          * Real.sqrt (ν.rnDeriv ξ ω).toReal with hdef
  have hh_nn : ∀ ω, 0 ≤ h ω := fun _ =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_meas : Measurable h :=
    (((Measure.measurable_rnDeriv μ ξ).ennreal_toReal).sqrt).mul
      (((Measure.measurable_rnDeriv ν ξ).ennreal_toReal).sqrt)
  have h_distr : ∀ X : Fin n → Ω,
      (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
        * (∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal)
      = ∏ j, h (X j) := by
    intro X; rw [← Finset.prod_mul_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall h_distr)]
  have h_prod_nn : ∀ X : Fin n → Ω, 0 ≤ ∏ j, h (X j) :=
    fun _ => Finset.prod_nonneg (fun _ _ => hh_nn _)
  have h_prod_meas : Measurable (fun X : Fin n → Ω => ∏ j, h (X j)) :=
    Finset.measurable_prod _ (fun j _ => h_meas.comp (measurable_pi_apply j))
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall h_prod_nn) h_prod_meas.aestronglyMeasurable]
  have h_ofReal_prod : ∀ X : Fin n → Ω,
      ENNReal.ofReal (∏ j, h (X j)) = ∏ j, ENNReal.ofReal (h (X j)) :=
    fun _ => ENNReal.ofReal_prod_of_nonneg (fun _ _ => hh_nn _)
  rw [show (fun X : Fin n → Ω => ENNReal.ofReal (∏ j, h (X j)))
        = (fun X : Fin n → Ω => ∏ j, ENNReal.ofReal (h (X j))) from
        funext h_ofReal_prod]
  rw [lintegral_prod_iid_eq_pow (μ := ξ) (n := n)
      (f := fun ω => ENNReal.ofReal (h ω))
      (ENNReal.measurable_ofReal.comp h_meas)]
  rw [ENNReal.toReal_pow]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hh_nn) h_meas.aestronglyMeasurable]

/-- *Per-sample residual square identity (Bochner)*:
  `∫ (√p − √q)² dξ = 2 − 2A`. -/
lemma integral_per_sample_residual_sq_eq
    {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    ∫ ω, (Real.sqrt (μ.rnDeriv ξ ω).toReal
            - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 ∂ξ
      = 2 - 2 * ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
                      * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ := by
  have hf_mem : MemLp (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal) 2 ξ :=
    memLp_sqrt_rnDeriv hμ
  have hg_mem : MemLp (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal) 2 ξ :=
    memLp_sqrt_rnDeriv hν
  have hf_sq : Integrable
      (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal ^ 2) ξ :=
    hf_mem.integrable_sq
  have hg_sq : Integrable
      (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal ^ 2) ξ :=
    hg_mem.integrable_sq
  have h_fg : Integrable
      (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
                * Real.sqrt (ν.rnDeriv ξ ω).toReal) ξ :=
    hf_mem.integrable_mul hg_mem
  have h_a := integral_sqrt_rnDeriv_sq (ν := μ) (μ := ξ) hμ
  have h_b := integral_sqrt_rnDeriv_sq (ν := ν) (μ := ξ) hν
  simp only [measure_univ, ENNReal.toReal_one] at h_a h_b
  -- Use `set` aliases to keep integrand parses clean.
  set fF : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal ^ 2 with hfF_def
  set gG : Ω → ℝ := fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal ^ 2 with hgG_def
  set H : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
                            * Real.sqrt (ν.rnDeriv ξ ω).toReal with hH_def
  have hF_int : Integrable fF ξ := hf_sq
  have hG_int : Integrable gG ξ := hg_sq
  have hH_int : Integrable H ξ := h_fg
  have hF_val : ∫ ω, fF ω ∂ξ = 1 := h_a
  have hG_val : ∫ ω, gG ω ∂ξ = 1 := h_b
  have h_pt : ∀ ω, (Real.sqrt (μ.rnDeriv ξ ω).toReal
                      - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2
                = fF ω + gG ω - 2 * H ω := by
    intro ω; simp only [hfF_def, hgG_def, hH_def]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_pt)]
  rw [integral_sub (hF_int.fun_add hG_int) (hH_int.const_mul 2)]
  rw [integral_add hF_int hG_int, integral_const_mul, hF_val, hG_val]
  ring

/-- *Product residual square identity*:
  `∫ (F − G)² d(ξ^n) = 2 − 2 Aⁿ`. -/
lemma integral_product_residual_sq_eq
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    ∫ X : Fin n → Ω,
        ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2
        ∂(Measure.pi (fun _ : Fin n => ξ))
      = 2 - 2 * (∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
                      * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ) ^ n := by
  set f : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
  set g : Ω → ℝ := fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal
  have hf_meas : Measurable f :=
    ((Measure.measurable_rnDeriv μ ξ).ennreal_toReal).sqrt
  have hg_meas : Measurable g :=
    ((Measure.measurable_rnDeriv ν ξ).ennreal_toReal).sqrt
  have hf_nn : ∀ ω, 0 ≤ f ω := fun _ => Real.sqrt_nonneg _
  have hg_nn : ∀ ω, 0 ≤ g ω := fun _ => Real.sqrt_nonneg _
  -- F² = ∏ p.toReal, G² = ∏ q.toReal pointwise.
  have hF_sq_pt : ∀ X : Fin n → Ω,
      (∏ j, f (X j)) ^ 2 = ∏ j, (μ.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun _ _ => ?_)
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hG_sq_pt : ∀ X : Fin n → Ω,
      (∏ j, g (X j)) ^ 2 = ∏ j, (ν.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun _ _ => ?_)
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hF_sq_int : Integrable (fun X : Fin n → Ω => (∏ j, f (X j)) ^ 2)
      (Measure.pi (fun _ : Fin n => ξ)) :=
    (integrable_prod_rnDeriv_toReal hμ).congr
      (Filter.Eventually.of_forall (fun X => (hF_sq_pt X).symm))
  have hG_sq_int : Integrable (fun X : Fin n → Ω => (∏ j, g (X j)) ^ 2)
      (Measure.pi (fun _ : Fin n => ξ)) :=
    (integrable_prod_rnDeriv_toReal hν).congr
      (Filter.Eventually.of_forall (fun X => (hG_sq_pt X).symm))
  have hF_sq_val : ∫ X, (∏ j, f (X j)) ^ 2
      ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hF_sq_pt)]
    exact integral_prod_rnDeriv_toReal_eq_one (μ := μ) (ξ := ξ) (n := n) hμ
  have hG_sq_val : ∫ X, (∏ j, g (X j)) ^ 2
      ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hG_sq_pt)]
    exact integral_prod_rnDeriv_toReal_eq_one (μ := ν) (ξ := ξ) (n := n) hν
  -- FG integrability via |FG| ≤ (F² + G²)/2.
  have hF_meas : Measurable (fun X : Fin n → Ω => ∏ j, f (X j)) :=
    Finset.measurable_prod _ (fun j _ => hf_meas.comp (measurable_pi_apply j))
  have hG_meas : Measurable (fun X : Fin n → Ω => ∏ j, g (X j)) :=
    Finset.measurable_prod _ (fun j _ => hg_meas.comp (measurable_pi_apply j))
  have hFG_int : Integrable (fun X : Fin n → Ω => (∏ j, f (X j)) * ∏ j, g (X j))
      (Measure.pi (fun _ : Fin n => ξ)) := by
    refine Integrable.mono ((hF_sq_int.add hG_sq_int).div_const 2)
      (hF_meas.mul hG_meas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun X => ?_))
    have h1 : 0 ≤ ∏ j, f (X j) := Finset.prod_nonneg (fun _ _ => hf_nn _)
    have h2 : 0 ≤ ∏ j, g (X j) := Finset.prod_nonneg (fun _ _ => hg_nn _)
    have hbd : (∏ j, f (X j)) * ∏ j, g (X j)
              ≤ ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) / 2 := by
      nlinarith [sq_nonneg ((∏ j, f (X j)) - ∏ j, g (X j))]
    have hr_nn : 0 ≤ ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) / 2 := by
      have : 0 ≤ (∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
    change (∏ j, f (X j)) * ∏ j, g (X j)
         ≤ ‖(fun X : Fin n → Ω =>
              ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) / 2) X‖
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]
    exact hbd
  have hFG_val :
      ∫ X, (∏ j, f (X j)) * (∏ j, g (X j))
        ∂(Measure.pi (fun _ : Fin n => ξ))
      = (∫ ω, f ω * g ω ∂ξ) ^ n :=
    integral_prod_sqrt_mul_prod_sqrt_eq_pow (μ := μ) (ν := ν) (ξ := ξ)
  -- Assemble: ∫ ((F − G)²) = 2 − 2 (∫ FG)^n.
  -- Strategy: expand (F − G)² = F² + G² − 2 FG pointwise, then integrate by linearity.
  -- Use `integral_finsetSum` to handle the sum cleanly (treating it as a 3-term sum).
  set F : (Fin n → Ω) → ℝ := fun X => (∏ j, f (X j)) ^ 2 with hF_def
  set G : (Fin n → Ω) → ℝ := fun X => (∏ j, g (X j)) ^ 2 with hG_def
  set H : (Fin n → Ω) → ℝ := fun X => (∏ j, f (X j)) * ∏ j, g (X j) with hH_def
  have hF_int : Integrable F (Measure.pi (fun _ : Fin n => ξ)) := hF_sq_int
  have hG_int : Integrable G (Measure.pi (fun _ : Fin n => ξ)) := hG_sq_int
  have hH_int : Integrable H (Measure.pi (fun _ : Fin n => ξ)) := hFG_int
  have hF_val : ∫ X, F X ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := hF_sq_val
  have hG_val : ∫ X, G X ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := hG_sq_val
  have hH_val : ∫ X, H X ∂(Measure.pi (fun _ : Fin n => ξ)) = (∫ ω, f ω * g ω ∂ξ) ^ n :=
    hFG_val
  have h_pt : ∀ X : Fin n → Ω,
      ((∏ j, f (X j)) - ∏ j, g (X j)) ^ 2 = F X + G X - 2 * H X := by
    intro X; simp only [hF_def, hG_def, hH_def]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_pt)]
  rw [integral_sub (hF_int.fun_add hG_int) (hH_int.const_mul 2)]
  rw [integral_add hF_int hG_int]
  rw [integral_const_mul]
  rw [hF_val, hG_val, hH_val]
  ring

/-- *Squared tensorisation inequality*:
  `∫ (F − G)² d(ξ^n) ≤ n · ∫ (f − g)² dξ`. -/
lemma hellinger_product_residual_sq_le_n_per_sample
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    ∫ X : Fin n → Ω,
        ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2
        ∂(Measure.pi (fun _ : Fin n => ξ))
      ≤ n * ∫ ω, (Real.sqrt (μ.rnDeriv ξ ω).toReal
                  - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 ∂ξ := by
  set A : ℝ := ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
                * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ
  have hA_nn : 0 ≤ A := integral_sqrt_mul_sqrt_nonneg μ ν ξ
  have hA_le_one : A ≤ 1 := integral_sqrt_mul_sqrt_le_one hμ hν
  rw [integral_product_residual_sq_eq (μ := μ) (ν := ν) (ξ := ξ) (n := n) hμ hν]
  rw [integral_per_sample_residual_sq_eq (μ := μ) (ν := ν) (ξ := ξ) hμ hν]
  have h_bern := one_sub_pow_le_nsmul_one_sub hA_nn hA_le_one n
  linarith

/-- *Tensorisation inequality (Bochner sqrt form)*:
  `√(∫ (F − G)² d(ξ^n)) ≤ √n · √(∫ (f − g)² dξ)`. -/
lemma hellinger_product_sqrt_residual_le_sqrt_n_per_sample
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    Real.sqrt (∫ X : Fin n → Ω,
        ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2
        ∂(Measure.pi (fun _ : Fin n => ξ)))
      ≤ Real.sqrt n * Real.sqrt (∫ ω,
            (Real.sqrt (μ.rnDeriv ξ ω).toReal
              - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 ∂ξ) := by
  have h_sq := hellinger_product_residual_sq_le_n_per_sample
    (μ := μ) (ν := ν) (ξ := ξ) (n := n) hμ hν
  have h_n_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc Real.sqrt _
      ≤ Real.sqrt _ := Real.sqrt_le_sqrt h_sq
    _ = Real.sqrt n * Real.sqrt _ := Real.sqrt_mul h_n_nn _

/-- Per-sample sqrt-residual `√p − √q ∈ L²(ξ)`. -/
lemma hellinger_per_sample_residual_memLp_two
    {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    MemLp (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
            - Real.sqrt (ν.rnDeriv ξ ω).toReal) 2 ξ :=
  (memLp_sqrt_rnDeriv hμ).sub (memLp_sqrt_rnDeriv hν)

/-- Product sqrt-residual (per-coord product form) is in `L²(ξ^n)`. -/
lemma hellinger_product_residual_memLp_two_perCoord
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    MemLp (fun X : Fin n → Ω =>
            (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
            - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal)
      2 (Measure.pi (fun _ : Fin n => ξ)) := by
  set f : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
  set g : Ω → ℝ := fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal
  have hf_meas : Measurable f :=
    ((Measure.measurable_rnDeriv μ ξ).ennreal_toReal).sqrt
  have hg_meas : Measurable g :=
    ((Measure.measurable_rnDeriv ν ξ).ennreal_toReal).sqrt
  have hF_meas : Measurable (fun X : Fin n → Ω => ∏ j, f (X j)) :=
    Finset.measurable_prod _ (fun j _ => hf_meas.comp (measurable_pi_apply j))
  have hG_meas : Measurable (fun X : Fin n → Ω => ∏ j, g (X j)) :=
    Finset.measurable_prod _ (fun j _ => hg_meas.comp (measurable_pi_apply j))
  have h_diff_meas := hF_meas.sub hG_meas
  erw [memLp_two_iff_integrable_sq h_diff_meas.aestronglyMeasurable]
  -- Bound (F − G)² ≤ 2(F² + G²) pointwise; both F², G² integrable.
  have hF_sq_pt : ∀ X : Fin n → Ω,
      (∏ j, f (X j)) ^ 2 = ∏ j, (μ.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun _ _ => ?_)
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hG_sq_pt : ∀ X : Fin n → Ω,
      (∏ j, g (X j)) ^ 2 = ∏ j, (ν.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun _ _ => ?_)
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hF_sq_int : Integrable (fun X : Fin n → Ω => (∏ j, f (X j)) ^ 2)
      (Measure.pi (fun _ : Fin n => ξ)) :=
    (integrable_prod_rnDeriv_toReal hμ).congr
      (Filter.Eventually.of_forall (fun X => (hF_sq_pt X).symm))
  have hG_sq_int : Integrable (fun X : Fin n → Ω => (∏ j, g (X j)) ^ 2)
      (Measure.pi (fun _ : Fin n => ξ)) :=
    (integrable_prod_rnDeriv_toReal hν).congr
      (Filter.Eventually.of_forall (fun X => (hG_sq_pt X).symm))
  refine Integrable.mono ((hF_sq_int.add hG_sq_int).const_mul 2)
    (h_diff_meas.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun X => ?_))
  -- Pointwise bound (F − G)² ≤ 2 (F² + G²).
  have h_bd : ((∏ j, f (X j)) - ∏ j, g (X j)) ^ 2
              ≤ 2 * ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) := by
    nlinarith [sq_nonneg ((∏ j, f (X j)) + ∏ j, g (X j)),
               sq_nonneg ((∏ j, f (X j)) - ∏ j, g (X j))]
  have hr_nn : 0 ≤ 2 * ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) := by
    have : 0 ≤ (∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ((∏ j, f (X j)) - ∏ j, g (X j)) ^ 2
       ≤ ‖(2 * ((fun X : Fin n → Ω => (∏ j, f (X j)) ^ 2)
              + fun X : Fin n → Ω => (∏ j, g (X j)) ^ 2) X)‖
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]
  exact h_bd

/-- **Headline tensorisation inequality** (eLpNorm form):
`(eLpNorm (√(∏p) − √(∏q)) 2 (ξ^n)).toReal ≤ √n · (eLpNorm (√p − √q) 2 ξ).toReal`. -/
theorem hellinger_product_eLpNorm_le_sqrt_n_per_sample
    {ξ : Measure Ω} [SigmaFinite ξ]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) (n : ℕ) :
    (eLpNorm
      (fun X : Fin n → Ω =>
        Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
        - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal)
      2 (Measure.pi (fun _ : Fin n => ξ))).toReal
      ≤ Real.sqrt n *
          (eLpNorm
            (fun ω : Ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
              - Real.sqrt (ν.rnDeriv ξ ω).toReal)
            2 ξ).toReal := by
  -- Rewrite the headline `√(∏p) − √(∏q)` form to per-coord `(∏ √p) − (∏ √q)` form.
  have h_prod_repl : ∀ X : Fin n → Ω,
      Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
          - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal
        = (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [prod_sqrt_eq_sqrt_prod_toReal, prod_sqrt_eq_sqrt_prod_toReal]
  have h_eLp_eq :
      eLpNorm (fun X : Fin n → Ω =>
        Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
        - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal)
        2 (Measure.pi (fun _ : Fin n => ξ))
      = eLpNorm (fun X : Fin n → Ω =>
        (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
        - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal)
        2 (Measure.pi (fun _ : Fin n => ξ)) := by
    congr 1; funext X; exact h_prod_repl X
  rw [h_eLp_eq]
  -- Convert eLpNorm to ∫·² via MemLp.eLpNorm_eq_integral_rpow_norm.
  have hPer_mem := hellinger_per_sample_residual_memLp_two (μ := μ) (ν := ν)
    (ξ := ξ) hμ hν
  have hProd_mem := hellinger_product_residual_memLp_two_perCoord (μ := μ) (ν := ν)
    (ξ := ξ) (n := n) hμ hν
  have h_per_form := hPer_mem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have h_prod_form := hProd_mem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  rw [h_prod_form, h_per_form]
  have h_two : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h_two]
  -- toReal of ENNReal.ofReal of nonneg = identity.
  set Iper : ℝ := ∫ ω, ‖Real.sqrt (μ.rnDeriv ξ ω).toReal
                  - Real.sqrt (ν.rnDeriv ξ ω).toReal‖ ^ (2 : ℝ) ∂ξ with hIperDef
  set Iprod : ℝ := ∫ X : Fin n → Ω,
                ‖(∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
                  - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal‖ ^ (2 : ℝ)
                ∂(Measure.pi (fun _ : Fin n => ξ)) with hIprodDef
  have hIper_nn : 0 ≤ Iper :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hIprod_nn : 0 ≤ Iprod :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hIper_nn _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hIprod_nn _)]
  -- Rewrite ‖·‖^(2:ℝ) as (·)^(2:ℕ) using Real.rpow_natCast + Real.norm_eq_abs + sq_abs.
  have h_per_norm_eq_sq : ∀ ω,
      ‖Real.sqrt (μ.rnDeriv ξ ω).toReal - Real.sqrt (ν.rnDeriv ξ ω).toReal‖ ^ (2 : ℝ)
        = (Real.sqrt (μ.rnDeriv ξ ω).toReal - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 := by
    intro ω
    rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
        Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have h_prod_norm_eq_sq : ∀ X : Fin n → Ω,
      ‖(∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal‖ ^ (2 : ℝ)
        = ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2 := by
    intro X
    rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
        Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have h_Iper_eq :
      Iper = ∫ ω, (Real.sqrt (μ.rnDeriv ξ ω).toReal
                    - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 ∂ξ := by
    simp_rw [hIperDef, h_per_norm_eq_sq]
  have h_Iprod_eq :
      Iprod = ∫ X : Fin n → Ω,
                ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
                  - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2
                ∂(Measure.pi (fun _ : Fin n => ξ)) := by
    simp_rw [hIprodDef, h_prod_norm_eq_sq]
  -- Identify rpow (2⁻¹) with Real.sqrt for nonneg.
  have h_rpow_half : ∀ x : ℝ, 0 ≤ x → x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
    intro x _
    rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) from by norm_num]
    rw [← Real.sqrt_eq_rpow]
  rw [h_rpow_half _ hIper_nn, h_rpow_half _ hIprod_nn]
  rw [h_Iper_eq, h_Iprod_eq]
  exact hellinger_product_sqrt_residual_le_sqrt_n_per_sample
    (μ := μ) (ν := ν) (ξ := ξ) (n := n) hμ hν

end AsymptoticStatistics.ForMathlib.HellingerProduct

end GLP0011B3Source11
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.L2Asymptotics`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source12



open MeasureTheory Filter Topology Asymptotics

namespace AsymptoticStatistics.L2Utils


end AsymptoticStatistics.L2Utils

end GLP0011B3Source12
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.L2Tail`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source13


/-!
# Tail controls from an L² approximation

Reusable Markov and uniform-integrability estimates for a family
`Wₜ = qₜ + zₜ`, where `qₜ` is `o(sₜ)` in L² and `zₜ` is dominated by
`sₜ g`.  The five declarations mirror the five estimates used in the
population log-likelihood Taylor remainder.
-/

open MeasureTheory Filter Topology Asymptotics

namespace AsymptoticStatistics.L2Utils

variable {α 𝒳 : Type*} [MeasurableSpace 𝒳]

set_option linter.unusedVariables false in
/-- Markov control: vanishing second moment makes every fixed `|W|` tail have
vanishing probability. -/
lemma l2_markov_tail_tendsto
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W : α → 𝒳 → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (hW_sq_zero : Tendsto (fun t => ∫ x, W t x ^ 2 ∂P) l (𝓝 0))
    (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun t => P {x | delta ≤ |W t x|}) l (𝓝 0) := by
  have hu : Tendsto
      (fun t => ENNReal.ofReal ((delta ^ 2)⁻¹ * ∫ x, W t x ^ 2 ∂P)) l (nhds 0) := by
    have ht : Tendsto (fun t => (delta ^ 2)⁻¹ * ∫ x, W t x ^ 2 ∂P) l (nhds 0) := by
      simpa using hW_sq_zero.const_mul (delta ^ 2)⁻¹
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using!
      (ENNReal.continuous_ofReal.tendsto 0).comp ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hW_mem] with t hwm
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun x => W t x ^ 2)
    (Eventually.of_forall fun _ => sq_nonneg _) hwm.integrable_sq (delta ^ 2)
  have hset : {x | delta ^ 2 ≤ W t x ^ 2} = {x | delta ≤ |W t x|} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    simpa [sq_abs] using (sq_le_sq₀ hdelta.le (abs_nonneg (W t x)))
  rw [hset] at hm
  have hreal : P.real {x | delta ≤ |W t x|} ≤
      (delta ^ 2)⁻¹ * ∫ x, W t x ^ 2 ∂P := by
    have hd2 : 0 < delta ^ 2 := sq_pos_of_pos hdelta
    calc
      P.real {x | delta ≤ |W t x|} ≤
          (∫ x, W t x ^ 2 ∂P) / delta ^ 2 :=
        (le_div_iff₀ hd2).2 (by simpa [mul_comm] using hm)
      _ = (delta ^ 2)⁻¹ * ∫ x, W t x ^ 2 ∂P := by rw [div_eq_inv_mul]
  rw [← ENNReal.toReal_le_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal]
  · simpa [measureReal_def] using hreal
  · exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (integral_nonneg fun _ => sq_nonneg _)

set_option linter.unusedVariables false in
/-- The square tail is `o(s²)` when `W = q + z`, the approximation error
has `o(s²)` squared norm, and `z² ≤ s² g` for an integrable envelope. -/
lemma l2_square_tail_isLittleO
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W q z : α → 𝒳 → ℝ) (s : α → ℝ) (g : 𝒳 → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (hq_mem : ∀ᶠ t in l, MemLp (q t) 2 P)
    (hqO : (fun t => ∫ x, q t x ^ 2 ∂P) =o[l] (fun t => s t ^ 2))
    (hg : Integrable g P)
    (hg_nonneg : ∀ᵐ x ∂P, 0 ≤ g x)
    (hs_nonneg : ∀ t, 0 ≤ s t)
    (hdecomp : ∀ t x, W t x = q t x + z t x)
    (hz_sq_le : ∀ t x, z t x ^ 2 ≤ s t ^ 2 * g x)
    (delta : ℝ) (hdelta : 0 < delta)
    (htail_prob : Tendsto (fun t => P {x | delta ≤ |W t x|}) l (𝓝 0)) :
    (fun t => ∫ x in {x | delta ≤ |W t x|}, W t x ^ 2 ∂P)
      =o[l] (fun t => s t ^ 2) := by
  let B : α → Set 𝒳 := fun t => {x | delta ≤ |W t x|}
  have hgtail : Tendsto (fun t => ∫ x in B t, g x ∂P) l (nhds 0) := by
    apply hg.tendsto_setIntegral_nhds_zero
    simpa only [Function.comp_apply, B] using! htail_prob
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hqbd := (Asymptotics.isLittleO_iff.mp hqO) (show 0 < c / 8 by positivity)
  have hgbd := hgtail.eventually (Iio_mem_nhds (show 0 < c / 8 by positivity))
  filter_upwards [hW_mem, hq_mem, hqbd, hgbd] with t hwm hqm hqbd hgbd
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hqbd ⊢
  have hmajor : IntegrableOn
      (fun x => 2 * q t x ^ 2 + 2 * (s t ^ 2 * g x)) (B t) P :=
    ((hqm.integrable_sq.const_mul 2).add
      ((hg.const_mul (s t ^ 2)).const_mul 2)).integrableOn
  have hle : ∫ x in B t, W t x ^ 2 ∂P ≤
      2 * (∫ x, q t x ^ 2 ∂P) + 2 * (s t ^ 2 * ∫ x in B t, g x ∂P) := by
    calc
      ∫ x in B t, W t x ^ 2 ∂P ≤
          ∫ x in B t, 2 * q t x ^ 2 + 2 * (s t ^ 2 * g x) ∂P := by
        refine setIntegral_mono_ae_restrict hwm.integrable_sq.integrableOn hmajor ?_
        filter_upwards with x
        calc
          W t x ^ 2 = (q t x + z t x) ^ 2 := by rw [hdecomp]
          _ ≤ 2 * q t x ^ 2 + 2 * z t x ^ 2 := sq_add_le_two_mul_sq _ _
          _ ≤ 2 * q t x ^ 2 + 2 * (s t ^ 2 * g x) := by
            gcongr
            exact hz_sq_le t x
      _ = 2 * (∫ x in B t, q t x ^ 2 ∂P) +
          2 * (s t ^ 2 * ∫ x in B t, g x ∂P) := by
        have h₁ : IntegrableOn (fun x => 2 * q t x ^ 2) (B t) P :=
          (hqm.integrable_sq.const_mul 2).integrableOn
        have h₂ : IntegrableOn (fun x => 2 * (s t ^ 2 * g x)) (B t) P :=
          ((hg.const_mul (s t ^ 2)).const_mul 2).integrableOn
        rw [integral_add h₁ h₂, integral_const_mul, integral_const_mul,
          integral_const_mul]
      _ ≤ 2 * (∫ x, q t x ^ 2 ∂P) +
          2 * (s t ^ 2 * ∫ x in B t, g x ∂P) := by
        have hqle := setIntegral_le_integral (s := B t) hqm.integrable_sq
          (Eventually.of_forall fun _ => sq_nonneg _)
        nlinarith
  have hprod : s t ^ 2 * ∫ x in B t, g x ∂P ≤ s t ^ 2 * (c / 8) :=
    mul_le_mul_of_nonneg_left (le_of_lt hgbd) (sq_nonneg _)
  exact hle.trans (by nlinarith [sq_nonneg (s t), hs_nonneg t])

/-- A positive threshold converts an `o(s²)` square-tail bound into the
same rate for the real-valued tail probability. -/
lemma l2_tail_measureReal_isLittleO
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W : α → 𝒳 → ℝ) (s : α → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (delta : ℝ) (hdelta : 0 < delta)
    (hW_tail : (fun t => ∫ x in {x | delta ≤ |W t x|}, W t x ^ 2 ∂P)
      =o[l] (fun t => s t ^ 2)) :
    (fun t => P.real {x | delta ≤ |W t x|}) =o[l] (fun t => s t ^ 2) := by
  let B : α → Set 𝒳 := fun t => {x | delta ≤ |W t x|}
  have hBmeas (t : α) : MeasurableSet (B t) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (hW_meas t))
  have hbound : (fun t => P.real (B t)) =O[l]
      (fun t => ∫ x in B t, W t x ^ 2 ∂P) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨(delta ^ 2)⁻¹, ?_⟩
    filter_upwards [hW_mem] with t hwm
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    have hm : delta ^ 2 * P.real (B t) ≤ ∫ x in B t, W t x ^ 2 ∂P := by
      have hcint : IntegrableOn (fun _ : 𝒳 => delta ^ 2) (B t) P :=
        (integrable_const (delta ^ 2)).integrableOn
      have hwint : IntegrableOn (fun x => W t x ^ 2) (B t) P :=
        hwm.integrable_sq.integrableOn
      have hpt : ∀ᵐ x ∂P.restrict (B t), delta ^ 2 ≤ W t x ^ 2 := by
        filter_upwards [ae_restrict_mem (hBmeas t)] with x hx
        exact ((sq_le_sq₀ hdelta.le (abs_nonneg _)).2 hx).trans_eq (sq_abs _)
      have := setIntegral_mono_ae_restrict hcint hwint hpt
      simpa [setIntegral_const, smul_eq_mul, mul_comm] using this
    have hd2 : 0 < delta ^ 2 := sq_pos_of_pos hdelta
    calc
      P.real (B t) ≤ (delta ^ 2)⁻¹ * (∫ x in B t, W t x ^ 2 ∂P) := by
        rw [← div_eq_inv_mul]
        exact (le_div_iff₀ hd2).2 (by simpa [mul_comm] using hm)
      _ = _ := rfl
  apply hbound.trans_isLittleO
  simpa only [B] using hW_tail

set_option linter.unusedVariables false in
/-- L² uniform integrability of an envelope, combined with an `o(s²)` tail
probability, controls `s · ∫_tail |m|` at order `o(s²)`. -/
lemma l2_envelope_tail_isLittleO
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W : α → 𝒳 → ℝ) (s : α → ℝ) (m : 𝒳 → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hm : MemLp m 2 P)
    (hs_nonneg : ∀ t, 0 ≤ s t)
    (delta : ℝ) (hdelta : 0 < delta)
    (htail_prob : Tendsto (fun t => P {x | delta ≤ |W t x|}) l (𝓝 0))
    (htail_rate : (fun t => P.real {x | delta ≤ |W t x|})
      =o[l] (fun t => s t ^ 2)) :
    (fun t => s t * ∫ x in {x | delta ≤ |W t x|}, |m x| ∂P)
      =o[l] (fun t => s t ^ 2) := by
  let B : α → Set 𝒳 := fun t => {x | delta ≤ |W t x|}
  have hBmeas (t : α) : MeasurableSet (B t) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (hW_meas t))
  let A : α → ℝ := fun t => ∫ x in B t, |m x| ^ 2 ∂P
  let Q : α → ℝ := fun t => P.real (B t)
  have hm2 : Integrable (fun x => |m x| ^ 2) P := by
    simpa [sq_abs] using hm.integrable_sq
  have hA0 : Tendsto A l (nhds 0) :=
    hm2.tendsto_setIntegral_nhds_zero (by
      simpa only [Function.comp_apply, B] using! htail_prob)
  have hAO : A =o[l] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 hA0
  have hQO : Q =o[l] (fun t => s t ^ 2) := by
    simpa only [Q, B] using htail_rate
  have hAs : (fun t => Real.sqrt (A t)) =o[l] (fun _ => (1 : ℝ)) := by
    convert! hAO.sqrt (Eventually.of_forall fun _ => zero_le_one) using 1
    simp
  have hQs : (fun t => Real.sqrt (Q t)) =o[l] s := by
    convert! hQO.sqrt (Eventually.of_forall fun t => sq_nonneg (s t)) using 1
    funext t
    exact (Real.sqrt_sq (hs_nonneg t)).symm
  have hprod : (fun t => Real.sqrt (A t) * Real.sqrt (Q t)) =o[l] s := by
    convert! hAs.mul hQs using 1
    simp
  have hcross : (fun t => ∫ x in B t, |m x| ∂P) =O[l]
      (fun t => Real.sqrt (A t) * Real.sqrt (Q t)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, Eventually.of_forall fun t => ?_⟩
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    let a : 𝒳 → ℝ := (B t).indicator fun x => |m x|
    let b : 𝒳 → ℝ := (B t).indicator fun _ => 1
    have ha : MemLp a 2 P := hm.norm.indicator (hBmeas t)
    have hb : MemLp b 2 P := memLp_indicator_const 2 (hBmeas t) 1
      (Or.inr (measure_ne_top P _))
    have hcs := abs_integral_mul_le_sqrt_integral_sq P ha hb
    have hab : (∫ x, a x * b x ∂P) = ∫ x in B t, |m x| ∂P := by
      rw [← integral_indicator (hBmeas t)]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ B t <;> simp [a, b, hx]
    have ha2 : (∫ x, a x ^ 2 ∂P) = A t := by
      change (∫ x, a x ^ 2 ∂P) = ∫ x in B t, |m x| ^ 2 ∂P
      rw [← integral_indicator (hBmeas t)]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ B t <;> simp [a, hx]
    have hb2 : (∫ x, b x ^ 2 ∂P) = Q t := by
      change (∫ x, b x ^ 2 ∂P) = P.real (B t)
      rw [show (fun x => b x ^ 2) = (B t).indicator (fun _ => (1 : ℝ)) by
        funext x
        by_cases hx : x ∈ B t <;> simp [b, hx]]
      simpa only [Pi.one_apply] using! (integral_indicator_one (μ := P) (hBmeas t))
    simpa [hab, ha2, hb2] using hcs
  have hcO := hcross.trans_isLittleO hprod
  have hmul := (Asymptotics.isBigO_refl s l).mul_isLittleO hcO
  convert! hmul using 1
  funext t
  ring

/-- On a tail above a positive threshold, the first absolute moment is
bounded by a constant times the second moment. -/
lemma l2_abs_tail_isLittleO
    (l : Filter α) (P : Measure 𝒳)
    (W : α → 𝒳 → ℝ) (s : α → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (delta : ℝ) (hdelta : 0 < delta)
    (hW_tail : (fun t => ∫ x in {x | delta ≤ |W t x|}, W t x ^ 2 ∂P)
      =o[l] (fun t => s t ^ 2)) :
    (fun t => ∫ x in {x | delta ≤ |W t x|}, |W t x| ∂P)
      =o[l] (fun t => s t ^ 2) := by
  let B : α → Set 𝒳 := fun t => {x | delta ≤ |W t x|}
  have hBmeas (t : α) : MeasurableSet (B t) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (hW_meas t))
  have hbound : (fun t => ∫ x in B t, |W t x| ∂P) =O[l]
      (fun t => ∫ x in B t, W t x ^ 2 ∂P) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨delta⁻¹, ?_⟩
    filter_upwards [hW_mem] with t hwm
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    have hpoint : ∀ᵐ x ∂P.restrict (B t), |W t x| ≤ delta⁻¹ * W t x ^ 2 := by
      filter_upwards [ae_restrict_mem (hBmeas t)] with x hx
      have habs := abs_nonneg (W t x)
      have hmul := mul_le_mul_of_nonneg_right hx habs
      rw [← sq_abs]
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hdelta).2 (by nlinarith)
    have habs_int : IntegrableOn (fun x => |W t x|) (B t) P :=
      Integrable.mono' (hwm.integrable_sq.const_mul delta⁻¹).integrableOn
        ((continuous_abs.measurable.comp (hW_meas t)).aestronglyMeasurable.restrict) (by
          filter_upwards [hpoint] with x hx
          simpa only [Real.norm_eq_abs, abs_abs] using hx)
    have hle : ∫ x in B t, |W t x| ∂P ≤
        ∫ x in B t, delta⁻¹ * W t x ^ 2 ∂P := by
      refine setIntegral_mono_ae_restrict
        habs_int
        (hwm.integrable_sq.const_mul delta⁻¹).integrableOn ?_
      exact hpoint
    rw [integral_const_mul] at hle
    exact hle
  apply hbound.trans_isLittleO
  simpa only [B] using hW_tail

/-- The complete five-part L² tail package used by the integrated logarithmic
Taylor remainder. -/
lemma l2_tail_controls_of_approx
    (l : Filter α) (P : Measure 𝒳) [IsFiniteMeasure P]
    (W q z : α → 𝒳 → ℝ) (s : α → ℝ) (g : 𝒳 → ℝ)
    (hW_meas : ∀ t, Measurable (W t))
    (hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P)
    (hW_sq_zero : Tendsto (fun t => ∫ x, W t x ^ 2 ∂P) l (𝓝 0))
    (hq_mem : ∀ᶠ t in l, MemLp (q t) 2 P)
    (hqO : (fun t => ∫ x, q t x ^ 2 ∂P) =o[l] (fun t => s t ^ 2))
    (hg : Integrable g P) (hg_nonneg : ∀ᵐ x ∂P, 0 ≤ g x)
    (hs_nonneg : ∀ t, 0 ≤ s t)
    (hdecomp : ∀ t x, W t x = q t x + z t x)
    (hz_sq_le : ∀ t x, z t x ^ 2 ≤ s t ^ 2 * g x)
    (m : 𝒳 → ℝ) (hm : MemLp m 2 P)
    (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun t => P {x | delta ≤ |W t x|}) l (𝓝 0) ∧
      (fun t => ∫ x in {x | delta ≤ |W t x|}, W t x ^ 2 ∂P)
        =o[l] (fun t => s t ^ 2) ∧
      (fun t => P.real {x | delta ≤ |W t x|}) =o[l] (fun t => s t ^ 2) ∧
      (fun t => s t * ∫ x in {x | delta ≤ |W t x|}, |m x| ∂P)
        =o[l] (fun t => s t ^ 2) ∧
      (fun t => ∫ x in {x | delta ≤ |W t x|}, |W t x| ∂P)
        =o[l] (fun t => s t ^ 2) := by
  have hprob := l2_markov_tail_tendsto l P W hW_meas hW_mem hW_sq_zero delta hdelta
  have hsq := l2_square_tail_isLittleO l P W q z s g hW_meas hW_mem hq_mem hqO hg
    hg_nonneg hs_nonneg hdecomp hz_sq_le delta hdelta hprob
  have hreal := l2_tail_measureReal_isLittleO l P W s hW_meas hW_mem delta hdelta hsq
  have henv := l2_envelope_tail_isLittleO l P W s m hW_meas hm hs_nonneg delta hdelta
    hprob hreal
  have habs := l2_abs_tail_isLittleO l P W s hW_meas hW_mem delta hdelta hsq
  exact ⟨hprob, hsq, hreal, henv, habs⟩

end AsymptoticStatistics.L2Utils

end GLP0011B3Source13
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.Core.NondominatedQMDProductComparison`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source14


/-! # Actual-likelihood product comparison for nondominated QMD paths -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace AsymptoticStatistics.Core.NondominatedQMDPath

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.ForMathlib.HellingerProduct
open AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

set_option linter.dupNamespace false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

namespace NondominatedQMDPath

/-- Baseline-absolutely-continuous part of a path law. -/
noncomputable def acPart (γ : NondominatedQMDPath P) (t : ℝ) : Measure Ω :=
  P.withDensity ((γ.curve t).rnDeriv P)

/-- Singular part of a path law relative to `P`; it may be nonzero. -/
noncomputable def singularPart (γ : NondominatedQMDPath P) (t : ℝ) : Measure Ω :=
  (γ.curve t).singularPart P

/-- Total singular mass; it is zero for a baseline-AC perturbation. -/
noncomputable def singularMass (γ : NondominatedQMDPath P) (t : ℝ) : ℝ≥0∞ :=
  γ.singularPart t Set.univ

/-- Baseline mass of the zero actual-likelihood event.  This is distinct
from `singularMass`, which measures a defect under the perturbed law. -/
noncomputable def baseZeroLikelihoodMass
    (γ : NondominatedQMDPath P) (t : ℝ) : ℝ≥0∞ :=
  P {ω | ((γ.curve t).rnDeriv P ω).toReal = 0}

/-- Actual RN likelihood of the all-AC part of the local product law. -/
noncomputable def acProductLikelihood
    (γ : NondominatedQMDPath P) (t : ℝ) (n : ℕ) : (Fin n → Ω) → ℝ≥0∞ :=
  fun X => ∏ i : Fin n, (γ.curve t).rnDeriv P (X i)

/-- Canonical-pairwise square-root QMD residual. -/
noncomputable def comparisonResidual
    (γ : NondominatedQMDPath P) (t : ℝ) : Ω → ℝ :=
  residualAgainst P (γ.curve t) (canonicalDominator P (γ.curve t))
    (γ.score : Ω → ℝ) t

private theorem comparisonResidual_aestronglyMeasurable
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) :
    AEStronglyMeasurable (γ.comparisonResidual t) (canonicalDominator P (γ.curve t)) := by
  let : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  let μ := canonicalDominator P (γ.curve t)
  let : SigmaFinite μ := by dsimp only [μ, canonicalDominator]; infer_instance
  have hPμ : P ≪ μ := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hw := (AsymptoticStatistics.ForMathlib.RnDerivSqrt.aestronglyMeasurable_sqrt_rnDeriv_mul_iff
    hPμ (γ.score : Ω → ℝ)).2 (Lp.aestronglyMeasurable γ.score.val)
  have hp := ((Measure.measurable_rnDeriv P μ).ennreal_toReal.sqrt).aestronglyMeasurable (μ := μ)
  have hq := ((Measure.measurable_rnDeriv (γ.curve t) μ).ennreal_toReal.sqrt).aestronglyMeasurable
      (μ := μ)
  have h := (hq.sub hp).sub (hw.const_mul (t / 2))
  convert! h using 1
  funext ω
  simp only [comparisonResidual, residualAgainst, Pi.sub_apply, μ]
  ring

/-- Lebesgue decomposition of a path law into singular and baseline-AC parts.

The proof uses Mathlib's Lebesgue decomposition with the probability-provided
sigma-finiteness instances. -/
theorem curve_eq_singularPart_add_acPart
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) :
    γ.curve t = γ.singularPart t + γ.acPart t := by
  let : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  exact Measure.haveLebesgueDecomposition_add (γ.curve t) P

/-- Singular mass is bounded by the squared canonical QMD residual norm.

On the zero-baseline-density set the score and baseline-root
terms vanish, leaving the perturbed square root. -/
theorem singularMass_le_residual_sq
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) :
    γ.singularMass t ≤
      eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) ^ 2 := by
  let : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  let μ := canonicalDominator P (γ.curve t)
  let : SigmaFinite μ := by
    dsimp only [μ, canonicalDominator]
    infer_instance
  let hsing := Measure.mutuallySingular_singularPart (γ.curve t) P
  let s := hsing.nullSetᶜ
  have hs : MeasurableSet s := hsing.measurableSet_nullSet.compl
  have hS : (γ.curve t).singularPart P = (γ.curve t).restrict s := by
    apply Measure.singularPart_eq_restrict
    · simpa only [s, compl_compl] using hsing.measure_nullSet
    · exact hsing.measure_compl_nullSet
  have hPμ : P ≪ μ := by
    exact (Measure.le_add_right le_rfl).absolutelyContinuous
  have hQμ : γ.curve t ≪ μ := by
    exact (Measure.le_add_left le_rfl).absolutelyContinuous
  have hPzero : P s = 0 := hsing.measure_compl_nullSet
  have hPint : ∫⁻ ω in s, P.rnDeriv μ ω ∂μ = 0 := by
    rw [Measure.setLIntegral_rnDeriv hPμ s, hPzero]
  have hpzero : P.rnDeriv μ =ᵐ[μ.restrict s] 0 := by
    exact (lintegral_eq_zero_iff'
      (Measure.measurable_rnDeriv P μ).aemeasurable.restrict).mp hPint
  have hpoint : ∀ᵐ ω ∂(μ.restrict s),
      (γ.curve t).rnDeriv μ ω ≤ ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hpzero,
      ae_restrict_of_ae (Measure.rnDeriv_ne_top (γ.curve t) μ)] with ω hp hq
    simp only [Pi.zero_apply] at hp
    have hp' : P.rnDeriv (canonicalDominator P (γ.curve t)) ω = 0 := by
      simpa only [μ] using hp
    have hq' : (γ.curve t).rnDeriv (canonicalDominator P (γ.curve t)) ω ≠ ⊤ := by
      simpa only [μ] using hq
    change (γ.curve t).rnDeriv (canonicalDominator P (γ.curve t)) ω ≤
      ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ)
    rw [comparisonResidual, residualAgainst, hp', ENNReal.toReal_zero,
      Real.sqrt_zero, mul_zero]
    simp only [sub_zero]
    rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hq']
  have hlin : γ.singularMass t ≤
      ∫⁻ ω, ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ := by
    rw [singularMass, singularPart, hS,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ← Measure.setLIntegral_rnDeriv hQμ s]
    exact (lintegral_mono_ae hpoint).trans (setLIntegral_le_lintegral s _)
  have hlin' : γ.singularMass t ≤
      ∫⁻ ω, ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ)
        ∂(canonicalDominator P (γ.curve t)) := by
    simpa only [μ] using hlin
  convert! hlin' using 1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (comparisonResidual_aestronglyMeasurable γ t (by positivity)),
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- QMD makes perturbed-law singular mass negligible at root-`n` scale.

The proof combines `singularMass_le_residual_sq` with `qmd_limit`. -/
theorem singular_mass_localScale_tendsto
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (n : ℝ≥0∞) *
      γ.singularMass (a * (Real.sqrt n)⁻¹)) atTop (nhds 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · have hz : (fun n : ℕ => (n : ℝ≥0∞) *
        γ.singularMass (0 * (Real.sqrt n)⁻¹)) = fun _ => 0 := by
      funext n
      simp [singularMass, singularPart, curve_at_zero]
    rw [hz]
    exact tendsto_const_nhds
  let u : ℕ → ℝ := fun n => a * (Real.sqrt n)⁻¹
  have hu_zero : Tendsto u atTop (nhds 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa only [u, mul_zero] using
      (tendsto_const_nhds.mul hsqrt.inv_tendsto_atTop :
        Tendsto (fun n : ℕ => a * (Real.sqrt n)⁻¹) atTop (nhds (a * 0)))
  have hu_pos : ∀ᶠ n : ℕ in atTop, 0 < u n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_pos ha (inv_pos.mpr (Real.sqrt_pos.mpr (by
      exact_mod_cast (show 0 < n by omega))))
  have hu_right : Tendsto u atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hu_zero, hu_pos⟩
  let r : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (γ.comparisonResidual (u n)) 2
      (canonicalDominator P (γ.curve (u n)))
  have hquot : Tendsto (fun n => r n / ENNReal.ofReal (u n))
      atTop (nhds 0) := by
    simpa only [IsRightQMD, comparisonResidual, Function.comp_apply, r] using!
      ((isRightQMD_iff_eLpNorm γ.curve γ.curve_isProbability
        (Lp.aestronglyMeasurable γ.score.val)).1 γ.qmd_limit).comp hu_right
  have henvelope : Tendsto
      (fun n => ENNReal.ofReal a ^ 2 *
        (r n / ENNReal.ofReal (u n)) ^ 2) atTop (nhds 0) := by
    have hsq : Tendsto (fun n =>
        (r n / ENNReal.ofReal (u n)) * (r n / ENNReal.ofReal (u n)))
        atTop (nhds 0) := by
      simpa only [zero_mul] using
        ENNReal.Tendsto.mul hquot (Or.inr ENNReal.zero_ne_top) hquot
          (Or.inr ENNReal.zero_ne_top)
    simpa only [pow_two, mul_zero] using ENNReal.Tendsto.const_mul hsq
      (Or.inr (by simp : ENNReal.ofReal a ^ 2 ≠ ⊤))
  have hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ≥0∞) * ENNReal.ofReal (u n) ^ 2 = ENNReal.ofReal a ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := by omega
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos_nat
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hreal : (n : ℝ) * (u n) ^ 2 = a ^ 2 := by
      dsimp only [u]
      rw [mul_pow]
      calc
        (n : ℝ) * (a ^ 2 * (Real.sqrt n)⁻¹ ^ 2) =
            a ^ 2 * ((n : ℝ) * (Real.sqrt n)⁻¹ ^ 2) := by ring
        _ = a ^ 2 := by
          have hfactor : (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 = 1 := by
            calc
              (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 =
                  (n : ℝ) / Real.sqrt n ^ 2 := by
                    rw [inv_pow, div_eq_mul_inv]
              _ = (n : ℝ) / n := by rw [Real.sq_sqrt hnpos.le]
              _ = 1 := div_self hnpos.ne'
          rw [hfactor, mul_one]
    calc
      (n : ℝ≥0∞) * ENNReal.ofReal (u n) ^ 2 =
          ENNReal.ofReal ((n : ℝ) * (u n) ^ 2) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
              ENNReal.ofReal_pow (show 0 ≤ u n by positivity)]
      _ = ENNReal.ofReal (a ^ 2) := by rw [hreal]
      _ = ENNReal.ofReal a ^ 2 := ENNReal.ofReal_pow ha.le 2
  have hupper : ∀ᶠ n : ℕ in atTop,
      (n : ℝ≥0∞) * γ.singularMass (u n) ≤
        ENNReal.ofReal a ^ 2 * (r n / ENNReal.ofReal (u n)) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1, hscale] with n hn hscale_n
    have hupos : 0 < u n := mul_pos ha (inv_pos.mpr
      (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))))
    have hd_ne : ENNReal.ofReal (u n) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hupos
    have hd_top : ENNReal.ofReal (u n) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      (n : ℝ≥0∞) * γ.singularMass (u n) ≤
          (n : ℝ≥0∞) * r n ^ 2 :=
        mul_le_mul_right (γ.singularMass_le_residual_sq (u n) hupos.le) _
      _ = ((n : ℝ≥0∞) * ENNReal.ofReal (u n) ^ 2) *
          (r n / ENNReal.ofReal (u n)) ^ 2 := by
        have hcancel : ENNReal.ofReal (u n) ^ 2 *
            (r n / ENNReal.ofReal (u n)) ^ 2 = r n ^ 2 := by
          rw [← mul_pow, ENNReal.mul_div_cancel hd_ne hd_top]
        calc
          (n : ℝ≥0∞) * r n ^ 2 =
              (n : ℝ≥0∞) * (ENNReal.ofReal (u n) ^ 2 *
                (r n / ENNReal.ofReal (u n)) ^ 2) := by rw [hcancel]
          _ = ((n : ℝ≥0∞) * ENNReal.ofReal (u n) ^ 2) *
              (r n / ENNReal.ofReal (u n)) ^ 2 := by
                rw [mul_assoc]
      _ = ENNReal.ofReal a ^ 2 *
          (r n / ENNReal.ofReal (u n)) ^ 2 := by rw [hscale_n]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds henvelope
    (Filter.Eventually.of_forall fun n => bot_le)
    hupper

/-- The baseline zero-likelihood mass is `o(t²)` from the right.

The proof uses the one-observation Hellinger/QMD inequality on the event where
the actual RN derivative vanishes. This estimate is distinct from
the singular-mass estimate. -/
theorem baseZeroLikelihoodMass_isLittleO
    (γ : NondominatedQMDPath P) :
    (fun t : ℝ => (γ.baseZeroLikelihoodMass t).toReal)
      =o[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ => t ^ 2) := by
  classical
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let g : Ω → ℝ := γ.score
  have hg_meas : Measurable g :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P)).measurable
  have hg_mem : MemLp g 2 P := Lp.memLp _
  have hg_sq : Integrable (fun ω => g ω ^ 2) P := hg_mem.integrable_sq
  have ht_zero : Tendsto (fun t : ℝ => t) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have htail : (fun t : ℝ => P.real {ω | 1 ≤ |t * g ω|})
      =o[l] (fun t : ℝ => t ^ 2) := by
    let W : ℝ → Ω → ℝ := fun t ω => t * g ω
    have hW_meas : ∀ t, Measurable (W t) :=
      fun _ => measurable_const.mul hg_meas
    have hW_mem : ∀ᶠ t in l, MemLp (W t) 2 P :=
      Filter.Eventually.of_forall fun t => hg_mem.const_mul t
    have hW_sq_zero : Tendsto (fun t => ∫ ω, W t ω ^ 2 ∂P) l (nhds 0) := by
      have hmain := (ht_zero.pow 2).mul_const (∫ ω, g ω ^ 2 ∂P)
      have hint : (fun t : ℝ => ∫ ω, W t ω ^ 2 ∂P) =
          fun t => t ^ 2 * ∫ ω, g ω ^ 2 ∂P := by
        funext t
        simp only [W, mul_pow, MeasureTheory.integral_const_mul]
      rw [hint]
      simpa using hmain
    have hqO : (fun t : ℝ => ∫ ω, (0 : ℝ) ^ 2 ∂P)
        =o[l] (fun t => |t| ^ 2) := by
      simp
    have hpack := AsymptoticStatistics.L2Utils.l2_tail_controls_of_approx
      l P W (fun _ _ => 0) W (fun t => |t|) (fun ω => g ω ^ 2)
      hW_meas hW_mem hW_sq_zero
      (Filter.Eventually.of_forall fun _ => MemLp.zero)
      hqO
      hg_sq (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (fun _ => abs_nonneg _) (fun _ _ => by simp)
      (fun t ω => by
        change (t * g ω) ^ 2 ≤ |t| ^ 2 * g ω ^ 2
        rw [mul_pow, sq_abs])
      (fun _ => 0) MemLp.zero 1 zero_lt_one
    simpa only [W, l, sq_abs] using hpack.2.2.1
  have hmass : ∀ t : ℝ, 0 < t →
      γ.baseZeroLikelihoodMass t ≤
        P {ω | 1 ≤ |t * g ω|} +
          4 * eLpNorm (γ.comparisonResidual t) 2
            (canonicalDominator P (γ.curve t)) ^ 2 := by
    intro t ht
    let : IsProbabilityMeasure (γ.curve t) :=
      γ.curve_isProbability t ht.le
    let μ := canonicalDominator P (γ.curve t)
    let p : Ω → ℝ≥0∞ := P.rnDeriv μ
    let qP : Ω → ℝ≥0∞ := (γ.curve t).rnDeriv P
    let q : Ω → ℝ≥0∞ := (γ.curve t).rnDeriv μ
    let Z : Set Ω := {ω | (qP ω).toReal = 0}
    let B : Set Ω := {ω | 1 ≤ |t * g ω|}
    let A : Set Ω := Z \ B
    let : SigmaFinite μ := by
      dsimp only [μ, canonicalDominator]
      infer_instance
    have hPμ : P ≪ μ := by
      exact (Measure.le_add_right le_rfl).absolutelyContinuous
    have hZ : MeasurableSet Z := by
      change MeasurableSet ((fun ω => ((γ.curve t).rnDeriv P ω).toReal) ⁻¹' {0})
      exact (Measure.measurable_rnDeriv (γ.curve t) P).ennreal_toReal
        (measurableSet_singleton 0)
    have hB : MeasurableSet B := by
      exact measurableSet_le measurable_const ((measurable_const.mul hg_meas).abs)
    have hA : MeasurableSet A := hZ.diff hB
    have hchainP :
        (γ.curve t).rnDeriv P * P.rnDeriv μ
          =ᵐ[P] (γ.curve t).rnDeriv μ :=
      Measure.rnDeriv_mul_rnDeriv' (μ := γ.curve t) (ν := P)
        (κ := μ) hPμ
    have hP_eq : μ.withDensity (P.rnDeriv μ) = P :=
      Measure.withDensity_rnDeriv_eq P μ hPμ
    have hchainP' :
        (γ.curve t).rnDeriv P * P.rnDeriv μ
          =ᵐ[μ.withDensity (P.rnDeriv μ)] (γ.curve t).rnDeriv μ := by
      simpa only [hP_eq] using hchainP
    have hchainμ : ∀ᵐ ω ∂μ, p ω ≠ 0 →
        qP ω * p ω = q ω := by
      simpa only [p, qP, q] using!
        (ae_withDensity_iff (Measure.measurable_rnDeriv P μ)).mp hchainP'
    have hqPfinP : ∀ᵐ ω ∂P, qP ω ≠ ⊤ := by
      simpa only [qP] using Measure.rnDeriv_ne_top (γ.curve t) P
    have hqPfinP' : ∀ᵐ ω ∂(μ.withDensity (P.rnDeriv μ)), qP ω ≠ ⊤ := by
      simpa only [hP_eq] using hqPfinP
    have hqPfinμ : ∀ᵐ ω ∂μ, p ω ≠ 0 → qP ω ≠ ⊤ := by
      simpa only [p] using
        (ae_withDensity_iff (Measure.measurable_rnDeriv P μ)).mp hqPfinP'
    have hpfin : ∀ᵐ ω ∂μ, p ω ≠ ⊤ := by
      simpa only [p] using Measure.rnDeriv_ne_top P μ
    have hpoint : ∀ᵐ ω ∂(μ.restrict A),
        p ω ≤ 4 * ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) := by
      filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae hchainμ,
        ae_restrict_of_ae hqPfinμ, ae_restrict_of_ae hpfin] with
        ω hω hchain hqPfin hpfinω
      by_cases hpzero : p ω = 0
      · simp [hpzero]
      have hqPzero : qP ω = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (qP ω)).mp hω.1 with hzero | htop
        · exact hzero
        · exact (hqPfin hpzero htop).elim
      have hqzero : q ω = 0 := by
        have hc := hchain hpzero
        simpa only [hqPzero, zero_mul] using hc.symm
      have hgood : |t * g ω| < 1 := lt_of_not_ge hω.2
      have hcoef : (1 / 2 : ℝ) ≤ 1 + t * g ω / 2 := by
        rw [abs_lt] at hgood
        linarith
      have hres : γ.comparisonResidual t ω =
          -(1 + t * g ω / 2) * Real.sqrt (p ω).toReal := by
        simp only [comparisonResidual, residualAgainst, q, p] at hqzero ⊢
        rw [hqzero, ENNReal.toReal_zero, Real.sqrt_zero, zero_sub]
        ring
      have hreal : (p ω).toReal ≤
          4 * (γ.comparisonResidual t ω) ^ 2 := by
        rw [hres]
        have hsqrt := Real.sqrt_nonneg (p ω).toReal
        have hsquare : Real.sqrt (p ω).toReal ^ 2 = (p ω).toReal :=
          Real.sq_sqrt ENNReal.toReal_nonneg
        have hcoef_nonneg : 0 ≤ 1 + t * g ω / 2 := by linarith
        have hmul : (1 / 2 : ℝ) * Real.sqrt (p ω).toReal ≤
            (1 + t * g ω / 2) * Real.sqrt (p ω).toReal :=
          mul_le_mul_of_nonneg_right hcoef hsqrt
        have hsqmul : ((1 / 2 : ℝ) * Real.sqrt (p ω).toReal) ^ 2 ≤
            ((1 + t * g ω / 2) * Real.sqrt (p ω).toReal) ^ 2 :=
          (sq_le_sq₀ (mul_nonneg (by norm_num) hsqrt)
            (mul_nonneg hcoef_nonneg hsqrt)).2 hmul
        nlinarith
      have hrespow : ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
        rw [ENNReal.rpow_two]
        simpa only [pow_two] using
          ENNReal.mul_ne_top (enorm_ne_top :
            ‖γ.comparisonResidual t ω‖ₑ ≠ ⊤) enorm_ne_top
      have hfour : (4 : ℝ≥0∞) *
          ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) hrespow
      rw [← ENNReal.toReal_le_toReal hpfinω hfour]
      simpa only [ENNReal.rpow_two, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
        ENNReal.toReal_pow, toReal_enorm, Real.norm_eq_abs, sq_abs] using hreal
    have hnormsq :
        eLpNorm (γ.comparisonResidual t) 2 μ ^ 2 =
          ∫⁻ ω, ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (comparisonResidual_aestronglyMeasurable γ t (by positivity)),
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num [μ]
    have hPA : P A ≤ 4 *
        eLpNorm (γ.comparisonResidual t) 2 μ ^ 2 := by
      rw [← Measure.setLIntegral_rnDeriv hPμ A]
      calc
        (∫⁻ ω in A, p ω ∂μ) ≤
            ∫⁻ ω in A, 4 * ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_mono_ae hpoint
        _ = 4 * ∫⁻ ω in A,
            ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ := by
              rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
        _ ≤ 4 * ∫⁻ ω,
            ‖γ.comparisonResidual t ω‖ₑ ^ (2 : ℝ) ∂μ :=
          mul_le_mul_right (setLIntegral_le_lintegral A _) _
        _ = 4 * eLpNorm (γ.comparisonResidual t) 2 μ ^ 2 := by
          rw [hnormsq]
    have hZA : P Z ≤ P B + P A := by
      calc
        P Z ≤ P (B ∪ A) := measure_mono (by
          intro ω hω
          by_cases hωB : ω ∈ B
          · exact Set.mem_union_left A hωB
          · exact Set.mem_union_right B ⟨hω, hωB⟩)
        _ ≤ P B + P A := measure_union_le B A
    have hZA' : P Z ≤ P B + 4 *
        eLpNorm (γ.comparisonResidual t) 2 μ ^ 2 :=
      hZA.trans (by gcongr)
    simpa only [baseZeroLikelihoodMass, Z, qP, B, g, μ] using hZA'
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have htail_bound := (Asymptotics.isLittleO_iff.mp htail) (half_pos hc)
  have hqmd := (isRightQMD_iff_eLpNorm γ.curve γ.curve_isProbability
    (Lp.aestronglyMeasurable γ.score.val)).1 γ.qmd_limit
  have hqmd_real :
      Tendsto (fun t : ℝ =>
        (eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal)
        l (nhds 0) := by
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hqmd
  have hqmd_bound : ∀ᶠ t : ℝ in l,
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal ^ 2 ≤
          c / 8 := by
    have hsqrt : 0 < Real.sqrt (c / 8) := Real.sqrt_pos.mpr (by positivity)
    have hevent := hqmd_real.eventually (Iio_mem_nhds hsqrt)
    filter_upwards [hevent] with t ht
    have hnonneg : 0 ≤
        (eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal :=
      ENNReal.toReal_nonneg
    nlinarith [Real.sq_sqrt (show 0 ≤ c / 8 by positivity)]
  have hqmd_lt : ∀ᶠ t : ℝ in l,
      eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t < 1 :=
    hqmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [self_mem_nhdsWithin, htail_bound, hqmd_bound, hqmd_lt] with
      t ht htail_t hqmd_t hqmd_lt_t
  have htpos : 0 < t := ht
  have hmass_t := hmass t htpos
  have hnorm_fin : eLpNorm (γ.comparisonResidual t) 2
      (canonicalDominator P (γ.curve t)) ≠ ⊤ := by
    intro htop
    have hden_top : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
    have hfalse : (⊤ : ℝ≥0∞) < 1 := by
      simpa only [htop, ENNReal.top_div, ite_eq_right hden_top] using hqmd_lt_t
    exact (not_lt_of_ge le_top hfalse).elim
  have hmass_real : (γ.baseZeroLikelihoodMass t).toReal ≤
      (P {ω | 1 ≤ |t * g ω|}).toReal +
        4 * (eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t))).toReal ^ 2 := by
    have hnormpow : eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) ^ 2 ≠ ⊤ := by
      simpa only [pow_two] using ENNReal.mul_ne_top hnorm_fin hnorm_fin
    have hfour : (4 : ℝ≥0∞) * eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) ^ 2 ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hnormpow
    have hrhs : P {ω | 1 ≤ |t * g ω|} +
        4 * eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t)) ^ 2 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, hfour⟩
    have hmono := ENNReal.toReal_mono hrhs hmass_t
    rw [ENNReal.toReal_add (measure_ne_top _ _) hfour,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_pow] at hmono
    exact hmono
  have hquot_eq :
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal =
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal / t := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal htpos.le]
  rw [hquot_eq] at hqmd_t
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at htail_t
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  have hres_bound : 4 *
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal ^ 2 ≤
      c / 2 * t ^ 2 := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
    rw [div_pow] at hqmd_t
    have hscaled := (div_le_iff₀ ht2).mp hqmd_t
    nlinarith
  calc
    (γ.baseZeroLikelihoodMass t).toReal ≤
        (P {ω | 1 ≤ |t * g ω|}).toReal +
          4 * (eLpNorm (γ.comparisonResidual t) 2
            (canonicalDominator P (γ.curve t))).toReal ^ 2 := hmass_real
    _ ≤ c / 2 * t ^ 2 + c / 2 * t ^ 2 :=
      add_le_add htail_t hres_bound
    _ = c * t ^ 2 := by ring

/-- Consequently an `n`-sample has vanishing baseline probability of any
zero local likelihood factor.

For `a > 0`, specialize `baseZeroLikelihoodMass_isLittleO` at
`a/sqrt n` and multiply by `n`; the case `a = 0` follows from `curve_at_zero`. -/
theorem base_zeroLikelihood_localScale_tendsto
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (n : ℝ≥0∞) *
      γ.baseZeroLikelihoodMass (a * (Real.sqrt n)⁻¹)) atTop (nhds 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · have hmass0 : γ.baseZeroLikelihoodMass 0 = 0 := by
      rw [baseZeroLikelihoodMass, curve_at_zero]
      have hset :
          {ω | (P.rnDeriv P ω).toReal = 0} =ᵐ[P] (∅ : Set Ω) := by
        filter_upwards [Measure.rnDeriv_self P] with ω hω
        change ((P.rnDeriv P ω).toReal = 0) = False
        rw [hω]
        norm_num
      simpa using measure_congr hset
    simp only [zero_mul, hmass0, mul_zero]
    exact tendsto_const_nhds
  let u : ℕ → ℝ := fun n => a * (Real.sqrt n)⁻¹
  have hu_zero : Tendsto u atTop (nhds 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa only [u, mul_zero] using
      (tendsto_const_nhds.mul hsqrt.inv_tendsto_atTop :
        Tendsto (fun n : ℕ => a * (Real.sqrt n)⁻¹) atTop (nhds (a * 0)))
  have hu_pos : ∀ᶠ n : ℕ in atTop, 0 < u n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_pos ha (inv_pos.mpr (Real.sqrt_pos.mpr (by
      exact_mod_cast (show 0 < n by omega))))
  have hu_right : Tendsto u atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hu_zero, hu_pos⟩
  have hsmall : (fun n => (γ.baseZeroLikelihoodMass (u n)).toReal)
      =o[atTop] (fun n => u n ^ 2) := by
    simpa only [Function.comp_apply] using!
      γ.baseZeroLikelihoodMass_isLittleO.comp_tendsto hu_right
  have hmul : (fun n : ℕ => (n : ℝ) *
      (γ.baseZeroLikelihoodMass (u n)).toReal)
      =o[atTop] (fun n => (n : ℝ) * u n ^ 2) :=
    (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO hsmall
  have hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * u n ^ 2 = a ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := by omega
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos_nat
    dsimp only [u]
    rw [mul_pow]
    calc
      (n : ℝ) * (a ^ 2 * (Real.sqrt n)⁻¹ ^ 2) =
          a ^ 2 * ((n : ℝ) * (Real.sqrt n)⁻¹ ^ 2) := by ring
      _ = a ^ 2 := by
        have hfactor : (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 = 1 := by
          calc
            (n : ℝ) * (Real.sqrt n)⁻¹ ^ 2 =
                (n : ℝ) / Real.sqrt n ^ 2 := by
                  rw [inv_pow, div_eq_mul_inv]
            _ = (n : ℝ) / n := by rw [Real.sq_sqrt hnpos.le]
            _ = 1 := div_self hnpos.ne'
        rw [hfactor, mul_one]
  have hscaleO : (fun n : ℕ => (n : ℝ) * u n ^ 2)
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (Filter.EventuallyEq.isBigO hscale).trans
      (Asymptotics.isBigO_const_one ℝ (a ^ 2) atTop)
  have hreal : Tendsto (fun n : ℕ => (n : ℝ) *
      (γ.baseZeroLikelihoodMass (u n)).toReal) atTop (nhds 0) := by
    exact (Asymptotics.isLittleO_one_iff ℝ).mp
      (hmul.trans_isBigO hscaleO)
  apply (ENNReal.tendsto_toReal_zero_iff (fun n => by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
      (measure_ne_top P _))).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, u] using hreal

/-- At a nonnegative path parameter, the product of AC parts is the baseline
product weighted by the actual product likelihood.

The proof uses `ht` to obtain the path-law probability/sigma-finiteness
instance, then apply finite-product induction and `withDensity` Fubini.

The side condition is internal and essential: a one-sided path imposes no
condition at negative parameters. -/
theorem pi_acPart_eq_withDensity_acProductLikelihood
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Measure.pi (fun _ : Fin n => γ.acPart t) =
      (Measure.pi (fun _ : Fin n => P)).withDensity
        (γ.acProductLikelihood t n) := by
  let : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  simpa only [acPart, acProductLikelihood] using!
    (MeasureTheory.pi_withDensity_prod (fun _ : Fin n =>
      Measure.measurable_rnDeriv (γ.curve t) P)).symm

/-- Exact integrability and normalization of the actual product likelihood.
The integral is `(1-singularMass)^n`, not one.

The proof passes `ht` to the product AC identity, integrates coordinatewise,
and uses the Lebesgue decomposition. -/
theorem integrable_acProductLikelihood_and_integral
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Integrable (fun X => (γ.acProductLikelihood t n X).toReal)
        (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ X, (γ.acProductLikelihood t n X).toReal
          ∂(Measure.pi (fun _ : Fin n => P)) =
        (1 - (γ.singularMass t).toReal) ^ n := by
  let : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  have h_one : Integrable (fun ω => ((γ.curve t).rnDeriv P ω).toReal) P := by
    simpa only [integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv
        (s := Set.univ) (measure_ne_top (γ.curve t) Set.univ))
  have h_int : ∫ ω, ((γ.curve t).rnDeriv P ω).toReal ∂P =
      1 - (γ.singularMass t).toReal := by
    simpa only [singularMass, singularPart, measureReal_def, measure_univ,
      ENNReal.toReal_one] using
      (Measure.integral_toReal_rnDeriv' (μ := γ.curve t) (ν := P))
  constructor
  · simpa only [acProductLikelihood, ENNReal.toReal_prod] using
      (Integrable.fintype_prod (fun _ : Fin n => h_one))
  · simpa only [acProductLikelihood, ENNReal.toReal_prod, h_int,
      Fintype.card_fin] using
      (MeasureTheory.integral_fintype_prod_eq_pow
        (fun ω => ((γ.curve t).rnDeriv P ω).toReal)
        (ι := Fin n) (μ := P))


end NondominatedQMDPath
end AsymptoticStatistics.Core.NondominatedQMDPath

end GLP0011B3Source14
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.IIdJointLaw`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source15


/-!
# iid joint-law bridge

Finite iid product measures are the pushforwards of the infinite product
under coordinate truncation:
```
Measure.pi (fun _ : Fin n => ν)
  = (Measure.infinitePi (fun _ : ℕ => ν)).map (fun ω i => ω i.val)
```
for a probability measure `ν`. The associated equality of event probabilities
transports convergence in probability from the infinite product to finite samples.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics


/-- `Fin n` and the Finset-range coercion `↥(Finset.range n)` are canonically
equivalent (both are `{k : ℕ // k < n}` up to `Finset.mem_range`). Packaged
as an `Equiv` for use with `Measure.pi`'s reindexing lemmas. -/
def rangeEquivFin (n : ℕ) : ↥(Finset.range n) ≃ Fin n where
  toFun i := ⟨i.val, Finset.mem_range.mp i.prop⟩
  invFun i := ⟨i.val, Finset.mem_range.mpr i.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma rangeEquivFin_apply_val (n : ℕ) (i : ↥(Finset.range n)) :
    ((rangeEquivFin n) i).val = i.val := rfl

@[simp] lemma rangeEquivFin_symm_apply_val (n : ℕ) (i : Fin n) :
    ((rangeEquivFin n).symm i).val = i.val := rfl


/-- **iid product = finite restriction of the Kolmogorov extension (`infinitePi` version)**.

This form matches `ProbabilityTheory.iIndepFun_infinitePi`, which is stated
for the general indexed product `Measure.infinitePi`.
-/
theorem pi_const_eq_infinitePi_map
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    (ν : Measure 𝓧) [IsProbabilityMeasure ν] (n : ℕ) :
    Measure.pi (fun _ : Fin n => ν)
      = (Measure.infinitePi (fun _ : ℕ => ν)).map
          (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) := by
  classical
  set ψ : (↥(Finset.range n) → 𝓧) → (Fin n → 𝓧) := fun f i =>
    f ((rangeEquivFin n).symm i) with hψ_def
  have hψ_meas : Measurable ψ := by
    refine Measurable.of_eval (fun i => ?_)
    exact measurable_pi_apply _
  have h_factor :
      (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
        = ψ ∘ (Finset.range n).restrict := by
    funext ω i; rfl
  have h_restrict_meas :
      Measurable ((Finset.range n).restrict : (ℕ → 𝓧) → (↥(Finset.range n) → 𝓧)) := by
    refine Measurable.of_eval (fun _ => ?_)
    exact measurable_pi_apply _
  have h_step1 : (Measure.infinitePi (fun _ : ℕ => ν)).map
        (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
      = ((Measure.infinitePi (fun _ : ℕ => ν)).map (Finset.range n).restrict).map ψ := by
    rw [h_factor, ← Measure.map_map hψ_meas h_restrict_meas]
  rw [h_step1, MeasureTheory.Measure.infinitePi_map_restrict]
  have h_ψ_eq : ψ = MeasurableEquiv.piCongrLeft (fun _ : Fin n => 𝓧)
      (rangeEquivFin n) := by
    funext f i
    rw [hψ_def, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [h_ψ_eq]
  have mp := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : Fin n => ν) (rangeEquivFin n)
  exact mp.map_eq.symm


/-- **Pinf → Pⁿ measure-on-set bridge for varying truncation**.

For each `n`, the probability under `Measure.pi (fun _ : Fin n => ν)` of a
predicate on `Fin n → 𝓧` equals the probability under `Measure.infinitePi (const ν)`
of the predicate composed with the truncation `ω ↦ fun i : Fin n => ω i.val`. This
is the per-n measure-equality consequence of `pi_const_eq_infinitePi_map` plus
`Measure.map_apply`, packaged for use inside Slutsky-style `hDist`-arguments where
the base measure varies in `n` and the predicate is parametrised by `n`. -/
lemma pi_meas_eq_infinitePi_meas_of_truncate
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    (ν : Measure 𝓧) [IsProbabilityMeasure ν] (n : ℕ)
    {s : Set (Fin n → 𝓧)} (hs : MeasurableSet s) :
    Measure.pi (fun _ : Fin n => ν) s
      = (Measure.infinitePi (fun _ : ℕ => ν))
          {ω | (fun i : Fin n => ω i.val) ∈ s} := by
  rw [pi_const_eq_infinitePi_map ν n]
  rw [Measure.map_apply (f := fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) ?_ hs]
  · rfl
  · refine Measurable.of_eval (fun _ => ?_)
    exact measurable_pi_apply _


end AsymptoticStatistics

end GLP0011B3Source15
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.Prohorov`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source16


/-!
# Tightness and subsequence extraction

The tightness argument in van der Vaart's representation theorem (Theorem 7.10,
§7.3, "Convergence to a Normal Experiment") combines joint tightness from
marginal tightness with extraction of a weakly convergent subsequence.
The corresponding lemmas here are `tight_prod_of_tight_marginals_local`
and `extract_weak_subseq_local`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics
namespace Prohorov


end Prohorov
end AsymptoticStatistics

end GLP0011B3Source16
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.InProbability`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source17


/-!
# Convergence in probability with varying base measures

Statistics `X k : Ω k → G` can live on different probability spaces `(Ω k, P k)`.
Their laws can be compared through pushforwards `(P k).map (X k)`.
The theorem `WeakConverges.slutsky_of_tendstoInMeasure_dist` uses this form of
convergence in probability.
-/

open MeasureTheory Filter Topology Set

namespace AsymptoticStatistics

variable {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]


end AsymptoticStatistics

end GLP0011B3Source17
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.EmpiricalAverage`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source18


/-!
# Empirical averages of finite samples

The empirical average of a real-valued function over a sample indexed by `Fin n`,
with the zero-sample and zero-function identities. This definition is independent
of measure theory.
-/

namespace AsymptoticStatistics.EmpiricalProcess

variable {Ω : Type*}

/-- The **empirical average** of `f` on the sample `X`:
`empiricalAvg f n X = (1/n) · Σᵢ f (X i)`.

Edge: for `n = 0`, the sum is empty and the prefactor `(0 : ℝ)⁻¹ = 0`
in Lean's convention, so the whole expression is `0`.

This is the real-valued shorthand for integration against an empirical measure,
in the form used in the proof of vdV Theorem 19.4. -/
noncomputable def empiricalAvg (f : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (X i)

@[simp] lemma empiricalAvg_zero (f : Ω → ℝ) (X : Fin 0 → Ω) :
    empiricalAvg f 0 X = 0 := by
  simp [empiricalAvg]

@[simp] lemma empiricalAvg_const_zero (n : ℕ) (X : Fin n → Ω) :
    empiricalAvg (fun _ => (0 : ℝ)) n X = 0 := by
  simp [empiricalAvg]


end AsymptoticStatistics.EmpiricalProcess

end GLP0011B3Source18
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.IidWLLN`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source19


/-!
# Generic i.i.d. weak law of large numbers in probability

For an L¹(P) function `f`, the coordinatewise empirical mean
`(1/n) Σᵢ f(Xᵢ)` converges to `∫ f ∂P` in `Pⁿ`-probability, where
`Pⁿ := Measure.pi (fun _ : Fin n => P)`.

The statement is the Mathlib bridge from the strong law of large numbers
(`ProbabilityTheory.strong_law_ae_real`, a.s. convergence) to convergence in
probability (`MeasureTheory.tendstoInMeasure_of_tendsto_ae`, a.s. → in-prob on
finite measures). The a.s. statement lives on the Kolmogorov extension
`Measure.infinitePi (fun _ : ℕ => P)` over `ℕ → Ω`; it is transported to
`Measure.pi (fun _ : Fin n => P)` over `Fin n → Ω` via the truncation identity
`pi_meas_eq_infinitePi_meas_of_truncate`.

-/

open MeasureTheory Filter Topology
open scoped ENNReal Function

namespace AsymptoticStatistics

/-- **Generic iid LLN in probability** under the product measure `Measure.pi`.

For an L¹(P) function `f`, the empirical mean of `f` along the i-th coordinate
converges to `∫ f ∂P` in `Pⁿ`-probability.

This is the Mathlib bridge from `ProbabilityTheory.strong_law_ae` (a.s.
convergence) + `tendstoInMeasure_of_tendsto_ae` (a.s. → in-prob for finite
measures). -/
lemma iid_lln_in_prob_l1
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (f : Ω → ℝ) (_hf : Integrable f P) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (X i)) - ∫ ω, f ω ∂P|})
      atTop (𝓝 0) := by
  classical
  -- Strategy: lift to the Kolmogorov extension `μ_inf := infinitePi (const P)` on
  -- `ℕ → Ω`, apply `strong_law_ae_real` to the iid sequence `Y i ω := f̃ (ω i)`
  -- (where `f̃` is the strongly measurable representative of `f`), convert
  -- a.s. → in measure via `tendstoInMeasure_of_tendsto_ae`, and pull the result
  -- back to `Measure.pi (Fin n → P)` via `pi_meas_eq_infinitePi_meas_of_truncate`.
  set μ_inf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P) with hμ_inf
  -- Strongly measurable representative `f̃` of `f`.
  have hf_aesm : AEStronglyMeasurable f P := _hf.aestronglyMeasurable
  set f' : Ω → ℝ := hf_aesm.mk f with hf'_def
  have hf'_meas : Measurable f' := hf_aesm.measurable_mk
  have hff' : f =ᵐ[P] f' := hf_aesm.ae_eq_mk
  have hf'_int : Integrable f' P := _hf.congr hff'
  have hf_integral : ∫ ω, f' ω ∂P = ∫ ω, f ω ∂P := integral_congr_ae hff'.symm
  -- Iid sequence on `(ℕ → Ω, μ_inf)`.
  set Y : ℕ → (ℕ → Ω) → ℝ := fun i ω => f' (ω i) with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := fun i =>
    hf'_meas.comp (measurable_pi_apply i)
  -- Each `eval i` is measure-preserving from `μ_inf` to `P`.
  have hMP : ∀ i : ℕ, MeasurePreserving (Function.eval i : (ℕ → Ω) → Ω) μ_inf P :=
    fun i => measurePreserving_eval_infinitePi (μ := fun _ : ℕ => P) i
  -- `Y 0` is integrable on `μ_inf` because `f'` is integrable on `P` and
  -- `eval 0` is measure-preserving.
  have hY0_int : Integrable (Y 0) μ_inf := by
    have := (hMP 0).integrable_comp hf'_meas.aestronglyMeasurable
    simpa [Y, Function.eval] using! this.mpr hf'_int
  -- Pairwise independence of the `Y i`'s.
  have h_iIndep : ProbabilityTheory.iIndepFun Y μ_inf := by
    simpa [Y, Function.eval] using
      (ProbabilityTheory.iIndepFun_infinitePi (Ω := fun _ : ℕ => Ω)
        (P := fun _ : ℕ => P) (X := fun _ : ℕ => f') (fun _ => hf'_meas))
  have h_pair :
      Pairwise ((fun X₁ X₂ : (ℕ → Ω) → ℝ => ProbabilityTheory.IndepFun X₁ X₂ μ_inf) on Y) :=
    fun i j hij => h_iIndep.indepFun hij
  -- All `Y i` are identically distributed: their `μ_inf`-pushforward equals
  -- `P.map f' = f'.map P` for every `i`.
  have hY_map : ∀ i, Measure.map (Y i) μ_inf = Measure.map f' P := by
    intro i
    have h_comp : Y i = f' ∘ (Function.eval i : (ℕ → Ω) → Ω) := by
      funext ω; rfl
    rw [h_comp, ← Measure.map_map hf'_meas (measurable_pi_apply i), (hMP i).map_eq]
  have h_ident : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ_inf μ_inf := fun i =>
    { aemeasurable_fst := (hY_meas i).aemeasurable
      aemeasurable_snd := (hY_meas 0).aemeasurable
      map_eq := by rw [hY_map i, hY_map 0] }
  -- Mean of `Y 0`: `∫ Y 0 ∂μ_inf = ∫ f' ∂P = ∫ f ∂P`.
  -- Use `integral_map` (pure aemeasurable hypotheses) — `MeasurePreserving.integral_comp`
  -- requires a `MeasurableEmbedding`, which is unavailable for `eval 0`.
  have h_mean : ∫ ω, Y 0 ω ∂μ_inf = ∫ ω, f ω ∂P := by
    have h_int : ∫ ω, f' ω ∂P = ∫ ω, Y 0 ω ∂μ_inf := by
      have hP_eq : P = Measure.map (Function.eval 0 : (ℕ → Ω) → Ω) μ_inf :=
        (hMP 0).map_eq.symm
      calc ∫ ω, f' ω ∂P
          = ∫ ω, f' ω ∂Measure.map (Function.eval 0 : (ℕ → Ω) → Ω) μ_inf := by rw [← hP_eq]
        _ = ∫ ω, f' ((Function.eval 0 : (ℕ → Ω) → Ω) ω) ∂μ_inf := by
            refine MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable ?_
            exact hf'_meas.aestronglyMeasurable
        _ = ∫ ω, Y 0 ω ∂μ_inf := by rfl
    rw [← h_int, hf_integral]
  -- Apply Etemadi's strong law: `(∑ i ∈ range n, Y i ω) / n → ∫ Y 0 ∂μ_inf` a.s.
  have h_sllN : ∀ᵐ ω ∂μ_inf,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y i ω) / n)
        atTop (𝓝 (∫ ω, Y 0 ω ∂μ_inf)) :=
    ProbabilityTheory.strong_law_ae_real Y hY0_int h_pair h_ident
  -- Bridge `(∑ range n, Y i ω) / n` to `(n : ℝ)⁻¹ * ∑ i : Fin n, f (ω i)`.
  -- (a) Rewrite the `Finset.range` sum as a `Fin n` sum, (b) convert
  -- `/n` to `(n : ℝ)⁻¹ * _`, and (c) replace `f' (ω i)` by `f (ω i)` a.e.
  -- Step (c): `f' (ω i) = f (ω i)` for all `i`, μ_inf-a.e.
  -- Uses `MeasurePreserving.quasiMeasurePreserving` + `QuasiMeasurePreserving.ae_eq`
  -- to lift `f =ᵐ[P] f'` along each evaluation `eval i : (ℕ → Ω) → Ω`, then
  -- intersects the resulting countable family of null sets.
  have h_ae_eq : ∀ᵐ ω ∂μ_inf, ∀ i : ℕ, f (ω i) = f' (ω i) := by
    rw [ae_all_iff]
    intro i
    have h_qmp : MeasureTheory.Measure.QuasiMeasurePreserving
        (fun ω : ℕ → Ω => ω i) μ_inf P := (hMP i).quasiMeasurePreserving
    -- `f ∘ eval i =ᵐ[μ_inf] f' ∘ eval i` from `f =ᵐ[P] f'`.
    have h_comp_ae : (fun ω : ℕ → Ω => f (ω i)) =ᵐ[μ_inf] fun ω => f' (ω i) :=
      h_qmp.ae_eq_comp hff'
    exact h_comp_ae
  -- Build the goal-form a.s. convergence: `(n)⁻¹ * ∑ i : Fin n, f (ω i) → ∫ f ∂P`.
  have h_target_ae : ∀ᵐ ω ∂μ_inf,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
        atTop (𝓝 (∫ ω, f ω ∂P)) := by
    filter_upwards [h_sllN, h_ae_eq] with ω h_lim h_eq_all
    -- Rewrite sequence on the LHS to match `h_lim`'s form.
    have h_seq_eq : ∀ n : ℕ,
        (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))
          = (∑ i ∈ Finset.range n, Y i ω) / n := by
      intro n
      have h_sum : (∑ i : Fin n, f (ω i)) = ∑ i ∈ Finset.range n, Y i ω := by
        rw [← Fin.sum_univ_eq_sum_range fun i => Y i ω]
        refine Finset.sum_congr rfl fun i _ => ?_
        -- Goal: `f (ω ↑i) = Y ↑i ω = f' (ω ↑i)`. Use `h_eq_all ↑i`.
        exact h_eq_all i.val
      rw [h_sum]
      ring
    have h_target_to_sllN :
        (fun n : ℕ => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
          = fun n : ℕ => (∑ i ∈ Finset.range n, Y i ω) / n := funext h_seq_eq
    rw [h_target_to_sllN, ← h_mean]
    exact h_lim
  -- Convert a.s. convergence to convergence in measure on `μ_inf`.
  have hF_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun ω : ℕ → Ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))) μ_inf := by
    intro n
    refine AEStronglyMeasurable.const_mul ?_ _
    refine Finset.aestronglyMeasurable_fun_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun i ω => f (ω i.val)) (μ := μ_inf) (fun i _ => ?_)
    have h_proj : MeasurePreserving (fun ω : ℕ → Ω => ω i.val) μ_inf P := hMP i.val
    exact hf_aesm.comp_measurePreserving h_proj
  have h_in_meas :
      MeasureTheory.TendstoInMeasure μ_inf
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
        atTop (fun _ => ∫ ω, f ω ∂P) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae hF_meas h_target_ae
  -- Translate to the `iff_norm` (= `abs` since target is ℝ) form, then transport
  -- to `Measure.pi (Fin n → P)` via the truncation bridge.
  have h_norm := (MeasureTheory.tendstoInMeasure_iff_norm
      (μ := μ_inf) (l := atTop)
      (f := fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
      (g := fun _ => ∫ ω, f ω ∂P)).mp h_in_meas
  intro ε hε
  have h_inf := h_norm ε hε
  -- For each n, bridge `μ_inf`-set-measure with `Measure.pi (Fin n → P)`-set-measure.
  -- Pass through the `f'`-version of the set (where `f'` is measurable, so the
  -- set is measurable), using the coordinatewise a.e. equality `f = f'`.
  have h_set_eq : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (X i)) - ∫ ω, f ω ∂P|}
      = μ_inf {ω : ℕ → Ω |
          ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖} := by
    intro n
    -- Step 1: replace `f` by `f'` inside the `Measure.pi`-set (a.e. on Pⁿ).
    have h_pi_ae : (fun (X : Fin n → Ω) i => f (X i)) =ᵐ[Measure.pi (fun _ : Fin n => P)]
        fun (X : Fin n → Ω) i => f' (X i) :=
      MeasureTheory.Measure.ae_eq_pi (μ := fun _ : Fin n => P)
        (f := fun _ => f) (f' := fun _ => f') (fun _ => hff')
    have h_pi_set_eq :
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (X i)) - ∫ ω, f ω ∂P|}
        = (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (X i)) - ∫ ω, f ω ∂P|} := by
      apply MeasureTheory.measure_congr
      filter_upwards [h_pi_ae] with X hX
      have hX_eq : ∀ i : Fin n, f (X i) = f' (X i) := fun i => congrFun hX i
      have h_sum_eq : (∑ i : Fin n, f (X i)) = (∑ i : Fin n, f' (X i)) :=
        Finset.sum_congr rfl fun i _ => hX_eq i
      -- Goal: `X ∈ {X | p_f X} = X ∈ {X | p_f' X}` (Prop equality from `Set.EventuallyEq`).
      change (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (X i)) - ∫ ω, f ω ∂P|) =
             (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (X i)) - ∫ ω, f ω ∂P|)
      rw [h_sum_eq]
    -- Step 2: bridge the `f'`-set via `pi_meas_eq_infinitePi_meas_of_truncate`.
    have hms_f' : MeasurableSet
        {X : Fin n → Ω |
          ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (X i)) - ∫ ω, f ω ∂P|} := by
      refine measurableSet_le measurable_const ?_
      refine (Measurable.sub ?_ measurable_const).abs
      refine Measurable.const_mul ?_ _
      exact Finset.measurable_sum _ fun i _ =>
        hf'_meas.comp (measurable_pi_apply i)
    have hbridge_f' :=
      AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate (ν := P) n hms_f'
    -- Step 3: replace `f'` by `f` inside the `μ_inf`-set (a.e. on μ_inf).
    -- Note: after `hbridge_f'` rewrites, the LHS is in
    -- `{ω | (fun i : Fin n => ω i.val) ∈ {X | ε ≤ |…f' (X i)…|}}` form;
    -- match that explicit form below.
    have h_inf_set_eq :
        μ_inf {ω : ℕ → Ω |
            (fun i : Fin n => ω i.val) ∈
              {X : Fin n → Ω |
                ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (X i)) - ∫ ω, f ω ∂P|}}
          = μ_inf {ω : ℕ → Ω |
            ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖} := by
      apply MeasureTheory.measure_congr
      filter_upwards [h_ae_eq] with ω hω
      have h_sum_eq : (∑ i : Fin n, f' (ω i.val)) = (∑ i : Fin n, f (ω i)) :=
        Finset.sum_congr rfl fun i _ => (hω i.val).symm
      -- Rewrite the two tail predicates using the a.e. equality of the empirical sums.
      change (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (ω i.val)) - ∫ ω, f ω ∂P|) =
             (ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖)
      rw [Real.norm_eq_abs, h_sum_eq]
    rw [h_pi_set_eq, hbridge_f', h_inf_set_eq]
  simp_rw [h_set_eq]
  exact h_inf


end AsymptoticStatistics

end GLP0011B3Source19
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ParametricFamily.Defs`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source20


/-!
# Parametric family of densities

A *parametric statistical model* is a family of probability densities
$\{p_\theta : \theta \in \Theta\}$ on a sample space $\mathcal X$, each taken with
respect to a common dominating $\sigma$-finite measure $\mu$. This file fixes the
density function with per-parameter measurability and pointwise nonnegativity.

A parametric family packages a family $\theta \mapsto p_\theta$ of pointwise
nonnegative functions, each measurable on $\mathcal X$. A family is a *probability-density
family* (relative to $\mu$) when, for every $\theta$, the density is $\mu$-integrable
and normalised, $\int_{\mathcal X} p_\theta \, d\mu = 1$.

The central analytic object is the **square-root density**
$$ s_\theta(x) \;=\; \sqrt{p_\theta(x)}, $$
which is measurable and non-negative, satisfies $s_\theta^2 = p_\theta$ pointwise, and
— precisely because $\int p_\theta \, d\mu = 1 < \infty$ — belongs to $L^2(\mu)$ with
$\lVert s_\theta \rVert_{L^2(\mu)}^2 = 1$. Representing densities through their square
roots is what turns the (nonlinear) statistical model into a curve in the Hilbert space
$L^2(\mu)$, and is the foundation for differentiability in quadratic mean and the
Hellinger geometry of vdV Chapter 7.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 7 (Local Asymptotic Normality), §7.2 (Expanding the Likelihood) —
the parametric-model setup and the square-root-density / $L^2(\mu)$ representation
underlying the differentiability-in-quadratic-mean definition.

-/

open MeasureTheory

namespace AsymptoticStatistics

/-- A parametric family of (μ-)densities indexed by a parameter `θ : Θ`.

The structure bundles per-parameter measurability and pointwise nonnegativity. -/
structure ParametricFamily
    (𝓧 : Type*) [MeasurableSpace 𝓧] (Θ : Type*) where
  /-- Density `p_θ(x)`. -/
  density : Θ → 𝓧 → ℝ
  density_meas : ∀ θ, Measurable (density θ)
  density_nonneg : ∀ θ x, 0 ≤ density θ x

/-- **PDF conditions**: the family `M` is a probability-density family with respect to
the dominating measure `μ`. Bundles the two universal regularity conditions that
typically appear as separate hypotheses in LAN-style theorems — normalisation and
integrability, each for every parameter `θ`.

The structure does **not** bundle ae-strict-positivity of `p_θ`: vdV's
Theorem 7.10 (and the LAN expansion it rests on) only needs the weaker condition
that the perturbation densities `p_{θ₀ + t·u}` are strictly positive on the support
of `p_{θ₀}` (i.e. ν-a.e. where ν = μ.withDensity p_{θ₀}). Consumers requiring that
condition should take it as a separate hypothesis in ν-form, not bake it in here. -/
structure IsPDFOf
    {𝓧 : Type*} [MeasurableSpace 𝓧] {Θ : Type*}
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) : Prop where
  /-- Density integrates to 1 (normalisation). -/
  density_integral_eq_one : ∀ θ, ∫ x, M.density θ x ∂μ = 1
  /-- Density is μ-integrable. -/
  density_integrable : ∀ θ, Integrable (M.density θ) μ

namespace ParametricFamily

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*}



/-- The square root density `√p_θ`. -/
noncomputable def sqrtDensity (M : ParametricFamily 𝓧 Θ) (θ : Θ) (x : 𝓧) : ℝ :=
  Real.sqrt (M.density θ x)


end ParametricFamily
end AsymptoticStatistics

end GLP0011B3Source20
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.DQM.Defs`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source21


/-!
# Differentiability in Quadratic Mean (DQM)

A statistical model $\{P_\theta\}$ with densities $p_\theta$ relative to a
dominating measure $\mu$ is **differentiable in quadratic mean** at the parameter
$\theta$ if there is a (vector-valued) score function $\ell$ such that the
Hellinger residual of $\sqrt{p_\theta}$ vanishes faster than $\|h\|$ in
$L^2(\mu)$ as $h \to 0$:
$$\int \left( \sqrt{p_{\theta+h}} - \sqrt{p_\theta}
  - \tfrac12 \langle h, \ell\rangle \sqrt{p_\theta} \right)^2 \, d\mu
  = o\!\left(\|h\|^2\right).$$
This is the central regularity condition behind Local Asymptotic Normality (LAN):
it is exactly the requirement that the root density map $h \mapsto \sqrt{p_{\theta+h}}$
be Fréchet-differentiable in $L^2(\mu)$ at $h = 0$, with derivative
$\tfrac12 \langle \cdot, \ell\rangle \sqrt{p_\theta}$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 7 (Local Asymptotic Normality), §7.2 (Differentiable in Quadratic Mean),
Eq. (7.1).

A Bochner-integral formulation must state eventual L²-membership of the residual
explicitly. A non-integrable function has Bochner integral zero by convention,
so the real-valued integral rate alone would hold vacuously for a residual
outside L². In the nonnegative Lebesgue-integral formulation, finiteness
already expresses square-integrability.

-/

open MeasureTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
variable {μ : Measure 𝓧}

/-- Differentiability in quadratic mean (DQM).

The model `M` is **DQM at `θ`** with score `ℓ : 𝓧 → Θ` w.r.t. the dominating measure `μ`
if the squared L²(μ) norm of the Hellinger residual is `o(‖h‖²)` as `h → 0`:
`∫ (√p_{θ+h} − √p_θ − ½⟨h, ℓ(x)⟩√p_θ)² dμ(x) = o(‖h‖²)`.

This is the central regularity condition of LAN (Local Asymptotic Normality);
see van der Vaart §7.2 (Eq. 7.1).

**Note on the conjunction.** In van der Vaart's definition the integral is the
Lebesgue integral of a non-negative function, where finiteness of the integral
is *the same as* `MemLp 2 μ`-membership of the residual.  When formalising with
Lean's Bochner integral `∫`, that equivalence breaks: a non-integrable
non-negative function has Bochner integral `0` by convention, so the
`o(‖h‖²)` rate condition is *trivially* satisfied for pathological models in
which the residual is never in `L²(μ)`. The eventual `L²(μ)`-membership of the
residual is therefore stated as a separate conjunct (`mem`), making the
integrability requirement explicit. -/
structure DifferentiableQuadraticMean
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ : Θ)
    (ℓ : 𝓧 → Θ) : Prop where
  /-- The Hellinger residual is in `L²(μ)` for every `h` in some neighbourhood
  of `0`. (Implicit in vdV via the Lebesgue interpretation of the integral.) -/
  mem : ∀ᶠ h in 𝓝 (0 : Θ),
    MemLp (fun x => M.sqrtDensity (θ + h) x - M.sqrtDensity θ x
                    - (1/2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ x) 2 μ
  /-- The squared L²(μ) norm of the Hellinger residual is `o(‖h‖²)` as `h → 0`. -/
  isLittleO :
    (fun h : Θ =>
      ∫ x, (M.sqrtDensity (θ + h) x
            - M.sqrtDensity θ x
            - (1/2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ x) ^ 2 ∂μ)
    =o[𝓝 (0 : Θ)] (fun h : Θ => ‖h‖ ^ 2)

end AsymptoticStatistics

end GLP0011B3Source21
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ParametricFamily.FisherInformation`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source22



open MeasureTheory
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]


end AsymptoticStatistics

end GLP0011B3Source22
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ParametricFamily.Score`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source23


/-! # Measurable score-function bundle -/

open MeasureTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

section ScoreFunction

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [MeasurableSpace Θ]

/-- A *score function* at a parameter `θ` for a model `M`: a measurable map `𝓧 → Θ`. -/
structure ScoreFunction
    (M : ParametricFamily 𝓧 Θ) (θ : Θ) where
  /-- The score map `ℓ_θ : 𝓧 → Θ`. -/
  toFun : 𝓧 → Θ
  measurable : Measurable toFun

instance {M : ParametricFamily 𝓧 Θ} {θ : Θ} :
    CoeFun (ScoreFunction M θ) (fun _ => 𝓧 → Θ) := ⟨ScoreFunction.toFun⟩

end ScoreFunction

namespace Score

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ]














end Score
end AsymptoticStatistics

end GLP0011B3Source23
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.LogTaylor`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source24


/-!
Asymptotic Statistics — Taylor remainder for `log(1 + x)` around `0`.

Provides a concrete remainder function `logTaylorRemainder` with

  `Real.log (1 + x) = x − x²/2 + x² · logTaylorRemainder (2 · x)`  (for `x > −1`)

and `logTaylorRemainder → 0` as `u → 0`. This is the form used in the vdV proof
of Theorem 7.2 Step 5, where the `2·x` shift matches the substitution
`x = W_n/2`.

## Contents

* `logTaylorRemainder` — the explicit remainder function.
* `log_one_add_eq_taylor` — the identity.
* `logTaylorRemainder_tendsto_zero` — the rate: `R(u) → 0` as `u → 0`.
-/

open Filter Topology Asymptotics

namespace AsymptoticStatistics
namespace ForMathlib

/-- Explicit second-order Taylor remainder of `log(1 + x)` at `0`, parameterised
so that the identity `log(1 + x) = x − x²/2 + x² · logTaylorRemainder (2 · x)`
holds (for `x > −1`).  Equal to `0` at the origin; elsewhere, the obvious
quotient expression. -/
noncomputable def logTaylorRemainder (u : ℝ) : ℝ :=
  if u = 0 then 0
  else 4 * (Real.log (1 + u / 2) - u / 2 + u ^ 2 / 8) / u ^ 2

@[simp] lemma logTaylorRemainder_zero : logTaylorRemainder 0 = 0 := by
  unfold logTaylorRemainder; simp

/-- **Taylor expansion identity for `log(1 + x)`.**

For every `x > −1`,
  `log(1 + x) = x − x²/2 + x² · logTaylorRemainder (2 · x)`.
(The hypothesis `x > −1` keeps the logarithm’s argument positive. The
algebraic identity itself follows from the definition of `logTaylorRemainder`.) -/
lemma log_one_add_eq_taylor {x : ℝ} (hx : -1 < x) :
    Real.log (1 + x) = x - (1 / 2) * x ^ 2 + x ^ 2 * logTaylorRemainder (2 * x) := by
  by_cases hx0 : x = 0
  · subst hx0; simp
  · have h2x_ne : (2 : ℝ) * x ≠ 0 := mul_ne_zero two_ne_zero hx0
    have hx_sq_ne : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    -- Unfold the remainder at `2 * x`.
    have h_unfold : logTaylorRemainder (2 * x) =
        4 * (Real.log (1 + x) - x + (2 * x) ^ 2 / 8) / (2 * x) ^ 2 := by
      unfold logTaylorRemainder
      rw [ite_eq_right h2x_ne]
      have h_div : (2 * x) / 2 = x := by ring
      rw [h_div]
    rw [h_unfold]
    -- Algebraic identity:
    --   x^2 * (4 * (log(1+x) - x + (2x)²/8) / (2x)²)
    --   = 4 x² (log(1+x) - x + x²/2) / (4 x²)
    --   = log(1+x) - x + x²/2.
    have h_rhs : x ^ 2 * (4 * (Real.log (1 + x) - x + (2 * x) ^ 2 / 8) / (2 * x) ^ 2)
        = Real.log (1 + x) - x + x ^ 2 / 2 := by
      field_simp
      ring
    linarith [h_rhs]

/-- Taylor identity for the logarithm of a nonnegative ratio, written through
the square-root ratio `w = 2 * (√(a / b) - 1)`.  Mathlib's totalized division
and convention `Real.log 0 = 0` make the identity valid also when `a / b = 0`;
then `w = -2` and the explicit remainder supplies the boundary value. -/
lemma log_div_nonneg_eq_sqrt_taylor {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let w := 2 * (Real.sqrt (a / b) - 1)
    Real.log (a / b) = w - w ^ 2 / 4 + w ^ 2 / 2 * logTaylorRemainder w := by
  dsimp only
  have hratio : 0 ≤ a / b := div_nonneg ha hb
  let y := Real.sqrt (a / b)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hy_sq : y ^ 2 = a / b := by
    rw [show y = Real.sqrt (a / b) by rfl, Real.sq_sqrt hratio]
  rcases hy.lt_or_eq with hy_pos | hy_zero
  · have hlog : Real.log (a / b) = 2 * Real.log y := by
      rw [← hy_sq, Real.log_pow]
      ring
    have htaylor := log_one_add_eq_taylor (show -1 < y - 1 by linarith)
    have hone : (1 : ℝ) + (y - 1) = y := by ring
    rw [hone] at htaylor
    rw [hlog, htaylor]
    ring
  · have hy_eq : y = 0 := hy_zero.symm
    have hratio_zero : a / b = 0 := by rw [← hy_sq, hy_eq]; ring
    have hrem : logTaylorRemainder (-2) = 3 / 2 := by
      unfold logTaylorRemainder
      rw [ite_eq_right (by norm_num : (-2 : ℝ) ≠ 0)]
      norm_num [Real.log_zero]
    rw [hratio_zero, Real.log_zero, show Real.sqrt 0 = 0 by simp]
    norm_num [hrem]

/-- **Remainder rate.** `logTaylorRemainder u → 0` as `u → 0`.

Proof uses `Real.abs_log_sub_add_sum_range_le` with `n = 2` and substitution
`x ↦ −u/2`, which gives `|log(1 + u/2) − u/2 + u²/8| ≤ |u/2|³ / (1 − |u/2|)`
for `|u/2| < 1`, i.e. `|u| < 2`.  Dividing by `|u|²/4` yields
`|logTaylorRemainder u| ≤ |u| / (2 − |u|)`, which is bounded by `|u|` for
`|u| ≤ 1` and hence tends to `0`. -/
lemma logTaylorRemainder_tendsto_zero :
    Tendsto logTaylorRemainder (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Choose δ := min ε 1. For |u| < δ, prove |R u| < ε via |R u| ≤ |u|.
  refine Metric.eventually_nhds_iff.mpr ⟨min ε 1, lt_min hε one_pos, fun u hu => ?_⟩
  rw [Real.dist_eq, sub_zero] at hu
  have hu_abs_lt : |u| < ε ∧ |u| < 1 := ⟨lt_of_lt_of_le hu (min_le_left _ _),
    lt_of_lt_of_le hu (min_le_right _ _)⟩
  rw [Real.dist_eq, sub_zero]
  -- Main bound: |R u| ≤ |u|.
  suffices hbd : |logTaylorRemainder u| ≤ |u| from lt_of_le_of_lt hbd hu_abs_lt.1
  by_cases hu0 : u = 0
  · subst hu0; simp
  -- For u ≠ 0: unfold and bound using `abs_log_sub_add_sum_range_le`.
  have h_half_abs : |u / 2| < 1 := by
    rw [abs_div]; simp only [abs_two]; linarith [hu_abs_lt.2]
  -- Mathlib's bound, with x = -(u/2) and n = 2:
  --   |((-u/2) + (-u/2)²/2) + log(1 - (-u/2))| ≤ |u/2|³ / (1 - |u/2|)
  -- i.e. |−u/2 + u²/8 + log(1+u/2)| ≤ |u/2|³ / (1 - |u/2|).
  have h_mathlib := Real.abs_log_sub_add_sum_range_le (x := -(u / 2)) (by rwa [abs_neg]) 2
  -- Unpack the sum and rewrite log(1 - (-u/2)) = log(1 + u/2).
  have h_sum : ∑ i ∈ Finset.range 2, (-(u / 2)) ^ (i + 1) / ((i : ℝ) + 1) =
      -(u / 2) + u ^ 2 / 8 := by
    simp [Finset.sum_range_succ]
    ring
  have h_log : Real.log (1 - -(u / 2)) = Real.log (1 + u / 2) := by ring_nf
  rw [h_sum, h_log] at h_mathlib
  -- h_mathlib : |−(u/2) + u²/8 + log(1 + u/2)| ≤ |u/2|³ / (1 − |u/2|)
  have h_pow : |(-(u / 2))| ^ (2 + 1) = |u| ^ 3 / 8 := by
    rw [abs_neg, abs_div]; simp only [abs_two]; ring
  rw [h_pow] at h_mathlib
  -- Rewrite 1 - |-(u/2)| = 1 - |u|/2 = (2 - |u|)/2.
  have h_denom : 1 - |(-(u / 2))| = (2 - |u|) / 2 := by
    rw [abs_neg, abs_div]; simp only [abs_two]
    ring
  rw [h_denom] at h_mathlib
  -- Rearrange LHS: |−u/2 + u²/8 + log(1+u/2)| = |log(1+u/2) − u/2 + u²/8|.
  have h_lhs_eq :
      |-(u / 2) + u ^ 2 / 8 + Real.log (1 + u / 2)|
        = |Real.log (1 + u / 2) - u / 2 + u ^ 2 / 8| := by
    congr 1; ring
  rw [h_lhs_eq] at h_mathlib
  -- Now bound |R u| = 4 * |log(1+u/2) - u/2 + u²/8| / u².
  unfold logTaylorRemainder
  rw [ite_eq_right hu0]
  have hu_sq_pos : 0 < u ^ 2 := by positivity
  have hu_sq_abs : |u ^ 2| = u ^ 2 := abs_of_pos hu_sq_pos
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), hu_sq_abs]
  -- Goal: 4 * |log(1+u/2) - u/2 + u²/8| / u² ≤ |u|.
  -- Use h_mathlib.
  have h_two_sub_pos : 0 < 2 - |u| := by linarith [hu_abs_lt.2]
  rw [div_le_iff₀ hu_sq_pos]
  calc 4 * |Real.log (1 + u / 2) - u / 2 + u ^ 2 / 8|
      ≤ 4 * (|u| ^ 3 / 8 / ((2 - |u|) / 2)) :=
        mul_le_mul_of_nonneg_left h_mathlib (by norm_num)
    _ = |u| ^ 3 / (2 - |u|) := by field_simp; ring
    _ ≤ |u| ^ 3 / 1 := by
        apply div_le_div_of_nonneg_left (by positivity) one_pos
        linarith [hu_abs_lt.2]
    _ = |u| ^ 3 := by ring
    _ = |u| * |u| ^ 2 := by ring
    _ = |u| * u ^ 2 := by rw [sq_abs]


end ForMathlib
end AsymptoticStatistics

end GLP0011B3Source24
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ParametricFamily.SqrtDensityRatio`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source25



namespace AsymptoticStatistics


end AsymptoticStatistics

end GLP0011B3Source25
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.DQM.Properties`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source26



open MeasureTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]




end AsymptoticStatistics

end GLP0011B3Source26
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.MeanVarConvergence`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source27



open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics


end AsymptoticStatistics

end GLP0011B3Source27
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.IntegrableTail`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source28



open MeasureTheory Filter Topology

namespace AsymptoticStatistics
namespace ForMathlib

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


end ForMathlib
end AsymptoticStatistics

end GLP0011B3Source28
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.Markov`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source29



open MeasureTheory Filter Topology

namespace AsymptoticStatistics
namespace ForMathlib

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


end ForMathlib
end AsymptoticStatistics

end GLP0011B3Source29
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.LocalAsymptoticNormality.LANExpansion`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source30



set_option linter.style.longFile 2500

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal

namespace AsymptoticStatistics
namespace LANExpansion

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [SecondCountableTopology Θ]
































end LANExpansion
end AsymptoticStatistics

end GLP0011B3Source30
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.LowerBounds.T6_FinDimLAN.Abstract1DLAN`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source31




open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace QMDPath

open AsymptoticStatistics.Core.Hilbert

/-- L²(γ.dominating)-membership of `√p_t` for any `t`.

For each `t`, `(γ.curve t)` is a probability measure absolutely continuous
w.r.t. `γ.dominating`, and `γ.dominating` is σ-finite. The conclusion is the
`RnDerivSqrt.memLp_sqrt_rnDeriv` Hellinger-type bound:
`‖√p_t‖²_{L²(γ.dominating)} = (γ.curve t)(univ) = 1`. -/
theorem memLp_sqrt_rnDeriv (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P)
    (t : ℝ) :
    MemLp (fun ω => Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal)
      2 γ.dominating := by
  have : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  have : SigmaFinite γ.dominating := γ.dominating_sigmaFinite
  exact AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
    (γ.curve_absContinuous t)








end QMDPath
end AsymptoticStatistics.LowerBounds.T6_FinDimLAN

end GLP0011B3Source31
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLAN`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source32


/-! # Literal LAN from nondominated one-sided QMD (vdV Lemma 25.14) -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLAN

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedQMDPath
open AsymptoticStatistics.Core.NondominatedQMDPath.NondominatedQMDPath
open AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The baseline-AC square-root residual is controlled by the canonical
pairwise residual.  The canonical norm additionally sees the singular part,
so only this direction is available without domination. -/
private theorem baseline_actualResidual_sq_le
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, (2 * (Real.sqrt ((γ.curve t).rnDeriv P ω).toReal - 1)
          - t * (γ.score : Ω → ℝ) ω) ^ 2 ∂P ≤
      4 * (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal ^ 2 := by
  let : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  let μ := canonicalDominator P (γ.curve t)
  let : SigmaFinite μ := by
    dsimp only [μ, canonicalDominator]
    infer_instance
  let p : Ω → ℝ≥0∞ := P.rnDeriv μ
  let q : Ω → ℝ≥0∞ := (γ.curve t).rnDeriv μ
  let L : Ω → ℝ≥0∞ := (γ.curve t).rnDeriv P
  let r : Ω → ℝ := γ.comparisonResidual t
  let D : Ω → ℝ := fun ω =>
    2 * (Real.sqrt (L ω).toReal - 1) - t * (γ.score : Ω → ℝ) ω
  have hPμ : P ≪ μ :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hscore_meas : Measurable (γ.score : Ω → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P)).measurable
  have hp : MemLp (fun ω => Real.sqrt (p ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv hPμ
  have hq : MemLp (fun ω => Real.sqrt (q ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv
      (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))
  have hscore_weighted : MemLp
      (fun ω => (γ.score : Ω → ℝ) ω * Real.sqrt (p ω).toReal) 2 μ := by
    have hsquare : Integrable (fun ω => (γ.score : Ω → ℝ) ω ^ 2) P :=
      (Lp.memLp (γ.score : Lp ℝ 2 P)).integrable_sq
    have hprod : AEStronglyMeasurable
        (fun ω => (γ.score : Ω → ℝ) ω * Real.sqrt (p ω).toReal) μ :=
      hscore_meas.aestronglyMeasurable.mul
        (Measure.measurable_rnDeriv P μ).ennreal_toReal.sqrt.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hprod]
    have hP : P = μ.withDensity (P.rnDeriv μ) :=
      (Measure.withDensity_rnDeriv_eq P μ hPμ).symm
    have hi := MeasureTheory.integrable_withDensity_iff
      (Measure.measurable_rnDeriv P μ) (Measure.rnDeriv_lt_top P μ)
      (g := fun ω => (γ.score : Ω → ℝ) ω ^ 2)
    rw [← hP] at hi
    convert! hi.mp hsquare using 1
    funext ω
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hr : MemLp r 2 μ := by
    change MemLp (fun ω => Real.sqrt (q ω).toReal - Real.sqrt (p ω).toReal -
      (t / 2) * (γ.score : Ω → ℝ) ω * Real.sqrt (p ω).toReal) 2 μ
    have hscaled := hscore_weighted.const_mul (t / 2)
    apply (hq.sub hp).sub
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun ω => by ring) hscaled
  have hchainP : L * p =ᵐ[P] q := by
    simpa only [L, p, q] using
      (Measure.rnDeriv_mul_rnDeriv' (μ := γ.curve t) (ν := P) (κ := μ) hPμ)
  have hP_eq : μ.withDensity (P.rnDeriv μ) = P :=
    Measure.withDensity_rnDeriv_eq P μ hPμ
  have hchain : ∀ᵐ ω ∂μ, p ω ≠ 0 → L ω * p ω = q ω := by
    have h' : L * p =ᵐ[μ.withDensity (P.rnDeriv μ)] q := by
      simpa only [hP_eq] using hchainP
    simpa only [p] using!
      (ae_withDensity_iff (Measure.measurable_rnDeriv P μ)).mp h'
  have hLfinP : ∀ᵐ ω ∂P, L ω ≠ ⊤ := by
    simpa only [L] using Measure.rnDeriv_ne_top (γ.curve t) P
  have hLfin : ∀ᵐ ω ∂μ, p ω ≠ 0 → L ω ≠ ⊤ := by
    have h' : ∀ᵐ ω ∂(μ.withDensity (P.rnDeriv μ)), L ω ≠ ⊤ := by
      simpa only [hP_eq] using hLfinP
    simpa only [p] using
      (ae_withDensity_iff (Measure.measurable_rnDeriv P μ)).mp h'
  have hpoint : (fun ω => D ω ^ 2 * (p ω).toReal) ≤ᵐ[μ]
      fun ω => 4 * r ω ^ 2 := by
    filter_upwards [hchain, hLfin, Measure.rnDeriv_ne_top P μ,
      Measure.rnDeriv_ne_top (γ.curve t) μ] with ω hchainω hLω hpω hqω
    by_cases hp0 : p ω = 0
    · simp only [hp0, ENNReal.toReal_zero, mul_zero]
      positivity
    · have hprod : (q ω).toReal = (L ω).toReal * (p ω).toReal := by
        rw [← hchainω hp0, ENNReal.toReal_mul]
      have hsqrt : Real.sqrt (q ω).toReal =
          Real.sqrt (L ω).toReal * Real.sqrt (p ω).toReal := by
        rw [hprod, Real.sqrt_mul ENNReal.toReal_nonneg]
      have hrid : r ω = Real.sqrt (p ω).toReal *
          (Real.sqrt (L ω).toReal - 1 - (t / 2) * (γ.score : Ω → ℝ) ω) := by
        change Real.sqrt (q ω).toReal - Real.sqrt (p ω).toReal -
          (t / 2) * (γ.score : Ω → ℝ) ω * Real.sqrt (p ω).toReal = _
        rw [hsqrt]
        ring
      have hDid : D ω = 2 *
          (Real.sqrt (L ω).toReal - 1 - (t / 2) * (γ.score : Ω → ℝ) ω) := by
        simp only [D]
        ring
      have hpsq : Real.sqrt (p ω).toReal ^ 2 = (p ω).toReal :=
        Real.sq_sqrt ENNReal.toReal_nonneg
      rw [hrid, hDid]
      nlinarith [hpsq]
  rw [AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
    hPμ (fun ω => D ω ^ 2)]
  change (∫ ω, D ω ^ 2 * (p ω).toReal ∂μ) ≤ _
  calc
    (∫ ω, D ω ^ 2 * (p ω).toReal ∂μ) ≤ ∫ ω, 4 * r ω ^ 2 ∂μ :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)
        (hr.integrable_sq.const_mul 4) hpoint
    _ = 4 * ∫ ω, r ω ^ 2 ∂μ := integral_const_mul 4 (fun ω => r ω ^ 2)
    _ = _ := by
      have hsqrt :=
        AsymptoticStatistics.ForMathlib.QMDAnalytic.sqrt_integral_sq_eq_eLpNorm_toReal hr
      have hnonneg : 0 ≤ ∫ ω, r ω ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
      rw [← Real.sq_sqrt hnonneg, hsqrt]

private theorem baseline_actualResidual_memLp
    (γ : NondominatedQMDPath P) (t : ℝ) (ht : 0 ≤ t) :
    MemLp (fun ω =>
      2 * (Real.sqrt ((γ.curve t).rnDeriv P ω).toReal - 1)
        - t * (γ.score : Ω → ℝ) ω) 2 P := by
  let : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  have hsqrt : MemLp
      (fun ω => Real.sqrt ((γ.curve t).rnDeriv P ω).toReal) 2 P := by
    have hmeas : AEStronglyMeasurable
        (fun ω => Real.sqrt ((γ.curve t).rnDeriv P ω).toReal) P :=
      (Measure.measurable_rnDeriv
        (γ.curve t) P).ennreal_toReal.sqrt.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    convert! Measure.integrable_toReal_rnDeriv (μ := γ.curve t) (ν := P) using 1
    funext ω
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
  have hW : MemLp
      (fun ω => 2 * (Real.sqrt ((γ.curve t).rnDeriv P ω).toReal - 1)) 2 P :=
    (hsqrt.sub hone).const_mul 2
  have hg : MemLp (fun ω => t * (γ.score : Ω → ℝ) ω) 2 P :=
    (Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul t
  exact hW.sub hg

private theorem baseline_actualResidual_sq_isLittleO
    (γ : NondominatedQMDPath P) :
    (fun t : ℝ => ∫ ω,
      (2 * (Real.sqrt ((γ.curve t).rnDeriv P ω).toReal - 1)
        - t * (γ.score : Ω → ℝ) ω) ^ 2 ∂P)
      =o[nhdsWithin 0 (Set.Ioi 0)] (fun t => t ^ 2) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hqmd := (isRightQMD_iff_eLpNorm γ.curve γ.curve_isProbability
    (Lp.aestronglyMeasurable γ.score.val)).1 γ.qmd_limit
  have hqmd_real : Tendsto (fun t : ℝ =>
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal)
      l (nhds 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hqmd
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hqmd_bound : ∀ᶠ t : ℝ in l,
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal ^ 2 ≤
          c / 4 := by
    have hsqrt : 0 < Real.sqrt (c / 4) := Real.sqrt_pos.mpr (by positivity)
    have hevent := hqmd_real.eventually (Iio_mem_nhds hsqrt)
    filter_upwards [hevent] with t ht
    have hnonneg : 0 ≤
        (eLpNorm (γ.comparisonResidual t) 2
          (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal :=
      ENNReal.toReal_nonneg
    nlinarith [Real.sq_sqrt (show 0 ≤ c / 4 by positivity)]
  have hqmd_lt : ∀ᶠ t : ℝ in l,
      eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t < 1 :=
    hqmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [self_mem_nhdsWithin, hqmd_bound, hqmd_lt] with t ht hbound hlt
  have htpos : 0 < t := ht
  have hnorm_fin : eLpNorm (γ.comparisonResidual t) 2
      (canonicalDominator P (γ.curve t)) ≠ ⊤ := by
    intro htop
    have hfalse : (⊤ : ℝ≥0∞) < 1 := by
      simpa only [htop, ENNReal.top_div, ite_eq_right ENNReal.ofReal_ne_top] using hlt
    exact (not_lt_of_ge le_top hfalse).elim
  have hquot_eq :
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t).toReal =
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal / t := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal htpos.le]
  rw [hquot_eq, div_pow] at hbound
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
  have hscaled := (div_le_iff₀ ht2).mp hbound
  rw [Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (baseline_actualResidual_sq_le γ t htpos.le).trans (by
    nlinarith [sq_nonneg
      (eLpNorm (γ.comparisonResidual t) 2
        (canonicalDominator P (γ.curve t))).toReal])

private theorem integral_score_sq_eq_norm_sq (γ : NondominatedQMDPath P) :
    ∫ x, (γ.score : Ω → ℝ) x ^ 2 ∂P = ‖γ.score‖ ^ 2 := by
  have hself :
      (⟪(γ.score : Lp ℝ 2 P), (γ.score : Lp ℝ 2 P)⟫_ℝ : ℝ) =
        ‖(γ.score : Lp ℝ 2 P)‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [MeasureTheory.L2.inner_def] at hself
  have hpoint :
      (fun x => ⟪(γ.score : Ω → ℝ) x, (γ.score : Ω → ℝ) x⟫_ℝ) =ᵐ[P]
        fun x => (γ.score : Ω → ℝ) x ^ 2 := by
    filter_upwards with x
    change (γ.score : Ω → ℝ) x * (γ.score : Ω → ℝ) x = _
    ring
  rw [integral_congr_ae hpoint] at hself
  exact hself

/-- LAN for the logarithm of the actual baseline RN product likelihood.

Proof idea: at each `a≥0`, truncate the square-root likelihood expansion,
use the distinct baseline-zero-likelihood rate to justify `log`, and apply
iid LLN to the quadratic term; split `a=0` at the base point. No MGF or
uniform-integrability assumption is required. -/
theorem log_acProductLikelihood_lan_tendstoInMeasure
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X | ε ≤ |Real.log
              (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal
            - (a * (Real.sqrt n)⁻¹ *
                ∑ i : Fin n, (γ.score : Ω → ℝ) (X i)
              - (a ^ 2 / 2 : ℝ) * ‖γ.score‖ ^ 2)|})
      atTop (nhds 0) := by
  classical
  rcases ha.eq_or_lt with rfl | ha
  · intro ε hε
    have hzero : ∀ n : ℕ,
        (Measure.pi (fun _ : Fin n => P))
          {X | ε ≤ |Real.log (γ.acProductLikelihood 0 n X).toReal|} = 0 := by
      intro n
      have hpi : (fun (X : Fin n → Ω) i => (P.rnDeriv P (X i)).toReal) =ᵐ[
          Measure.pi (fun _ : Fin n => P)] fun _ _ => (1 : ℝ) := by
        exact Measure.ae_eq_pi (μ := fun _ : Fin n => P)
          (f := fun _ ω => (P.rnDeriv P ω).toReal)
          (f' := fun _ _ => (1 : ℝ)) (fun _ => by
            filter_upwards [Measure.rnDeriv_self P] with ω hω
            simp [hω])
      have hset : {X : Fin n → Ω |
          ε ≤ |Real.log (γ.acProductLikelihood 0 n X).toReal|} =ᵐ[
            Measure.pi (fun _ : Fin n => P)] (∅ : Set (Fin n → Ω)) := by
        filter_upwards [hpi] with X hX
        change (ε ≤ |Real.log (γ.acProductLikelihood 0 n X).toReal|) = False
        simp only [acProductLikelihood, curve_at_zero, ENNReal.toReal_prod]
        rw [show (∏ i : Fin n, (P.rnDeriv P (X i)).toReal) = 1 by
          simp [hX]]
        simp [not_le.mpr hε]
      simpa using measure_congr hset
    simp [hzero]
  · let u : ℕ → ℝ := fun n => a * (Real.sqrt n)⁻¹
    let W : ℕ → Ω → ℝ := fun n ω =>
      2 * (Real.sqrt ((γ.curve (u n)).rnDeriv P ω).toReal - 1)
    let D : ℕ → Ω → ℝ := fun n ω => W n ω - u n * (γ.score : Ω → ℝ) ω
    let I : ℝ := ∫ ω, (γ.score : Ω → ℝ) ω ^ 2 ∂P
    have hu_zero : Tendsto u atTop (nhds 0) := by
      have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa only [u, mul_zero] using
        (tendsto_const_nhds.mul hsqrt.inv_tendsto_atTop :
          Tendsto (fun n : ℕ => a * (Real.sqrt n)⁻¹) atTop (nhds (a * 0)))
    have hu_pos : ∀ᶠ n : ℕ in atTop, 0 < u n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact mul_pos ha (inv_pos.mpr (Real.sqrt_pos.mpr (by
        exact_mod_cast (show 0 < n by omega))))
    have hu_right : Tendsto u atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hu_zero, hu_pos⟩
    have hscale : ∀ᶠ n : ℕ in atTop, (n : ℝ) * u n ^ 2 = a ^ 2 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      dsimp only [u]
      rw [mul_pow]
      calc
        (n : ℝ) * (a ^ 2 * (Real.sqrt n)⁻¹ ^ 2) =
            a ^ 2 * ((n : ℝ) * (Real.sqrt n)⁻¹ ^ 2) := by ring
        _ = a ^ 2 := by
          rw [inv_pow, ← div_eq_mul_inv, Real.sq_sqrt hnpos.le, div_self hnpos.ne',
            mul_one]
    have hDsqO : (fun n => ∫ ω, D n ω ^ 2 ∂P) =o[atTop] fun n => u n ^ 2 := by
      simpa only [Function.comp_apply, D, W] using!
        (baseline_actualResidual_sq_isLittleO γ).comp_tendsto hu_right
    have hDscaled : Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, D n ω ^ 2 ∂P)
        atTop (nhds 0) := by
      have hmul : (fun n : ℕ => (n : ℝ) * ∫ ω, D n ω ^ 2 ∂P) =o[atTop]
          (fun n : ℕ => (n : ℝ) * u n ^ 2) :=
        (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO hDsqO
      have hscaleO : (fun n : ℕ => (n : ℝ) * u n ^ 2) =O[atTop]
          (fun _ : ℕ => (1 : ℝ)) :=
        (Filter.EventuallyEq.isBigO hscale).trans
          (Asymptotics.isBigO_const_one ℝ (a ^ 2) atTop)
      exact (Asymptotics.isLittleO_one_iff ℝ).mp (hmul.trans_isBigO hscaleO)
    have hW_mem : ∀ n, MemLp (W n) 2 P := by
      intro n
      have hu_nn : 0 ≤ u n := mul_nonneg ha.le (inv_nonneg.mpr (Real.sqrt_nonneg _))
      have hD := baseline_actualResidual_memLp γ (u n) hu_nn
      have hg := (Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul (u n)
      have hsum := hD.add hg
      convert! hsum using 1
      funext ω
      simp only [Pi.add_apply]
      ring
    have hD_mem : ∀ n, MemLp (D n) 2 P := by
      intro n
      exact (hW_mem n).sub ((Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul (u n))
    have hFsq : Tendsto (fun n : ℕ => ∫ ω,
        (Real.sqrt n * W n ω - a * (γ.score : Ω → ℝ) ω) ^ 2 ∂P)
        atTop (nhds 0) := by
      apply hDscaled.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
      have hsu : Real.sqrt n * u n = a := by
        dsimp only [u]
        calc
          Real.sqrt n * (a * (Real.sqrt n)⁻¹) =
              a * (Real.sqrt n * (Real.sqrt n)⁻¹) := by ring
          _ = a := by rw [mul_inv_cancel₀ hsqrtpos.ne', mul_one]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      have hsquare : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
      calc
        (n : ℝ) * D n ω ^ 2 = Real.sqrt n ^ 2 * D n ω ^ 2 := by rw [hsquare]
        _ = (Real.sqrt n * D n ω) ^ 2 := by ring
        _ = (Real.sqrt n * W n ω - a * (γ.score : Ω → ℝ) ω) ^ 2 := by
          congr 1
          simp only [D]
          calc
            Real.sqrt n * (W n ω - u n * (γ.score : Ω → ℝ) ω) =
                Real.sqrt n * W n ω -
                  (Real.sqrt n * u n) * (γ.score : Ω → ℝ) ω := by ring
            _ = _ := by rw [hsu]
    have hgscaled : MemLp (fun ω => a * (γ.score : Ω → ℝ) ω) 2 P :=
      (Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul a
    have hFmem : ∀ n : ℕ, MemLp
        (fun ω => Real.sqrt n * W n ω - a * (γ.score : Ω → ℝ) ω) 2 P :=
      fun n => (hW_mem n).const_mul (Real.sqrt n) |>.sub hgscaled
    have hnsqW : Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, W n ω ^ 2 ∂P)
        atTop (nhds (a ^ 2 * I)) := by
      have hsquares := AsymptoticStatistics.L2Utils.tendsto_integral_sq_of_tendsto_integral_diff_sq
        P hgscaled (Filter.Eventually.of_forall hFmem) hFsq
      have htarget : ∫ ω, (a * (γ.score : Ω → ℝ) ω) ^ 2 ∂P = a ^ 2 * I := by
        simp only [mul_pow, I]
        rw [integral_const_mul]
      rw [htarget] at hsquares
      apply hsquares.congr'
      filter_upwards with n
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    have hmeanW : Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, W n ω ∂P)
        atTop (nhds (-(a ^ 2 / 4) * I)) := by
      have hsing := γ.singular_mass_localScale_tendsto a ha.le
      have hsing_real : Tendsto
          (fun n : ℕ => (n : ℝ) * (γ.singularMass (u n)).toReal) atTop (nhds 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsing
        convert! this using 1
        · funext n
          simp only [Function.comp_apply, ENNReal.toReal_mul, ENNReal.toReal_natCast, u]
      have hidentity : ∀ n : ℕ,
          ∫ ω, W n ω ∂P =
            -(1 / 4 : ℝ) * ∫ ω, W n ω ^ 2 ∂P - (γ.singularMass (u n)).toReal := by
        intro n
        let : IsProbabilityMeasure (γ.curve (u n)) := γ.curve_isProbability (u n)
          (mul_nonneg ha.le (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        have hL_int : Integrable
            (fun ω => ((γ.curve (u n)).rnDeriv P ω).toReal) P :=
          Measure.integrable_toReal_rnDeriv
        have hW_int := (hW_mem n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        have hWsq_int := (hW_mem n).integrable_sq
        have hpoint : ∀ ω, W n ω = -(1 / 4 : ℝ) * W n ω ^ 2 +
            ((γ.curve (u n)).rnDeriv P ω).toReal - 1 := by
          intro ω
          have hs := Real.sq_sqrt
            (show 0 ≤ ((γ.curve (u n)).rnDeriv P ω).toReal from ENNReal.toReal_nonneg)
          dsimp only [W]
          nlinarith
        calc
          ∫ ω, W n ω ∂P = ∫ ω, (-(1 / 4 : ℝ) * W n ω ^ 2 +
              ((γ.curve (u n)).rnDeriv P ω).toReal - 1) ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall hpoint)
          _ = -(1 / 4 : ℝ) * ∫ ω, W n ω ^ 2 ∂P +
              ∫ ω, ((γ.curve (u n)).rnDeriv P ω).toReal ∂P - 1 := by
            calc
              ∫ ω, (-(1 / 4 : ℝ) * W n ω ^ 2 +
                  ((γ.curve (u n)).rnDeriv P ω).toReal - 1) ∂P =
                  (∫ ω, (-(1 / 4 : ℝ) * W n ω ^ 2 +
                    ((γ.curve (u n)).rnDeriv P ω).toReal) ∂P) -
                    ∫ _ : Ω, (1 : ℝ) ∂P :=
                integral_sub ((hWsq_int.const_mul _).add hL_int) (integrable_const 1)
              _ = (∫ ω, -(1 / 4 : ℝ) * W n ω ^ 2 ∂P) +
                    ∫ ω, ((γ.curve (u n)).rnDeriv P ω).toReal ∂P -
                    ∫ _ : Ω, (1 : ℝ) ∂P := by
                rw [integral_add (hWsq_int.const_mul _) hL_int]
              _ = _ := by
                rw [integral_const_mul, integral_const]
                simp
          _ = _ := by
            rw [show ∫ ω, ((γ.curve (u n)).rnDeriv P ω).toReal ∂P =
                1 - (γ.singularMass (u n)).toReal by
              simpa only [singularMass, singularPart, measureReal_def, measure_univ,
                ENNReal.toReal_one] using
                (Measure.integral_toReal_rnDeriv' (μ := γ.curve (u n)) (ν := P))]
            ring
      have hmain := (hnsqW.const_mul (-(1 / 4 : ℝ))).sub hsing_real
      convert! hmain using 1
      · funext n
        rw [hidentity]
        ring
      · ring_nf
    let A : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n X =>
      (∑ i : Fin n, D n (X i)) - (n : ℝ) * ∫ ω, D n ω ∂P
    have hA : ∀ ε > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          {X | ε ≤ |A n X|}) atTop (nhds 0) := by
      intro ε hε
      have hmem : ∀ n, MemLp (A n) 2 (Measure.pi (fun _ : Fin n => P)) := by
        intro n
        have hcoord : ∀ i : Fin n, MemLp (fun X : Fin n → Ω => D n (X i)) 2
            (Measure.pi (fun _ : Fin n => P)) := fun i =>
          (hD_mem n).comp_measurePreserving (measurePreserving_eval _ i)
        have hsum : MemLp (fun X : Fin n → Ω => ∑ i : Fin n, D n (X i)) 2
            (Measure.pi (fun _ : Fin n => P)) := by
          simpa only using MeasureTheory.memLp_finsetSum Finset.univ fun i _ => hcoord i
        exact hsum.sub (memLp_const _)
      have hmean : ∀ n, ∫ X, A n X ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
        intro n
        have hDint := (hD_mem n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        have hcoordint : ∀ i : Fin n, Integrable
            (fun X : Fin n → Ω => D n (X i)) (Measure.pi (fun _ : Fin n => P)) :=
          fun i => MeasureTheory.integrable_comp_eval hDint
        have hcoordval : ∀ i : Fin n,
            ∫ X : Fin n → Ω, D n (X i) ∂(Measure.pi (fun _ : Fin n => P)) =
              ∫ ω, D n ω ∂P := fun i =>
          MeasureTheory.integral_comp_eval (μ := fun _ : Fin n => P) (i := i)
            (hD_mem n).aestronglyMeasurable
        dsimp only [A]
        rw [integral_sub (integrable_finsetSum Finset.univ fun i _ => hcoordint i)
          (integrable_const _), integral_finsetSum _ fun i _ => hcoordint i]
        simp_rw [hcoordval]
        simp [integral_const]
      have hvarle : ∀ n, variance (A n) (Measure.pi (fun _ : Fin n => P)) ≤
          (n : ℝ) * ∫ ω, D n ω ^ 2 ∂P := by
        intro n
        have hsum_meas : AEStronglyMeasurable
            (fun X : Fin n → Ω => ∑ i : Fin n, D n (X i))
            (Measure.pi (fun _ : Fin n => P)) := by
          exact Finset.aestronglyMeasurable_fun_sum Finset.univ
            (fun i _ => ((hD_mem n).comp_measurePreserving
              (measurePreserving_eval _ i)).aestronglyMeasurable)
        rw [show A n = fun X => (∑ i : Fin n, D n (X i)) -
            (n : ℝ) * ∫ ω, D n ω ∂P by rfl,
          variance_sub_const hsum_meas]
        rw [show (fun X : Fin n → Ω => ∑ i : Fin n, D n (X i)) =
            ∑ i : Fin n, fun X => D n (X i) by funext X; simp [Finset.sum_apply],
          variance_sum_pi (fun _ : Fin n => hD_mem n)]
        have hv : variance (D n) P ≤ ∫ ω, D n ω ^ 2 ∂P :=
          variance_le_expectation_sq (hD_mem n).aestronglyMeasurable
        simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using
          mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg n)
      have hbound : Tendsto (fun n : ℕ => ENNReal.ofReal
          (((n : ℝ) * ∫ ω, D n ω ^ 2 ∂P) / ε ^ 2)) atTop (nhds 0) := by
        have hr := (hDscaled.div_const (ε ^ 2))
        have hr' : Tendsto
            (fun n : ℕ => ((n : ℝ) * ∫ ω, D n ω ^ 2 ∂P) / ε ^ 2)
            atTop (nhds 0) := by simpa using hr
        have hc := (ENNReal.continuous_ofReal.tendsto 0).comp hr'
        simpa using! hc
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hbound (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hc := meas_ge_le_variance_div_sq (hmem n) hε
      rw [hmean n] at hc
      have hc' : (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |A n X|} ≤
          ENNReal.ofReal (variance (A n) (Measure.pi (fun _ : Fin n => P)) / ε ^ 2) := by
        simpa only [sub_zero, Real.norm_eq_abs] using hc
      exact hc'.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (hvarle n) (sq_nonneg _)))
    let F : ℕ → Ω → ℝ := fun n ω =>
      Real.sqrt n * W n ω - a * (γ.score : Ω → ℝ) ω
    let G : ℕ → Ω → ℝ := fun n ω =>
      Real.sqrt n * W n ω + a * (γ.score : Ω → ℝ) ω
    have hGmem : ∀ n, MemLp (G n) 2 P := fun n =>
      ((hW_mem n).const_mul (Real.sqrt n)).add hgscaled
    have hGsqBound : ∀ n, ∫ ω, G n ω ^ 2 ∂P ≤
        2 * ∫ ω, F n ω ^ 2 ∂P + 8 * a ^ 2 * I := by
      intro n
      have hmajor : Integrable (fun ω => 2 * F n ω ^ 2 +
          8 * (a * (γ.score : Ω → ℝ) ω) ^ 2) P :=
        ((hFmem n).integrable_sq.const_mul 2).add (hgscaled.integrable_sq.const_mul 8)
      have hle : (∫ ω, G n ω ^ 2 ∂P) ≤
          ∫ ω, 2 * F n ω ^ 2 + 8 * (a * (γ.score : Ω → ℝ) ω) ^ 2 ∂P :=
        integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hmajor (Filter.Eventually.of_forall fun ω => by
          have hrel : G n ω = F n ω + 2 * (a * (γ.score : Ω → ℝ) ω) := by
            dsimp only [F, G]
            ring
          change G n ω ^ 2 ≤
            2 * F n ω ^ 2 + 8 * (a * (γ.score : Ω → ℝ) ω) ^ 2
          rw [hrel]
          nlinarith [sq_nonneg
            (F n ω - 2 * (a * (γ.score : Ω → ℝ) ω))])
      calc
        ∫ ω, G n ω ^ 2 ∂P ≤
            ∫ ω, 2 * F n ω ^ 2 + 8 * (a * (γ.score : Ω → ℝ) ω) ^ 2 ∂P := hle
        _ = 2 * ∫ ω, F n ω ^ 2 ∂P + 8 * a ^ 2 * I := by
          rw [integral_add ((hFmem n).integrable_sq.const_mul 2)
            (hgscaled.integrable_sq.const_mul 8), integral_const_mul,
            integral_const_mul]
          simp only [mul_pow, I]
          rw [integral_const_mul]
          ring
    have hL1 : Tendsto (fun n : ℕ => ∫ ω,
        |(n : ℝ) * W n ω ^ 2 - a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2| ∂P)
        atTop (nhds 0) := by
      have hFsqF : Tendsto (fun n => ∫ ω, F n ω ^ 2 ∂P) atTop (nhds 0) := by
        simpa only [F] using hFsq
      have hFroot : Tendsto (fun n => Real.sqrt (∫ ω, F n ω ^ 2 ∂P))
          atTop (nhds 0) := by
        simpa only [Real.sqrt_zero] using! (Real.continuous_sqrt.tendsto 0).comp hFsqF
      have hGbd : ∀ᶠ n : ℕ in atTop, ∫ ω, G n ω ^ 2 ∂P ≤ 2 + 8 * a ^ 2 * I := by
        have hev := hFsqF.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
        filter_upwards [hev] with n hn
        exact (hGsqBound n).trans (by linarith)
      have hGroot_bd : ∀ᶠ n : ℕ in atTop,
          Real.sqrt (∫ ω, G n ω ^ 2 ∂P) ≤
            Real.sqrt (2 + 8 * a ^ 2 * I) := by
        filter_upwards [hGbd] with n hn
        exact Real.sqrt_le_sqrt hn
      have hprod : Tendsto (fun n =>
          Real.sqrt (∫ ω, F n ω ^ 2 ∂P) * Real.sqrt (∫ ω, G n ω ^ 2 ∂P))
          atTop (nhds 0) := by
        refine squeeze_zero'
          (g := fun n => Real.sqrt (∫ ω, F n ω ^ 2 ∂P) *
            Real.sqrt (2 + 8 * a ^ 2 * I)) ?_ ?_ ?_
        · filter_upwards with n
          exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · filter_upwards [hGroot_bd] with n hn
          exact mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
        · simpa only [zero_mul] using
            hFroot.mul_const (Real.sqrt (2 + 8 * a ^ 2 * I))
      refine squeeze_zero'
        (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
        ?_ hprod
      filter_upwards with n
      have hcs := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq P
        (hFmem n).norm (hGmem n).norm
      have hpoint : (fun ω => |F n ω| * |G n ω|) =
          fun ω => |(n : ℝ) * W n ω ^ 2 -
            a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2| := by
        funext ω
        rw [← abs_mul]
        have hsquare : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
        dsimp only [F, G]
        congr 1
        nlinarith
      rw [← hpoint]
      have hnonneg : 0 ≤ ∫ ω, |F n ω| * |G n ω| ∂P :=
        integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hcs' : ∫ ω, |F n ω| * |G n ω| ∂P ≤
          Real.sqrt (∫ ω, F n ω ^ 2 ∂P) *
            Real.sqrt (∫ ω, G n ω ^ 2 ∂P) := by
        rw [← abs_of_nonneg hnonneg]
        simpa only [Real.norm_eq_abs, abs_abs, sq_abs] using hcs
      exact hcs'
    let Δ : ℕ → Ω → ℝ := fun n ω =>
      (n : ℝ) * W n ω ^ 2 - a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2
    have hΔint : ∀ n, Integrable (Δ n) P := by
      intro n
      exact ((hW_mem n).integrable_sq.const_mul (n : ℝ)).sub
        ((Lp.memLp (γ.score : Lp ℝ 2 P)).integrable_sq.const_mul (a ^ 2))
    let E : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n X =>
      (n : ℝ)⁻¹ * ∑ i : Fin n, Δ n (X i)
    have hEint : ∀ n, Integrable (E n) (Measure.pi (fun _ : Fin n => P)) := by
      intro n
      exact (integrable_finsetSum Finset.univ fun i _ =>
        MeasureTheory.integrable_comp_eval (hΔint n)).const_mul _
    have hEabs : ∀ n, ∫ X, |E n X| ∂(Measure.pi (fun _ : Fin n => P)) ≤
        ∫ ω, |Δ n ω| ∂P := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [E, Nat.cast_zero, inv_zero, zero_mul, Finset.univ_eq_empty,
          Finset.sum_empty, abs_zero, integral_zero]
        exact integral_nonneg fun _ => abs_nonneg _
      · have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
        have hpoint : ∀ X : Fin n → Ω,
            |E n X| ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |Δ n (X i)| := by
          intro X
          dsimp only [E]
          rw [abs_mul, abs_of_pos (inv_pos.mpr hnR)]
          exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
            (inv_nonneg.mpr hnR.le)
        have hsumabs : Integrable (fun X : Fin n → Ω =>
            ∑ i : Fin n, |Δ n (X i)|) (Measure.pi (fun _ : Fin n => P)) :=
          integrable_finsetSum Finset.univ fun i _ =>
            MeasureTheory.integrable_comp_eval (μ := fun _ : Fin n => P) (i := i)
              (hΔint n).abs
        calc
          ∫ X, |E n X| ∂(Measure.pi (fun _ : Fin n => P)) ≤
              ∫ X, (n : ℝ)⁻¹ * ∑ i : Fin n, |Δ n (X i)|
                ∂(Measure.pi (fun _ : Fin n => P)) :=
            integral_mono (hEint n).abs (hsumabs.const_mul _) hpoint
          _ = (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ ω, |Δ n ω| ∂P := by
            rw [integral_const_mul]
            congr 1
            calc
              ∫ X : Fin n → Ω, ∑ i : Fin n, |Δ n (X i)|
                  ∂(Measure.pi (fun _ : Fin n => P)) =
                  ∑ i : Fin n, ∫ X : Fin n → Ω, |Δ n (X i)|
                    ∂(Measure.pi (fun _ : Fin n => P)) :=
                integral_finsetSum Finset.univ fun i _ =>
                  MeasureTheory.integrable_comp_eval (μ := fun _ : Fin n => P) (i := i)
                    (hΔint n).abs
              _ = ∑ i : Fin n, ∫ ω, |Δ n ω| ∂P := by
                apply Finset.sum_congr rfl
                intro i hi
                exact MeasureTheory.integral_comp_eval (μ := fun _ : Fin n => P) (i := i)
                  (hΔint n).abs.aestronglyMeasurable
          _ = ∫ ω, |Δ n ω| ∂P := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, ← mul_assoc,
              inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_mul]
    have hE : ∀ ε > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |E n X|})
        atTop (nhds 0) := by
      intro ε hε
      have hupper : Tendsto (fun n : ℕ => ENNReal.ofReal
          ((∫ ω, |Δ n ω| ∂P) / ε)) atTop (nhds 0) := by
        have hr : Tendsto (fun n : ℕ => (∫ ω, |Δ n ω| ∂P) / ε)
            atTop (nhds 0) := by
          simpa only [Δ, zero_div] using hL1.div_const ε
        simpa using! (ENNReal.continuous_ofReal.tendsto 0).comp hr
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
        (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hmark := mul_meas_ge_le_integral_of_nonneg
        (μ := Measure.pi (fun _ : Fin n => P)) (f := fun X => |E n X|)
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hEint n).abs ε
      have hreal : (Measure.pi (fun _ : Fin n => P)).real {X | ε ≤ |E n X|} ≤
          (∫ ω, |Δ n ω| ∂P) / ε := by
        apply (le_div_iff₀' hε).2
        exact hmark.trans (hEabs n)
      rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal]
      · exact hreal
      · exact div_nonneg (integral_nonneg fun _ => abs_nonneg _) hε.le
    have hscore2int : Integrable
        (fun ω => a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2) P :=
      (Lp.memLp (γ.score : Lp ℝ 2 P)).integrable_sq.const_mul _
    have hLLN := AsymptoticStatistics.iid_lln_in_prob_l1
      (P := P) (fun ω => a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2) hscore2int
    have hmeanScore2 : ∫ ω, a ^ 2 * (γ.score : Ω → ℝ) ω ^ 2 ∂P =
        a ^ 2 * I := by rw [integral_const_mul]
    have hB : ∀ ε > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          {X | ε ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|})
        atTop (nhds 0) := by
      intro ε hε
      let δ := ε / 2
      have hδ : 0 < δ := by dsimp only [δ]; positivity
      have hlln := hLLN δ hδ
      rw [hmeanScore2] at hlln
      have herr := hE δ hδ
      have hsum : Tendsto (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
              {X | δ ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n,
                a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I|} +
            (Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |E n X|})
          atTop (nhds 0) := by
        simpa using hlln.add herr
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hsum (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hdecomp : ∀ X : Fin n → Ω,
          ∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I =
            ((n : ℝ)⁻¹ * ∑ i : Fin n,
                a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I) + E n X := by
        intro X
        dsimp only [E, Δ]
        have hpt : ∀ i : Fin n,
            a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 +
              ((n : ℝ) * W n (X i) ^ 2 -
                a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2) =
              (n : ℝ) * W n (X i) ^ 2 := by intro i; ring
        calc
          ∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I =
              ((n : ℝ)⁻¹ * ∑ i : Fin n,
                a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 +
                (n : ℝ)⁻¹ * ∑ i : Fin n,
                  ((n : ℝ) * W n (X i) ^ 2 -
                    a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2)) - a ^ 2 * I := by
            congr 1
            rw [← mul_add, ← Finset.sum_add_distrib]
            simp_rw [hpt]
            rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hnpos.ne', one_mul]
          _ = _ := by ring
      have hincl : {X : Fin n → Ω |
          ε ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|} ⊆
          {X | δ ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n,
            a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I|} ∪
          {X | δ ≤ |E n X|} := by
        intro X hX
        rw [Set.mem_union]
        by_contra hnot
        rw [not_or] at hnot
        have h1 : |(n : ℝ)⁻¹ * ∑ i : Fin n,
            a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I| < δ := by
          simpa only [Set.mem_ofPred_eq, not_le] using hnot.1
        have h2 : |E n X| < δ := by
          simpa only [Set.mem_ofPred_eq, not_le] using hnot.2
        rw [Set.mem_ofPred_eq, hdecomp X] at hX
        have ht := abs_add_le
          ((n : ℝ)⁻¹ * ∑ i : Fin n,
            a ^ 2 * (γ.score : Ω → ℝ) (X i) ^ 2 - a ^ 2 * I) (E n X)
        dsimp only [δ] at h1 h2
        linarith
      exact (measure_mono hincl).trans (measure_union_le _ _)
    have hW_meas : ∀ n, Measurable (W n) := by
      intro n
      exact measurable_const.mul
        ((Measure.measurable_rnDeriv (γ.curve (u n)) P).ennreal_toReal.sqrt.sub
          measurable_const)
    have hI_nonneg : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
    have hDsq0 : Tendsto (fun n => ∫ ω, D n ω ^ 2 ∂P) atTop (nhds 0) := by
      have hu2 : Tendsto (fun n => u n ^ 2) atTop (nhds 0) := by
        convert! hu_zero.pow 2 using 1
        norm_num
      exact hDsqO.isBigO.trans_tendsto hu2
    have hWsq0 : Tendsto (fun n => ∫ ω, W n ω ^ 2 ∂P) atTop (nhds 0) := by
      have hupper : Tendsto (fun n =>
          2 * ∫ ω, D n ω ^ 2 ∂P + 2 * u n ^ 2 * I) atTop (nhds 0) := by
        have hu2 := hu_zero.pow 2
        simpa [mul_assoc] using
          (hDsq0.const_mul 2).add ((hu2.const_mul 2).mul_const I)
      refine squeeze_zero' (g := fun n =>
          2 * ∫ ω, D n ω ^ 2 ∂P + 2 * u n ^ 2 * I)
        (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_ hupper
      filter_upwards with n
      have hmajor : Integrable (fun ω =>
          2 * D n ω ^ 2 + 2 * (u n * (γ.score : Ω → ℝ) ω) ^ 2) P :=
        ((hD_mem n).integrable_sq.const_mul 2).add
          (((Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul (u n)).integrable_sq.const_mul 2)
      calc
        ∫ ω, W n ω ^ 2 ∂P ≤
            ∫ ω, 2 * D n ω ^ 2 +
              2 * (u n * (γ.score : Ω → ℝ) ω) ^ 2 ∂P := by
          apply integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => sq_nonneg _) hmajor
          filter_upwards with ω
          have hrel : W n ω = D n ω + u n * (γ.score : Ω → ℝ) ω := by
            dsimp only [D]
            ring
          rw [hrel]
          nlinarith [sq_nonneg (D n ω - u n * (γ.score : Ω → ℝ) ω)]
        _ = 2 * ∫ ω, D n ω ^ 2 ∂P + 2 * u n ^ 2 * I := by
          rw [integral_add ((hD_mem n).integrable_sq.const_mul 2)
            (((Lp.memLp (γ.score : Lp ℝ 2 P)).const_mul (u n)).integrable_sq.const_mul 2),
            integral_const_mul, integral_const_mul]
          simp only [mul_pow, I, integral_const_mul]
          ring
    have htailO : ∀ δ > 0,
        (fun n : ℕ => P.real {ω | δ ≤ |W n ω|}) =o[atTop] (fun n => u n ^ 2) := by
      intro δ hδ
      have hpack := AsymptoticStatistics.L2Utils.l2_tail_controls_of_approx
        atTop P W D (fun n ω => u n * (γ.score : Ω → ℝ) ω) u
        (fun ω => (γ.score : Ω → ℝ) ω ^ 2)
        hW_meas (Filter.Eventually.of_forall hW_mem) hWsq0
        (Filter.Eventually.of_forall hD_mem) hDsqO
        (Lp.memLp (γ.score : Lp ℝ 2 P)).integrable_sq
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (fun n => mul_nonneg ha.le (inv_nonneg.mpr (Real.sqrt_nonneg n)))
        (fun n ω => by dsimp only [D]; ring)
        (fun n ω => by simp only [mul_pow]; exact le_rfl)
        (fun _ => (0 : ℝ)) MemLp.zero δ hδ
      exact hpack.2.2.1
    have htailScaled : ∀ δ > 0, Tendsto
        (fun n : ℕ => (n : ℝ) * P.real {ω | δ ≤ |W n ω|})
        atTop (nhds 0) := by
      intro δ hδ
      have hmul : (fun n : ℕ => (n : ℝ) * P.real {ω | δ ≤ |W n ω|})
          =o[atTop] (fun n => (n : ℝ) * u n ^ 2) :=
        (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO
          (htailO δ hδ)
      have hscaleO : (fun n : ℕ => (n : ℝ) * u n ^ 2) =O[atTop]
          (fun _ : ℕ => (1 : ℝ)) :=
        (Filter.EventuallyEq.isBigO hscale).trans
          (Asymptotics.isBigO_const_one ℝ (a ^ 2) atTop)
      exact (Asymptotics.isLittleO_one_iff ℝ).mp (hmul.trans_isBigO hscaleO)
    have hMax : ∀ δ > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          (⋃ i ∈ (Finset.univ : Finset (Fin n)), {X | δ ≤ |W n (X i)|}))
        atTop (nhds 0) := by
      intro δ hδ
      have hsingle : Tendsto (fun n : ℕ => ENNReal.ofReal
          ((n : ℝ) * P.real {ω | δ ≤ |W n ω|})) atTop (nhds 0) := by
        simpa only [Function.comp_apply, ENNReal.ofReal_zero] using!
          (ENNReal.continuous_ofReal.tendsto 0).comp (htailScaled δ hδ)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hsingle (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hset : MeasurableSet {ω | δ ≤ |W n ω|} :=
        measurableSet_le measurable_const ((hW_meas n).abs)
      have heach : ∀ i : Fin n,
          (Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |W n (X i)|} =
            P {ω | δ ≤ |W n ω|} := by
        intro i
        rw [show {X : Fin n → Ω | δ ≤ |W n (X i)|} =
            (fun X : Fin n → Ω => X i) ⁻¹' {ω | δ ≤ |W n ω|} by rfl,
          ← Measure.map_apply (measurable_pi_apply i) hset,
          (measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
      calc
        (Measure.pi (fun _ : Fin n => P))
            (⋃ i ∈ (Finset.univ : Finset (Fin n)), {X | δ ≤ |W n (X i)|}) ≤
            ∑ i ∈ (Finset.univ : Finset (Fin n)),
              (Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |W n (X i)|} :=
          measure_biUnion_finset_le _ _
        _ = (n : ℕ) • P {ω | δ ≤ |W n ω|} := by simp only [heach,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ = ENNReal.ofReal ((n : ℝ) * P.real {ω | δ ≤ |W n ω|}) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_toReal (measure_ne_top P _),
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
          rfl
    let R : ℝ → ℝ := AsymptoticStatistics.ForMathlib.logTaylorRemainder
    have hC : ∀ ε > 0, Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          {X | ε ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|})
        atTop (nhds 0) := by
      intro ε hε
      let Mbd : ℝ := a ^ 2 * I + 1
      have hMbd : 0 < Mbd := by dsimp only [Mbd]; positivity
      let ε' : ℝ := ε / (2 * Mbd)
      have hε' : 0 < ε' := by dsimp only [ε']; positivity
      obtain ⟨η, hη, hR⟩ := Metric.tendsto_nhds_nhds.mp
        AsymptoticStatistics.ForMathlib.logTaylorRemainder_tendsto_zero ε' hε'
      have hηtwo : 0 < η / 2 := by positivity
      have hmax := hMax (η / 2) hηtwo
      have hb := hB 1 one_pos
      have hsum : Tendsto (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
              (⋃ i ∈ (Finset.univ : Finset (Fin n)), {ω | η / 2 ≤ |W n (ω i)|}) +
            (Measure.pi (fun _ : Fin n => P))
              {X | 1 ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|})
          atTop (nhds 0) := by
        simpa using hmax.add hb
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hsum (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hincl : {X : Fin n → Ω |
          ε ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|} ⊆
          (⋃ i ∈ (Finset.univ : Finset (Fin n)), {X | η / 2 ≤ |W n (X i)|}) ∪
            {X | 1 ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|} := by
        intro X hX
        rw [Set.mem_union]
        by_contra hnot
        rw [not_or] at hnot
        have hsmall : ∀ i : Fin n, |W n (X i)| < η / 2 := by
          intro i
          have hi : ¬ X ∈ {X : Fin n → Ω | η / 2 ≤ |W n (X i)|} := by
            intro hi
            exact hnot.1 (Set.mem_biUnion (Finset.mem_univ i) hi)
          simpa only [Set.mem_ofPred_eq, not_le] using hi
        have hBlt : ∑ i : Fin n, W n (X i) ^ 2 < Mbd := by
          have hb' : |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I| < 1 := by
            simpa only [Set.mem_ofPred_eq, not_le] using hnot.2
          have hab := abs_lt.mp hb'
          dsimp only [Mbd]
          linarith [hab.2]
        have hRsmall : ∀ i : Fin n, |R (W n (X i))| < ε' := by
          intro i
          have hw : |W n (X i)| < η := lt_trans (hsmall i) (by linarith)
          have hd : dist (W n (X i)) (0 : ℝ) < η := by
            simpa only [dist_zero_right, Real.norm_eq_abs] using hw
          have := hR hd
          simpa only [R, dist_zero_right, Real.norm_eq_abs] using this
        have hsummand : ∀ i : Fin n,
            |W n (X i) ^ 2 * R (W n (X i))| ≤ W n (X i) ^ 2 * ε' := by
          intro i
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hRsmall i).le (sq_nonneg _)
        have habssum := Finset.abs_sum_le_sum_abs
          (fun i : Fin n => W n (X i) ^ 2 * R (W n (X i))) Finset.univ
        have hsumle : ∑ i : Fin n, |W n (X i) ^ 2 * R (W n (X i))| ≤
            ε' * ∑ i : Fin n, W n (X i) ^ 2 := by
          calc
            ∑ i : Fin n, |W n (X i) ^ 2 * R (W n (X i))| ≤
                ∑ i : Fin n, W n (X i) ^ 2 * ε' :=
              Finset.sum_le_sum fun i _ => hsummand i
            _ = _ := by rw [← Finset.sum_mul, mul_comm]
        have hfinal : |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| < ε := by
          have heq : ε' * Mbd = ε / 2 := by dsimp only [ε']; field_simp
          calc
            |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| ≤
                ∑ i : Fin n, |W n (X i) ^ 2 * R (W n (X i))| := habssum
            _ ≤ ε' * ∑ i : Fin n, W n (X i) ^ 2 := hsumle
            _ < ε' * Mbd := mul_lt_mul_of_pos_left hBlt hε'
            _ = ε / 2 := heq
            _ < ε := by linarith
        exact (not_lt_of_ge hX) hfinal
      exact (measure_mono hincl).trans (measure_union_le _ _)
    have hzero : Tendsto
        (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
          (⋃ i ∈ (Finset.univ : Finset (Fin n)),
            {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}))
        atTop (nhds 0) := by
      have hlocal := γ.base_zeroLikelihood_localScale_tendsto a ha.le
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hlocal (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards with n
      have hset : MeasurableSet
          {ω | ((γ.curve (u n)).rnDeriv P ω).toReal = 0} :=
        (Measure.measurable_rnDeriv (γ.curve (u n)) P).ennreal_toReal
          (measurableSet_singleton 0)
      have heach : ∀ i : Fin n,
          (Measure.pi (fun _ : Fin n => P))
              {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0} =
            γ.baseZeroLikelihoodMass (u n) := by
        intro i
        rw [show {X : Fin n → Ω | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0} =
            (fun X : Fin n → Ω => X i) ⁻¹'
              {ω | ((γ.curve (u n)).rnDeriv P ω).toReal = 0} by rfl,
          ← Measure.map_apply (measurable_pi_apply i) hset,
          (measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
        rfl
      calc
        (Measure.pi (fun _ : Fin n => P))
            (⋃ i ∈ (Finset.univ : Finset (Fin n)),
              {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}) ≤
            ∑ i ∈ (Finset.univ : Finset (Fin n)),
              (Measure.pi (fun _ : Fin n => P))
                {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0} :=
          measure_biUnion_finset_le _ _
        _ = (n : ℕ) • γ.baseZeroLikelihoodMass (u n) := by
          simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        _ = (n : ℝ≥0∞) * γ.baseZeroLikelihoodMass
              (a * (Real.sqrt n)⁻¹) := by
          rw [nsmul_eq_mul]
    have hscoreMean : ∫ ω, (γ.score : Ω → ℝ) ω ∂P = 0 := by
      have hmem : (γ.score : Lp ℝ 2 P) ∈ L2ZeroMean P := γ.score.2
      change (γ.score : Lp ℝ 2 P) ∈
        LinearMap.ker (integralL2 P).toLinearMap at hmem
      rw [LinearMap.mem_ker] at hmem
      have hinner : ⟪oneL2 P, (γ.score : Lp ℝ 2 P)⟫_ℝ = 0 := hmem
      rw [MeasureTheory.L2.inner_def] at hinner
      have hone : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      have heq : ∫ ω, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
            ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ ∂P =
          ∫ ω, (γ.score : Ω → ℝ) ω ∂P := by
        apply integral_congr_ae
        filter_upwards [hone] with ω hω
        rw [show ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
            ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ =
              (γ.score : Ω → ℝ) ω * (oneL2 P : Ω → ℝ) ω by rfl,
          hω, mul_one]
      rw [heq] at hinner
      exact hinner
    have hDmean : ∀ n, ∫ ω, D n ω ∂P = ∫ ω, W n ω ∂P := by
      intro n
      have hWint := (hW_mem n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hgint := (Lp.memLp (γ.score : Lp ℝ 2 P)).integrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hscaled : ∫ ω, u n * (γ.score : Ω → ℝ) ω ∂P =
          u n * ∫ ω, (γ.score : Ω → ℝ) ω ∂P :=
        integral_const_mul (u n) (γ.score : Ω → ℝ)
      change (∫ ω, W n ω - u n * (γ.score : Ω → ℝ) ω ∂P) = _
      rw [integral_sub hWint (hgint.const_mul _), hscaled, hscoreMean,
        mul_zero, sub_zero]
    have hAid : ∀ n (X : Fin n → Ω), A n X =
        ∑ i : Fin n, W n (X i) - u n * ∑ i : Fin n, (γ.score : Ω → ℝ) (X i) -
          (n : ℝ) * ∫ ω, W n ω ∂P := by
      intro n X
      change (∑ i : Fin n,
          (W n (X i) - u n * (γ.score : Ω → ℝ) (X i))) -
          (n : ℝ) * ∫ ω, D n ω ∂P = _
      rw [hDmean]
      have hscaled : ∑ i : Fin n, u n * (γ.score : Ω → ℝ) (X i) =
          u n * ∑ i : Fin n, (γ.score : Ω → ℝ) (X i) := by
        rw [Finset.mul_sum]
      rw [Finset.sum_sub_distrib, hscaled]
    have hmeanDet : Tendsto (fun n : ℕ =>
        (n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I) atTop (nhds 0) := by
      convert! hmeanW.add_const (a ^ 2 / 4 * I) using 1
      ring_nf
    have hnormI : I = ‖γ.score‖ ^ 2 := integral_score_sq_eq_norm_sq γ
    let Z : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n X =>
      Real.log (γ.acProductLikelihood (u n) n X).toReal -
        (u n * ∑ i : Fin n, (γ.score : Ω → ℝ) (X i) -
          a ^ 2 / 2 * ‖γ.score‖ ^ 2)
    have hdecomp : ∀ n (X : Fin n → Ω),
        X ∉ (⋃ i ∈ (Finset.univ : Finset (Fin n)),
          {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}) →
        Z n X =
          ((A n X + ((n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I)) +
            (-(1 / 4 : ℝ) * (∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I))) +
            (1 / 2 : ℝ) * ∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i)) := by
      intro n X hnonzero
      have hfac : ∀ i : Fin n, ((γ.curve (u n)).rnDeriv P (X i)).toReal ≠ 0 := by
        intro i hi
        exact hnonzero (Set.mem_biUnion (Finset.mem_univ i) hi)
      have hlog : Real.log (γ.acProductLikelihood (u n) n X).toReal =
          ∑ i : Fin n, Real.log (((γ.curve (u n)).rnDeriv P (X i)).toReal) := by
        simp only [acProductLikelihood, ENNReal.toReal_prod]
        exact Real.log_prod fun i _ => hfac i
      have htaylor : ∀ i : Fin n,
          Real.log (((γ.curve (u n)).rnDeriv P (X i)).toReal) =
            W n (X i) - W n (X i) ^ 2 / 4 +
              W n (X i) ^ 2 / 2 * R (W n (X i)) := by
        intro i
        have ht := AsymptoticStatistics.ForMathlib.log_div_nonneg_eq_sqrt_taylor
          (a := ((γ.curve (u n)).rnDeriv P (X i)).toReal) (b := 1)
          ENNReal.toReal_nonneg zero_le_one
        simpa only [div_one, W, R] using ht
      dsimp only [Z]
      rw [hlog]
      rw [Finset.sum_congr rfl fun i _ => htaylor i]
      have hsplit : ∑ i : Fin n,
          (W n (X i) - W n (X i) ^ 2 / 4 +
            W n (X i) ^ 2 / 2 * R (W n (X i))) =
          (∑ i : Fin n, W n (X i)) -
            (1 / 4 : ℝ) * ∑ i : Fin n, W n (X i) ^ 2 +
            (1 / 2 : ℝ) * ∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsplit, hAid, hnormI]
      ring
    intro ε hε
    let δ : ℝ := ε / 5
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    have hAδ := hA δ hδ
    have hBδ := hB (4 * δ) (mul_pos (by norm_num) hδ)
    have hCδ := hC (2 * δ) (mul_pos (by norm_num) hδ)
    have hdet : Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|})
        atTop (nhds 0) := by
      have hev := hmeanDet.eventually (Metric.ball_mem_nhds (0 : ℝ) hδ)
      have heq : (fun n : ℕ =>
          (Measure.pi (fun _ : Fin n => P))
            {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|}) =ᶠ[atTop]
          (fun _ => (0 : ℝ≥0∞)) := by
        filter_upwards [hev] with n hn
        rw [show {X : Fin n → Ω |
            δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|} = ∅ by
          ext X
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
          simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, iff_false] using
            (not_le.mpr hn), measure_empty]
      exact (tendsto_congr' heq).mpr tendsto_const_nhds
    have hsum : Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
            (⋃ i ∈ (Finset.univ : Finset (Fin n)),
              {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}) +
          ((Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |A n X|} +
          ((Measure.pi (fun _ : Fin n => P))
            {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|} +
          ((Measure.pi (fun _ : Fin n => P))
            {X | 4 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|} +
          (Measure.pi (fun _ : Fin n => P))
            {X | 2 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|}))))
        atTop (nhds 0) := by
      simpa using hzero.add (hAδ.add (hdet.add (hBδ.add hCδ)))
    have hbound : ∀ n,
        (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |Z n X|} ≤
          (Measure.pi (fun _ : Fin n => P))
              (⋃ i ∈ (Finset.univ : Finset (Fin n)),
                {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}) +
            ((Measure.pi (fun _ : Fin n => P)) {X | δ ≤ |A n X|} +
            ((Measure.pi (fun _ : Fin n => P))
              {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|} +
            ((Measure.pi (fun _ : Fin n => P))
              {X | 4 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|} +
            (Measure.pi (fun _ : Fin n => P))
              {X | 2 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|}))) := by
      intro n
      let Z0 : Set (Fin n → Ω) :=
        ⋃ i ∈ (Finset.univ : Finset (Fin n)),
          {X | ((γ.curve (u n)).rnDeriv P (X i)).toReal = 0}
      let EA : Set (Fin n → Ω) := {X | δ ≤ |A n X|}
      let ED : Set (Fin n → Ω) :=
        {X | δ ≤ |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I|}
      let EB : Set (Fin n → Ω) :=
        {X | 4 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I|}
      let EC : Set (Fin n → Ω) :=
        {X | 2 * δ ≤ |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))|}
      have hincl : {X : Fin n → Ω | ε ≤ |Z n X|} ⊆
          Z0 ∪ (EA ∪ (ED ∪ (EB ∪ EC))) := by
        intro X hX
        by_contra hnot
        simp only [Set.mem_union, not_or] at hnot
        obtain ⟨hz, hA', hD', hB', hC'⟩ := hnot
        have hdec := hdecomp n X hz
        have ha' : |A n X| < δ := by simpa only [EA, Set.mem_ofPred_eq, not_le] using hA'
        have hd' : |(n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I| < δ := by
          simpa only [ED, Set.mem_ofPred_eq, not_le] using hD'
        have hb' : |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I| < 4 * δ := by
          simpa only [EB, Set.mem_ofPred_eq, not_le] using hB'
        have hc' : |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| < 2 * δ := by
          simpa only [EC, Set.mem_ofPred_eq, not_le] using hC'
        rw [Set.mem_ofPred_eq, hdec] at hX
        have htri1 := abs_add_le (A n X)
          ((n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I)
        have htri2 := abs_add_le
          (A n X + ((n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I))
          (-(1 / 4 : ℝ) * (∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I))
        have htri3 := abs_add_le
          ((A n X + ((n : ℝ) * ∫ ω, W n ω ∂P + a ^ 2 / 4 * I)) +
            (-(1 / 4 : ℝ) * (∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I)))
          ((1 / 2 : ℝ) * ∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i)))
        have hquarter : |-(1 / 4 : ℝ) *
            (∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I)| =
              (1 / 4 : ℝ) * |∑ i : Fin n, W n (X i) ^ 2 - a ^ 2 * I| := by
          rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        have hhalf : |(1 / 2 : ℝ) *
            ∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| =
              (1 / 2 : ℝ) * |∑ i : Fin n, W n (X i) ^ 2 * R (W n (X i))| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        rw [hquarter] at htri2
        rw [hhalf] at htri3
        dsimp only [δ] at ha' hd' hb' hc'
        linarith
      calc
        (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |Z n X|} ≤
            (Measure.pi (fun _ : Fin n => P)) (Z0 ∪ (EA ∪ (ED ∪ (EB ∪ EC)))) :=
          measure_mono hincl
        _ ≤ (Measure.pi (fun _ : Fin n => P)) Z0 +
            ((Measure.pi (fun _ : Fin n => P)) EA +
              ((Measure.pi (fun _ : Fin n => P)) ED +
                ((Measure.pi (fun _ : Fin n => P)) EB +
                  (Measure.pi (fun _ : Fin n => P)) EC))) := by
          have h4 : (Measure.pi (fun _ : Fin n => P)) (EB ∪ EC) ≤
              (Measure.pi (fun _ : Fin n => P)) EB +
                (Measure.pi (fun _ : Fin n => P)) EC := measure_union_le _ _
          have h3 : (Measure.pi (fun _ : Fin n => P)) (ED ∪ (EB ∪ EC)) ≤
              (Measure.pi (fun _ : Fin n => P)) ED +
                ((Measure.pi (fun _ : Fin n => P)) EB +
                  (Measure.pi (fun _ : Fin n => P)) EC) :=
            (measure_union_le _ _).trans (add_le_add_right h4 _)
          have h2 : (Measure.pi (fun _ : Fin n => P)) (EA ∪ (ED ∪ (EB ∪ EC))) ≤
              (Measure.pi (fun _ : Fin n => P)) EA +
                ((Measure.pi (fun _ : Fin n => P)) ED +
                  ((Measure.pi (fun _ : Fin n => P)) EB +
                    (Measure.pi (fun _ : Fin n => P)) EC)) :=
            (measure_union_le _ _).trans (add_le_add_right h3 _)
          exact (measure_union_le _ _).trans (add_le_add_right h2 _)
    have hZ : Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P)) {X | ε ≤ |Z n X|}) atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Filter.Eventually.of_forall fun _ => bot_le)
        (Filter.Eventually.of_forall hbound)
    simpa only [Z, u] using hZ

/-- Full nondominated form of vdV Lemma 25.14: a measurable bare right-QMD
score is mean zero and square integrable, and generates the literal actual-RN
LAN expansion at `1/sqrt n`.

Proof idea: construct a `NondominatedQMDPath` from the bare score, invoke the
actual-likelihood LAN theorem, and transport all terms across the `P`-a.e.
representative. -/
theorem qmd_score_mean_integrable_and_lan_nondominated
    (P : Measure Ω) [IsProbabilityMeasure P]
    (curve : ℝ → Measure Ω)
    -- A one-sided probability path through `P`; vdV Lemma 25.14.
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t))
    (hzero : curve 0 = P)
    (g : Ω → ℝ)
    -- Measurability of the score representative.
    (hg : Measurable g)
    -- Right differentiability in quadratic mean with score `g`;
    -- vdV Lemma 25.14.
    (hqmd : IsRightQMD P curve g)
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → Ω)
    -- Measurability of each sample coordinate.
    (hX_meas : ∀ i, Measurable (X i))
    -- Iid observations with common law `P`; vdV Lemma 25.14.
    (hindep : ProbabilityTheory.iIndepFun X P')
    (hident : ∀ i, IdentDistrib (X i) (X 0) P' P')
    (hlaw : Measure.map (X 0) P' = P) :
    (∫ ω, g ω ∂P = 0) ∧ Integrable (fun ω => g ω ^ 2) P ∧
      TendstoInMeasure P'
        (fun n ω =>
          (∑ i ∈ Finset.range n,
            Real.log (((curve ((Real.sqrt n)⁻¹)).rnDeriv P (X i ω)).toReal))
            - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)
            + (1 / 2 : ℝ) * ∫ x, g x ^ 2 ∂P)
        atTop (fun _ => (0 : ℝ)) := by
  classical
  obtain ⟨γ, hγcurve, hgscore⟩ :=
    exists_nondominatedQMDPath_of_bare_qmd P curve hprob hzero g hg hqmd
  have hscoreMean : ∫ ω, (γ.score : Ω → ℝ) ω ∂P = 0 := by
    have hmem : (γ.score : Lp ℝ 2 P) ∈ L2ZeroMean P := γ.score.2
    change (γ.score : Lp ℝ 2 P) ∈
      LinearMap.ker (integralL2 P).toLinearMap at hmem
    rw [LinearMap.mem_ker] at hmem
    have hinner : ⟪oneL2 P, (γ.score : Lp ℝ 2 P)⟫_ℝ = 0 := hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    have hone : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    have heq : ∫ ω, ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
          ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ ∂P =
        ∫ ω, (γ.score : Ω → ℝ) ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hone] with ω hω
      rw [show ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) ω,
          ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω⟫_ℝ =
            (γ.score : Ω → ℝ) ω * (oneL2 P : Ω → ℝ) ω by rfl,
        hω, mul_one]
    rw [heq] at hinner
    exact hinner
  have hmean : ∫ ω, g ω ∂P = 0 := by
    rw [integral_congr_ae hgscore]
    exact hscoreMean
  have hgmem : MemLp g 2 P :=
    (memLp_congr_ae hgscore).mpr (Lp.memLp (γ.score : Lp ℝ 2 P))
  have hgsq : Integrable (fun ω => g ω ^ 2) P := hgmem.integrable_sq
  refine ⟨hmean, hgsq, ?_⟩
  have hI : ∫ ω, g ω ^ 2 ∂P = ‖γ.score‖ ^ 2 := by
    have hpow : (fun ω => g ω ^ 2) =ᵐ[P]
        fun ω => (γ.score : Ω → ℝ) ω ^ 2 := by
      filter_upwards [hgscore] with ω hω
      rw [hω]
    rw [integral_congr_ae hpow]
    exact integral_score_sq_eq_norm_sq γ
  let T : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n Y =>
    Real.log (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n Y).toReal -
      ((Real.sqrt n)⁻¹ * ∑ i : Fin n, (γ.score : Ω → ℝ) (Y i) -
        (1 / 2 : ℝ) * ‖γ.score‖ ^ 2)
  let S : ∀ n : ℕ, (Fin n → Ω) → ℝ := fun n Y =>
    (∑ i : Fin n,
      Real.log (((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal)) -
      (Real.sqrt n)⁻¹ * ∑ i : Fin n, g (Y i) +
      (1 / 2 : ℝ) * ∫ x, g x ^ 2 ∂P
  have hLAN : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)) {Y | ε ≤ |T n Y|})
      atTop (nhds 0) := by
    intro ε hε
    simpa only [T, one_mul, one_pow] using
      log_acProductLikelihood_lan_tendstoInMeasure γ 1 zero_le_one ε hε
  have hzeroProd : Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        (⋃ i ∈ (Finset.univ : Finset (Fin n)),
          {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0}))
      atTop (nhds 0) := by
    have hlocal := γ.base_zeroLikelihood_localScale_tendsto 1 zero_le_one
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hlocal (Filter.Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards with n
    have hset : MeasurableSet
        {ω | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P ω).toReal = 0} :=
      (Measure.measurable_rnDeriv (γ.curve ((Real.sqrt n)⁻¹)) P).ennreal_toReal
        (measurableSet_singleton 0)
    have heach : ∀ i : Fin n,
        (Measure.pi (fun _ : Fin n => P))
            {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0} =
          γ.baseZeroLikelihoodMass ((Real.sqrt n)⁻¹) := by
      intro i
      rw [show {Y : Fin n → Ω |
          ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0} =
          (fun Y : Fin n → Ω => Y i) ⁻¹'
            {ω | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P ω).toReal = 0} by rfl,
        ← Measure.map_apply (measurable_pi_apply i) hset,
        (measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
      rfl
    calc
      (Measure.pi (fun _ : Fin n => P))
          (⋃ i ∈ (Finset.univ : Finset (Fin n)),
            {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0}) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            (Measure.pi (fun _ : Fin n => P))
              {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0} :=
        measure_biUnion_finset_le _ _
      _ = (n : ℕ) • γ.baseZeroLikelihoodMass ((Real.sqrt n)⁻¹) := by
        simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = (n : ℝ≥0∞) * γ.baseZeroLikelihoodMass
          (1 * (Real.sqrt n)⁻¹) := by rw [nsmul_eq_mul, one_mul]
  have hsumLAN : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)) {Y | ε ≤ |S n Y|})
      atTop (nhds 0) := by
    intro ε hε
    have hupper : Tendsto (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
            (⋃ i ∈ (Finset.univ : Finset (Fin n)),
              {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0}) +
          (Measure.pi (fun _ : Fin n => P)) {Y | ε ≤ |T n Y|})
        atTop (nhds 0) := by
      simpa using hzeroProd.add (hLAN ε hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper (Filter.Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards with n
    have hgpi : (fun (Y : Fin n → Ω) i => g (Y i)) =ᵐ[
        Measure.pi (fun _ : Fin n => P)]
          fun Y i => (γ.score : Ω → ℝ) (Y i) :=
      Measure.ae_eq_pi (μ := fun _ : Fin n => P)
        (f := fun _ ω => g ω)
        (f' := fun _ ω => (γ.score : Ω → ℝ) ω) (fun _ => hgscore)
    have hincl : ∀ᵐ Y ∂(Measure.pi (fun _ : Fin n => P)),
        Y ∈ {Y : Fin n → Ω | ε ≤ |S n Y|} →
          Y ∈ ((⋃ i ∈ (Finset.univ : Finset (Fin n)),
            {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0}) ∪
            {Y | ε ≤ |T n Y|}) := by
      filter_upwards [hgpi] with Y hY
      intro hbad
      by_cases hz : Y ∈ (⋃ i ∈ (Finset.univ : Finset (Fin n)),
          {Y | ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal = 0})
      · exact Or.inl hz
      · apply Or.inr
        have hfac : ∀ i : Fin n,
            ((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal ≠ 0 := by
          intro i hi
          exact hz (Set.mem_biUnion (Finset.mem_univ i) hi)
        have hlog : Real.log
              (γ.acProductLikelihood ((Real.sqrt n)⁻¹) n Y).toReal =
            ∑ i : Fin n,
              Real.log (((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal) := by
          simp only [acProductLikelihood, ENNReal.toReal_prod]
          exact Real.log_prod fun i _ => hfac i
        have hsumg : ∑ i : Fin n, g (Y i) =
            ∑ i : Fin n, (γ.score : Ω → ℝ) (Y i) := by
          rw [hY]
        have hST : S n Y = T n Y := by
          dsimp only [S, T]
          rw [hlog, hsumg, hI]
          ring
        rwa [hST] at hbad
    exact (measure_mono_ae hincl).trans (measure_union_le _ _)
  let Y : ∀ n : ℕ, Ω' → (Fin n → Ω) := fun n ω i => X i.val ω
  have hYmeas : ∀ n, Measurable (Y n) := by
    intro n
    exact Measurable.of_eval fun i => hX_meas i.val
  have hjoint : ∀ n, Measure.map (Y n) P' =
      Measure.pi (fun _ : Fin n => P) := by
    intro n
    have hfin : iIndepFun (fun i : Fin n => X i.val) P' :=
      ProbabilityTheory.iIndepFun.precomp Fin.val_injective hindep
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (hX_meas i.val).aemeasurable)).mp hfin
    calc
      Measure.map (Y n) P' =
          Measure.pi (fun i : Fin n => Measure.map (X i.val) P') := hmap
      _ = Measure.pi (fun _ : Fin n => P) := by
        congr 1
        funext i
        rw [(hident i.val).map_eq, hlaw]
  have hSmeas : ∀ n, Measurable (S n) := by
    intro n
    dsimp only [S]
    have hlogmeas : Measurable (fun Y : Fin n → Ω =>
        ∑ i : Fin n,
          Real.log (((γ.curve ((Real.sqrt n)⁻¹)).rnDeriv P (Y i)).toReal)) :=
      Finset.measurable_sum _ fun i _ =>
        ((Measure.measurable_rnDeriv (γ.curve ((Real.sqrt n)⁻¹)) P).comp
          (measurable_pi_apply i)).ennreal_toReal.log
    have hgmeas : Measurable (fun Y : Fin n → Ω =>
        ∑ i : Fin n, g (Y i)) :=
      Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)
    exact (hlogmeas.sub (hgmeas.const_mul _)).add_const _
  rw [MeasureTheory.tendstoInMeasure_iff_norm]
  intro ε hε
  have hp := hsumLAN ε hε
  convert! hp using 1
  funext n
  have hset : MeasurableSet {Z : Fin n → Ω | ε ≤ |S n Z|} :=
    measurableSet_le measurable_const (hSmeas n).abs
  have hstat : ∀ ω : Ω',
      ((∑ i ∈ Finset.range n,
          Real.log (((curve ((Real.sqrt n)⁻¹)).rnDeriv P (X i ω)).toReal))
        - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)
        + (1 / 2 : ℝ) * ∫ x, g x ^ 2 ∂P) = S n (Y n ω) := by
    intro ω
    dsimp only [S, Y]
    rw [hγcurve]
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  calc
    P' {ω |
        ε ≤
          ‖((∑ i ∈ Finset.range n,
              Real.log (((curve ((Real.sqrt n)⁻¹)).rnDeriv P (X i ω)).toReal))
            - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)
            + (1 / 2 : ℝ) * ∫ x, g x ^ 2 ∂P) - 0‖} =
        P' ((Y n) ⁻¹' {Z : Fin n → Ω | ε ≤ |S n Z|}) := by
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_zero, Real.norm_eq_abs]
      rw [hstat]
    _ = Measure.map (Y n) P' {Z : Fin n → Ω | ε ≤ |S n Z|} := by
      rw [Measure.map_apply (hYmeas n) hset]
    _ = (Measure.pi (fun _ : Fin n => P)) {Z : Fin n → Ω | ε ≤ |S n Z|} := by
      rw [hjoint]

end AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLAN

end GLP0011B3Source32
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.Probability.ScoreCLT`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source33


/-!
# Multivariate central limit theorem for iid vectors (Cramér–Wold via Lévy)

Let $Y_1, Y_2, \dots$ be independent and identically distributed random vectors taking
values in $\mathbb{R}^k$, with mean zero and finite covariance matrix $\Sigma$ (positive
semidefinite), so that $\mathbb{E}\langle u, Y_0\rangle = 0$ and
$\mathbb{E}\big[\langle u, Y_0\rangle\,\langle v, Y_0\rangle\big] = u^{\top}\Sigma\, v$
for all directions $u, v \in \mathbb{R}^k$. Then the normalized partial sum
$\frac{1}{\sqrt{n}}\sum_{i=0}^{n-1} Y_i$ converges in distribution to the multivariate
normal law $N(0, \Sigma)$.

This is the device invoked as Step 1 of the score-statistic argument in van der Vaart
Theorem 7.10 (§7.3, Convergence to a Normal Experiment): the asymptotic normality of a
sum of iid score contributions follows from the multivariate CLT applied to those
contributions.

The moment data are expressed as
explicit hypotheses on the projections $\langle u, Y_0\rangle$ — zero mean
(`h_zero_mean`), the covariance identity $u^{\top}\Sigma\,v$ (`h_cov`), and a square
integrability assumption `MemLp (Y 0) 2 P` (`hL2`) — rather than abstractly assuming
"$Y_0$ has mean $0$ and covariance $\Sigma$". These together encode exactly the finite
second-moment hypotheses of the classical statement.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 7
(Local Asymptotic Normality), Theorem 7.10 (§7.3, Convergence to a Normal Experiment),
Step 1 of the proof. The underlying classical result is the multivariate Lindeberg–Lévy
CLT together with the Cramér–Wold device (van der Vaart, Chapter 2, §2.3 Characteristic
Functions, Example 2.18 and the Cramér–Wold lemma, p. 16).

**Proof.** The proof uses the Cramér–Wold device implemented through
Lévy's continuity theorem. For every test direction $t \in \mathbb{R}^k$, the scalar
projection $Z_i := \langle t, Y_i\rangle$ is iid with zero mean (from `h_zero_mean`) and
variance $t^{\top}\Sigma\, t$ (from `h_cov`). Mathlib's 1D CLT
(`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`) gives
$\tfrac{1}{\sqrt{n}}\sum_i Z_i \rightsquigarrow N\!\big(0, \operatorname{Var}[Z_0]\big)$.
Its characteristic function at the point $s = 1$ converges to
$\exp(-\operatorname{Var}[Z_0]/2)$, which equals
$\operatorname{charFun}\!\big(N(0,\Sigma)\big)(t)$. Lévy's continuity theorem
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`) promotes this pointwise
characteristic-function convergence to weak convergence in `ProbabilityMeasure`, which
is unpacked as `WeakConverges`.

-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

namespace AsymptoticStatistics
namespace ScoreCLT

variable {k : ℕ}

/-- **Multivariate central limit theorem** (iid finite-dimensional vectors).

Given iid `EuclideanSpace ℝ (Fin k)`-valued random variables `Y_i` on `(Ω, P)`
with zero mean and covariance matrix `cov` (PosSemidef), the normalized sum
`(1/√n) ∑_{i<n} Y_i` converges weakly to `multivariateGaussian 0 cov`.

**Proof**: Cramér–Wold via Lévy's continuity theorem. For each `t`, the scalar
projection `Z_i := ⟪t, Y_i⟫` is iid with zero mean and variance
`⟨t, cov t⟩`; Mathlib's 1D CLT gives weak convergence of `(√n)⁻¹ ∑ Z_i` to
`gaussianReal 0 ⟨t, cov t⟩`. The characteristic function at `s = 1` converges
accordingly, matching `charFun (multivariateGaussian 0 cov) t`. Lévy's
continuity promotes pointwise charFun convergence to `Tendsto` in
`ProbabilityMeasure`, which unpacks to `WeakConverges`. -/
theorem clt_finDim
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → EuclideanSpace ℝ (Fin k)) (hY_meas : ∀ i, Measurable (Y i))
    (hindep : iIndepFun Y P)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (h_zero_mean : ∀ u : EuclideanSpace ℝ (Fin k),
      (∫ ω, ⟪u, Y 0 ω⟫ ∂P) = 0)
    (cov : Matrix (Fin k) (Fin k) ℝ) (hcov_psd : cov.PosSemidef)
    (h_cov : ∀ u v : EuclideanSpace ℝ (Fin k),
      (∫ ω, ⟪u, Y 0 ω⟫ * ⟪v, Y 0 ω⟫ ∂P) =
        u.ofLp ⬝ᵥ cov.mulVec v.ofLp)
    (hL2 : MemLp (Y 0) 2 P) :
    WeakConverges
      (fun n => P.map (fun ω => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i ω))
      (ProbabilityTheory.multivariateGaussian 0 cov) := by
  -- Measurability of the normalized sum.
  have hW_meas : ∀ n : ℕ,
      Measurable (fun ω : Ω => (Real.sqrt n)⁻¹ •
        ∑ i ∈ Finset.range n, Y i ω : Ω → EuclideanSpace ℝ (Fin k)) := fun n =>
    (Finset.measurable_sum _ (fun i _ => hY_meas i)).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have hP_map_prob : ∀ n : ℕ, IsProbabilityMeasure
      (P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, Y i ω : Ω → EuclideanSpace ℝ (Fin k))) := fun n =>
    (by infer_instance)
  -- Reduce weak convergence to pointwise charFun convergence via Lévy continuity.
  suffices h_charFun : ∀ t : EuclideanSpace ℝ (Fin k),
      Tendsto (fun n : ℕ => charFun
        (P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, Y i ω)) t) atTop
        (𝓝 (charFun (ProbabilityTheory.multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin k)) cov) t)) by
    intro f
    have h_levy : Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
        (fun n : ℕ => ⟨P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, Y i ω), hP_map_prob n⟩)
        atTop (𝓝 ⟨ProbabilityTheory.multivariateGaussian 0 cov, inferInstance⟩) :=
      ProbabilityMeasure.tendsto_of_tendsto_charFun h_charFun
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_levy) f
  -- Fix a test direction `t`.
  intro t
  -- The 1D projection `Z_i ω := ⟪t, Y_i ω⟫`.
  have hproj_meas : Measurable (fun y : EuclideanSpace ℝ (Fin k) => ⟪t, y⟫ : _ → ℝ) :=
    (continuous_const.inner continuous_id).measurable
  have hZ_meas : ∀ i, Measurable (fun ω : Ω => ⟪t, Y i ω⟫ : Ω → ℝ) :=
    fun i => hproj_meas.comp (hY_meas i)
  -- `Z_i` are iid under `P` (composition of `Y_i` iid with fixed linear functional).
  have hZ_iid : iIndepFun (fun i (ω : Ω) => ⟪t, Y i ω⟫ : ℕ → Ω → ℝ) P :=
    hindep.comp (fun _ => fun y : EuclideanSpace ℝ (Fin k) => ⟪t, y⟫)
      (fun _ => hproj_meas)
  have hZ_ident : ∀ i, IdentDistrib
      (fun ω : Ω => ⟪t, Y i ω⟫) (fun ω : Ω => ⟪t, Y 0 ω⟫) P P := fun i =>
    (hident i).comp (u := fun y : EuclideanSpace ℝ (Fin k) => ⟪t, y⟫) hproj_meas
  -- Zero mean and L² control.
  have hZ_mean : P[fun ω => ⟪t, Y 0 ω⟫] = 0 := h_zero_mean t
  have hZ_L2 : MemLp (fun ω : Ω => ⟪t, Y 0 ω⟫) 2 P := by
    have h := hL2.inner_const (𝕜 := ℝ) t
    exact h.ae_eq (Filter.Eventually.of_forall
      fun ω => (real_inner_comm (Y 0 ω) t).symm)
  -- Variance: `Var[Z_0; P] = ⟨t, cov t⟩_Mat`.
  have hZ_var : Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P] = t.ofLp ⬝ᵥ cov.mulVec t.ofLp := by
    rw [variance_eq_integral (hZ_meas 0).aemeasurable, hZ_mean]
    simp only [sub_zero]
    have h_sq : (fun ω => ⟪t, Y 0 ω⟫ ^ 2)
        =ᵐ[P] (fun ω => ⟪t, Y 0 ω⟫ * ⟪t, Y 0 ω⟫) := by
      filter_upwards with ω; ring
    rw [integral_congr_ae h_sq]
    exact h_cov t t
  have hZ_var_nn : 0 ≤ Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P] := variance_nonneg _ _
  -- Apply Mathlib's 1D CLT to the projection.
  have h1D := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := fun i ω => ⟪t, Y i ω⟫)
    (Y := (id : ℝ → ℝ))
    (P' := gaussianReal 0 Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P].toNNReal)
    HasLaw.id hZ_L2 hZ_iid hZ_ident
  -- Simplify the summand using `P[Z_0] = 0` via `TendstoInDistribution.congr`.
  have h1D' := h1D.congr (Y := fun (n : ℕ) (ω : Ω) => (Real.sqrt (n : ℝ))⁻¹ *
      ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫)
    (T := (id : ℝ → ℝ))
    (fun (n : ℕ) => Filter.Eventually.of_forall fun ω => by
      change (Real.sqrt (n : ℝ))⁻¹ *
        (∑ k ∈ Finset.range n, ⟪t, Y k ω⟫ - (n : ℝ) * P[fun ω' => ⟪t, Y 0 ω'⟫])
        = (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫
      rw [hZ_mean]; ring)
    (Filter.Eventually.of_forall fun _ => rfl)
  -- Extract pointwise charFun convergence at s = 1 via Lévy iff.
  have h_charFun_1D := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h1D'.tendsto 1
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at h_charFun_1D
  -- Evaluate `charFun (gaussianReal 0 v) 1 = exp(-v/2)`.
  have h_gauss : charFun
      (gaussianReal 0 Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P].toNNReal) 1
      = Complex.exp (- ((Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P] : ℂ)) / 2) := by
    rw [charFun_gaussianReal]
    push_cast
    rw [Real.coe_toNNReal _ hZ_var_nn]
    ring_nf
  rw [h_gauss] at h_charFun_1D
  -- Evaluate `charFun (multivariateGaussian 0 cov) t = exp(-⟨t, cov t⟩/2)`.
  have h_charFun_ν : charFun (ProbabilityTheory.multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin k)) cov) t
      = Complex.exp (- ((Var[(fun ω : Ω => ⟪t, Y 0 ω⟫); P] : ℂ)) / 2) := by
    rw [ProbabilityTheory.charFun_multivariateGaussian hcov_psd t]
    rw [show (inner ℝ t (0 : EuclideanSpace ℝ (Fin k))) = (0 : ℝ) from inner_zero_right t]
    rw [hZ_var]
    push_cast
    ring_nf
  rw [h_charFun_ν]
  -- Rewrite LHS: `charFun (P.map W_n) t = charFun (P.map ((√n)⁻¹ * ∑ Z_k)) 1`.
  have h_charFun_lhs : ∀ n : ℕ,
      charFun (P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ •
        ∑ i ∈ Finset.range n, Y i ω)) t
      = charFun (P.map (fun ω : Ω => (Real.sqrt (n : ℝ))⁻¹ *
        ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫)) 1 := by
    intro n
    rw [charFun_apply, charFun_apply_real]
    rw [MeasureTheory.integral_map (hW_meas n).aemeasurable
        (by fun_prop : AEStronglyMeasurable
          (fun x : EuclideanSpace ℝ (Fin k) =>
            Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I))
          (P.map _))]
    rw [MeasureTheory.integral_map
        ((Finset.aemeasurable_fun_sum _
          (fun _ _ => (hZ_meas _).aemeasurable)).const_mul _)
        (by fun_prop : AEStronglyMeasurable
          (fun x : ℝ => Complex.exp (((1 : ℝ) : ℂ) * (x : ℂ) * Complex.I))
          (P.map _))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    congr 1
    -- Goal: `⟪W n ω, t⟫ * I = 1 * ((√n)⁻¹ * ∑ Z_k ω) * I` (both in ℂ)
    have h_inner : (inner ℝ ((Real.sqrt (n : ℝ))⁻¹ •
          ∑ i ∈ Finset.range n, Y i ω : EuclideanSpace ℝ (Fin k)) t : ℝ)
        = (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫ := by
      rw [real_inner_smul_left, sum_inner]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact (real_inner_comm (Y i ω) t).symm
    rw [show ⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, Y i ω, t⟫
          = (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, ⟪t, Y k ω⟫ from h_inner]
    push_cast
    ring
  simp_rw [h_charFun_lhs]
  exact h_charFun_1D

end ScoreCLT
end AsymptoticStatistics

end GLP0011B3Source33
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.GaussianMGF`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source34


/-!
# Gaussian exponential tilting

The one-dimensional Gaussian moment-generating function is expressed as
`∫ exp(t · x) dN(μ, v)(x) = exp(μ t + v t²/2)`.
Exponential tilting shifts Gaussian means: first in one dimension, then in
finite products, and finally for multivariate Gaussians through their
square-root covariance representation. These identities underlie the
Gaussian tilt in van der Vaart's Theorem 7.10.
-/

open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder ENNReal

namespace ProbabilityTheory

/-- **1D Gaussian moment-generating function**, stated as a plain integral. For
`x ∼ N(μ, v)`, `∫ exp(t · x) dN(μ, v)(x) = exp(μ t + v t² / 2)`. -/
lemma integral_exp_mul_gaussianReal (μ : ℝ) (v : NNReal) (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂gaussianReal μ v
      = Real.exp (μ * t + (v : ℝ) * t ^ 2 / 2) := by
  have hmap : Measure.map (id : ℝ → ℝ) (gaussianReal μ v) = gaussianReal μ v := by
    simp [Measure.map_id]
  have := mgf_gaussianReal ⟨aemeasurable_id, hmap⟩ t
  simpa [mgf, id] using this


/-- **CLM lift of `Matrix.toLpLin 2 2`** for rectangular matrices.

For `A : Matrix (Fin d) (Fin k) ℝ`, the linear map
`Matrix.toLpLin 2 2 A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)`
becomes a continuous linear map via `LinearMap.toContinuousLinearMap` (the source
is finite-dim).

Companion to `Matrix.toEuclideanCLM` (which is a star-algebra equivalence only
available for square matrices); this rectangular version supports transporting
Gaussian laws and losses through matrices of shape `d × k`. -/
noncomputable def matrixToEuclideanCLMRect
    {d k : ℕ} (A : Matrix (Fin d) (Fin k) ℝ) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 A)

@[simp]
lemma ofLp_matrixToEuclideanCLMRect
    {d k : ℕ} (A : Matrix (Fin d) (Fin k) ℝ) (v : EuclideanSpace ℝ (Fin k)) :
    (matrixToEuclideanCLMRect A v).ofLp = A.mulVec v.ofLp := rfl


/-- **Girsanov / Esscher identity for 1D standard Gaussian**. Tilting
`gaussianReal 0 1` by the exponential density `exp(a · x - a² / 2)` produces
`gaussianReal a 1` — i.e., shifts the mean by `a`.

Proof by PDF comparison: both sides rewrite to `volume.withDensity f` via
`gaussianReal_of_var_ne_zero`, then `withDensity_mul` composes the 0-mean PDF
with the exponential tilt, and the resulting density matches the `a`-mean PDF
because `exp(-(x-a)²/2) = exp(-x²/2) · exp(a·x - a²/2)`.

First step of the Girsanov chain for Theorem 7.10; lifts
to the multivariate case via the product-measure representation of `stdGaussian`. -/
lemma gaussianReal_withDensity_exp_shift (a : ℝ) :
    (gaussianReal 0 1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2)))
      = gaussianReal a 1 := by
  -- Both `gaussianReal`s admit an explicit `volume.withDensity gaussianPDF` form
  -- (since `v = 1 ≠ 0`), turning the identity into a density-side comparison.
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (by norm_num : (1 : NNReal) ≠ 0)]
  have h_tilt_meas :
      Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2))) := by
    fun_prop
  rw [← MeasureTheory.withDensity_mul volume (measurable_gaussianPDF 0 1) h_tilt_meas]
  congr 1
  ext x
  -- Pointwise identity on densities. Move ENNReal.ofReal out and reduce to real algebra.
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  -- Real identity: `gaussianPDFReal 0 1 x · exp(a·x - a²/2) = gaussianPDFReal a 1 x`.
  -- Expand the PDFs and collapse `exp(-x²/2) · exp(a·x - a²/2) = exp(-(x-a)²/2)`.
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Pi-product Girsanov for standard 1D Gaussians**. Tilting the product of `ι`
copies of `gaussianReal 0 1` by `exp(∑ᵢ aᵢ yᵢ - ∑ᵢ aᵢ² / 2)` shifts the mean in each
coordinate:
```
(Measure.pi (fun _ => gaussianReal 0 1)).withDensity
    (fun y => ENNReal.ofReal (Real.exp (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)))
  = Measure.pi (fun i => gaussianReal (a i) 1).
```

Proof goes through `pi_withDensity_prod`: the exponential density factors as a
product `∏ i, exp(aᵢ yᵢ - aᵢ² / 2)`, each factor is the 1D Girsanov density, and
`gaussianReal_withDensity_exp_shift` shifts each component individually.

Second step of the multivariate Girsanov chain (Theorem 7.10). -/
lemma pi_gaussianReal_withDensity_exp_shift {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)))
      = Measure.pi (fun i : ι => gaussianReal (a i) 1) := by
  classical
  -- Record the 1D Girsanov identity on each coordinate; this gives the
  -- `IsProbabilityMeasure` instance needed for `pi_withDensity_prod`.
  have h1d : ∀ i, (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - a i ^ 2 / 2)))
        = gaussianReal (a i) 1 := fun i => gaussianReal_withDensity_exp_shift (a i)
  -- Factor the product density: `exp(∑ aᵢyᵢ - ∑ aᵢ²/2) = ∏ exp(aᵢyᵢ - aᵢ²/2)`.
  have h_density : (fun y : ι → ℝ =>
        ENNReal.ofReal (Real.exp (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)))
      = fun y => ∏ i, ENNReal.ofReal (Real.exp (a i * y i - a i ^ 2 / 2)) := by
    funext y
    rw [show (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)
          = ∑ i, (a i * y i - a i ^ 2 / 2) from (Finset.sum_sub_distrib _ _).symm,
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg
        (fun i _ => Real.exp_nonneg _)]
  rw [h_density, pi_withDensity_prod
    (f := fun i x => ENNReal.ofReal (Real.exp (a i * x - a i ^ 2 / 2)))
    (fun i => by fun_prop)]
  congr 1
  funext i
  exact h1d i

/-- **Standard Gaussian Girsanov on `EuclideanSpace ℝ ι`** (Esscher shift). Tilting
the standard Gaussian by `exp(⟪a, y⟫ - ‖a‖² / 2)` shifts the mean by `a`:
```
(stdGaussian (EuclideanSpace ℝ ι)).withDensity
    (fun y => ENNReal.ofReal (Real.exp (⟪a, y⟫ - ‖a‖² / 2)))
  = (stdGaussian (EuclideanSpace ℝ ι)).map (fun y => y + a).
```

Lifts the pi-version `pi_gaussianReal_withDensity_exp_shift` through the isomorphism
`(Measure.pi …).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ ι)` on both
sides. The LHS commutes withDensity past map (`withDensity_map_eq_map_withDensity`)
and expands `⟪a, toLp y⟫` / `‖a‖²` into coordinate sums. The RHS composes the maps
(`Measure.map_map`), rewrites `+ a` on the Lp side as `+ a.ofLp` on the pi side
(linearity of `WithLp.toLp`), and distributes via `pi_map_pi` + `gaussianReal_map_add_const`. -/
theorem stdGaussian_withDensity_exp_shift {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (⟪a, y⟫ - ‖a‖ ^ 2 / 2)))
      = (stdGaussian (EuclideanSpace ℝ ι)).map (fun y => y + a) := by
  classical
  -- Pull both sides back to `pi` via `map_pi_eq_stdGaussian`.
  rw [← map_pi_eq_stdGaussian (ι := ι)]
  -- LHS: commute withDensity past map. RHS: compose the two maps.
  rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity _ _
    (by fun_prop) _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  -- Rewrite RHS function `(· + a) ∘ toLp = toLp ∘ (· + a.ofLp)` by linearity of `toLp`,
  -- then split the composed map back so both sides have `.map (toLp)` outermost.
  have h_add : ((fun y : EuclideanSpace ℝ ι => y + a) ∘ WithLp.toLp 2 (V := ι → ℝ))
      = (WithLp.toLp 2) ∘ fun y : ι → ℝ => y + a.ofLp := by
    funext y
    simp only [Function.comp_apply]
    rw [WithLp.toLp_add, WithLp.toLp_ofLp]
  rw [h_add, ← Measure.map_map (by fun_prop) (by fun_prop)]
  -- Strip the common `.map (toLp 2)` from both sides.
  congr 1
  -- LHS: rewrite the pulled-back density in pi-coord form, then apply pi-Girsanov.
  have h_density : ((fun y : EuclideanSpace ℝ ι =>
        ENNReal.ofReal (Real.exp (⟪a, y⟫ - ‖a‖ ^ 2 / 2))) ∘ WithLp.toLp 2 (V := ι → ℝ))
      = fun y : ι → ℝ =>
          ENNReal.ofReal (Real.exp (∑ i, a.ofLp i * y i - ∑ i, a.ofLp i ^ 2 / 2)) := by
    funext y
    simp only [Function.comp_apply]
    have h_inner : ⟪a, (WithLp.toLp 2 y : EuclideanSpace ℝ ι)⟫
        = ∑ i, a.ofLp i * y i := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change y i * a.ofLp i = a.ofLp i * y i
      ring
    have h_norm : (‖a‖ : ℝ) ^ 2 / 2 = (∑ i, a.ofLp i ^ 2) / 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    rw [h_inner, h_norm, Finset.sum_div]
  rw [h_density, pi_gaussianReal_withDensity_exp_shift (fun i => a.ofLp i)]
  -- RHS: distribute the coordinate-wise shift through `pi_map_pi`.
  rw [show (fun y : ι → ℝ => y + a.ofLp) = (fun y i => y i + a.ofLp i) from rfl,
    Measure.pi_map_pi (fun i =>
      (by fun_prop : Measurable (fun x : ℝ => x + a.ofLp i)).aemeasurable)]
  simp_rw [gaussianReal_map_add_const, zero_add]

/-- **Multivariate Gaussian Girsanov / Esscher identity**. Tilting the centred
multivariate Gaussian `N(0, S)` by `exp(⟪h, y⟫ - ⟨h, S h⟩ / 2)` shifts the mean to
`S h`:
```
(multivariateGaussian 0 S).withDensity
    (fun y => ENNReal.ofReal (Real.exp (⟪h, y⟫ - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2)))
  = multivariateGaussian (toEuclideanCLM S h) S.
```

Lifts the `stdGaussian` version `stdGaussian_withDensity_exp_shift` through the
square-root decomposition `multivariateGaussian μ S = stdGaussian.map (μ + √S ·)`.

Let `A = toEuclideanCLM (sqrt S)`; by CFC, `A ∘ A = toEuclideanCLM S`, and since
`sqrt S ≥ 0`, `A` is self-adjoint. The LHS density composed with `A` simplifies:
`⟪h, A x⟫ = ⟪A h, x⟫` (self-adjoint) and `⟨h, S h⟩ = ‖A h‖²` (`A ∘ A = S`),
so `(tilt h) ∘ A = tilt_std (A h)`. Applying the `stdGaussian` shift at parameter
`A h` produces `stdGaussian.map (· + A h)`, and composing with `A` on the outside
yields `stdGaussian.map (fun x => A x + A (A h)) = stdGaussian.map (fun x =>
toEuclideanCLM S h + A x)`, which is `multivariateGaussian (toEuclideanCLM S h) S`
by definition. -/
theorem multivariateGaussian_withDensity_exp_shift {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (h : EuclideanSpace ℝ ι) :
    (multivariateGaussian 0 S).withDensity
        (fun y => ENNReal.ofReal (Real.exp (⟪h, y⟫
          - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2)))
      = multivariateGaussian (toEuclideanCLM (𝕜 := ℝ) S h) S := by
  classical
  -- Abbreviation `A := toEuclideanCLM (sqrt S)` : self-adjoint, `A ∘ A = toEuclideanCLM S`.
  set A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hA_def
  set_option backward.isDefEq.respectTransparency false in
  have hA_sa : IsSelfAdjoint A :=
    (CFC.sqrt_nonneg S).isSelfAdjoint.map (toEuclideanCLM (𝕜 := ℝ))
  have hAA : A ∘L A = toEuclideanCLM (𝕜 := ℝ) S := by
    change A * A = toEuclideanCLM (𝕜 := ℝ) S
    rw [hA_def, ← map_mul, CFC.sqrt_mul_sqrt_self _ hS.nonneg]
  have hA_meas : Measurable A := A.continuous.measurable
  -- Adjoint-swap helper.
  have h_inner_swap : ∀ u v, ⟪u, A v⟫ = ⟪A u, v⟫ := fun u v => by
    have := ContinuousLinearMap.adjoint_inner_left A v u
    rw [hA_sa.adjoint_eq] at this
    exact this.symm
  -- `A (A h) = toEuclideanCLM S h` from `A ∘L A = toEuclideanCLM S`.
  have hAAh : A (A h) = (toEuclideanCLM (𝕜 := ℝ) S) h := by
    change (A ∘L A) h = _
    rw [hAA]
  -- Unfold `multivariateGaussian 0 S = stdGaussian.map A` (the `0 +` simplifies).
  have hMvG0 : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map A := by
    rw [multivariateGaussian]
    congr 1
    funext x
    simp [hA_def]
  -- Unfold RHS similarly.
  have hMvGSh : multivariateGaussian (toEuclideanCLM (𝕜 := ℝ) S h) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map
          (fun x => toEuclideanCLM (𝕜 := ℝ) S h + A x) := by
    rw [multivariateGaussian]
  rw [hMvG0, hMvGSh]
  -- Commute withDensity past `.map A` on the LHS.
  rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity _ _ hA_meas _
    (by fun_prop)]
  -- Rewrite the pulled-back density as the stdGaussian-tilt at parameter `A h`.
  have h_density : ((fun y : EuclideanSpace ℝ ι =>
        ENNReal.ofReal (Real.exp (⟪h, y⟫ - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2))) ∘ A)
      = fun x => ENNReal.ofReal (Real.exp (⟪A h, x⟫ - ‖A h‖ ^ 2 / 2)) := by
    funext x
    simp only [Function.comp_apply]
    -- Inner-product swap: `⟪h, A x⟫ = ⟪A h, x⟫`.
    have h_inner : ⟪h, A x⟫ = ⟪A h, x⟫ := h_inner_swap h x
    -- `‖A h‖² = h.ofLp ⬝ᵥ S.mulVec h.ofLp`.
    have h_norm_sq : ‖A h‖ ^ 2 = h.ofLp ⬝ᵥ S.mulVec h.ofLp := by
      rw [sq, ← real_inner_self_eq_norm_mul_norm, h_inner_swap, hAAh,
        real_inner_comm, Matrix.inner_toEuclideanCLM]
    rw [h_inner, h_norm_sq]
  rw [h_density, stdGaussian_withDensity_exp_shift (A h),
    Measure.map_map hA_meas (by fun_prop)]
  -- Collapse `A ∘ (· + A h) = (toEuclideanCLM S h + ·) ∘ A`.
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [A.map_add, hAAh, add_comm]

/-- **Pushforward of a centered multivariate Gaussian under an inner-product
projection** is a centered 1-D Gaussian with variance `⟨h, J h⟩_Mat`.

Proved by `charFun` uniqueness: both sides have characteristic function
`exp(-(h · J · h) t²/2)` — the LHS via `charFun_multivariateGaussian` applied
to the argument `t • h` (after transporting through `integral_map`), the RHS
by `charFun_gaussianReal`. -/
theorem multivariateGaussian_map_inner_eq_gaussianReal
    {k : ℕ} (h : EuclideanSpace ℝ (Fin k))
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosSemidef) :
    Measure.map (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫)
        (multivariateGaussian 0 J)
      = gaussianReal 0 (h.ofLp ⬝ᵥ J.mulVec h.ofLp).toNNReal := by
  classical
  have hL_meas : Measurable (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫) :=
    (continuous_const.inner continuous_id).measurable
  have : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  -- Nonneg quadratic form.
  have h_quad_nn : 0 ≤ h.ofLp ⬝ᵥ J.mulVec h.ofLp := by
    have := hJ.re_dotProduct_nonneg (x := (h.ofLp : Fin k → ℝ))
    simpa using this
  apply MeasureTheory.Measure.ext_of_charFun
  funext t
  -- LHS: `charFun ((mvG 0 J).map L) t = charFun (mvG 0 J) (t • h)`.
  have hLHS : charFun (Measure.map (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫)
        (multivariateGaussian 0 J)) t
      = charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) (t • h) := by
    rw [charFun_apply_real, charFun_apply]
    have h_integrand_meas : AEStronglyMeasurable
        (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))
        (Measure.map (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫)
          (multivariateGaussian 0 J)) :=
      (by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (↑t * ↑x * Complex.I)).aestronglyMeasurable
    rw [integral_map hL_meas.aemeasurable h_integrand_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only []
    -- Identity: `⟨y, t • h⟩ = t * ⟨h, y⟩` (linearity + symmetry).
    rw [real_inner_smul_right, real_inner_comm]
    push_cast
    ring
  rw [hLHS, charFun_multivariateGaussian hJ,
    charFun_gaussianReal]
  -- Clean up mean term: `⟨t • h, 0⟩ = 0`.
  have hmean : (inner ℝ (t • h) (0 : EuclideanSpace ℝ (Fin k))) = 0 := by
    rw [inner_zero_right]
  rw [hmean]
  -- Clean up quadratic: `(t • h).ofLp ⬝ᵥ J.mulVec (t • h).ofLp = t² · (h · J · h)`.
  have hquad : (t • h).ofLp ⬝ᵥ J.mulVec (t • h).ofLp
      = t ^ 2 * (h.ofLp ⬝ᵥ J.mulVec h.ofLp) := by
    have h1 : (t • h).ofLp = t • h.ofLp := rfl
    rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [hquad]
  -- Clean up the target-RHS constant: `↑(x.toNNReal) = x` when `x ≥ 0`.
  rw [Real.coe_toNNReal _ h_quad_nn]
  -- Final algebra: both sides equal `exp(-t² (h · J · h) / 2)`.
  push_cast
  ring_nf

end ProbabilityTheory

end GLP0011B3Source34
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.ForMathlib.Slutsky`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source35


/-!
# Slutsky perturbation for `WeakConverges`

Slutsky's theorem in the "close-in-probability" form, stated at the
pushforward-measure level (`WeakConverges`). Given two sequences of random variables
`X n, Y n : Ω n → E` (probability measures `P n` on varying spaces), if

* the push-forward laws `(P n).map (X n)` weakly converge to `ν`, and
* the pair `dist (X n) (Y n)` converges to `0` in `P n`-probability,

then `(P n).map (Y n)` weakly converges to `ν` as well. This is the "varying base"
version — Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub` only covers a
single fixed base measure on a single space.

In Theorem 7.10 Step 3, this absorbs the LAN residual (an `o_P(1)` under
`P^n_{θ₀}`) into joint weak convergence of `(T_n, log-likelihood)`.

The proof mirrors Mathlib's: reduce to Lipschitz test functions via
`tendsto_iff_forall_lipschitz_integral_tendsto`, then split `|F(Y) − F(X)|` on
`{dist < ε/2} ∪ {dist ≥ ε/2}` using the Lipschitz bound and the sup norm.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- **Slutsky-by-distance for `WeakConverges`**: if `(P n).map (X n) ⇝ ν` and
`dist (X n) (Y n) →_P 0` under `P n`, then `(P n).map (Y n) ⇝ ν`.

Varying-base version (each `P n` lives on its own space `Ω n`). Adapted from
`MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`, which is stated for a
single base `μ''` on a normed additive group. The three-piece estimate
`|∫F Y − ∫F ν| ≤ L·(ε/2) + 2·‖F‖∞ · P{dist ≥ ε/2} + |∫F X − ∫F ν|` carries over
with `dist` in place of `‖·-·‖`.
The underlying Mathlib proof is Apache-2.0; see NOTICE at the repository root.
-/
theorem WeakConverges.slutsky_of_tendstoInMeasure_dist
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [Nonempty E]
    [OpensMeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Ω n → E} {ν : Measure E} [IsProbabilityMeasure ν]
    (hX_meas : ∀ n, AEMeasurable (X n) (P n))
    (hY_meas : ∀ n, AEMeasurable (Y n) (P n))
    (hX : WeakConverges (fun n => (P n).map (X n)) ν)
    (hDist : ∀ ε > 0,
        Tendsto (fun n => (P n).real {ω | ε ≤ dist (X n ω) (Y n ω)}) atTop (𝓝 0)) :
    WeakConverges (fun n => (P n).map (Y n)) ν := by
  classical
  have h_prob_X : ∀ n, IsProbabilityMeasure ((P n).map (X n)) := fun n =>
    (by infer_instance)
  have h_prob_Y : ∀ n, IsProbabilityMeasure ((P n).map (Y n)) := fun n =>
    (by infer_instance)
  -- Package the pushforwards as `ProbabilityMeasure` to apply the Lipschitz
  -- characterisation of weak convergence. Use local `let`-bindings to keep the
  -- subtype folded under `rw [tendsto_iff_forall_lipschitz_integral_tendsto]`.
  let pX : ℕ → ProbabilityMeasure E := fun n => ⟨(P n).map (X n), h_prob_X n⟩
  let pY : ℕ → ProbabilityMeasure E := fun n => ⟨(P n).map (Y n), h_prob_Y n⟩
  let pν : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have h_coe_X : ∀ n, (pX n : Measure E) = (P n).map (X n) := fun _ => rfl
  have h_coe_Y : ∀ n, (pY n : Measure E) = (P n).map (Y n) := fun _ => rfl
  have h_coe_ν : (pν : Measure E) = ν := rfl
  -- `hX` rewrites to `Tendsto pX atTop (𝓝 pν)`.
  have h_probmeas_tendsto : Tendsto pX atTop (𝓝 pν) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simp_rw [h_coe_X, h_coe_ν]
    exact hX f
  -- Conclude via the same bridge applied to `pY`.
  suffices h_target : Tendsto pY atTop (𝓝 pν) by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h_target
    intro f
    simpa [h_coe_Y, h_coe_ν] using h_target f
  -- Reduce to Lipschitz test functions.
  rw [tendsto_iff_forall_lipschitz_integral_tendsto] at h_probmeas_tendsto ⊢
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  simp_rw [h_coe_X, h_coe_ν] at h_probmeas_tendsto
  simp_rw [h_coe_Y, h_coe_ν]
  let x₀ : E := Classical.arbitrary E
  -- Bounded Lipschitz test function. Degenerate L = 0 ⇒ F constant.
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul, probReal_univ]
    exact tendsto_const_nhds
  -- Now `F` is `L`-Lipschitz with `L > 0`; use a classic three-piece ε-δ estimate.
  have hF_cont : Continuous F := hF_lip.continuous
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in atTop, |∫ ω, F ω ∂((P n).map (Y n))
      - ∫ ω, F ω ∂ν| < L * ε by
    intro ε hε
    convert this (ε / L) (by positivity)
    field_simp
  intro ε hε
  -- Step A: transfer the integrals from pushforward to base via `integral_map`.
  have h_push_X : ∀ n, ∫ ω, F ω ∂((P n).map (X n)) = ∫ ω, F (X n ω) ∂(P n) := fun n =>
    integral_map (hX_meas n) hF_cont.aestronglyMeasurable
  have h_push_Y : ∀ n, ∫ ω, F ω ∂((P n).map (Y n)) = ∫ ω, F (Y n ω) ∂(P n) := fun n =>
    integral_map (hY_meas n) hF_cont.aestronglyMeasurable
  -- Step B: the three-piece inequality — bound `|∫F(Y) − ∫F(ν)|` in terms of
  -- `|∫F(X) − ∫F(ν)|` plus Lipschitz-residual and tail contributions.
  have h_le : ∀ n, |∫ ω, F ω ∂((P n).map (Y n)) - ∫ ω, F ω ∂ν|
      ≤ L * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ dist (X n ω) (Y n ω)}
        + |∫ ω, F ω ∂((P n).map (X n)) - ∫ ω, F ω ∂ν| := by
    intro n
    refine (abs_sub_le (∫ ω, F ω ∂((P n).map (Y n))) (∫ ω, F ω ∂((P n).map (X n)))
      (∫ ω, F ω ∂ν)).trans ?_
    gcongr
    -- The first piece: `|∫F(Y) − ∫F(X)| ≤ L·(ε/2) + M·P{dist ≥ ε/2}`.
    rw [h_push_Y, h_push_X]
    have h_int_X : Integrable (fun ω => F (X n ω)) (P n) := by
      refine Integrable.of_bound (hF_cont.aemeasurable.comp_aemeasurable (hX_meas n)
        |>.aestronglyMeasurable) (‖F x₀‖ + M) ?_
      refine ae_of_all _ (fun a => ?_)
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans (hF_bounded _ _)
    have h_int_Y : Integrable (fun ω => F (Y n ω)) (P n) := by
      refine Integrable.of_bound (hF_cont.aemeasurable.comp_aemeasurable (hY_meas n)
        |>.aestronglyMeasurable) (‖F x₀‖ + M) ?_
      refine ae_of_all _ (fun a => ?_)
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans (hF_bounded _ _)
    have h_int_sub : Integrable (fun ω => ‖F (Y n ω) - F (X n ω)‖) (P n) :=
      (h_int_Y.sub h_int_X).norm
    rw [← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ ω, F (Y n ω) - F (X n ω) ∂(P n)‖
        ≤ ∫ ω, ‖F (Y n ω) - F (X n ω)‖ ∂(P n) := norm_integral_le_integral_norm _
      _ = ∫ ω in {a | dist (X n a) (Y n a) < ε / 2},
            ‖F (Y n ω) - F (X n ω)‖ ∂(P n)
          + ∫ ω in {a | ε / 2 ≤ dist (X n a) (Y n a)},
            ‖F (Y n ω) - F (X n ω)‖ ∂(P n) := by
          symm
          simp_rw [← not_lt]
          refine integral_add_compl₀ ?_ h_int_sub
          refine nullMeasurableSet_lt ?_ (by fun_prop)
          exact (hX_meas n).dist (hY_meas n)
      _ ≤ ∫ ω in {a | dist (X n a) (Y n a) < ε / 2}, L * (ε / 2) ∂(P n)
          + ∫ ω in {a | ε / 2 ≤ dist (X n a) (Y n a)}, M ∂(P n) := by
          gcongr ?_ + ?_
          · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_
              (fun ω hω => ?_)
            · refine nullMeasurableSet_lt ?_ (by fun_prop)
              exact (hX_meas n).dist (hY_meas n)
            · simp only [Set.mem_ofPred_eq] at hω
              have h_le : dist (Y n ω) (X n ω) ≤ ε / 2 := by
                rw [dist_comm]; exact hω.le
              have := hF_lip.dist_le_mul_of_le h_le
              simpa [Real.dist_eq, Real.norm_eq_abs] using this
          · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const (fun a => ?_)
            rw [← dist_eq_norm]
            convert hF_bounded _ _
      _ = L * (ε / 2) * (P n).real {a | dist (X n a) (Y n a) < ε / 2}
          + M * (P n).real {a | ε / 2 ≤ dist (X n a) (Y n a)} := by
          simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
            Set.univ_inter, smul_eq_mul]
          ring
      _ ≤ L * (ε / 2)
          + M * (P n).real {a | ε / 2 ≤ dist (X n a) (Y n a)} := by
          rw [mul_assoc]
          gcongr
          grw [measureReal_le_one, mul_one]
  -- Step C: the RHS tends to `L * (ε / 2) + 0 + 0`; the strict bound follows from `L * (ε / 2) < L * ε`.
  have h_tendsto : Tendsto (fun n =>
      L * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ dist (X n ω) (Y n ω)}
        + |∫ ω, F ω ∂((P n).map (X n)) - ∫ ω, F ω ∂ν|)
      atTop (𝓝 (L * (ε / 2))) := by
    suffices Tendsto (fun n =>
        L * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ dist (X n ω) (Y n ω)}
          + |∫ ω, F ω ∂((P n).map (X n)) - ∫ ω, F ω ∂ν|)
        atTop (𝓝 (L * (ε / 2) + M * 0 + 0)) by simpa using this
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · exact tendsto_const_nhds
    · exact hDist (ε / 2) (by positivity)
    · -- `|∫F(X) − ∫F(ν)| → 0` from the assumed weak convergence.
      have := h_probmeas_tendsto F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
      simp_rw [Metric.tendsto_nhds, Real.dist_eq] at this
      rw [Metric.tendsto_nhds]
      intro δ hδ
      filter_upwards [this δ hδ] with n hn
      rw [Real.dist_eq, sub_zero, abs_abs]
      exact hn
  have h_strict : (L : ℝ) * (ε / 2) < L * ε := by
    have : (0 : ℝ) < L * (ε / 2) := by positivity
    linarith [this]
  have := h_tendsto.eventually_lt_const h_strict
  filter_upwards [this] with n hn
  exact lt_of_le_of_lt (h_le n) hn

end AsymptoticStatistics

end GLP0011B3Source35
end AronowAudit.P001.Wave1.GLP0011B3

/-! Adapted from StatLean module `AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird`. -/
namespace AronowAudit.P001.Wave1.GLP0011B3
section GLP0011B3Source36


/-! # Le Cam theory for nondominated QMD paths -/

set_option linter.style.longFile 1600

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedQMDPath
open AsymptoticStatistics.Core.NondominatedQMDPath.NondominatedQMDPath
open AsymptoticStatistics.Contiguity

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Normalized empirical sum; the empty sum is zero. -/
noncomputable def normalizedScoreSum
    (u : ↥(L2ZeroMean P)) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i : Fin n, (u : Ω → ℝ) (X i)

/-- Possibly singular two-coordinate Gram Gaussian. -/
noncomputable def scorePairGaussian
    (γ : NondominatedQMDPath P) (u : ↥(L2ZeroMean P)) : Measure (ℝ × ℝ) :=
  let v : Fin 2 → ↥(L2ZeroMean P) := ![u, γ.score]
  (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (Matrix.gram ℝ v)).map
    (fun z => (z 0, z 1))

private lemma integral_l2ZeroMean_eq_zero (u : ↥(L2ZeroMean P)) :
    ∫ x, (u : Ω → ℝ) x ∂P = 0 := by
  have hu : integralL2 P (u : Lp ℝ 2 P) = 0 := by
    have hmem : (u : Lp ℝ 2 P) ∈ L2ZeroMean P := u.2
    change (u : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at hmem
    rw [LinearMap.mem_ker] at hmem
    exact hmem
  change ⟪oneL2 P, (u : Lp ℝ 2 P)⟫_ℝ = 0 at hu
  rw [MeasureTheory.L2.inner_def] at hu
  have hone : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  rw [integral_congr_ae (hone.mono fun x hx => by
    change (u : Ω → ℝ) x * (oneL2 P : Ω → ℝ) x = (u : Ω → ℝ) x
    rw [hx, mul_one])] at hu
  exact hu

private lemma integral_l2ZeroMean_mul (u v : ↥(L2ZeroMean P)) :
    ∫ x, (u : Ω → ℝ) x * (v : Ω → ℝ) x ∂P = ⟪u, v⟫_ℝ := by
  change ∫ x, (u : Ω → ℝ) x * (v : Ω → ℝ) x ∂P =
    ⟪(u : Lp ℝ 2 P), (v : Lp ℝ 2 P)⟫_ℝ
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  change (u : Ω → ℝ) x * (v : Ω → ℝ) x =
    (v : Ω → ℝ) x * (u : Ω → ℝ) x
  ring_nf

private noncomputable def scoreVector
    (v : Fin 2 → ↥(L2ZeroMean P)) (x : Ω) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i => ((v i : Lp ℝ 2 P) : Ω → ℝ) x)

private lemma measurable_scoreVector (v : Fin 2 → ↥(L2ZeroMean P)) :
    Measurable (scoreVector (P := P) v) := by
  unfold scoreVector
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  exact Measurable.of_eval fun i => (Lp.stronglyMeasurable (v i : Lp ℝ 2 P)).measurable

private lemma inner_scoreVector (v : Fin 2 → ↥(L2ZeroMean P))
    (a : EuclideanSpace ℝ (Fin 2)) (x : Ω) :
    ⟪a, scoreVector v x⟫_ℝ = ∑ i, a i * (v i : Ω → ℝ) x := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (v i : Ω → ℝ) x * a i = a i * (v i : Ω → ℝ) x
  ring_nf

private noncomputable def actualLogLikelihood
    (γ : NondominatedQMDPath P) (a : ℝ) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  Real.log (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal

private lemma measurable_acProductLikelihood_toReal
    (γ : NondominatedQMDPath P) (t : ℝ) (n : ℕ) :
    Measurable (fun X : Fin n → Ω => (γ.acProductLikelihood t n X).toReal) := by
  unfold acProductLikelihood
  exact (Finset.measurable_prod Finset.univ fun i _ =>
    (Measure.measurable_rnDeriv (γ.curve t) P).comp
      (measurable_pi_apply i)).ennreal_toReal

private lemma measurable_actualLogLikelihood
    (γ : NondominatedQMDPath P) (a : ℝ) (n : ℕ) :
    Measurable (actualLogLikelihood γ a n) := by
  exact (measurable_acProductLikelihood_toReal γ
    (a * (Real.sqrt n)⁻¹) n).log

private lemma acProductLikelihood_toReal_zero_mass_le
    (γ : NondominatedQMDPath P) (t : ℝ) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => P))
        {X | (γ.acProductLikelihood t n X).toReal = 0} ≤
      (n : ℝ≥0∞) * γ.baseZeroLikelihoodMass t := by
  classical
  let Z : Set Ω := {x | ((γ.curve t).rnDeriv P x).toReal = 0}
  let Zn : Set (Fin n → Ω) := {X | (γ.acProductLikelihood t n X).toReal = 0}
  have hsubset : Zn ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin n)),
      (fun X : Fin n → Ω => X i) ⁻¹' Z := by
    intro X hX
    simp only [Set.mem_iUnion, Finset.mem_univ]
    by_contra hall
    push Not at hall
    have hfactor : ∀ i : Fin n,
        ((γ.curve t).rnDeriv P (X i)).toReal ≠ 0 := by
      intro i hi
      exact hall i trivial
        (by simpa only [Z, Set.mem_preimage, Set.mem_ofPred_eq] using hi)
    have hprod : (γ.acProductLikelihood t n X).toReal ≠ 0 := by
      rw [ENNReal.toReal_ne_zero]
      constructor
      · unfold acProductLikelihood
        rw [Finset.prod_ne_zero_iff]
        intro i _
        exact (ENNReal.toReal_ne_zero.mp (hfactor i)).1
      · unfold acProductLikelihood
        exact ENNReal.prod_ne_top fun i _ =>
          (ENNReal.toReal_ne_zero.mp (hfactor i)).2
    exact hprod hX
  have hZmeas : MeasurableSet Z := by
    exact (measurableSet_singleton 0).preimage
      (Measure.measurable_rnDeriv (γ.curve t) P).ennreal_toReal
  have hcoord : ∀ i : Fin n,
      (Measure.pi (fun _ : Fin n => P)) ((fun X : Fin n → Ω => X i) ⁻¹' Z) =
        γ.baseZeroLikelihoodMass t := by
    intro i
    calc
      (Measure.pi (fun _ : Fin n => P)) ((fun X : Fin n → Ω => X i) ⁻¹' Z) =
          ((Measure.pi (fun _ : Fin n => P)).map (fun X => X i)) Z := by
            rw [Measure.map_apply (measurable_pi_apply i) hZmeas]
      _ = P Z := by rw [Measure.pi_map_eval]; simp
      _ = γ.baseZeroLikelihoodMass t := by rfl
  calc
    (Measure.pi (fun _ : Fin n => P))
          {X | (γ.acProductLikelihood t n X).toReal = 0} =
        (Measure.pi (fun _ : Fin n => P)) Zn := rfl
    _ ≤ (Measure.pi (fun _ : Fin n => P))
          (⋃ i ∈ (Finset.univ : Finset (Fin n)),
            (fun X : Fin n → Ω => X i) ⁻¹' Z) := measure_mono hsubset
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)),
          (Measure.pi (fun _ : Fin n => P))
            ((fun X : Fin n → Ω => X i) ⁻¹' Z) :=
      measure_biUnion_finset_le Finset.univ _
    _ = (n : ℝ≥0∞) * γ.baseZeroLikelihoodMass t := by
      simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

private lemma integrable_exp_actualLogLikelihood
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Integrable (fun X => Real.exp (actualLogLikelihood γ a n X))
      (Measure.pi (fun _ : Fin n => P)) := by
  let t := a * (Real.sqrt n)⁻¹
  have ht : 0 ≤ t := mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hL := (γ.integrable_acProductLikelihood_and_integral t ht n).1
  have hmajor : Integrable
      (fun X : Fin n → Ω =>
        (γ.acProductLikelihood t n X).toReal + 1)
      (Measure.pi (fun _ : Fin n => P)) := hL.add (integrable_const 1)
  refine hmajor.mono' ((measurable_actualLogLikelihood γ a n).exp.aestronglyMeasurable) ?_
  filter_upwards with X
  by_cases hzero : (γ.acProductLikelihood t n X).toReal = 0
  · norm_num [actualLogLikelihood, t, hzero]
  · rw [show actualLogLikelihood γ a n X =
        Real.log (γ.acProductLikelihood t n X).toReal by rfl,
      Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero))]
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact le_add_of_nonneg_right zero_le_one

private lemma integral_exp_actualLogLikelihood_sub_likelihood
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (∫ X, Real.exp (actualLogLikelihood γ a n X)
        ∂(Measure.pi (fun _ : Fin n => P))) -
      ∫ X, (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal
        ∂(Measure.pi (fun _ : Fin n => P)) =
      ((Measure.pi (fun _ : Fin n => P))
        {X | (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal = 0}).toReal := by
  let t := a * (Real.sqrt n)⁻¹
  let Z : Set (Fin n → Ω) :=
    {X | (γ.acProductLikelihood t n X).toReal = 0}
  have ht : 0 ≤ t := mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hexp := integrable_exp_actualLogLikelihood γ a ha n
  have hL := (γ.integrable_acProductLikelihood_and_integral t ht n).1
  have hZmeas : MeasurableSet Z :=
    (measurableSet_singleton 0).preimage
      (measurable_acProductLikelihood_toReal γ t n)
  rw [← MeasureTheory.integral_sub hexp hL]
  have hpw : (fun X : Fin n → Ω =>
      Real.exp (actualLogLikelihood γ a n X) -
        (γ.acProductLikelihood t n X).toReal) = Z.indicator (fun _ => (1 : ℝ)) := by
    funext X
    by_cases hzero : (γ.acProductLikelihood t n X).toReal = 0
    · simp [Z, hzero, actualLogLikelihood, t]
    · simp only [Z, Set.indicator_of_notMem, Set.mem_ofPred_eq, hzero, not_false_eq_true]
      rw [show actualLogLikelihood γ a n X =
          Real.log (γ.acProductLikelihood t n X).toReal by rfl,
        Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero))]
      simp
  rw [hpw, MeasureTheory.integral_indicator hZmeas]
  simp only [integral_const, smul_eq_mul, mul_one,
    Measure.real_def, Z, t]
  rw [Measure.restrict_apply_univ]

private lemma integral_acProductLikelihood_localScale_tendsto_one
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n =>
      ∫ X, (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 1) := by
  have hint : ∀ n,
      ∫ X, (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal
          ∂(Measure.pi (fun _ : Fin n => P)) =
        (1 - (γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal) ^ n := by
    intro n
    exact (γ.integrable_acProductLikelihood_and_integral _
      (mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _))) n).2
  have hs := γ.singular_mass_localScale_tendsto a ha
  have hsreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hs
  have hsreal' : Tendsto (fun n : ℕ =>
      ((n : ℝ≥0∞) * γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal)
      atTop (nhds 0) := by simpa only [Function.comp_apply, ENNReal.toReal_zero] using! hsreal
  have hndiff : Tendsto (fun n : ℕ => (n : ℝ) *
      ((1 - (γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal) - 1))
      atTop (nhds 0) := by
    convert hsreal'.neg using 1
    · funext n
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
      ring_nf
    · simp
  have hpow := Real.tendsto_one_add_pow_exp_of_tendsto hndiff
  simp only [Real.exp_zero] at hpow
  refine hpow.congr' ?_
  filter_upwards with n
  rw [hint n]
  congr 1
  ring_nf

private lemma integral_exp_actualLogLikelihood_tendsto_one
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n => ∫ X, Real.exp (actualLogLikelihood γ a n X)
      ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 1) := by
  have hzero := γ.base_zeroLikelihood_localScale_tendsto a ha
  have hzero_real := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hzero
  have hbad : Tendsto (fun n =>
      ((Measure.pi (fun _ : Fin n => P))
        {X | (γ.acProductLikelihood (a * (Real.sqrt n)⁻¹) n X).toReal = 0}).toReal)
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hzero_real (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_
    filter_upwards with n
    exact ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
        (measure_ne_top P _))
      (acProductLikelihood_toReal_zero_mass_le γ _ n)
  have hsum := (integral_acProductLikelihood_localScale_tendsto_one γ a ha).add hbad
  simpa only [add_zero] using hsum.congr' (Filter.Eventually.of_forall fun n => by
    rw [← integral_exp_actualLogLikelihood_sub_likelihood γ a ha n]
    ring_nf)

private lemma actualLog_integral_comparison_bound
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a)
    (Y : ∀ n, (Fin n → Ω) → ℝ) (hY : ∀ n, Measurable (Y n))
    (f : BoundedContinuousFunction ℝ ℝ) (n : ℕ) :
    |∫ X, f (Y n X) ∂(Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) -
      ∫ X, f (Y n X) * Real.exp (actualLogLikelihood γ a n X)
        ∂(Measure.pi (fun _ : Fin n => P))| ≤
      ‖f‖ * ((((n : ℝ≥0∞) *
          γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal) +
        (((n : ℝ≥0∞) *
          γ.baseZeroLikelihoodMass (a * (Real.sqrt n)⁻¹)).toReal)) := by
  classical
  let t := a * (Real.sqrt n)⁻¹
  have ht : 0 ≤ t := mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _))
  let : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t ht
  let Q : Measure Ω := γ.curve t
  let A : Measure Ω := γ.acPart t
  let ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => Q)
  let ρ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => A)
  let Pn : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => P)
  let L : (Fin n → Ω) → ℝ≥0∞ := γ.acProductLikelihood t n
  let F : (Fin n → Ω) → ℝ := fun X => f (Y n X)
  have hAQ : A ≤ Q := by
    simpa only [A, Q, acPart] using
      Measure.withDensity_rnDeriv_le (γ.curve t) P
  let : IsFiniteMeasure A := isFiniteMeasure_of_le Q hAQ
  have hAac : A ≪ Q := hAQ.absolutelyContinuous
  have hρν : ρ ≤ ν := by
    let D : (Fin n → Ω) → ℝ≥0∞ :=
      fun X => ∏ i : Fin n, A.rnDeriv Q (X i)
    have hcoord : ∀ i : Fin n, A.rnDeriv Q ≤ᵐ[Q] 1 :=
      fun _ => Measure.rnDeriv_le_one_of_le hAQ
    have hall : (fun X : Fin n → Ω => fun i : Fin n => A.rnDeriv Q (X i))
        ≤ᵐ[ν] (fun _ => fun _ : Fin n => (1 : ℝ≥0∞)) := by
      simpa only [ν] using! Measure.ae_le_pi hcoord
    have hDle : D ≤ᵐ[ν] 1 := by
      filter_upwards [hall] with X hX
      exact Finset.prod_le_one₀ (fun _ _ => zero_le)
        (fun i _ => hX i)
    have htilt : ν.withDensity D = ρ := by
      have hcoordtilt : Q.withDensity (A.rnDeriv Q) = A :=
        Measure.withDensity_rnDeriv_eq A Q hAac
      calc
        ν.withDensity D =
            Measure.pi (fun _ : Fin n => Q.withDensity (A.rnDeriv Q)) := by
          simpa only [ν, D] using MeasureTheory.pi_withDensity_prod
            (fun _ : Fin n => Measure.measurable_rnDeriv A Q)
        _ = ρ := by simp only [hcoordtilt, ρ]
    rw [← htilt]
    simpa using withDensity_mono hDle
  let R : Measure (Fin n → Ω) := ν - ρ
  have hRρ : R + ρ = ν := Measure.sub_add_cancel_of_le hρν
  have hFmeas : Measurable F := f.continuous.measurable.comp (hY n)
  have hFν : Integrable F ν := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable ‖f‖ ?_
    exact Filter.Eventually.of_forall fun X => f.norm_coe_le_norm (Y n X)
  have hFρ : Integrable F ρ := hFν.mono_measure hρν
  have hRν : R ≤ ν := Measure.sub_le
  have hFR : Integrable F R := hFν.mono_measure hRν
  have hfull : ∫ X, F X ∂ν = (∫ X, F X ∂R) + ∫ X, F X ∂ρ := by
    rw [← hRρ, integral_add_measure hFR hFρ]
  have hρbase : ρ = Pn.withDensity L := by
    simpa only [ρ, Pn, L, A] using
      γ.pi_acPart_eq_withDensity_acProductLikelihood t ht n
  have hLmeas : Measurable L := by
    dsimp only [L, acProductLikelihood]
    exact Finset.measurable_prod _ fun i _ =>
      (Measure.measurable_rnDeriv (γ.curve t) P).comp
        (measurable_pi_apply i)
  have hLfin : ∀ᵐ X ∂Pn, L X < ⊤ := by
    have hcoordfin : ∀ i : Fin n,
        (fun _ : Ω => True) ≤ᵐ[P]
          (fun ω => (γ.curve t).rnDeriv P ω ≠ ⊤) := by
      intro i
      filter_upwards [Measure.rnDeriv_ne_top (γ.curve t) P] with ω hω
      exact fun _ => hω
    have hall : (fun X : Fin n → Ω => fun _ : Fin n => True)
        ≤ᵐ[Pn] (fun X i => (γ.curve t).rnDeriv P (X i) ≠ ⊤) := by
      simpa only [Pn] using Measure.ae_le_pi hcoordfin
    filter_upwards [hall] with X hX
    exact lt_top_iff_ne_top.mpr (by
      dsimp only [L, acProductLikelihood]
      exact ENNReal.prod_ne_top fun i _ => hX i trivial)
  have hweighted : ∫ X, F X * (L X).toReal ∂Pn = ∫ X, F X ∂ρ := by
    rw [hρbase,
      integral_withDensity_eq_integral_toReal_smul hLmeas hLfin F]
    apply integral_congr_ae
    filter_upwards with X
    simp only [smul_eq_mul, mul_comm]
  have hdiff : (∫ X, F X ∂ν) - ∫ X, F X * (L X).toReal ∂Pn =
      ∫ X, F X ∂R := by rw [hweighted, hfull]; ring_nf
  have hboundR : |∫ X, F X ∂R| ≤ ‖f‖ * R.real Set.univ := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := R) (f := F) (C := ‖f‖)
        (Filter.Eventually.of_forall fun X => f.norm_coe_le_norm (Y n X)))
  have hsfin : γ.singularMass t ≠ ⊤ := ne_top_of_le_ne_top
    (measure_ne_top (γ.curve t) _)
    (Measure.singularPart_le (γ.curve t) P Set.univ)
  have hsle : (γ.singularMass t).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    apply (ENNReal.toReal_le_toReal hsfin ENNReal.one_ne_top).2
    exact (Measure.singularPart_le (γ.curve t) P Set.univ).trans_eq measure_univ
  have hA_mass : (A Set.univ).toReal = 1 - (γ.singularMass t).toReal := by
    have hdec := γ.curve_eq_singularPart_add_acPart t ht
    have happ := congrArg (fun M : Measure Ω => M Set.univ) hdec
    have hAfin : A Set.univ ≠ ⊤ := measure_ne_top _ _
    have happ' : (1 : ℝ≥0∞) = γ.singularMass t + A Set.univ := by
      simpa only [Measure.add_apply, measure_univ, singularMass, singularPart,
        acPart, A] using happ
    have hreal := congrArg ENNReal.toReal happ'
    rw [ENNReal.toReal_one, ENNReal.toReal_add hsfin hAfin] at hreal
    linarith
  have hρ_mass : ρ.real Set.univ =
      (1 - (γ.singularMass t).toReal) ^ n := by
    simp only [ρ, measureReal_def, Measure.pi_univ, Finset.prod_const,
      ENNReal.toReal_pow, hA_mass]
    rw [Finset.card_univ, Fintype.card_fin]
  have hR_mass : R.real Set.univ =
      1 - (1 - (γ.singularMass t).toReal) ^ n := by
    change ((ν - ρ) Set.univ).toReal = _
    rw [Measure.sub_apply MeasurableSet.univ hρν,
      ENNReal.toReal_sub_of_le (hρν Set.univ) (measure_ne_top ν Set.univ)]
    have hρ_mass' : (ρ Set.univ).toReal =
        (1 - (γ.singularMass t).toReal) ^ n := by
      simpa only [measureReal_def] using hρ_mass
    rw [measure_univ, ENNReal.toReal_one, hρ_mass']
  have hmissing : R.real Set.univ ≤
      ((n : ℝ≥0∞) * γ.singularMass t).toReal := by
    rw [hR_mass, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have hsnonneg : 0 ≤ (γ.singularMass t).toReal := ENNReal.toReal_nonneg
    simpa only [sub_sub_cancel] using
      (AsymptoticStatistics.ForMathlib.HellingerProduct.one_sub_pow_le_nsmul_one_sub
        (x := 1 - (γ.singularMass t).toReal)
        (by linarith [hsle]) (by linarith [hsnonneg]) n)
  have hactual : |∫ X, F X ∂ν - ∫ X, F X * (L X).toReal ∂Pn| ≤
      ‖f‖ * (((n : ℝ≥0∞) * γ.singularMass t).toReal) := by
    rw [hdiff]
    exact hboundR.trans (mul_le_mul_of_nonneg_left hmissing (norm_nonneg f))
  have hLint := (γ.integrable_acProductLikelihood_and_integral t ht n).1
  have hFL : Integrable (fun X => F X * (L X).toReal) Pn :=
    hLint.bdd_mul hFmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => f.norm_coe_le_norm (Y n X))
  have hexp := integrable_exp_actualLogLikelihood γ a ha n
  have hFexp : Integrable (fun X => F X * Real.exp (actualLogLikelihood γ a n X)) Pn :=
    hexp.bdd_mul hFmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => f.norm_coe_le_norm (Y n X))
  let Z : Set (Fin n → Ω) := {X | (L X).toReal = 0}
  have hZmeas : MeasurableSet Z :=
    (measurableSet_singleton 0).preimage hLmeas.ennreal_toReal
  have hpw : (fun X => F X * Real.exp (actualLogLikelihood γ a n X) -
      F X * (L X).toReal) = Z.indicator F := by
    funext X
    by_cases hzero : (L X).toReal = 0
    · simp [Z, hzero, actualLogLikelihood, L, t]
    · simp only [Z, Set.indicator_of_notMem, Set.mem_ofPred_eq, hzero, not_false_eq_true]
      rw [show actualLogLikelihood γ a n X = Real.log (L X).toReal by rfl,
        Real.exp_log (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero))]
      ring_nf
  have hexp_actual : |∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn -
      ∫ X, F X * (L X).toReal ∂Pn| ≤
      ‖f‖ * (((n : ℝ≥0∞) * γ.baseZeroLikelihoodMass t).toReal) := by
    rw [← MeasureTheory.integral_sub hFexp hFL, hpw]
    rw [MeasureTheory.integral_indicator hZmeas]
    have hset : |∫ X in Z, F X ∂Pn| ≤ ‖f‖ * (Pn Z).toReal := by
      simpa only [Real.norm_eq_abs, measureReal_def] using
        (MeasureTheory.norm_setIntegral_le_of_norm_le_const
          (μ := Pn) (f := F) (C := ‖f‖) (measure_lt_top Pn Z)
          (fun X _ => f.norm_coe_le_norm (Y n X)))
    refine hset.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg f))
    exact ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_ne_top P _))
      (acProductLikelihood_toReal_zero_mass_le γ t n)
  change |∫ X, F X ∂ν -
      ∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn| ≤ _
  calc
    |∫ X, F X ∂ν - ∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn| ≤
        |∫ X, F X ∂ν - ∫ X, F X * (L X).toReal ∂Pn| +
          |∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn -
            ∫ X, F X * (L X).toReal ∂Pn| := by
      rw [abs_sub_comm (∫ X, F X * Real.exp (actualLogLikelihood γ a n X) ∂Pn)]
      exact abs_sub_le _ _ _
    _ ≤ ‖f‖ * (((n : ℝ≥0∞) * γ.singularMass t).toReal) +
        ‖f‖ * (((n : ℝ≥0∞) * γ.baseZeroLikelihoodMass t).toReal) :=
      add_le_add hactual hexp_actual
    _ = _ := by rw [mul_add]

private lemma actualLog_integral_comparison
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a)
    (Y : ∀ n, (Fin n → Ω) → ℝ) (hY : ∀ n, Measurable (Y n)) :
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (nhds 0) ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ) (n : ℕ),
        |∫ X, f (Y n X) ∂(Measure.pi (fun _ : Fin n =>
              γ.curve (a * (Real.sqrt n)⁻¹))) -
          ∫ X, f (Y n X) * Real.exp (actualLogLikelihood γ a n X)
            ∂(Measure.pi (fun _ : Fin n => P))| ≤ ‖f‖ * ρ n := by
  let ρ : ℕ → ℝ := fun n =>
    (((n : ℝ≥0∞) * γ.singularMass (a * (Real.sqrt n)⁻¹)).toReal) +
      (((n : ℝ≥0∞) * γ.baseZeroLikelihoodMass
        (a * (Real.sqrt n)⁻¹)).toReal)
  refine ⟨ρ, ?_, fun f n => actualLog_integral_comparison_bound γ a ha Y hY f n⟩
  have hs := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (γ.singular_mass_localScale_tendsto a ha)
  have hz := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (γ.base_zeroLikelihood_localScale_tendsto a ha)
  simpa only [ρ, Function.comp_apply, ENNReal.toReal_zero, zero_add] using hs.add hz

private lemma measurable_normalizedScoreSum
    (u : ↥(L2ZeroMean P)) (n : ℕ) :
    Measurable (normalizedScoreSum u n) := by
  unfold normalizedScoreSum
  exact Measurable.const_mul
    (Finset.measurable_sum _ fun i _ =>
      (Lp.stronglyMeasurable (u : Lp ℝ 2 P)).measurable.comp
        (measurable_pi_apply i)) _

private lemma scorePairGaussian_snd
    (γ : NondominatedQMDPath P) (u : ↥(L2ZeroMean P)) :
    (scorePairGaussian γ u).map Prod.snd =
      gaussianReal 0 (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _)) := by
  classical
  let v : Fin 2 → ↥(L2ZeroMean P) := ![u, γ.score]
  let e : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have he : (fun z : EuclideanSpace ℝ (Fin 2) => z 1) =
      fun z => ⟪e, z⟫_ℝ := by
    funext z
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    dsimp [e]
    change z 1 = z 0 * 0 + z 1 * 1
    ring_nf
  rw [scorePairGaussian, Measure.map_map measurable_snd (by fun_prop)]
  change (multivariateGaussian 0 (Matrix.gram ℝ v)).map
    (fun z : EuclideanSpace ℝ (Fin 2) => z 1) = _
  rw [he, ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal e
    (Matrix.posSemidef_gram ℝ v)]
  congr 2
  apply NNReal.eq
  have hq : 0 ≤ e.ofLp ⬝ᵥ (Matrix.gram ℝ v).mulVec e.ofLp := by
    simpa using (Matrix.posSemidef_gram ℝ v).re_dotProduct_nonneg e.ofLp
  rw [Real.coe_toNNReal _ hq]
  change e.ofLp ⬝ᵥ (Matrix.gram ℝ v).mulVec e.ofLp = ‖γ.score‖ ^ 2
  simp [e, dotProduct, Matrix.mulVec, Matrix.gram_apply, v, Fin.sum_univ_two]

private lemma scorePairGaussian_tilt_fst
    (γ : NondominatedQMDPath P) (a : ℝ) (u : ↥(L2ZeroMean P)) :
    ((scorePairGaussian γ u).withDensity (fun q => ENNReal.ofReal (Real.exp
      (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst =
    gaussianReal (a * ⟪u, γ.score⟫_ℝ) (NNReal.mk (‖u‖ ^ 2) (sq_nonneg _)) := by
  classical
  let v : Fin 2 → ↥(L2ZeroMean P) := ![u, γ.score]
  let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.gram ℝ v
  let coord : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun z => (z 0, z 1)
  let h : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, a]
  have hS : S.PosSemidef := Matrix.posSemidef_gram ℝ v
  have hcoord : Measurable coord := by fun_prop
  have hdens : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp
      (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2))) := by fun_prop
  rw [scorePairGaussian]
  change (((multivariateGaussian 0 S).map coord).withDensity _).map Prod.fst = _
  rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
    _ coord hcoord _ hdens]
  rw [Measure.map_map measurable_fst hcoord]
  have hdensity : ((fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp
      (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2))) ∘ coord) =
      fun z : EuclideanSpace ℝ (Fin 2) => ENNReal.ofReal (Real.exp
        (⟪h, z⟫_ℝ - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2)) := by
    funext z
    have hi : ⟪h, z⟫_ℝ = a * z 1 := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      dsimp [h]
      change z 0 * 0 + z 1 * a = a * z 1
      ring_nf
    have hq : h.ofLp ⬝ᵥ S.mulVec h.ofLp = a ^ 2 * ‖γ.score‖ ^ 2 := by
      simp [h, S, v, dotProduct, Matrix.mulVec, Matrix.gram_apply,
        Fin.sum_univ_two]
      ring_nf
    rw [hi, hq]
    dsimp only [coord, Function.comp_apply]
    ring_nf
  rw [hdensity, ProbabilityTheory.multivariateGaussian_withDensity_exp_shift hS h]
  change (multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) S h) S).map
    (fun z => z 0) = _
  rw [(ProbabilityTheory.measurePreserving_eval_multivariateGaussian hS
    (μ := Matrix.toEuclideanCLM (𝕜 := ℝ) S h) (i := (0 : Fin 2))).map_eq]
  have hmean : (Matrix.toEuclideanCLM (𝕜 := ℝ) S h) 0 =
      a * ⟪u, γ.score⟫_ℝ := by
    change (S.mulVec h.ofLp) 0 = _
    simp only [S, h, v, Matrix.mulVec, Matrix.gram_apply, dotProduct,
      Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Submodule.coe_inner, mul_zero, zero_add]
    change ⟪u, γ.score⟫_ℝ * a = a * ⟪u, γ.score⟫_ℝ
    ring_nf
  have hvar : (S (0 : Fin 2) 0).toNNReal =
      (NNReal.mk (‖u‖ ^ 2) (sq_nonneg _)) := by
    apply NNReal.eq
    have hdiag : 0 ≤ S (0 : Fin 2) 0 := hS.diag_nonneg
    rw [Real.coe_toNNReal _ hdiag]
    simp [S, v, Matrix.gram_apply]
  rw [hmean, hvar]

private lemma exp_affine_score_integrable_and_integral
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (γ : NondominatedQMDPath P) (a : ℝ)
    (hsnd : π.map Prod.snd =
      gaussianReal 0 (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))) :
    let tiltMap : ℝ × ℝ → ℝ × ℝ := fun q =>
      (q.1, a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)
    Integrable (fun q : ℝ × ℝ => Real.exp q.2) (π.map tiltMap) ∧
      ∫ q, Real.exp q.2 ∂(π.map tiltMap) = 1 := by
  dsimp only
  let c : ℝ := (a ^ 2 / 2) * ‖γ.score‖ ^ 2
  let g : ℝ → ℝ := fun x => Real.exp (a * x - c)
  let tiltMap : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, a * q.2 - c)
  have hg_meas : Measurable g := by fun_prop
  have htilt : Measurable tiltMap := by fun_prop
  have hgauss : Integrable g (gaussianReal 0 (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))) := by
    have hbase := ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := (0 : ℝ)) (v := (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))) a
    have hmul := hbase.mul_const (Real.exp (-c))
    exact hmul.congr (Filter.Eventually.of_forall fun x => by
      dsimp only [g]
      rw [sub_eq_add_neg, Real.exp_add])
  have hgauss_int : ∫ x, g x
        ∂(gaussianReal 0 (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))) = 1 := by
    dsimp only [g]
    simp_rw [sub_eq_add_neg, Real.exp_add]
    rw [integral_mul_const,
      ProbabilityTheory.integral_exp_mul_gaussianReal]
    dsimp only [c]
    rw [← Real.exp_add]
    simp
    ring_nf
  have hpull : Integrable (fun q : ℝ × ℝ => g q.2) π := by
    rw [← hsnd] at hgauss
    exact hgauss.comp_measurable measurable_snd
  constructor
  · refine (integrable_map_measure (by fun_prop) htilt.aemeasurable).mpr ?_
    simpa only [Function.comp_apply, tiltMap, g] using! hpull
  · rw [integral_map htilt.aemeasurable (by fun_prop)]
    change ∫ q, g q.2 ∂π = 1
    calc
      ∫ q, g q.2 ∂π = ∫ x, g x ∂(π.map Prod.snd) := by
        rw [integral_map measurable_snd.aemeasurable hg_meas.aestronglyMeasurable]
      _ = ∫ x, g x
          ∂(gaussianReal 0 (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))) := by rw [hsnd]
      _ = 1 := hgauss_int

/-- Baseline joint CLT for a score pair, including singular Gram covariance.

Proof idea: finite-dimensional iid CLT and the `L²₀` moment facts. -/
theorem weakConverges_scorePair_under_pi
    (γ : NondominatedQMDPath P) (u : ↥(L2ZeroMean P)) :
    AsymptoticStatistics.WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (fun X => (normalizedScoreSum u n X,
          normalizedScoreSum γ.score n X)))
      (scorePairGaussian γ u) := by
  classical
  let v : Fin 2 → ↥(L2ZeroMean P) := ![u, γ.score]
  let Pinf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P)
  let Y : ℕ → (ℕ → Ω) → EuclideanSpace ℝ (Fin 2) :=
    fun i X => scoreVector v (X i)
  have : IsProbabilityMeasure Pinf := by dsimp [Pinf]; infer_instance
  have hYmeas : ∀ i, Measurable (Y i) := fun i =>
    (measurable_scoreVector v).comp (measurable_pi_apply i)
  have hiid : iIndepFun Y Pinf := by
    have heval : iIndepFun (fun i (X : ℕ → Ω) => X i) Pinf := by
      dsimp only [Pinf]
      exact iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
    exact heval.comp (g := fun _ => scoreVector v) fun _ => measurable_scoreVector v
  have hevalLaw : ∀ i, Pinf.map (fun X : ℕ → Ω => X i) = P := fun i => by
    dsimp only [Pinf]
    exact Measure.infinitePi_map_eval (fun _ : ℕ => P) i
  have hYlaw : ∀ i, Pinf.map (Y i) = P.map (scoreVector v) := fun i => by
    rw [show Y i = scoreVector v ∘ fun X : ℕ → Ω => X i from rfl,
      ← Measure.map_map (measurable_scoreVector v) (measurable_pi_apply i), hevalLaw]
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) Pinf Pinf := fun i =>
    ⟨(hYmeas i).aemeasurable, (hYmeas 0).aemeasurable, by rw [hYlaw i, hYlaw 0]⟩
  have hzero : ∀ a : EuclideanSpace ℝ (Fin 2),
      ∫ X, ⟪a, Y 0 X⟫_ℝ ∂Pinf = 0 := by
    intro a
    have hasm : AEStronglyMeasurable
        (fun x : Ω => ⟪a, scoreVector v x⟫_ℝ)
        (Pinf.map (fun X : ℕ → Ω => X 0)) := by
      rw [hevalLaw 0]
      exact (((continuous_const.inner continuous_id).measurable.comp
        (measurable_scoreVector v)).aestronglyMeasurable)
    have hmap :
        ∫ x, ⟪a, scoreVector v x⟫_ℝ ∂(Pinf.map (fun X : ℕ → Ω => X 0)) =
          ∫ X, ⟪a, scoreVector v (X 0)⟫_ℝ ∂Pinf :=
      MeasureTheory.integral_map (measurable_pi_apply (0 : ℕ)).aemeasurable hasm
    rw [hevalLaw 0] at hmap
    rw [← hmap, integral_congr_ae (Filter.Eventually.of_forall fun x => inner_scoreVector v a x)]
    rw [MeasureTheory.integral_finsetSum _]
    · simp [MeasureTheory.integral_const_mul, integral_l2ZeroMean_eq_zero]
    · intro i _
      exact ((Lp.memLp (v i : Lp ℝ 2 P)).integrable (by norm_num)).const_mul (a i)
  have hcov : ∀ a b : EuclideanSpace ℝ (Fin 2),
      ∫ X, ⟪a, Y 0 X⟫_ℝ * ⟪b, Y 0 X⟫_ℝ ∂Pinf =
        a.ofLp ⬝ᵥ (Matrix.gram ℝ v).mulVec b.ofLp := by
    intro a b
    have hasm : AEStronglyMeasurable
        (fun x : Ω => ⟪a, scoreVector v x⟫_ℝ * ⟪b, scoreVector v x⟫_ℝ)
        (Pinf.map (fun X : ℕ → Ω => X 0)) := by
      rw [hevalLaw 0]
      exact (((((continuous_const.inner continuous_id).measurable.comp
          (measurable_scoreVector v))).mul
        (((continuous_const.inner continuous_id).measurable.comp
          (measurable_scoreVector v)))).aestronglyMeasurable)
    have hmap :
        ∫ x, ⟪a, scoreVector v x⟫_ℝ * ⟪b, scoreVector v x⟫_ℝ
            ∂(Pinf.map (fun X : ℕ → Ω => X 0)) =
          ∫ X, ⟪a, scoreVector v (X 0)⟫_ℝ *
            ⟪b, scoreVector v (X 0)⟫_ℝ ∂Pinf :=
      MeasureTheory.integral_map (measurable_pi_apply (0 : ℕ)).aemeasurable hasm
    rw [hevalLaw 0] at hmap
    rw [← hmap]
    have hpw : (fun x => ⟪a, scoreVector v x⟫_ℝ * ⟪b, scoreVector v x⟫_ℝ) =
        fun x => ∑ i, ∑ j, (a i * b j) * ((v i : Ω → ℝ) x * (v j : Ω → ℝ) x) := by
      funext x
      rw [inner_scoreVector v a x, inner_scoreVector v b x, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring_nf
    have hint : ∀ i j : Fin 2, MeasureTheory.Integrable
        (fun x : Ω => (a i * b j) * ((v i : Ω → ℝ) x * (v j : Ω → ℝ) x)) P := by
      intro i j
      exact ((Lp.memLp (v i : Lp ℝ 2 P)).integrable_mul
        (Lp.memLp (v j : Lp ℝ 2 P))).const_mul (a i * b j)
    rw [hpw, MeasureTheory.integral_finsetSum _]
    · simp only [dotProduct, Matrix.mulVec]
      apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint i j)]
      simp_rw [MeasureTheory.integral_const_mul, integral_l2ZeroMean_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.gram_apply]
      ring_nf
    · intro i _
      apply MeasureTheory.integrable_finsetSum
      intro j _
      exact hint i j
  have hL2atom : MemLp (scoreVector v) 2 P := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp (v i : Lp ℝ 2 P)
  have hL2 : MemLp (Y 0) 2 Pinf := by
    change MemLp (scoreVector v ∘ fun X : ℕ → Ω => X 0) 2 Pinf
    refine (MeasureTheory.memLp_map_measure_iff ?_ (measurable_pi_apply (0 : ℕ)).aemeasurable).mp ?_
    · rw [hevalLaw 0]
      exact (measurable_scoreVector v).aestronglyMeasurable
    · rw [hevalLaw 0]
      exact hL2atom
  have hclt := AsymptoticStatistics.ScoreCLT.clt_finDim Pinf Y hYmeas hiid hident hzero
    (Matrix.gram ℝ v) (Matrix.posSemidef_gram ℝ v) hcov hL2
  let V : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin 2) := fun n X =>
    WithLp.toLp 2 (fun i => normalizedScoreSum (v i) n X)
  have hVmeas : ∀ n, Measurable (V n) := fun n => by
    dsimp only [V, normalizedScoreSum]
    refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
    exact Measurable.of_eval fun i => Measurable.const_mul
      (Finset.measurable_sum _ fun j _ =>
        (Lp.stronglyMeasurable (v i : Lp ℝ 2 P)).measurable.comp
          (measurable_pi_apply j)) _
  have hrestrict : ∀ n, Measurable (fun X : ℕ → Ω => fun i : Fin n => X i.val) :=
    fun n => Measurable.of_eval fun i => measurable_pi_apply i.val
  have heq : ∀ n, (Measure.pi (fun _ : Fin n => P)).map (V n) =
      Pinf.map (fun X => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i X) := by
    intro n
    rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n,
      Measure.map_map (hVmeas n) (hrestrict n)]
    congr 1
    funext X
    apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
    funext i
    change (Real.sqrt n)⁻¹ * ∑ j : Fin n, (v i : Ω → ℝ) (X j.val) =
      (((Real.sqrt n)⁻¹ • ∑ j ∈ Finset.range n, Y j X :
        EuclideanSpace ℝ (Fin 2)).ofLp) i
    have hsum : (((∑ j ∈ Finset.range n, Y j X) :
        EuclideanSpace ℝ (Fin 2)).ofLp) i =
        ∑ j ∈ Finset.range n, ((Y j X : EuclideanSpace ℝ (Fin 2)).ofLp) i := by
      have hlin : (((∑ j ∈ Finset.range n, Y j X) :
          EuclideanSpace ℝ (Fin 2)).ofLp) =
          ∑ j ∈ Finset.range n, ((Y j X : EuclideanSpace ℝ (Fin 2)).ofLp) :=
        map_sum (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap _ _
      rw [hlin]
      exact Finset.sum_apply i _ _
    rw [show (((Real.sqrt n)⁻¹ • ∑ j ∈ Finset.range n, Y j X :
        EuclideanSpace ℝ (Fin 2)).ofLp) i =
      (Real.sqrt n)⁻¹ * (((∑ j ∈ Finset.range n, Y j X :
        EuclideanSpace ℝ (Fin 2)).ofLp) i) from rfl, hsum]
    change (Real.sqrt n)⁻¹ * ∑ j : Fin n, (v i : Ω → ℝ) (X j.val) =
      (Real.sqrt n)⁻¹ * ∑ j ∈ Finset.range n, (v i : Ω → ℝ) (X j)
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun j => ((v i : Lp ℝ 2 P) : Ω → ℝ) (X j)) n
  have hvec : WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map (V n))
      (multivariateGaussian 0 (Matrix.gram ℝ v)) := by
    intro f
    simpa only [heq] using hclt f
  have hcoord_cont : Continuous
      (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0).prodMk
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1)
  have hcoord_meas := hcoord_cont.measurable
  have hpair := hvec.map
    (f := fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1))
    hcoord_cont hcoord_meas
  change WeakConverges
      (fun n => ((Measure.pi (fun _ : Fin n => P)).map (V n)).map
        (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)))
      ((multivariateGaussian 0 (Matrix.gram ℝ v)).map
        (fun z => (z 0, z 1))) at hpair
  have hseq : ∀ n, ((Measure.pi (fun _ : Fin n => P)).map (V n)).map
      (fun z : EuclideanSpace ℝ (Fin 2) => (z 0, z 1)) =
      (Measure.pi (fun _ : Fin n => P)).map
        (fun X => (normalizedScoreSum u n X,
          normalizedScoreSum γ.score n X)) := by
    intro n
    rw [Measure.map_map hcoord_meas (hVmeas n)]
    congr 1
  simp_rw [hseq] at hpair
  simpa only [scorePairGaussian, v] using hpair

private lemma weakConverges_normalizedScore_under_pi
    (γ : NondominatedQMDPath P) :
    WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (normalizedScoreSum γ.score n))
      (gaussianReal 0 (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))) := by
  have hpair := weakConverges_scorePair_under_pi γ γ.score
  have hsnd := hpair.map (f := Prod.snd) continuous_snd measurable_snd
  rw [scorePairGaussian_snd] at hsnd
  have hpairMeas : ∀ n, Measurable (fun X : Fin n → Ω =>
      (normalizedScoreSum γ.score n X, normalizedScoreSum γ.score n X)) :=
    fun n => (measurable_normalizedScoreSum γ.score n).prodMk
      (measurable_normalizedScoreSum γ.score n)
  change WeakConverges
    (fun n => ((Measure.pi (fun _ : Fin n => P)).map
      (fun X => (normalizedScoreSum γ.score n X,
        normalizedScoreSum γ.score n X))).map Prod.snd) _ at hsnd
  simpa only [Measure.map_map measurable_snd (hpairMeas _)] using! hsnd

private lemma weakConverges_actualLogLikelihood_under_pi
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (actualLogLikelihood γ a n))
      (gaussianReal
        (-((NNReal.mk (a ^ 2 * ‖γ.score‖ ^ 2)
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))) : NNReal) / 2)
        (NNReal.mk (a ^ 2 * ‖γ.score‖ ^ 2) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))) := by
  let c : ℝ := (a ^ 2 / 2) * ‖γ.score‖ ^ 2
  let vScore : NNReal := (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))
  let vLog : NNReal := (NNReal.mk (a ^ 2 * ‖γ.score‖ ^ 2) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have haff : Measurable (fun x : ℝ => a * x - c) := by fun_prop
  let : IsProbabilityMeasure
      ((gaussianReal 0 vScore).map (fun x : ℝ => a * x - c)) :=
    (by infer_instance)
  have hscore := weakConverges_normalizedScore_under_pi γ
  have hlin0 := hscore.map
    (f := fun x : ℝ => a * x - c) (by fun_prop) (by fun_prop)
  have hlin : WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (fun X => a * normalizedScoreSum γ.score n X - c))
      ((gaussianReal 0 vScore).map (fun x : ℝ => a * x - c)) := by
    change WeakConverges
      (fun n => ((Measure.pi (fun _ : Fin n => P)).map
        (normalizedScoreSum γ.score n)).map (fun x : ℝ => a * x - c)) _ at hlin0
    simpa only [Measure.map_map haff
      (measurable_normalizedScoreSum γ.score _), Function.comp_apply,
      vScore] using! hlin0
  have hdist : ∀ ε > 0, Tendsto
      (fun n => (Measure.pi (fun _ : Fin n => P)).real
        {X | ε ≤ dist
          (a * normalizedScoreSum γ.score n X - c)
          (actualLogLikelihood γ a n X)})
      atTop (nhds 0) := by
    intro ε hε
    have hset : ∀ n,
        {X : Fin n → Ω | ε ≤ dist
          (a * normalizedScoreSum γ.score n X - c)
          (actualLogLikelihood γ a n X)} =
        {X | ε ≤ |actualLogLikelihood γ a n X -
          (a * (Real.sqrt n)⁻¹ *
              ∑ i : Fin n, (γ.score : Ω → ℝ) (X i) -
            (a ^ 2 / 2) * ‖γ.score‖ ^ 2)|} := by
      intro n
      ext X
      simp only [Set.mem_ofPred_eq, Real.dist_eq, normalizedScoreSum,
        actualLogLikelihood, c]
      rw [abs_sub_comm]
      ring_nf
    have hlan :=
      NondominatedQMDLAN.log_acProductLikelihood_lan_tendstoInMeasure γ a ha ε hε
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlan
    simpa only [measureReal_def, hset, Function.comp_apply,
      ENNReal.toReal_zero] using! hreal
  have hactual := WeakConverges.slutsky_of_tendstoInMeasure_dist
    (fun n => ((measurable_normalizedScoreSum γ.score n).const_mul a).sub_const c |>.aemeasurable)
    (fun n => (measurable_actualLogLikelihood γ a n).aemeasurable)
    hlin hdist
  have hgauss : (gaussianReal 0 vScore).map (fun x : ℝ => a * x - c) =
      gaussianReal (-(vLog : ℝ) / 2) vLog := by
    calc
      (gaussianReal 0 vScore).map (fun x : ℝ => a * x - c) =
          ((gaussianReal 0 vScore).map (fun x : ℝ => a * x)).map
            (fun x : ℝ => x - c) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = gaussianReal (-(vLog : ℝ) / 2) vLog := by
        rw [ProbabilityTheory.gaussianReal_map_const_mul,
          ProbabilityTheory.gaussianReal_map_sub_const]
        congr 2
        dsimp only [c, vLog]
        simp
        ring_nf
  rw [hgauss] at hactual
  simpa only [vLog] using hactual

/-- Subsequence Le Cam third lemma using the actual RN product likelihood.

Proof idea: bounded-test product comparison, actual-likelihood LAN,
truncation, normalization, and uniform integrability. -/
theorem qmd_lecamThird_along_subseq
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a)
    (Y : ∀ n, (Fin n → Ω) → ℝ) (hY : ∀ n, Measurable (Y n))
    (χ : ℕ → ℕ) (hχ : StrictMono χ)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hπ : AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X, normalizedScoreSum γ.score (χ k) X))) π) :
    AsymptoticStatistics.WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) =>
        γ.curve (a * (Real.sqrt (χ k))⁻¹))).map (Y (χ k)))
      ((π.withDensity (fun q => ENNReal.ofReal (Real.exp
        (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst) := by
  let c : ℝ := (a ^ 2 / 2) * ‖γ.score‖ ^ 2
  let vScore : NNReal := (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))
  let vLog : NNReal := (NNReal.mk (a ^ 2 * ‖γ.score‖ ^ 2) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  let tiltMap : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, a * q.2 - c)
  have htilt_cont : Continuous tiltMap := by fun_prop
  have htilt : Measurable tiltMap := htilt_cont.measurable
  have : IsProbabilityMeasure (π.map tiltMap) :=
    (by infer_instance)
  have hpairMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
      (Y (χ k) X, normalizedScoreSum γ.score (χ k) X)) := fun k =>
    (hY (χ k)).prodMk (measurable_normalizedScoreSum γ.score (χ k))
  have hscore_sub : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (normalizedScoreSum γ.score (χ k)))
      (gaussianReal 0 vScore) := by
    simpa only [vScore] using
      (weakConverges_normalizedScore_under_pi γ).comp hχ
  have hscore_as_snd : WeakConverges
      (fun k => ((Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X, normalizedScoreSum γ.score (χ k) X))).map Prod.snd)
      (gaussianReal 0 vScore) := by
    simpa only [Measure.map_map measurable_snd (hpairMeas _)] using! hscore_sub
  have hπsnd : π.map Prod.snd = gaussianReal 0 vScore :=
    WeakConverges.snd_eq hπ hscore_as_snd
  have hlin := hπ.map htilt_cont htilt
  change WeakConverges
      (fun k => ((Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X, normalizedScoreSum γ.score (χ k) X))).map tiltMap)
      (π.map tiltMap) at hlin
  have hlinMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
      (Y (χ k) X, a * normalizedScoreSum γ.score (χ k) X - c)) := fun k =>
    (hY (χ k)).prodMk
      (((measurable_normalizedScoreSum γ.score (χ k)).const_mul a).sub_const c)
  have hlin' : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X,
          a * normalizedScoreSum γ.score (χ k) X - c)))
      (π.map tiltMap) := by
    simpa only [Measure.map_map htilt (hpairMeas _), tiltMap, Function.comp_apply] using! hlin
  have hactualMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
      (Y (χ k) X, actualLogLikelihood γ a (χ k) X)) := fun k =>
    (hY (χ k)).prodMk (measurable_actualLogLikelihood γ a (χ k))
  have hdist : ∀ ε > 0, Tendsto
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).real
        {X | ε ≤ dist
          (Y (χ k) X, a * normalizedScoreSum γ.score (χ k) X - c)
          (Y (χ k) X, actualLogLikelihood γ a (χ k) X)})
      atTop (nhds 0) := by
    intro ε hε
    have hset : ∀ k,
        {X : Fin (χ k) → Ω | ε ≤ dist
          (Y (χ k) X, a * normalizedScoreSum γ.score (χ k) X - c)
          (Y (χ k) X, actualLogLikelihood γ a (χ k) X)} =
        {X | ε ≤ |actualLogLikelihood γ a (χ k) X -
          (a * (Real.sqrt (χ k))⁻¹ *
              ∑ i : Fin (χ k), (γ.score : Ω → ℝ) (X i) -
            (a ^ 2 / 2) * ‖γ.score‖ ^ 2)|} := by
      intro k
      ext X
      simp only [Set.mem_ofPred_eq, dist_prod_same_left, Real.dist_eq,
        normalizedScoreSum, actualLogLikelihood, c]
      rw [abs_sub_comm]
      ring_nf
    have hlan :=
      NondominatedQMDLAN.log_acProductLikelihood_lan_tendstoInMeasure γ a ha ε hε
    have hlan_sub := hlan.comp hχ.tendsto_atTop
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlan_sub
    simpa only [measureReal_def, hset, Function.comp_apply, ENNReal.toReal_zero] using! hreal
  have hjointLog : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => (Y (χ k) X, actualLogLikelihood γ a (χ k) X)))
      (π.map tiltMap) :=
    WeakConverges.slutsky_of_tendstoInMeasure_dist
      (fun k => (hlinMeas k).aemeasurable)
      (fun k => (hactualMeas k).aemeasurable) hlin' hdist
  have htilt_snd : (π.map tiltMap).map Prod.snd =
      gaussianReal (-(vLog : ℝ) / 2) vLog := by
    calc
      (π.map tiltMap).map Prod.snd =
          π.map (fun q : ℝ × ℝ => a * q.2 - c) := by
        rw [Measure.map_map measurable_snd htilt]
        rfl
      _ = (π.map Prod.snd).map (fun x : ℝ => a * x - c) := by
        rw [Measure.map_map (by fun_prop) measurable_snd]
        rfl
      _ = (gaussianReal 0 vScore).map (fun x : ℝ => a * x - c) := by rw [hπsnd]
      _ = ((gaussianReal 0 vScore).map (fun x : ℝ => a * x)).map
          (fun x : ℝ => x - c) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = gaussianReal (-(vLog : ℝ) / 2) vLog := by
        rw [ProbabilityTheory.gaussianReal_map_const_mul,
          ProbabilityTheory.gaussianReal_map_sub_const]
        congr 2
        dsimp only [c, vLog]
        simp
        ring_nf
  have hlogWeak : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map
        (actualLogLikelihood γ a (χ k)))
      (gaussianReal (-(vLog : ℝ) / 2) vLog) := by
    have hsnd := hjointLog.map (f := Prod.snd) continuous_snd measurable_snd
    rw [htilt_snd] at hsnd
    simpa only [Measure.map_map measurable_snd (hactualMeas _)] using! hsnd
  have h_exp_int : ∀ k, Integrable
      (fun X => Real.exp (actualLogLikelihood γ a (χ k) X))
      (Measure.pi (fun _ : Fin (χ k) => P)) := fun k =>
    integrable_exp_actualLogLikelihood γ a ha (χ k)
  have h_mass : Tendsto (fun k =>
      ∫ X, Real.exp (actualLogLikelihood γ a (χ k) X)
        ∂(Measure.pi (fun _ : Fin (χ k) => P))) atTop (nhds 1) :=
    (integral_exp_actualLogLikelihood_tendsto_one γ a ha).comp hχ.tendsto_atTop
  let : ∀ k, IsProbabilityMeasure
      (Measure.pi (fun _ : Fin (χ k) => γ.curve (a * (Real.sqrt (χ k))⁻¹))) :=
    fun k => by
      let : IsProbabilityMeasure (γ.curve (a * (Real.sqrt (χ k))⁻¹)) :=
        γ.curve_isProbability _
          (mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      infer_instance
  have hUI := uniform_integrability_exp_L_of_integral_tendsto_one
    (Ω := fun k => Fin (χ k) → Ω)
    (fun k => Measure.pi (fun _ : Fin (χ k) => P))
    (fun k => Measure.pi (fun _ : Fin (χ k) =>
      γ.curve (a * (Real.sqrt (χ k))⁻¹)))
    (fun k => actualLogLikelihood γ a (χ k))
    (fun k => measurable_actualLogLikelihood γ a (χ k))
    h_exp_int h_mass vLog hlogWeak
  obtain ⟨ρ, hρ, hcmp⟩ := actualLog_integral_comparison γ a ha Y hY
  have hcmp_sub : ∃ ρ' : ℕ → ℝ, Tendsto ρ' atTop (nhds 0) ∧
      ∀ (f : BoundedContinuousFunction ℝ ℝ) (k : ℕ),
        |∫ X, f (Y (χ k) X) ∂(Measure.pi (fun _ : Fin (χ k) =>
              γ.curve (a * (Real.sqrt (χ k))⁻¹))) -
          ∫ X, f (Y (χ k) X) * Real.exp (actualLogLikelihood γ a (χ k) X)
            ∂(Measure.pi (fun _ : Fin (χ k) => P))| ≤ ‖f‖ * ρ' k :=
    ⟨ρ ∘ χ, hρ.comp hχ.tendsto_atTop, fun f k => hcmp f (χ k)⟩
  have hmgf := exp_affine_score_integrable_and_integral π γ a (by
    simpa only [vScore] using hπsnd)
  have hlecam := weak_limit_under_Q_of_lecam_third_of_integral_comparison
    (Ω := fun k => Fin (χ k) → Ω) (E := ℝ)
    (fun k => Measure.pi (fun _ : Fin (χ k) => P))
    (fun k => Measure.pi (fun _ : Fin (χ k) =>
      γ.curve (a * (Real.sqrt (χ k))⁻¹)))
    (fun k => Y (χ k)) (fun k => actualLogLikelihood γ a (χ k))
    (fun k => hY (χ k))
    (fun k => measurable_actualLogLikelihood γ a (χ k))
    hcmp_sub (π.map tiltMap) hjointLog hUI hmgf.1 hmgf.2
  have htarget :
      ((π.map tiltMap).withDensity
        (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst =
      (π.withDensity (fun q => ENNReal.ofReal (Real.exp
        (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst := by
    have hdens : Measurable
        (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.2)) := by fun_prop
    rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
      π tiltMap htilt _ hdens]
    rw [Measure.map_map measurable_fst htilt]
    rfl
  rw [← htarget]
  exact hlecam

/-- Local score CLT under a nonnegative one-sided QMD tilt.

Proof idea: score-pair CLT, `qmd_lecamThird_along_subseq`, and the tilted
possibly-singular Gram-Gaussian calculation. -/
theorem qmd_local_score_clt
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a)
    (u : ↥(L2ZeroMean P)) :
    AsymptoticStatistics.WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))).map (normalizedScoreSum u n))
      (gaussianReal (a * ⟪u, γ.score⟫_ℝ)
        (NNReal.mk (‖u‖ ^ 2) (sq_nonneg _))) := by
  let : IsProbabilityMeasure (scorePairGaussian γ u) := by
    unfold scorePairGaussian
    exact (by infer_instance)
  have h := qmd_lecamThird_along_subseq γ a ha
    (fun n => normalizedScoreSum u n)
    (fun n => measurable_normalizedScoreSum u n)
    id strictMono_id (scorePairGaussian γ u)
    (by simpa only [Function.id_def] using! weakConverges_scorePair_under_pi γ u)
  rw [scorePairGaussian_tilt_fst] at h
  simpa only [Function.id_def] using! h

/-- Every fixed nonnegative local path law is contiguous to the baseline.

Proof idea: actual LAN and Le Cam's first lemma, including the zero-score
normalization split. -/
theorem qmd_local_contiguous
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a) :
    Contiguous atTop
      (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n => Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) := by
  let vLog : NNReal := (NNReal.mk (a ^ 2 * ‖γ.score‖ ^ 2) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  let : ∀ n, IsProbabilityMeasure
      (Measure.pi (fun _ : Fin n => γ.curve (a * (Real.sqrt n)⁻¹))) :=
    fun n => by
      let : IsProbabilityMeasure (γ.curve (a * (Real.sqrt n)⁻¹)) :=
        γ.curve_isProbability _
          (mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      infer_instance
  have hlog : WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (actualLogLikelihood γ a n))
      (gaussianReal (-(vLog : ℝ) / 2) vLog) := by
    simpa only [vLog] using weakConverges_actualLogLikelihood_under_pi γ a ha
  have h_exp_int : ∀ n, Integrable
      (fun X => Real.exp (actualLogLikelihood γ a n X))
      (Measure.pi (fun _ : Fin n => P)) :=
    fun n => integrable_exp_actualLogLikelihood γ a ha n
  have hUI := uniform_integrability_exp_L_of_integral_tendsto_one
    (fun n => Measure.pi (fun _ : Fin n => P))
    (fun n => Measure.pi (fun _ : Fin n =>
      γ.curve (a * (Real.sqrt n)⁻¹)))
    (actualLogLikelihood γ a)
    (measurable_actualLogLikelihood γ a)
    h_exp_int (integral_exp_actualLogLikelihood_tendsto_one γ a ha)
    vLog hlog
  intro A hA hPA
  have hPAreal : Tendsto (fun n =>
      ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal) atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hPA
    simpa only [Function.comp_apply, ENNReal.toReal_zero] using! h
  let Y : ∀ n, (Fin n → Ω) → ℝ := fun n => (A n).indicator (fun _ => 1)
  have hY : ∀ n, Measurable (Y n) := fun n => measurable_one.indicator (hA n)
  let clip : BoundedContinuousFunction ℝ ℝ :=
    { toFun := fun x => min (max x 0) 1
      continuous_toFun := (continuous_id.max continuous_const).min continuous_const
      map_bounded' := ⟨1, fun x y => by
        rw [Real.dist_eq]
        have hx0 : 0 ≤ min (max x 0) 1 :=
          le_min (le_max_right _ _) zero_le_one
        have hy0 : 0 ≤ min (max y 0) 1 :=
          le_min (le_max_right _ _) zero_le_one
        have hx1 : min (max x 0) 1 ≤ 1 := min_le_right _ _
        have hy1 : min (max y 0) 1 ≤ 1 := min_le_right _ _
        rw [abs_le]
        constructor <;> linarith⟩ }
  have hclipY : ∀ n X, clip (Y n X) = Y n X := by
    intro n X
    by_cases hX : X ∈ A n <;> simp [clip, Y, hX]
  obtain ⟨ρ, hρ, hcmp⟩ := actualLog_integral_comparison γ a ha Y hY
  have hweighted : Tendsto (fun n =>
      ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM, N₁, hN₁⟩ := hUI (ε / 2) (by linarith)
    have hM1 : 0 < M + 1 := by linarith
    have hthreshold : 0 < ε / (2 * (M + 1)) := by positivity
    have hPsmall := (Metric.tendsto_nhds.mp hPAreal)
      (ε / (2 * (M + 1))) hthreshold
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hPsmall
    rw [Filter.eventually_atTop]
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn₁ : N₁ ≤ n := le_of_max_le_left hn
    have hn₂ : N₂ ≤ n := le_of_max_le_right hn
    have hYnonneg : ∀ X, 0 ≤ Y n X := by
      intro X
      by_cases hX : X ∈ A n <;> simp [Y, hX]
    have hYle : ∀ X, Y n X ≤ 1 := by
      intro X
      by_cases hX : X ∈ A n <;> simp [Y, hX]
    have htrunc : Integrable (fun X =>
        min (Real.exp (actualLogLikelihood γ a n X)) M)
        (Measure.pi (fun _ : Fin n => P)) := by
      refine (h_exp_int n).mono' ?_ ?_
      · exact (((measurable_actualLogLikelihood γ a n).exp).min
          measurable_const).aestronglyMeasurable
      · filter_upwards with X
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact min_le_left _ _
        · exact le_min (Real.exp_pos _).le hM
    have htail : Integrable (fun X =>
        Real.exp (actualLogLikelihood γ a n X) -
          min (Real.exp (actualLogLikelihood γ a n X)) M)
        (Measure.pi (fun _ : Fin n => P)) := (h_exp_int n).sub htrunc
    have hYint : Integrable (Y n) (Measure.pi (fun _ : Fin n => P)) := by
      exact (integrable_const (1 : ℝ)).indicator (hA n)
    have hMY : Integrable (fun X => M * Y n X)
        (Measure.pi (fun _ : Fin n => P)) := hYint.const_mul M
    have hright := hMY.add htail
    have hmono :
        ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
            ∂(Measure.pi (fun _ : Fin n => P)) ≤
          ∫ X, M * Y n X +
              (Real.exp (actualLogLikelihood γ a n X) -
                min (Real.exp (actualLogLikelihood γ a n X)) M)
            ∂(Measure.pi (fun _ : Fin n => P)) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun X =>
          mul_nonneg (hYnonneg X) (Real.exp_pos _).le
      · exact hright
      · filter_upwards with X
        by_cases hX : X ∈ A n
        · have hmin := min_le_right
              (Real.exp (actualLogLikelihood γ a n X)) M
          simp only [Y, Set.indicator_of_mem hX, one_mul]
          linarith
        · simp only [Y, Set.indicator_of_notMem hX,
            zero_mul, mul_zero, zero_add, sub_nonneg]
          exact min_le_left _ _
    have htail_bound := hN₁ n hn₁
    have hPbound :
        ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal <
          ε / (2 * (M + 1)) := by
      have hn' := hN₂ n hn₂
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hn'
      exact hn'
    have hMP : M * ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal < ε / 2 := by
      calc
        M * ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal ≤
            (M + 1) * ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal := by
              gcongr
              linarith
        _ < (M + 1) * (ε / (2 * (M + 1))) := by
              exact mul_lt_mul_of_pos_left hPbound hM1
        _ = ε / 2 := by field_simp
    have hweighted_nonneg : 0 ≤
        ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
          ∂(Measure.pi (fun _ : Fin n => P)) :=
      integral_nonneg fun X => mul_nonneg (hYnonneg X) (Real.exp_pos _).le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hweighted_nonneg]
    calc
      ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
          ∂(Measure.pi (fun _ : Fin n => P)) ≤
          ∫ X, M * Y n X +
              (Real.exp (actualLogLikelihood γ a n X) -
                min (Real.exp (actualLogLikelihood γ a n X)) M)
            ∂(Measure.pi (fun _ : Fin n => P)) := hmono
      _ = M * ((Measure.pi (fun _ : Fin n => P)) (A n)).toReal +
          ∫ X, Real.exp (actualLogLikelihood γ a n X) -
              min (Real.exp (actualLogLikelihood γ a n X)) M
            ∂(Measure.pi (fun _ : Fin n => P)) := by
            rw [integral_add hMY htail, integral_const_mul]
            congr 2
            simpa only [Y, measureReal_def] using!
              (integral_indicator_one
                (μ := Measure.pi (fun _ : Fin n => P)) (hA n))
      _ < ε := by linarith
  have herror : Tendsto (fun n =>
      (∫ X, Y n X ∂(Measure.pi (fun _ : Fin n =>
          γ.curve (a * (Real.sqrt n)⁻¹)))) -
        ∫ X, Y n X * Real.exp (actualLogLikelihood γ a n X)
          ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 0) := by
    have hρscaled : Tendsto (fun n => ‖clip‖ * ρ n) atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hρ :
          Tendsto (fun n => ‖clip‖ * ρ n) atTop (nhds (‖clip‖ * 0)))
    rw [Metric.tendsto_nhds]
    intro ε hε
    have herr := (Metric.tendsto_nhds.mp
      hρscaled) ε hε
    filter_upwards [herr] with n hn
    have hc := hcmp clip n
    simp_rw [hclipY] at hc
    rw [Real.dist_eq, sub_zero]
    exact hc.trans_lt ((le_abs_self _).trans_lt (by
      simpa only [Real.dist_eq, sub_zero] using hn))
  have hQreal : Tendsto (fun n =>
      ((Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) (A n)).toReal)
      atTop (nhds 0) := by
    have hsum := herror.add hweighted
    have hQrepr : ∀ n,
        ((Measure.pi (fun _ : Fin n =>
          γ.curve (a * (Real.sqrt n)⁻¹))) (A n)).toReal =
        ∫ X, Y n X ∂(Measure.pi (fun _ : Fin n =>
          γ.curve (a * (Real.sqrt n)⁻¹))) := by
      intro n
      simpa only [Y, measureReal_def] using!
        (integral_indicator_one
          (μ := Measure.pi (fun _ : Fin n =>
            γ.curve (a * (Real.sqrt n)⁻¹))) (hA n)).symm
    simpa only [hQrepr, sub_add_cancel, zero_add] using hsum
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hQreal
  have heq : (fun n => ENNReal.ofReal
      ((Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) (A n)).toReal) =
      fun n => (Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) (A n) := by
    funext n
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change Tendsto (fun n => ENNReal.ofReal
      ((Measure.pi (fun _ : Fin n =>
        γ.curve (a * (Real.sqrt n)⁻¹))) (A n)).toReal)
      atTop (nhds (ENNReal.ofReal 0)) at hofReal
  rw [heq] at hofReal
  simpa only [ENNReal.ofReal_zero] using hofReal


end AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird

end GLP0011B3Source36
end AronowAudit.P001.Wave1.GLP0011B3

/-!
## P001-T12: regular local-alternative score identity

The coordinate QMD path constructions include S-finite dominating measures.
The local score CLT and contiguity results give the statistical inputs for
the score identity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option autoImplicit false

namespace AronowAudit.P001.Wave1

local instance instDecidableGLP0011B3Bridge (p : Prop) : Decidable p :=
  Classical.propDecidable p

lemma GLP0011B3_density_integrable {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (f : E → ℝ) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (hnorm : (∫⁻ x, ENNReal.ofReal (f x) ∂ρ) = 1) :
    Integrable f ρ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
  rw [hnorm]
  exact ENNReal.one_lt_top

lemma GLP0011B3_sqrt_memLp {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (f : E → ℝ) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (hnorm : (∫⁻ x, ENNReal.ofReal (f x) ∂ρ) = 1) :
    MemLp (fun x => Real.sqrt (f x)) 2 ρ := by
  rw [memLp_two_iff_integrable_sq hf.sqrt.aestronglyMeasurable]
  simp_rw [Real.sq_sqrt (h0 _)]
  exact GLP0011B3_density_integrable ρ f hf h0 hnorm

lemma GLP0011B3_weighted_score_memLp {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (f s : E → ℝ) (hf : Measurable f) (hs : Measurable s)
    (h0 : ∀ x, 0 ≤ f x)
    (hs2 : MemLp s 2 (ρ.withDensity (fun x => ENNReal.ofReal (f x)))) :
    MemLp (fun x => s x * Real.sqrt (f x)) 2 ρ := by
  apply (memLp_two_iff_integrable_sq (show AEStronglyMeasurable
    (fun x => s x * Real.sqrt (f x)) ρ from (hs.mul hf.sqrt).aestronglyMeasurable)).2
  have hi := (integrable_withDensity_iff hf.ennreal_ofReal
    (ae_of_all ρ (fun _ => ENNReal.ofReal_lt_top))).1 hs2.integrable_sq
  simp only [ENNReal.toReal_ofReal (h0 _)] at hi
  convert hi using 1
  funext x
  rw [mul_pow, Real.sq_sqrt (h0 x)]

lemma GLP0011B3_pairwise_dominator {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (f q : E → ℝ) (hf : Measurable f) (hq : Measurable q)
    (hf0 : ∀ x, 0 ≤ f x) (hq0 : ∀ x, 0 ≤ q x) :
    ρ.withDensity (fun x => ENNReal.ofReal (f x + q x)) =
      ρ.withDensity (fun x => ENNReal.ofReal (f x)) +
        ρ.withDensity (fun x => ENNReal.ofReal (q x)) := by
  simp_rw [ENNReal.ofReal_add (hf0 _) (hq0 _)]
  exact withDensity_add_left hf.ennreal_ofReal _

lemma GLP0011B3_pairwise_rnDeriv {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (f q : E → ℝ) (hf : Measurable f) (hq : Measurable q)
    (hf0 : ∀ x, 0 ≤ f x) (hq0 : ∀ x, 0 ≤ q x)
    [IsFiniteMeasure (ρ.withDensity (fun x => ENNReal.ofReal (f x)))]
    [IsFiniteMeasure (ρ.withDensity (fun x => ENNReal.ofReal (q x)))] :
    let μ := ρ.withDensity (fun x => ENNReal.ofReal (f x)) +
      ρ.withDensity (fun x => ENNReal.ofReal (q x))
    (ρ.withDensity (fun x => ENNReal.ofReal (f x))).rnDeriv μ =ᵐ[μ]
      fun x => ENNReal.ofReal (f x / (f x + q x)) := by
  dsimp only
  let μ := ρ.withDensity (fun x => ENNReal.ofReal (f x)) +
    ρ.withDensity (fun x => ENNReal.ofReal (q x))
  have hm : Measurable (fun x => ENNReal.ofReal (f x / (f x + q x))) :=
    (hf.div (hf.add hq)).ennreal_ofReal
  have heq : μ.withDensity (fun x => ENNReal.ofReal (f x / (f x + q x))) =
      ρ.withDensity (fun x => ENNReal.ofReal (f x)) := by
    dsimp only [μ]
    rw [← GLP0011B3_pairwise_dominator ρ f q hf hq hf0 hq0,
      ← withDensity_mul ρ (f := fun x => ENNReal.ofReal (f x + q x))
        (hf.add hq).ennreal_ofReal hm]
    apply withDensity_congr_ae
    filter_upwards with x
    change ENNReal.ofReal (f x + q x) * ENNReal.ofReal (f x / (f x + q x)) = _
    rw [← ENNReal.ofReal_mul (add_nonneg (hf0 x) (hq0 x))]
    congr 1
    by_cases hz : f x + q x = 0
    · have hfx : f x = 0 := by linarith [hf0 x, hq0 x]
      simp [hfx]
    · field_simp
  change (ρ.withDensity (fun x => ENNReal.ofReal (f x))).rnDeriv μ =ᵐ[μ] _
  rw [← heq]
  exact Measure.rnDeriv_withDensity μ hm

open GLP0011B3.AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

lemma GLP0011B3_residual_ratio (f q s t : ℝ) (hf : 0 ≤ f) (hq : 0 ≤ q) :
    Real.sqrt (f + q) *
      (Real.sqrt (q / (f + q)) - Real.sqrt (f / (f + q)) -
        (t / 2) * s * Real.sqrt (f / (f + q))) =
      Real.sqrt q - Real.sqrt f - (t / 2) * s * Real.sqrt f := by
  by_cases hz : f + q = 0
  · have hfz : f = 0 := by linarith
    have hqz : q = 0 := by linarith
    simp [hfz, hqz]
  · have hsz : Real.sqrt (f + q) ≠ 0 :=
      (Real.sqrt_pos.2 (lt_of_le_of_ne (add_nonneg hf hq) (Ne.symm hz))).ne'
    rw [Real.sqrt_div hq, Real.sqrt_div hf]
    field_simp
    <;> ring

lemma GLP0011B3_pairwise_residual_norm {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (f q s : E → ℝ) (hf : Measurable f) (hq : Measurable q)
    (hf0 : ∀ x, 0 ≤ f x) (hq0 : ∀ x, 0 ≤ q x)
    [IsFiniteMeasure (ρ.withDensity (fun x => ENNReal.ofReal (f x)))]
    [IsFiniteMeasure (ρ.withDensity (fun x => ENNReal.ofReal (q x)))] (t : ℝ) :
    let P := ρ.withDensity (fun x => ENNReal.ofReal (f x))
    let Q := ρ.withDensity (fun x => ENNReal.ofReal (q x))
    eLpNorm' (residualAgainst P Q (P + Q) s t) 2 (P + Q) =
      eLpNorm' (fun x => Real.sqrt (q x) - Real.sqrt (f x) -
        (t / 2) * s x * Real.sqrt (f x)) 2 ρ := by
  let P := ρ.withDensity (fun x => ENNReal.ofReal (f x))
  let Q := ρ.withDensity (fun x => ENNReal.ofReal (q x))
  let μ := P + Q
  have hp : P.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (f x / (f x + q x)) :=
    GLP0011B3_pairwise_rnDeriv ρ f q hf hq hf0 hq0
  have hq' : Q.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (q x / (f x + q x)) := by
    simpa only [add_comm] using GLP0011B3_pairwise_rnDeriv ρ q f hq hf hq0 hf0
  have hae : residualAgainst P Q μ s t =ᵐ[μ]
      fun x => Real.sqrt (q x / (f x + q x)) - Real.sqrt (f x / (f x + q x)) -
        (t / 2) * s x * Real.sqrt (f x / (f x + q x)) := by
    filter_upwards [hp, hq'] with x hpx hqx
    simp only [residualAgainst, hpx, hqx,
      ENNReal.toReal_ofReal (div_nonneg (hf0 x) (add_nonneg (hf0 x) (hq0 x))),
      ENNReal.toReal_ofReal (div_nonneg (hq0 x) (add_nonneg (hf0 x) (hq0 x)))]
  change eLpNorm' (residualAgainst P Q μ s t) 2 μ = _
  rw [eLpNorm'_congr_ae hae]
  rw [show μ = ρ.withDensity (fun x => ENNReal.ofReal (f x + q x)) from
    (GLP0011B3_pairwise_dominator ρ f q hf hq hf0 hq0).symm]
  simp only [eLpNorm'_eq_lintegral_enorm]
  congr 1
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable ρ
    (f := fun x => ENNReal.ofReal (f x + q x))
    (hf.add hq).ennreal_ofReal (ae_of_all ρ (fun _ => ENNReal.ofReal_lt_top))]
  apply lintegral_congr_ae
  filter_upwards with x
  simp only [Pi.mul_apply, ENNReal.rpow_two, ← enorm_pow,
    Real.enorm_of_nonneg (sq_nonneg _)]
  rw [← ENNReal.ofReal_mul (add_nonneg (hf0 x) (hq0 x))]
  congr 1
  have h := GLP0011B3_residual_ratio (f x) (q x) (s x) t (hf0 x) (hq0 x)
  calc
    _ = (Real.sqrt (f x + q x) *
        (Real.sqrt (q x / (f x + q x)) - Real.sqrt (f x / (f x + q x)) -
          (t / 2) * s x * Real.sqrt (f x / (f x + q x)))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (add_nonneg (hf0 x) (hq0 x))]
    _ = _ := by rw [h]

lemma GLP0011B3_qmd_of_integral {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (f : ℝ → E → ℝ) (s : E → ℝ)
    (hf : ∀ t, Measurable (f t)) (hf0 : ∀ t x, 0 ≤ f t x)
    (hprob : ∀ t, IsProbabilityMeasure (ρ.withDensity (fun x => ENNReal.ofReal (f t x))))
    (hres : ∀ t, MemLp (fun x => Real.sqrt (f t x) - Real.sqrt (f 0 x) -
      (t / 2) * s x * Real.sqrt (f 0 x)) 2 ρ)
    (hqm : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      |t| < δ → (∫ x, (Real.sqrt (f t x) - Real.sqrt (f 0 x) -
        (t / 2) * s x * Real.sqrt (f 0 x)) ^ 2 ∂ρ) ≤ ε * t ^ 2) :
    IsRightQMD (ρ.withDensity (fun x => ENNReal.ofReal (f 0 x)))
      (fun t => ρ.withDensity (fun x => ENNReal.ofReal (f t x))) s := by
  let R : ℝ → E → ℝ := fun t x => Real.sqrt (f t x) - Real.sqrt (f 0 x) -
    (t / 2) * s x * Real.sqrt (f 0 x)
  have hnorm : Tendsto (fun t => (eLpNorm (R t) 2 ρ).toReal / |t|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hqm ((ε / 2) ^ 2) (sq_pos_of_pos (by positivity))
    have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), |t| < δ := by
      exact ((continuous_abs.tendsto 0).mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (by simpa using hδ))
    filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0
    have htp : 0 < t := ht0
    have hnormbound : (eLpNorm (R t) 2 ρ).toReal ≤ (ε / 2) * |t| := by
      rw [← sqrt_integral_sq_eq_lpNorm (hres t)]
      apply Real.sqrt_le_iff.2
      refine ⟨by positivity, ?_⟩
      simpa only [R, mul_pow, sq_abs, mul_assoc] using hbound t ht
    have hdiv : (eLpNorm (R t) 2 ρ).toReal / |t| ≤ ε / 2 :=
      (div_le_iff₀ (abs_pos.2 htp.ne')).2 hnormbound
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (div_nonneg ENNReal.toReal_nonneg (abs_nonneg t))]
    linarith
  have hext := ENNReal.tendsto_ofReal hnorm
  simp only [ENNReal.ofReal_zero] at hext
  apply hext.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  letI : IsProbabilityMeasure (ρ.withDensity (fun x => ENNReal.ofReal (f 0 x))) := hprob 0
  letI : IsProbabilityMeasure (ρ.withDensity (fun x => ENNReal.ofReal (f t x))) := hprob t
  change ENNReal.ofReal ((eLpNorm (R t) 2 ρ).toReal / |t|) =
    eLpNorm' (residualAgainst _ _ _ s t) 2 _ / ENNReal.ofReal t
  rw [canonicalDominator, GLP0011B3_pairwise_residual_norm ρ (f 0) (f t) s
    (hf 0) (hf t) (hf0 0) (hf0 t) t,
    ← GLP0011B3.MeasureTheory.eLpNorm_two_eq_eLpNorm' (hres t).aestronglyMeasurable,
    abs_of_pos ht, ENNReal.ofReal_div_of_pos ht,
    ENNReal.ofReal_toReal (hres t).ne]

open GLP0011B3.AsymptoticStatistics.Core
open GLP0011B3.AsymptoticStatistics.Core.Hilbert
open GLP0011B3.AsymptoticStatistics.Core.NondominatedQMDPath

def GLP0011B3_coordinate {τ : ℕ} (θ : Fin τ → ℝ) (k : Fin τ) (t : ℝ) :
    Fin τ → ℝ := θ + t • (Pi.single k (1 : ℝ) : Fin τ → ℝ)

lemma GLP0011B3_coordinate_dist {τ : ℕ} (θ : Fin τ → ℝ) (k : Fin τ) (t : ℝ) :
    dist (GLP0011B3_coordinate θ k t) θ = |t| := by
  simp [GLP0011B3_coordinate, dist_eq_norm, norm_smul, Pi.norm_single, Real.norm_eq_abs]

lemma GLP0011B3_coordinate_sum {τ : ℕ} (θ : Fin τ → ℝ) (k : Fin τ) (t : ℝ)
    (s : Fin τ → ℝ) :
    (∑ j, (GLP0011B3_coordinate θ k t j - θ j) * s j) = t * s k := by
  simp [GLP0011B3_coordinate, Pi.single_apply, eq_comm]

lemma GLP0011B3_coordinate_path {K τ : ℕ}
    (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
    (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
    (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hg : ∀ t ∈ Metric.ball θ δ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
    (hpos : ∀ t ∈ Metric.ball θ δ, ∀ y x, 0 ≤ g y x t)
    (hnorm : ∀ t ∈ Metric.ball θ δ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ) = 1)
    (hqm : QuadraticMeanModel νX κ g θ)
    (hs2 : ∀ j, MemLp (fun xy : (Fin K → ℝ) × ℝ => modelScore g xy.2 xy.1 θ j)
      2 (conditionalModelLaw νX κ g θ))
    (hs0 : ∀ j, mean (conditionalModelLaw νX κ g θ)
      (fun xy => modelScore g xy.2 xy.1 θ j) = 0)
    (k : Fin τ) :
    letI := conditional_model_probability νX κ g θ (hg θ (by simp [hδ]))
      (hnorm θ (by simp [hδ]))
    ∃ γ : NondominatedQMDPath (conditionalModelLaw νX κ g θ),
      (γ.score : ((Fin K → ℝ) × ℝ) → ℝ) =ᵐ[conditionalModelLaw νX κ g θ]
        (fun xy => modelScore g xy.2 xy.1 θ k) ∧
      ∀ᶠ n : ℕ in atTop, γ.curve ((Real.sqrt n)⁻¹) =
        conditionalModelLaw νX κ g (θ + (Real.sqrt n)⁻¹ • (Pi.single k (1 : ℝ) : Fin τ → ℝ)) := by
  letI instGLP0011B3PathBase : IsProbabilityMeasure (conditionalModelLaw νX κ g θ) :=
    conditional_model_probability νX κ g θ (hg θ (by simp [hδ])) (hnorm θ (by simp [hδ]))
  let ρ := νX.prod κ
  let v : ℝ → Fin τ → ℝ := fun t =>
    if |t| < δ then GLP0011B3_coordinate θ k t else θ
  have hv0 : v 0 = θ := by simp [v, GLP0011B3_coordinate, hδ]
  have hvball (t : ℝ) : v t ∈ Metric.ball θ δ := by
    by_cases ht : |t| < δ
    · simpa [v, ht, Metric.mem_ball, GLP0011B3_coordinate_dist] using ht
    · simp [v, ht, hδ]
  let f : ℝ → ((Fin K → ℝ) × ℝ) → ℝ := fun t xy => g xy.2 xy.1 (v t)
  have hf (t : ℝ) : Measurable (f t) := hg (v t) (hvball t)
  have hf0 (t : ℝ) (xy : (Fin K → ℝ) × ℝ) : 0 ≤ f t xy :=
    hpos (v t) (hvball t) xy.2 xy.1
  have hprob (t : ℝ) : IsProbabilityMeasure (ρ.withDensity (fun xy => ENNReal.ofReal (f t xy))) :=
    conditional_model_probability νX κ g (v t) (hf t) (hnorm (v t) (hvball t))
  have hnormjoint (t : ℝ) : (∫⁻ xy, ENNReal.ofReal (f t xy) ∂ρ) = 1 := by
    rw [lintegral_prod _ (hf t).ennreal_ofReal.aemeasurable]
    simp only [f, hnorm (v t) (hvball t), lintegral_const, measure_univ, mul_one]
  let c : CandidateIF (conditionalModelLaw νX κ g θ) :=
    ⟨fun xy => modelScore g xy.2 xy.1 θ k, hs2 k, hs0 k⟩
  let sc : ↥(L2ZeroMean (conditionalModelLaw νX κ g θ)) := c.toL2ZeroMean
  have hsc : Measurable (sc : ((Fin K → ℝ) × ℝ) → ℝ) :=
    (Lp.stronglyMeasurable (sc : Lp ℝ 2 (conditionalModelLaw νX κ g θ))).measurable
  have hscae : (sc : ((Fin K → ℝ) × ℝ) → ℝ) =ᵐ[conditionalModelLaw νX κ g θ]
      fun xy => modelScore g xy.2 xy.1 θ k := c.coeFn_toL2ZeroMean
  have hweighted : (fun xy => (sc : ((Fin K → ℝ) × ℝ) → ℝ) xy * Real.sqrt (g xy.2 xy.1 θ)) =ᵐ[ρ]
      fun xy => modelScore g xy.2 xy.1 θ k * Real.sqrt (g xy.2 xy.1 θ) := by
    have hon := (ae_withDensity_iff (hg θ (by simp [hδ])).ennreal_ofReal).1 hscae
    filter_upwards [hon] with xy hxy
    by_cases hz : g xy.2 xy.1 θ = 0
    · simp [hz]
    · rw [hxy ((ENNReal.ofReal_pos.2 (lt_of_le_of_ne
        (hpos θ (by simp [hδ]) xy.2 xy.1) (Ne.symm hz))).ne')]
  have hsc2 : MemLp (sc : ((Fin K → ℝ) × ℝ) → ℝ) 2
      (ρ.withDensity (fun xy => ENNReal.ofReal (f 0 xy))) := by
    simpa only [f, hv0, ρ, conditionalModelLaw] using
      Lp.memLp (sc : Lp ℝ 2 (conditionalModelLaw νX κ g θ))
  have hres (t : ℝ) : MemLp (fun xy => Real.sqrt (f t xy) - Real.sqrt (f 0 xy) -
      (t / 2) * (sc : ((Fin K → ℝ) × ℝ) → ℝ) xy * Real.sqrt (f 0 xy)) 2 ρ := by
    have hsqrt0 := GLP0011B3_sqrt_memLp ρ (f 0) (hf 0) (hf0 0) (hnormjoint 0)
    have hsqrtt := GLP0011B3_sqrt_memLp ρ (f t) (hf t) (hf0 t) (hnormjoint t)
    have hscore := GLP0011B3_weighted_score_memLp ρ (f 0) sc (hf 0) hsc (hf0 0) hsc2
    convert (hsqrtt.sub hsqrt0).sub (hscore.const_mul (t / 2)) using 1
    funext xy
    simp only [Pi.sub_apply]
    ring
  have hint : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ,
      |t| < r → (∫ xy, (Real.sqrt (f t xy) - Real.sqrt (f 0 xy) -
        (t / 2) * (sc : ((Fin K → ℝ) × ℝ) → ℝ) xy * Real.sqrt (f 0 xy)) ^ 2 ∂ρ) ≤ ε * t ^ 2 := by
    intro ε hε
    obtain ⟨r, hr, hb⟩ := hqm ε hε
    refine ⟨min δ r, lt_min hδ hr, ?_⟩
    intro t ht
    have htδ : |t| < δ := lt_of_lt_of_le ht (min_le_left _ _)
    have htr : |t| < r := lt_of_lt_of_le ht (min_le_right _ _)
    have htθ : dist (GLP0011B3_coordinate θ k t) θ < r := by
      simpa only [GLP0011B3_coordinate_dist] using htr
    have hft : f t = fun xy => g xy.2 xy.1 (GLP0011B3_coordinate θ k t) := by
      simp only [f, v, if_pos htδ]
    have hfzero : f 0 = fun xy => g xy.2 xy.1 θ := by simp only [f, hv0]
    rw [hft, hfzero]
    calc
      _ = ∫ xy, (Real.sqrt (g xy.2 xy.1 (GLP0011B3_coordinate θ k t)) -
          Real.sqrt (g xy.2 xy.1 θ) -
          (∑ j, (GLP0011B3_coordinate θ k t j - θ j) *
            modelScore g xy.2 xy.1 θ j) * Real.sqrt (g xy.2 xy.1 θ) / 2) ^ 2 ∂ρ := by
        apply integral_congr_ae
        filter_upwards [hweighted] with xy hxy
        rw [GLP0011B3_coordinate_sum]
        have he : (t / 2) * (sc : ((Fin K → ℝ) × ℝ) → ℝ) xy * Real.sqrt (g xy.2 xy.1 θ) =
            t * modelScore g xy.2 xy.1 θ k * Real.sqrt (g xy.2 xy.1 θ) / 2 := by
          calc
            _ = (t / 2) * ((sc : ((Fin K → ℝ) × ℝ) → ℝ) xy * Real.sqrt (g xy.2 xy.1 θ)) := by ring
            _ = _ := by rw [hxy]; ring
        rw [he]
      _ ≤ _ := by
        simpa only [GLP0011B3_coordinate_dist, sq_abs] using hb _ htθ
  let γ : NondominatedQMDPath (conditionalModelLaw νX κ g θ) := {
    curve := fun t => ρ.withDensity (fun xy => ENNReal.ofReal (f t xy))
    curve_at_zero := by simp only [f, hv0, ρ, conditionalModelLaw]
    curve_isProbability := fun t _ => hprob t
    score := sc
    qmd_limit := by
      simpa only [f, hv0, ρ, conditionalModelLaw] using
        GLP0011B3_qmd_of_integral ρ f sc hf hf0 hprob hres hint }
  refine ⟨γ, hscae, ?_⟩
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall := hinv.abs.eventually (Iio_mem_nhds (by simpa using hδ))
  filter_upwards [hsmall] with n hn
  simp only [γ, f, v, if_pos hn, GLP0011B3_coordinate, ρ, conditionalModelLaw]

open scoped InnerProductSpace RealInnerProductSpace
open GLP0011B3.AsymptoticStatistics
open GLP0011B3.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird

lemma GLP0011B3_regularity_forces_coordinate {E : Type*} [MeasurableSpace E] {τ : ℕ}
    (ν : (Fin τ → ℝ) → Measure E) (θ : Fin τ → ℝ) [IsProbabilityMeasure (ν θ)]
    (T : (n : ℕ) → (Fin n → E) → Fin τ → ℝ) (ψ : E → Fin τ → ℝ)
    (hregular : RegularAL ν θ T ψ) (j k : Fin τ) (s : E → ℝ)
    (γ : NondominatedQMDPath (ν θ)) (hscore : (γ.score : E → ℝ) =ᵐ[ν θ] s)
    (hpath : ∀ᶠ n : ℕ in atTop, γ.curve ((Real.sqrt n)⁻¹) =
      ν (θ + (Real.sqrt n)⁻¹ • (Pi.single k (1 : ℝ) : Fin τ → ℝ))) :
    mean (ν θ) (fun x => ψ x j * s x) = if j = k then 1 else 0 := by
  rcases hregular with ⟨hT, hψ, hψ2, hψ0, hAL, hlocal⟩
  let c : CandidateIF (ν θ) := ⟨fun x => ψ x j, hψ2 j, hψ0 j⟩
  let u : ↥(L2ZeroMean (ν θ)) := c.toL2ZeroMean
  have huae : (u : E → ℝ) =ᵐ[ν θ] fun x => ψ x j := c.coeFn_toL2ZeroMean
  let P : (n : ℕ) → Measure (Fin n → E) := fun n => iidObservationLaw (ν θ) n
  let Q : (n : ℕ) → Measure (Fin n → E) := fun n =>
    iidObservationLaw (γ.curve ((Real.sqrt n)⁻¹)) n
  let A : (n : ℕ) → (Fin n → E) → ℝ := normalizedScoreSum u
  let W : (n : ℕ) → (Fin n → E) → ℝ := fun n z => Real.sqrt n * (T n z j - θ j)
  have hA (n : ℕ) : Measurable (A n) := by
    unfold A normalizedScoreSum
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
      (Lp.stronglyMeasurable (u : Lp ℝ 2 (ν θ))).measurable.comp (measurable_pi_apply i)))
  have hW (n : ℕ) : Measurable (W n) :=
    measurable_const.mul (((measurable_pi_apply j).comp (hT n)).sub measurable_const)
  letI instGLP0011B3P (n : ℕ) : IsProbabilityMeasure (P n) := by
    dsimp [P, iidObservationLaw]
    infer_instance
  letI instGLP0011B3Q (n : ℕ) : IsProbabilityMeasure (Q n) := by
    haveI instGLP0011B3Curve : IsProbabilityMeasure (γ.curve ((Real.sqrt n)⁻¹)) :=
      γ.curve_isProbability _ (inv_nonneg.2 (Real.sqrt_nonneg _))
    dsimp [Q, iidObservationLaw]
    infer_instance
  have hclt : WeakConverges (fun n => (Q n).map (A n))
      (gaussianReal ⟪u, γ.score⟫_ℝ (NNReal.mk (‖u‖ ^ 2) (sq_nonneg _))) := by
    simpa only [one_mul, Q, A, iidObservationLaw] using qmd_local_score_clt γ 1 (by norm_num) u
  have hcont := qmd_local_contiguous γ 1 (by norm_num)
  simp only [one_mul] at hcont
  have hraw (n : ℕ) : A n =ᵐ[P n]
      fun z => (Real.sqrt n)⁻¹ * ∑ i, ψ (z i) j := by
    have hpi := Measure.ae_eq_pi (μ := fun _ : Fin n => ν θ) (fun _ => huae)
    filter_upwards [hpi] with z hz
    change (Real.sqrt n)⁻¹ * ∑ i, (u : E → ℝ) (z i) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun hz i
  have hbase (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => (P n).real {z | ε ≤ dist (A n z) (W n z)}) atTop (nhds 0) := by
    have hle (n : ℕ) : (P n).real {z | ε ≤ dist (A n z) (W n z)} ≤
        prob (iidObservationLaw (ν θ) n)
          {z | ε ≤ dist (Real.sqrt n • (T n z - θ))
            ((Real.sqrt n)⁻¹ • (fun l => ∑ i, ψ (z i) l))} := by
      change ((P n) {z | ε ≤ dist (A n z) (W n z)}).toReal ≤
        ((P n) {z | ε ≤ dist (Real.sqrt n • (T n z - θ))
          ((Real.sqrt n)⁻¹ • (fun l => ∑ i, ψ (z i) l))}).toReal
      apply ENNReal.toReal_mono (by finiteness)
      apply measure_mono_ae
      filter_upwards [hraw n] with z hz
      intro hzε
      have hd := dist_le_pi_dist (Real.sqrt n • (T n z - θ))
        ((Real.sqrt n)⁻¹ • (fun l => ∑ i, ψ (z i) l)) j
      have hscal : dist (A n z) (W n z) ≤
          dist (Real.sqrt n • (T n z - θ))
            ((Real.sqrt n)⁻¹ • (fun l => ∑ i, ψ (z i) l)) := by
        rw [hz, dist_comm]
        simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using hd
      exact le_trans hzε hscal
    exact squeeze_zero (fun n => measureReal_nonneg) hle (hAL ε hε)
  have hDist (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => (Q n).real {z | ε ≤ dist (A n z) (W n z)}) atTop (nhds 0) := by
    have hb : Tendsto (fun n => (P n) {z | ε ≤ dist (A n z) (W n z)})
        atTop (nhds 0) := (ENNReal.tendsto_toReal_zero_iff (fun n => by finiteness)).1 (hbase ε hε)
    have hq := hcont (fun n => {z | ε ≤ dist (A n z) (W n z)})
      (fun n => measurableSet_le measurable_const ((hA n).dist (hW n))) hb
    exact (ENNReal.tendsto_toReal_zero_iff (fun n => by finiteness)).2 hq
  have hWclt : WeakConverges (fun n => (Q n).map (W n))
      (gaussianReal ⟪u, γ.score⟫_ℝ (NNReal.mk (‖u‖ ^ 2) (sq_nonneg _))) :=
    WeakConverges.slutsky_of_tendstoInMeasure_dist
      (fun n => (hA n).aemeasurable) (fun n => (hW n).aemeasurable) hclt hDist
  let h : Fin τ → ℝ := Pi.single k 1
  let G : Measure (Fin τ → ℝ) := normalVectorLaw (covarianceMatrix (ν θ) ψ)
  let limitLaw : Measure ℝ := G.map (fun x => x j + h j)
  have hmap : Measurable (fun x : Fin τ → ℝ => x j + h j) :=
    (measurable_pi_apply j).add measurable_const
  letI instGLP0011B3G : IsProbabilityMeasure G := by
    dsimp [G, normalVectorLaw]
    infer_instance
  letI instGLP0011B3Limit : IsProbabilityMeasure limitLaw := by
    dsimp [limitLaw]
    infer_instance
  have hWreg : WeakConverges (fun n => (Q n).map (W n)) limitLaw := by
    intro b
    have hbc : Continuous (fun x : Fin τ → ℝ => b (x j + h j)) :=
      b.continuous.comp ((continuous_apply j).add continuous_const)
    have hbb : ∃ C : ℝ, ∀ x : Fin τ → ℝ, |b (x j + h j)| ≤ C :=
      ⟨‖b‖, fun x => by simpa only [Real.norm_eq_abs] using b.norm_coe_le_norm (x j + h j)⟩
    have hl := hlocal h (fun x => b (x j + h j)) hbc hbb
    rw [show (∫ x, b x ∂limitLaw) = ∫ x, b (x j + h j) ∂G from
      integral_map hmap.aemeasurable b.continuous.aestronglyMeasurable]
    apply hl.congr'
    filter_upwards [hpath, eventually_ge_atTop 1] with n hn hn1
    rw [integral_map (hW n).aemeasurable b.continuous.aestronglyMeasurable]
    change mean (iidObservationLaw (ν (θ + (Real.sqrt n)⁻¹ • h)) n)
      (fun z => b ((Real.sqrt n • (T n z - (θ + (Real.sqrt n)⁻¹ • h))) j + h j)) =
      ∫ z, b (W n z) ∂iidObservationLaw (γ.curve ((Real.sqrt n)⁻¹)) n
    rw [hn]
    apply integral_congr_ae
    filter_upwards with z
    congr 1
    have hsne : Real.sqrt (n : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (Nat.cast_pos.2 (by omega : 0 < n))).ne'
    dsimp only [W, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    <;> ring
  have heq := hWclt.unique hWreg
  have hGi : Integrable (fun x : Fin τ → ℝ => x j) G := by
    dsimp only [G, normalVectorLaw]
    apply (integrable_map_measure (continuous_apply j).aestronglyMeasurable (by fun_prop)).2
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp IsGaussian.integrable_fun_id
  have hG0 : (∫ x : Fin τ → ℝ, x j ∂G) = 0 := by
    dsimp only [G, normalVectorLaw]
    rw [integral_map (by fun_prop) (continuous_apply j).aestronglyMeasurable]
    change (∫ x, (EuclideanSpace.proj (𝕜 := ℝ) j) x
      ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin τ)) (covarianceMatrix (ν θ) ψ)) = 0
    rw [(EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm IsGaussian.integrable_fun_id]
    simp
  have hmeans : ⟪u, γ.score⟫_ℝ = h j := by
    have hm := congrArg (fun ρ : Measure ℝ => ∫ x, x ∂ρ) heq
    rw [integral_id_gaussianReal] at hm
    rw [integral_map hmap.aemeasurable (by fun_prop),
      integral_add hGi (integrable_const (h j)), hG0, integral_const] at hm
    simpa only [zero_add, probReal_univ, smul_eq_mul, one_mul] using hm
  have hinner : ⟪u, γ.score⟫_ℝ = mean (ν θ) (fun x => ψ x j * s x) := by
    change ⟪(u : Lp ℝ 2 (ν θ)), (γ.score : Lp ℝ 2 (ν θ))⟫_ℝ = _
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [huae, hscore] with x hx hxs
    change (γ.score : E → ℝ) x * (u : E → ℝ) x = ψ x j * s x
    rw [hx, hxs, mul_comm]
  rw [← hinner, hmeans]
  simp [h, Pi.single_apply, eq_comm]

theorem regular_local_alternative_score_identity_proof {K τ : ℕ}
  (νX : Measure (Fin K → ℝ)) [IsProbabilityMeasure νX] (κ : Measure ℝ) [SFinite κ]
  (g : ℝ → (Fin K → ℝ) → (Fin τ → ℝ) → ℝ)
  (θ : Fin τ → ℝ) (δ : ℝ) (hδ : 0 < δ)
  (hg : ∀ t ∈ Metric.ball θ δ, Measurable (fun xy : (Fin K → ℝ) × ℝ => g xy.2 xy.1 t))
  (hpos : ∀ t ∈ Metric.ball θ δ, ∀ y x, 0 ≤ g y x t)
  (hnorm : ∀ t ∈ Metric.ball θ δ, ∀ x, (∫⁻ y, ENNReal.ofReal (g y x t) ∂κ)=1)
  (hqm : QuadraticMeanModel νX κ g θ)
  (hs2 : ∀ j, MemLp (fun xy : (Fin K → ℝ) × ℝ => modelScore g xy.2 xy.1 θ j)
    2 (conditionalModelLaw νX κ g θ))
  (hs0 : ∀ j, mean (conditionalModelLaw νX κ g θ)
    (fun xy => modelScore g xy.2 xy.1 θ j)=0)
  (I : Matrix (Fin τ) (Fin τ) ℝ)
  (hI : ∀ j k, I j k=mean (conditionalModelLaw νX κ g θ)
    (fun xy => modelScore g xy.2 xy.1 θ j*modelScore g xy.2 xy.1 θ k))
  (hpd : I.PosDef)
  (T : (n : ℕ) → (Fin n → (Fin K → ℝ) × ℝ) → Fin τ → ℝ)
  (ψ : (Fin K → ℝ) × ℝ → Fin τ → ℝ)
  (hregular : RegularAL (conditionalModelLaw νX κ g) θ T ψ) :
  (∀ j k, mean (conditionalModelLaw νX κ g θ)
    (fun xy => ψ xy j*modelScore g xy.2 xy.1 θ k)=if j=k then 1 else 0) ∧
  ∀ a : Fin τ → ℝ, 0 ≤ ∑ j, ∑ k,
    a j*(covarianceMatrix (conditionalModelLaw νX κ g θ) ψ j k-I⁻¹ j k)*a k := by
  have hθball : θ ∈ Metric.ball θ δ := by simp [hδ]
  letI instGLP0011B3Base : IsProbabilityMeasure (conditionalModelLaw νX κ g θ) :=
    conditional_model_probability νX κ g θ (hg θ hθball) (hnorm θ hθball)
  have hid (j k : Fin τ) : mean (conditionalModelLaw νX κ g θ)
      (fun xy => ψ xy j * modelScore g xy.2 xy.1 θ k) = if j = k then 1 else 0 := by
    obtain ⟨γ, hscore, hpath⟩ :=
      GLP0011B3_coordinate_path νX κ g θ δ hδ hg hpos hnorm hqm hs2 hs0 k
    exact GLP0011B3_regularity_forces_coordinate (conditionalModelLaw νX κ g)
      θ T ψ hregular j k (fun xy => modelScore g xy.2 xy.1 θ k) γ hscore hpath
  refine ⟨hid, ?_⟩
  exact regular_influence_information_lower_bound_proof
    (conditionalModelLaw νX κ g θ) (fun xy => modelScore g xy.2 xy.1 θ) ψ
    hs2 hregular.2.2.1 hs0 hregular.2.2.2.1 I hI hpd hid

end AronowAudit.P001.Wave1


