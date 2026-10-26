/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space



/-!
# Parametric family of densities

A *parametric statistical model* is a family of probability densities
$\{p_\theta : \theta \in \Theta\}$ on a sample space $\mathcal X$, each taken with
respect to a common dominating $\sigma$-finite measure $\mu$.

`ParametricFamily` records nonnegative functions $p_\theta : \mathcal X \to \mathbb R$
that are measurable in the sample variable $x$ for each fixed $\theta$.
The parameter type has no measurable-space requirement: measurability in
$\theta$ and joint measurability in $(\theta,x)$ are not assumed.
The separate `IsPDFOf` condition makes the family a probability-density
family relative to $\mu$: every $p_\theta$ is $\mu$-integrable and normalised,
$\int_{\mathcal X} p_\theta \, d\mu = 1$.

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

**Bibliographic comments.** The square-root / Hilbert-space representation of a
parametric model — and the resulting Hellinger and $L^2$ geometry — is classical
statistical folklore with no single seminal origin. Its modern asymptotic use
traces through L. Le Cam's work on differentiability in quadratic mean and contiguity
(L. Le Cam, *Asymptotic Methods in Statistical Decision Theory*, Springer, 1986) and
the earlier C. R. Rao / J. Hájek tradition on regular parametric families; the
synthesis followed here is van der Vaart (1998), Chapter 7. No original
research paper is attributed for these definitional objects.
-/

open MeasureTheory

namespace AsymptoticStatistics

/-- A parametric family of (μ-)densities indexed by a parameter `θ : Θ`.

For every fixed parameter, the density is measurable in the sample variable
and pointwise nonnegative. No measurable structure on `Θ`, parameter
measurability, or joint measurability is required. Normalization and
integrability belong to the separate `IsPDFOf` condition. -/
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

We deliberately do **not** bundle ae-strict-positivity of `p_θ` here: vdV's
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
