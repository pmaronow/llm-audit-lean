/-
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.ParametricFamily.Defs
import AronowAudit.External.StatLean.AsymptoticStatistics.DQM.Defs
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.L2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Zero mean of the score function

Let $(P_\theta : \theta \in \Theta)$ be a statistical model with densities
$p_\theta$ with respect to a dominating measure $\mu$. Suppose the model is
*differentiable in quadratic mean* at $\theta_0$ with score function
$\ell_{\theta_0} : \mathcal X \to \Theta$; that is, the map
$\theta \mapsto \sqrt{p_\theta}$ admits an $L^2(\mu)$ derivative
$\tfrac12\,\langle \cdot, \ell_{\theta_0}\rangle\,\sqrt{p_{\theta_0}}$ at
$\theta_0$. Then the score has **zero mean** under $P_{\theta_0}$: for every
direction $u \in \Theta$,
$$\int \langle u, \ell_{\theta_0}(x)\rangle\, p_{\theta_0}(x)\, d\mu(x) = 0,$$
equivalently $P_{\theta_0}\,\ell_{\theta_0} = 0$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 7 (Local Asymptotic Normality), §7.2 (Expanding the Likelihood),
Theorem 7.2, differentiability-in-quadratic-mean condition Eq (7.1). Van der
Vaart's Theorem 7.2 states that DQM at $\theta$ implies both
$P_\theta\,\ell_\theta = 0$ and existence of the Fisher information
$I_\theta = P_\theta\,\ell_\theta\ell_\theta^\top$.

**Proof outline.** The argument follows van der Vaart's proof of
Theorem 7.2. It uses the inner-product identity in $L^2(\mu)$
$$\big\langle \sqrt{n}\,(\sqrt{p_n} - \sqrt{p}),\ \sqrt{p_n} + \sqrt{p}\big\rangle_{L^2(\mu)}
  = \sqrt{n}\int (p_n - p)\, d\mu = 0,$$
which vanishes because both densities integrate to $1$.
Taking the limit along a perturbation $\theta_0 + t\cdot u$ as $t \to 0$ and using
the DQM-induced $L^2$ convergence together with continuity of the $L^2$ inner
product gives
$\langle \tfrac12\,\langle u, \ell\rangle\,\sqrt{p},\ 2\sqrt{p}\rangle
  = \int \langle u, \ell\rangle\, p\, d\mu$,
so the limit equals $0$ and the score has zero mean.

**Bibliographic comments.** The zero-mean identity for the score is classical
folklore in mathematical statistics, tracing to R. A. Fisher's foundational work
on maximum likelihood estimation and information (R. A. Fisher, "On the
mathematical foundations of theoretical statistics," *Philosophical Transactions
of the Royal Society A* **222** (1922), 309–368; "Theory of statistical
estimation," *Proceedings of the Cambridge Philosophical Society* **22** (1925),
700–725). It has no single seminal source as an isolated proposition. The
specific derivation — obtaining $P_\theta\,\ell_\theta = 0$ from
differentiability in quadratic mean *without* assuming pointwise differentiability
— is due to the Le Cam–Hájek school of asymptotic decision theory (L. Le Cam,
*Asymptotic Methods in Statistical Decision Theory*, Springer, 1986; J. Hájek,
"Local asymptotic minimax and admissibility in estimation," *Proc. Sixth Berkeley
Symp. on Math. Statist. and Prob.*, vol. 1, 1972, 175–194) and is presented in
textbook form as van der Vaart's Theorem 7.2.
-/

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

/-! ## Analytical consequences of DQM

The score-mean argument uses analytical consequences of DQM.
-/


/-! ## Lemma 1 — Difference-of-squares identity (the key cancellation)

For any `θ, θ' ∈ Θ`, if both densities integrate to 1, then
`∫ (√p_{θ'} − √p_θ)(√p_{θ'} + √p_θ) dμ = 0`.

This is `(a-b)(a+b) = a²-b² = p_{θ'} - p_θ`, integrated. -/

/-! ## Lemma 2 — Inner-product continuity for L²(μ)

For sequences `f_t, g_t : 𝓧 → ℝ` with
* `∫ (f_t − f)² dμ → 0`
* `∫ (g_t − g)² dμ → 0`

and with `f, g, f_t, g_t ∈ L²(μ)`, the integral `∫ f_t·g_t dμ → ∫ f·g dμ`.

Proof structure:
1. Algebraic identity  `f_t·g_t − f·g = (f_t − f)·g_t + f·(g_t − g)`.
2. Cauchy–Schwarz on each summand:
   `|∫ (f_t − f)·g_t dμ| ≤ √(∫ (f_t−f)² dμ) · √(∫ g_t² dμ)`,
   `|∫ f·(g_t − g) dμ| ≤ √(∫ f² dμ) · √(∫ (g_t−g)² dμ)`.
3. `√(∫ g_t² dμ) ≤ √(∫ (g_t − g)² dμ) + √(∫ g² dμ)` — L² triangle inequality,
   showing the first factor stays bounded.
4. First factor of first term → 0, second factor bounded ⇒ term → 0.
   First factor of second term bounded (constant), second factor → 0 ⇒ term → 0.
5. Sum of two tendsto-zero sequences → 0, which means `|∫ f_t·g_t − ∫ f·g| → 0`.
-/

/-! ## Lemma 3 — DQM-derived L² approximation, for the inner-product step

This is the application of DQM along the sequence `h_t = t • u`. -/

/-! ## Lemma 4 — Sum convergence is a corollary of rate-control

Convergence of the square-root density sum follows from the rescaled L² convergence.

**Strategy**.  Let `r_t := t⁻¹·(√p_{θ+tu} − √p_θ) − ½·⟨u,ℓ⟩·√p_θ` (the residual
controlled by the rescaled L² convergence).  Rearranging,
`√p_{θ+tu} − √p_θ = t·r_t + (t/2)·⟨u,ℓ⟩·√p_θ`.
Squaring and using `(a+b)² ≤ 2a² + 2b²`,
`(√p_{θ+tu} − √p_θ)² ≤ 2·t²·r_t² + (t²/2)·⟨u,ℓ⟩²·p_θ`.
Integrating and taking `t → 0`, both terms tend to 0 — the first because
`t² → 0` and `∫ r_t² → 0`, the second because `t² → 0` and
`∫ ⟨u,ℓ⟩²·p_θ` is a fixed finite constant (Fisher information at `u`).  The
squeeze theorem then gives the result.
-/

/-! ## Final assembly: score has zero mean

The argument combines the four mathematical steps above.

Strategy:
  1. Pick any direction `u : Θ`.
  2. The integrand `(√p_{θ₀+t·u} − √p_{θ₀}) (√p_{θ₀+t·u} + √p_{θ₀})` integrates to 0
     for every `t ≠ 0` (Lemma 1).
  3. Multiplying by `t⁻¹`, the integrand factors as `(t⁻¹·diff) · sum`. By Lemma 2 +
     Lemma 3 + Lemma 4, this integral converges to `∫ (½ ⟨u, ℓ⟩ √p_θ)(2 √p_θ) dμ
       = ⟨u, ∫ ℓ x · p_{θ₀}(x) dμ⟩`.
  4. The LHS is 0 for every `t ≠ 0`, hence the limit is 0.
  5. Therefore `⟨u, ∫ ℓ p_{θ₀} dμ⟩ = 0` for *every* `u`, which gives
     `∫ ℓ p_{θ₀} dμ = 0` and in particular `∫ ⟨u, ℓ x⟩ p_{θ₀} x dμ = 0`. -/

end Score
end AsymptoticStatistics
