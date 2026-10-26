/-
Documentation corrected for llm-audit-lean.
Upstream project: StatLean.
Modified for llm-audit-lean: import paths adapted and declarations not used by this repository removed.
-/
import AronowAudit.External.StatLean.AsymptoticStatistics.Core.Hilbert
import AronowAudit.External.StatLean.AsymptoticStatistics.Core.CandidateIF
import AronowAudit.External.StatLean.AsymptoticStatistics.ForMathlib.QMDAnalytic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

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

The QMD limit can be stated in `ℝ≥0∞`-quotient form `eLpNorm … / ofReal |t| → 0`
rather than the classical `.toReal²/t² → 0` form: the latter would be
vacuously satisfied whenever the residual leaves `L²(μ)` (since
`(⊤ : ℝ≥0∞).toReal = 0`), whereas the `ℝ≥0∞` form forces
finiteness of the residual L²-norm near `t = 0`.

**Bibliographic comments.** Differentiability in quadratic mean originates
with L. Le Cam, "On the assumptions used to prove asymptotic normality of
maximum likelihood estimates", *Annals of Mathematical Statistics* 41(3)
(1970), 802–828. Le Cam introduced the square-root-density (DQM) condition
precisely to replace the classical pointwise-differentiability and
domination hypotheses of Cramér with a single quadratic-mean condition,
under which asymptotic normality of the MLE still holds. van der Vaart's
Chapter 25 develops this for the more general semiparametric setting of
differentiable submodels (paths) and their score functions; the mean-zero
property of the score (Lemma 25.14) is a direct consequence of the DQM
expansion that Le Cam established for the parametric case.
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
function `score : ↥(L2ZeroMean P)`. The L²(dominating) derivative of the
square-root density is `(score / 2) · sqrt(p₀)`, where
`p₀ ω := ((curve 0).rnDeriv dominating ω).toReal` is the baseline density
relative to `dominating`.

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
  eq 25.13 uses formal `dP^{1/2}` symbols and is *nondominated*; the
  dominated specialisation uses Mathlib's RN-derivative +
  `eLpNorm` machinery, which operates on densities, not on
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
