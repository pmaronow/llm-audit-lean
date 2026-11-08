import AronowAudit.P001.P001_Foundations

/-!
# Shared blueprint nodes for the two P001-T102 PDA refutations (records 1-2)

Blueprint (Wave 1, group P001a). This module fixes the explicit continuous joint law on
which both `printed_pda_is_distributional` and `printed_pda_local_support_invariance` fail
(paper proof, mapper report records 1-2, and "Shared lemmas" item 5):

* `gapJointLaw` (P001_Foundations.lean:667) is `X ⊗ Y` with `X` of density
  `gapPDF = (1/2)·1_{[-2,-1] ∪ [1,2]}` and `Y ~ Uniform[-1,1]`, independent;
* the covariate is lifted to `Fin 1 → ℝ` by `gapX (x, y) = fun _ => x`;
* the two CEF versions are `0` and `bumpVec x = pdaBump (x 0)`, where
  `pdaBump x = x (1 - x²)²` on `|x| < 1` and `0` elsewhere (P001_Foundations.lean:142).

Both versions vanish on the support, both are globally `C¹`, the covariate mean is `0`
(outside the support), and their coordinate derivatives at the mean are `0` and `1`.

Node dependencies are explicit implications, so every node can be proved independently.
Writers prove `theorem nk_proof : Nk` in `AronowAudit/P001/Wave1/GapLaw/Nk.lean`.
Never use the sorry-bearing drafts `pda_extrapolation_witness`,
`pda_joint_cef_counterexample` or `pda_extrapolation_witness_supporting` (they depend on
`sorryAx`), nor the frozen false theorems being refuted.
-/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1.GapLaw

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section

/-- The covariate density's law on `ℝ`: Lebesgue measure with density `gapPDF`
(the first factor of `gapJointLaw`). -/
abbrev gapMarginal : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (gapPDF x))

/-- The one-coordinate covariate vector `X(x, y) = (x)` on the joint sample space. -/
def gapX : ℝ × ℝ → Fin 1 → ℝ := fun xy _ => xy.1

/-- The bump CEF version on `Fin 1 → ℝ`: `m'(x) = pdaBump (x 0)`. -/
def bumpVec : (Fin 1 → ℝ) → ℝ := fun x => pdaBump (x 0)

/-- **Node GapLaw.N1** (paper proof, record 1, first two paragraphs: "Each interval has
length one, so ∫f=1. Also ∫xf(x)dx=(1/2)((-3/2)+(3/2))=0 ... The joint density is
f(x)1_{[-1,1]}(y)/2, with total integral one. Both coordinates are measurable, bounded
almost surely and integrable"). The joint law is a probability measure, both coordinates
are integrable, the first coordinate has mean `0`, the covariate lies a.s. in
`{1 ≤ |x| ≤ 2}`, and the outcome lies a.s. in `[-1,1]` with mean `0`.
Suggested route: `gapMarginal` is a probability measure (`withDensity` of a simple
function: `lintegral` of `ofReal (1/2)` over two unit intervals), `uniformLaw (-1) 1` is
a probability measure; `Measure.prod` of probability measures; `integral_prod`,
`integral_withDensity_eq_integral_toReal_smul` / `integral_withDensity_eq_integral_smul`,
`integral_Icc_eq_integral_Ioc`, `intervalIntegral.integral_id`; boundedness a.e. via
`ae_withDensity_iff` and `Measure.ae_prod_mem_iff_ae_ae_mem` (or `ae_prod_iff`). -/
def N1 : Prop :=
  IsProbabilityMeasure gapJointLaw ∧
    Integrable Prod.fst gapJointLaw ∧ Integrable Prod.snd gapJointLaw ∧
    ∫ ω, ω.1 ∂gapJointLaw = 0 ∧ ∫ ω, ω.2 ∂gapJointLaw = 0 ∧
    (∀ᵐ ω ∂gapJointLaw, 1 ≤ |ω.1| ∧ |ω.1| ≤ 2) ∧
    (∀ᵐ ω ∂gapJointLaw, ω.2 ∈ Set.Icc (-1 : ℝ) 1)

/-- **Node GapLaw.N2** (paper proof, record 1, first paragraph: "On (-1,1), b is the
polynomial x-2x³+x⁵ with derivative 1-6x²+5x⁴ ... At each of -1 and 1 its value and its
derivative are zero. The extension by zero therefore has a derivative everywhere and that
derivative is continuous ... Thus b is globally C¹, b'(0)=1, and b vanishes at every point
of S"). `pdaBump` is globally `C¹`, vanishes off `(-1,1)`, and has derivative `1` at `0`.
Suggested route: show `HasDerivAt pdaBump (pdaBump' x) x` for every `x`, with
`pdaBump' x = if |x| < 1 then 1 - 6x² + 5x⁴ else 0`, splitting `|x| < 1` (local polynomial,
`HasDerivAt.congr_of_eventuallyEq`), `|x| > 1` (locally zero) and `x = ±1` (one-sided
estimates `|pdaBump y| ≤ C |y - x|²` near `x`, e.g. `hasDerivAt_iff_isLittleO`, or
one-sided derivatives combined by `HasDerivWithinAt.union` and `HasDerivWithinAt.hasDerivAt`); then `contDiff_one_iff_deriv` with continuity of
`pdaBump'` (`Continuous.if_le`/`continuous_if` with matching values `0` at `|x| = 1`). -/
def N2 : Prop :=
  ContDiff ℝ 1 pdaBump ∧ (∀ x : ℝ, 1 ≤ |x| → pdaBump x = 0) ∧ HasDerivAt pdaBump 1 0

/-- **Node GapLaw.N3** (paper proof, record 1, second paragraph: "For every Borel A,
Fubini gives ∫_{X∈A}Y=(∫_A f)(∫_{-1}^1 y/2 dy)=0. Since b(X)=0 almost surely, the same set
integral equals ∫_{X∈A}b(X). Thus both zero and b are genuine CEF versions of this same Y
given X"). On the scalar covariate `Prod.fst`, both `0` and `pdaBump` are CEFs of the
outcome `Prod.snd` under `gapJointLaw`. Stated under `N1` (integrability, a.s. support)
and `N2` (`pdaBump = 0` off `(-1,1)`; measurability of `pdaBump` from continuity).
Suggested route: `Prod.fst ⁻¹' A = A ×ˢ univ`; `setIntegral_prod`, `integral_prod_mul` or
`integral_prod` with the rectangle `A ×ˢ univ`; the inner integral is `∫ y ∂uniform = 0`;
`setIntegral_congr_ae` with `pdaBump (ω.1) = 0` a.e. -/
def N3 : Prop :=
  N1 → N2 →
    IsCEF gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
      IsCEF gapJointLaw Prod.fst Prod.snd pdaBump

/-- **Node GapLaw.N4** (paper proof, record 1, third and fourth paragraphs: "Identify ℝ with
Fin 1→ℝ by e(r)(0)=r ... every coordinate has mean zero ... For record 1 take ν to be the
law of the lifted covariate ... It is a probability measure with integrable coordinates
... m=m′ ν-almost everywhere. The vector mean is zero"). Moment and null-set facts for the
lifted covariate law `gapJointLaw.map gapX`. Stated under `N1` and `N2`.
Suggested route: `measurable_pi_lambda`; `IsProbabilityMeasure (μ.map f)` is an automatic
instance in this Mathlib;
`integrable_map_measure`, `integral_map`, `ae_map_iff` (the set `{x | 0 = pdaBump (x 0)}`
is measurable since `pdaBump` is continuous), and `N2.2.1` with `N1`'s a.s. bound. -/
def N4 : Prop :=
  N1 → N2 →
    Measurable gapX ∧ IsProbabilityMeasure (gapJointLaw.map gapX) ∧
    (∀ j, Integrable (fun x : Fin 1 → ℝ => x j) (gapJointLaw.map gapX)) ∧
    (∀ j, Integrable (fun ω => gapX ω j) gapJointLaw) ∧
    (fun j => ∫ x, x j ∂(gapJointLaw.map gapX)) = 0 ∧
    mean gapJointLaw (fun ω => gapX ω 0) = 0 ∧
    (fun _ : Fin 1 → ℝ => (0 : ℝ)) =ᵐ[gapJointLaw.map gapX] bumpVec

/-- **Node GapLaw.N5** (paper proof, record 1, third paragraph: "This measurable linear
isometry preserves Lebesgue measure; its inverse is evaluation at 0. Consequently the
lifted X has vector density v↦f(v 0) ... and composing either CEF with evaluation at 0
preserves measurability, integrability, the CEF set-integral identities"). The lifted
covariate has the vector PDF `x ↦ gapPDF (x 0)` and both CEF versions transport to
`gapX`. Stated under `N1`, `N2`, `N3`.
Suggested route: copy the transport pattern of `pda_vector_pdf`
(P001_ConfidenceInstances.lean:137): `MeasurableEquiv.funUnique (Fin 1) ℝ`,
`volume_preserving_funUnique`, `MeasurePreserving.setLIntegral_comp_preimage_emb`,
`Measure.map_apply`, `withDensity_apply`, and `gapX = e.symm ∘ Prod.fst`; for the CEFs,
`gapX ⁻¹' A = Prod.fst ⁻¹' (e.symm ⁻¹' A)` and `bumpVec ∘ gapX = pdaBump ∘ Prod.fst`. -/
def N5 : Prop :=
  N1 → N2 → N3 →
    HasVectorPDF (gapJointLaw.map gapX) (fun x => gapPDF (x 0)) ∧
    IsCEF gapJointLaw gapX Prod.snd (fun _ => 0) ∧ IsCEF gapJointLaw gapX Prod.snd bumpVec

/-- Sanity check of the encoding: on the lifted covariate, `bumpVec ∘ gapX` is the scalar
bump of the first coordinate. -/
example (xy : ℝ × ℝ) : bumpVec (gapX xy) = pdaBump xy.1 := rfl

end

end AronowAudit.P001.Wave1.GapLaw
