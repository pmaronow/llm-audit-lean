import AronowAudit.P001.P001_Foundations

/-!
# A joint law for the P001-T102 PDA counterexamples

The continuous joint law `gapJointLaw` is the product of a covariate with density
`gapPDF = (1/2)·1_{[-2,-1] ∪ [1,2]}` and an independent outcome uniform on `[-1,1]`.
The covariate is lifted to `Fin 1 → ℝ` by `gapX (x, y) = fun _ => x`.
The two CEF versions are `0` and `bumpVec x = pdaBump (x 0)`, where
`pdaBump x = x (1 - x²)²` on `|x| < 1` and `0` elsewhere.

Both versions vanish on the support, both are globally `C¹`, the covariate mean is `0`
(outside the support), and their coordinate derivatives at the mean are `0` and `1`.
The propositions below describe the joint law, the bump function, and transport of
moments, densities, and CEFs to the one-coordinate vector space.
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

/-- Each interval in the covariate support has length one, so its density integrates
to one. Its first moment is `(1/2)((-3/2)+(3/2)) = 0`. The joint density is
`gapPDF(x)1_{[-1,1]}(y)/2`, with total integral one. The joint law is a probability
measure, both coordinates are measurable, bounded almost surely and integrable,
the first coordinate has mean `0`, the covariate lies a.s. in `{1 ≤ |x| ≤ 2}`,
and the outcome lies a.s. in `[-1,1]` with mean `0`.

For normalization, `gapMarginal` is a probability measure (`withDensity` of a simple
function: `lintegral` of `ofReal (1/2)` over two unit intervals), and `uniformLaw (-1) 1`
is a probability measure. Product integrals give the moments, using `integral_prod`,
`integral_withDensity_eq_integral_toReal_smul` / `integral_withDensity_eq_integral_smul`,
`integral_Icc_eq_integral_Ioc`, and `intervalIntegral.integral_id`. Almost-sure bounds
follow from `ae_withDensity_iff` and `Measure.ae_prod_mem_iff_ae_ae_mem` (or `ae_prod_iff`). -/
def N1 : Prop :=
  IsProbabilityMeasure gapJointLaw ∧
    Integrable Prod.fst gapJointLaw ∧ Integrable Prod.snd gapJointLaw ∧
    ∫ ω, ω.1 ∂gapJointLaw = 0 ∧ ∫ ω, ω.2 ∂gapJointLaw = 0 ∧
    (∀ᵐ ω ∂gapJointLaw, 1 ≤ |ω.1| ∧ |ω.1| ≤ 2) ∧
    (∀ᵐ ω ∂gapJointLaw, ω.2 ∈ Set.Icc (-1 : ℝ) 1)

/-- On `(-1,1)`, `pdaBump` is the polynomial `x - 2x³ + x⁵` with derivative
`1 - 6x² + 5x⁴`. At each of `-1` and `1` its value and its derivative are zero.
The extension by zero is globally `C¹`, vanishes off `(-1,1)`, and has derivative
`1` at `0`.

The derivative is `1 - 6x² + 5x⁴` for `|x| < 1` and zero otherwise. The interior
and exterior follow from local equality with a polynomial and with zero,
respectively (`HasDerivAt.congr_of_eventuallyEq`). At `x = ±1`, one-sided estimates
`|pdaBump y| ≤ C |y - x|²` near `x` give zero derivative
(`hasDerivAt_iff_isLittleO`); alternatively, derivatives within the two pieces
combine using `HasDerivWithinAt.union` and `HasDerivWithinAt.hasDerivAt`.
Continuity of the derivative follows from the matching boundary values, and
`contDiff_one_iff_deriv` gives global `C¹` regularity. -/
def N2 : Prop :=
  ContDiff ℝ 1 pdaBump ∧ (∀ x : ℝ, 1 ≤ |x| → pdaBump x = 0) ∧ HasDerivAt pdaBump 1 0

/-- For every Borel set `A`, Fubini gives
`∫_{X∈A} Y = (∫_A gapPDF)(∫_{-1}^1 y/2 dy) = 0`.
Since `pdaBump(X) = 0` almost surely, the same set integral equals
`∫_{X∈A} pdaBump(X)`. Thus, for the scalar covariate `Prod.fst`, both `0` and
`pdaBump` are CEFs of the outcome `Prod.snd` under `gapJointLaw`.
The hypotheses are `N1` (integrability and a.s. support) and `N2`
(vanishing off `(-1,1)` and continuity, hence measurability).

The identity `Prod.fst ⁻¹' A = A ×ˢ univ` reduces the integrals to rectangles,
using `setIntegral_prod`, `integral_prod_mul`, or `integral_prod`.
The inner outcome integral is zero; `setIntegral_congr_ae` then applies to
`pdaBump (ω.1) = 0` a.e. -/
def N3 : Prop :=
  N1 → N2 →
    IsCEF gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
      IsCEF gapJointLaw Prod.fst Prod.snd pdaBump

/-- Moment and null-set facts for the lifted covariate law `gapJointLaw.map gapX`,
under `N1` and `N2`. Identifying `ℝ` with `Fin 1 → ℝ` by evaluation at `0`
gives a probability law with integrable coordinates and zero vector mean.
The zero function and `bumpVec` agree almost everywhere under this law.

Measurability follows from `measurable_pi_lambda`; probability is preserved by
measurable pushforward. The moment identities use `integrable_map_measure` and
`integral_map`. For `ae_map_iff`, the equality set is measurable by continuity of
`pdaBump`, and its full measure follows from the support bound and vanishing
property in `N1` and `N2`. -/
def N4 : Prop :=
  N1 → N2 →
    Measurable gapX ∧ IsProbabilityMeasure (gapJointLaw.map gapX) ∧
    (∀ j, Integrable (fun x : Fin 1 → ℝ => x j) (gapJointLaw.map gapX)) ∧
    (∀ j, Integrable (fun ω => gapX ω j) gapJointLaw) ∧
    (fun j => ∫ x, x j ∂(gapJointLaw.map gapX)) = 0 ∧
    mean gapJointLaw (fun ω => gapX ω 0) = 0 ∧
    (fun _ : Fin 1 → ℝ => (0 : ℝ)) =ᵐ[gapJointLaw.map gapX] bumpVec

/-- The lifted covariate has vector PDF `x ↦ gapPDF (x 0)`, and both CEF versions
transport to `gapX`, under `N1`, `N2`, and `N3`. The identification of `ℝ` with
`Fin 1 → ℝ` is a measurable linear isometry preserving Lebesgue measure;
its inverse is evaluation at `0`.

The transport uses `MeasurableEquiv.funUnique (Fin 1) ℝ`,
`volume_preserving_funUnique`, `MeasurePreserving.setLIntegral_comp_preimage_emb`,
`Measure.map_apply`, and `withDensity_apply`. Writing this equivalence as `e`,
`gapX = e.symm ∘ Prod.fst`. For the CEF identities,
`gapX ⁻¹' A = Prod.fst ⁻¹' (e.symm ⁻¹' A)` and
`bumpVec ∘ gapX = pdaBump ∘ Prod.fst`. -/
def N5 : Prop :=
  N1 → N2 → N3 →
    HasVectorPDF (gapJointLaw.map gapX) (fun x => gapPDF (x 0)) ∧
    IsCEF gapJointLaw gapX Prod.snd (fun _ => 0) ∧ IsCEF gapJointLaw gapX Prod.snd bumpVec

end

end AronowAudit.P001.Wave1.GapLaw
