import AronowAudit.P001.P001_Foundations

/-! # Blueprint: P001-T3 refutation — the PDA at the covariate mean is not identified

Record 40 of dossier group P001c (`AronowAudit.P001.pda_extrapolation_witness_supporting`,
resolution `refute`). Definition 4.3.7 (Partial Derivative at the Average), p. 167
(PDF p. 185); the remark that the PDA "has a well-defined meaning", p. 168 (PDF p. 186);
footnote 13, p. 166; CEF determined only on the covariate support, Definition 2.2.15, p. 69.

The refuted printed contract: under the stated conditions (continuous covariate, CEF
differentiable at every covariate value with positive density) any two CEF versions have a
common derivative at `E[X]`. Witness (validator): `X` with density `½·1_{[-2,-1] ∪ [1,2]}`,
independent `Y ~ U[-1,1]`, `E[X] = 0` outside the support. The zero function and every
multiple `a · pdaBump` (`pdaBump x = x(1-x²)²` on `|x| < 1`, zero elsewhere) are `C¹` CEF
versions for the same law, with derivative `a` at `E[X] = 0`.

The frozen source declarations `pda_extrapolation_witness_supporting`,
`pda_joint_cef_counterexample` and `pda_extrapolation_witness` all have unfinished placeholder
proofs (their axiom closure is not clean); they must NOT be used.

Map-P001c report, record 40; both referees accepted without fixes.

Final declaration (writer): `AronowAudit.P001.Wave1.pda_at_mean_not_identified`
in `AronowAudit/P001/Wave1/PdaMeanNotIdentified.lean`.
-/

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Frozen target (map-P001c `pda_at_mean_not_identified`): the fixed gap-uniform product law
is an admissible bounded, jointly continuous, independent law with `E[X] = 0 ∉ supp X`; both
`0` and every `a · pdaBump` are `C¹` CEF versions, the latter with derivative `a` at `E[X]`;
and the printed well-definedness implication (two CEF versions differentiable on the
positive-density set have a common derivative at the mean) fails for this law. -/
def Target : Prop :=
  IsProbabilityMeasure gapJointLaw ∧
  HasJointPDF gapJointLaw (fun xy => gapPDF xy.1 *
    (if xy.2 ∈ Set.Icc (-1 : ℝ) 1 then 1 / 2 else 0)) ∧
  HasPDF (gapJointLaw.map Prod.fst) gapPDF ∧
  gapJointLaw.map Prod.snd = uniformLaw (-1) 1 ∧
  gapJointLaw = (gapJointLaw.map Prod.fst).prod (gapJointLaw.map Prod.snd) ∧
  (∀ᵐ xy ∂gapJointLaw,
    xy.1 ∈ Set.Icc (-2 : ℝ) 2 ∧ xy.2 ∈ Set.Icc (-1 : ℝ) 1) ∧
  mean gapJointLaw Prod.fst = 0 ∧ gapPDF 0 = 0 ∧
  IsCEF gapJointLaw Prod.fst Prod.snd (fun _ => 0) ∧
  ContDiff ℝ 1 pdaBump ∧
  (∀ a : ℝ, IsCEF gapJointLaw Prod.fst Prod.snd (fun x => a * pdaBump x) ∧
    deriv (fun x => a * pdaBump x) (mean gapJointLaw Prod.fst) = a) ∧
  ¬ (∀ m m' : ℝ → ℝ,
    IsCEF gapJointLaw Prod.fst Prod.snd m →
    IsCEF gapJointLaw Prod.fst Prod.snd m' →
    (∀ x, 0 < gapPDF x → DifferentiableAt ℝ m x) →
    (∀ x, 0 < gapPDF x → DifferentiableAt ℝ m' x) →
    ∃ a : ℝ, HasDerivAt m a (mean gapJointLaw Prod.fst) ∧
      HasDerivAt m' a (mean gapJointLaw Prod.fst))

/-- The covariate marginal `ν_X`: Lebesgue measure with density `gapPDF`. By definition
`gapJointLaw = gapMarginal.prod (uniformLaw (-1) 1)` (`rfl`). -/
def gapMarginal : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (gapPDF x))

/-- The derivative of `pdaBump`: `q'(x) = 1 - 6x² + 5x⁴` on `|x| < 1`, zero elsewhere
(`q(x) = x - 2x³ + x⁵`). -/
def pdaBumpDeriv (x : ℝ) : ℝ := if |x| < 1 then 1 - 6 * x ^ 2 + 5 * x ^ 4 else 0

/-- N1 (paper-proof step "the density `f = 1_S/2`, `S = [-2,-1] ∪ [1,2]`, is measurable,
nonnegative and integrable, and vanishes outside `S`; `f(0) = 0`"). The support clause is
stated through `|x|`. -/
def N1 : Prop :=
  Measurable gapPDF ∧ (∀ x, 0 ≤ gapPDF x) ∧ Integrable gapPDF volume ∧
    (∀ x, 0 < gapPDF x → 1 ≤ |x| ∧ |x| ≤ 2) ∧ gapPDF 0 = 0

/-- N2 (paper-proof step "its integral is `(1/2)(1+1) = 1`", so `ν_X` is a probability law;
`ν_X`-almost every covariate has positive density). -/
def N2 : Prop :=
  IsProbabilityMeasure gapMarginal ∧ ∀ᵐ x ∂gapMarginal, 0 < gapPDF x

/-- N3 (paper-proof step "its first moment is `(1/2)(∫_{-2}^{-1} x dx + ∫_1^2 x dx) =
(1/2)(-3/2 + 3/2) = 0`"), stated with integrability so the value is not a junk zero. -/
def N3 : Prop :=
  Integrable (fun x : ℝ => x) gapMarginal ∧ ∫ x, x ∂gapMarginal = 0

/-- N4 (paper-proof step "`ν_Y` with density `1_{[-1,1]}/2` integrates to one"; `|Y| ≤ 1`
almost surely). -/
def N4 : Prop :=
  IsProbabilityMeasure (uniformLaw (-1) 1) ∧
    ∀ᵐ y ∂(uniformLaw (-1) 1), y ∈ Set.Icc (-1 : ℝ) 1

/-- N5 (paper-proof step "product-measure integration gives a probability law with joint
density `f(x)1_{[-1,1]}(y)/2`"): the project's `HasJointPDF` for `gapJointLaw`. -/
def N5 : Prop :=
  HasJointPDF gapJointLaw (fun xy => gapPDF xy.1 *
    (if xy.2 ∈ Set.Icc (-1 : ℝ) 1 then 1 / 2 else 0))

/-- N6 (paper-proof step "for each Borel `A`, Fubini gives `∫_{X ∈ A} Y dν =
ν_X(A) ∫ y dν_Y = 0`; all factors are absolutely integrable"). -/
def N6 : Prop :=
  Integrable Prod.snd gapJointLaw ∧
    ∀ A : Set ℝ, MeasurableSet A → ∫ xy in Prod.fst ⁻¹' A, xy.2 ∂gapJointLaw = 0

/-- N7 (paper-proof step "inside `(-1,1)`, `b' = q' = 1 - 6x² + 5x⁴`; outside `[-1,1]`,
`b' = 0`"): `pdaBump` has derivative `pdaBumpDeriv x` at every `x` with `|x| ≠ 1`. -/
def N7 : Prop := ∀ x : ℝ, |x| ≠ 1 → HasDerivAt pdaBump (pdaBumpDeriv x) x

/-- N8 (paper-proof step "for `x → e = ±1` from inside, `q(x)/(x-e) = x(x-e)(x+e)² → 0`;
from outside the quotient is identically zero; hence `b'(e) = 0`"). Writer note: with N7 and
N9 (import their files), at `e = 1` use `hasDerivWithinAt_Iic_of_tendsto_deriv` with
`s = Ioo 0 1` and `hasDerivWithinAt_Ici_of_tendsto_deriv` with `s = Ioi 1`; at `e = -1` use
`s = Iio (-1)` and `s = Ioo (-1) 0`; combine with `HasDerivWithinAt.union`, `Set.Iic_union_Ici`
and `hasDerivWithinAt_univ`. (`hasDerivAt_of_hasDerivAt_of_ne` needs the derivative at every
other point, so it applies only once one endpoint is done.) -/
def N8 : Prop := HasDerivAt pdaBump 0 1 ∧ HasDerivAt pdaBump 0 (-1)

/-- N9 (paper-proof step "the displayed polynomial derivative tends to zero at both
endpoints, so the piecewise derivative is continuous"). -/
def N9 : Prop := Continuous pdaBumpDeriv

/-- The nodes suffice. Marginals come from `Measure.map_fst_prod`/`map_snd_prod`, the mean
from `integral_fun_fst`, a.e. statements are pulled back along the product projections, the
`C¹` property from `contDiff_one_iff_deriv`, every function vanishing on the positive-density
set is a CEF version (it is `gapJointLaw`-a.e. zero and `Y` has zero integral over every
covariate event), and the final implication fails at `m = 0`, `m' = pdaBump` by uniqueness of
derivatives (`0 ≠ 1`). -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6)
    (h7 : N7) (h8 : N8) (h9 : N9) : Target := by
  obtain ⟨hpdfm, hpdf0, hpdfi, hsupp, hzero⟩ := h1
  obtain ⟨hXprob, hXpos⟩ := h2
  obtain ⟨hYprob, hYbd⟩ := h4
  obtain ⟨hYint, hYcef⟩ := h6
  have := hXprob
  have := hYprob
  have hjoint : gapJointLaw = gapMarginal.prod (uniformLaw (-1) 1) := rfl
  have hfst : gapJointLaw.map Prod.fst = gapMarginal := by
    rw [hjoint, Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : gapJointLaw.map Prod.snd = uniformLaw (-1) 1 := by
    rw [hjoint, Measure.map_snd_prod, measure_univ, one_smul]
  have hmean : mean gapJointLaw Prod.fst = 0 := by
    unfold mean
    rw [hjoint, integral_fun_fst (fun x : ℝ => x), h3.2, smul_zero]
  have hD : ∀ x, HasDerivAt pdaBump (pdaBumpDeriv x) x := by
    intro x
    by_cases hx : |x| = 1
    · rcases (abs_eq zero_le_one).mp hx with h | h
      · subst h
        simpa [pdaBumpDeriv] using h8.1
      · subst h
        simpa [pdaBumpDeriv] using h8.2
    · exact h7 x hx
  have hderiv : deriv pdaBump = pdaBumpDeriv := funext fun x => (hD x).deriv
  have hC1 : ContDiff ℝ 1 pdaBump :=
    contDiff_one_iff_deriv.mpr ⟨fun x => (hD x).differentiableAt, hderiv ▸ h9⟩
  have hD0 : HasDerivAt pdaBump 1 0 := by simpa [pdaBumpDeriv] using hD 0
  have hvan : ∀ x, 0 < gapPDF x → pdaBump x = 0 := by
    intro x hx
    simp [pdaBump, not_lt.mpr (hsupp x hx).1]
  have hcef : ∀ m : ℝ → ℝ, Measurable m → (∀ x, 0 < gapPDF x → m x = 0) →
      IsCEF gapJointLaw Prod.fst Prod.snd m := by
    intro m hm hm0
    have hae : (fun xy : ℝ × ℝ => m xy.1) =ᵐ[gapJointLaw] fun _ => (0 : ℝ) := by
      rw [hjoint]
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := gapMarginal)
        (ν := uniformLaw (-1) 1)).ae hXpos] with xy hxy using hm0 _ hxy
    refine ⟨hm, hYint, (integrable_zero _ _ _).congr hae.symm, fun A hA => ?_⟩
    rw [hYcef A hA, integral_congr_ae (ae_restrict_of_ae hae), integral_zero]
  have hbounds : ∀ᵐ xy ∂gapJointLaw,
      xy.1 ∈ Set.Icc (-2 : ℝ) 2 ∧ xy.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hjoint]
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := gapMarginal)
        (ν := uniformLaw (-1) 1)).ae hXpos,
      (Measure.quasiMeasurePreserving_snd (μ := gapMarginal)
        (ν := uniformLaw (-1) 1)).ae hYbd] with xy hx hy
    exact ⟨abs_le.mp (hsupp _ hx).2, hy⟩
  refine ⟨?_, h5, ?_, hsnd, ?_, hbounds, hmean, hzero,
    hcef _ measurable_const (fun _ _ => rfl), hC1, ?_, ?_⟩
  · rw [hjoint]
    infer_instance
  · rw [hfst]
    exact ⟨hpdfm.aemeasurable, hpdf0, hpdfi, rfl⟩
  · simp only [hfst, hsnd]
    rfl
  · intro a
    refine ⟨hcef _ (measurable_const.mul hC1.continuous.measurable)
      (fun x hx => by simp [hvan x hx]), ?_⟩
    rw [hmean]
    simpa using (hD0.const_mul a).deriv
  · intro h
    obtain ⟨a, ha0, ha1⟩ := h (fun _ => 0) pdaBump
      (hcef _ measurable_const (fun _ _ => rfl))
      (hcef _ hC1.continuous.measurable hvan)
      (fun x _ => differentiableAt_const _) (fun x _ => (hD x).differentiableAt)
    rw [hmean] at ha0 ha1
    have e0 : a = 0 := ha0.unique (hasDerivAt_const _ _)
    have e1 : a = 1 := ha1.unique hD0
    exact zero_ne_one (e0.symm.trans e1)

/- The target has no hypotheses; the witness itself is the fixed law `gapJointLaw`
(referees: `ν_X = ½·λ|_{[-2,-1]∪[1,2]}`, product with `U[-1,1]`, coordinates `X, Y`). -/

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
