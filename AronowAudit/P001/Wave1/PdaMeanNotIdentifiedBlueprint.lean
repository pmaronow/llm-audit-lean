import AronowAudit.P001.P001_Foundations

/-!
# The PDA at the covariate mean is not identified (P001-T3)

Definition 4.3.7 (Partial Derivative at the Average), p. 167 (PDF p. 185);
the remark that the PDA "has a well-defined meaning", p. 168 (PDF p. 186);
footnote 13, p. 166; CEF determined only on the covariate support,
Definition 2.2.15, p. 69.

The printed well-definedness implication asserts that, for a continuous covariate,
any two CEF versions differentiable at every positive-density value have a common
derivative at `E[X]`. The counterexample has covariate density
`½·1_{[-2,-1] ∪ [1,2]}`, independent `Y ~ U[-1,1]`, and `E[X] = 0` outside the support.
The zero function and every multiple `a · pdaBump`, where
`pdaBump x = x(1-x²)²` on `|x| < 1` and is zero elsewhere, are `C¹` CEF versions
for the same law, with derivative `a` at `E[X] = 0`.
-/

namespace AronowAudit.P001.Wave1.PdaMeanNotIdentified

set_option autoImplicit false
noncomputable section
open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Counterexample to PDA well-definedness: the fixed gap-uniform product law
has a joint density and independent bounded coordinates, with `E[X] = 0` and `gapPDF 0 = 0`; both
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

/-- `gapPDF` is measurable, nonnegative, and integrable; positive density requires
`1 ≤ |x| ≤ 2`, and the density vanishes at zero. -/
def N1 : Prop :=
  Measurable gapPDF ∧ (∀ x, 0 ≤ gapPDF x) ∧ Integrable gapPDF volume ∧
    (∀ x, 0 < gapPDF x → 1 ≤ |x| ∧ |x| ≤ 2) ∧ gapPDF 0 = 0

/-- `gapMarginal` is a probability measure with positive density almost everywhere. -/
def N2 : Prop :=
  IsProbabilityMeasure gapMarginal ∧ ∀ᵐ x ∂gapMarginal, 0 < gapPDF x

/-- The covariate is integrable under `gapMarginal` and has mean zero. -/
def N3 : Prop :=
  Integrable (fun x : ℝ => x) gapMarginal ∧ ∫ x, x ∂gapMarginal = 0

/-- The uniform outcome law is a probability measure concentrated on `[-1,1]`. -/
def N4 : Prop :=
  IsProbabilityMeasure (uniformLaw (-1) 1) ∧
    ∀ᵐ y ∂(uniformLaw (-1) 1), y ∈ Set.Icc (-1 : ℝ) 1

/-- The product law `gapJointLaw` has joint density `gapPDF(x) 1_{[-1,1]}(y) / 2`. -/
def N5 : Prop :=
  HasJointPDF gapJointLaw (fun xy => gapPDF xy.1 *
    (if xy.2 ∈ Set.Icc (-1 : ℝ) 1 then 1 / 2 else 0))

/-- The outcome is integrable and has integral zero over every measurable covariate event. -/
def N6 : Prop :=
  Integrable Prod.snd gapJointLaw ∧
    ∀ A : Set ℝ, MeasurableSet A → ∫ xy in Prod.fst ⁻¹' A, xy.2 ∂gapJointLaw = 0

/-- Away from `|x| = 1`, the derivative of `pdaBump` equals `pdaBumpDeriv x`. -/
def N7 : Prop := ∀ x : ℝ, |x| ≠ 1 → HasDerivAt pdaBump (pdaBumpDeriv x) x

/-- `pdaBump` has derivative zero at both endpoints `1` and `-1`. -/
def N8 : Prop := HasDerivAt pdaBump 0 1 ∧ HasDerivAt pdaBump 0 (-1)

/-- The piecewise derivative `pdaBumpDeriv` is continuous. -/
def N9 : Prop := Continuous pdaBumpDeriv

/-- Under `N1`–`N9`, the product law has the stated marginals and mean, and
`pdaBump` is `C¹`. Every measurable function vanishing on the positive-density set is a CEF
version: it is a.e. zero and the outcome has zero integral over every covariate event.
The zero and bump versions have distinct derivatives at the mean. -/
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

/- The target has no hypotheses; the witness itself is the fixed law `gapJointLaw`:
`ν_X = ½·λ|_{[-2,-1]∪[1,2]}`, product with `U[-1,1]`, coordinates `X, Y`. -/

end
end AronowAudit.P001.Wave1.PdaMeanNotIdentified
