import AronowAudit.P047.Wave1.ImpossibilityBlueprint
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

/-- Uniform lower-tail mass, including the probabilities zero and one. -/
theorem uniform01_Iic (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniform01 (Set.Iic p) = ENNReal.ofReal p := by
  rw [uniform01, Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic p ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 p := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨hv, hv0, hv1⟩
      exact ⟨hv0, hv⟩
    · rintro ⟨hv0, hv⟩
      exact ⟨hv, hv0, hv.trans hp1⟩
  rw [hset, Real.volume_Ioc, sub_zero]

/-- Integrating a two-valued threshold needs no assumption about the two values. -/
theorem uniform01_integral_ite (p t f : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ v : ℝ, (if v ≤ p then t else f) ∂uniform01) = p * t + (1 - p) * f := by
  have hfun : (fun v : ℝ => if v ≤ p then t else f) =
      (Set.Iic p).piecewise (fun _ => t) (fun _ => f) := by
    funext v
    by_cases hv : v ≤ p <;> simp [Set.piecewise, Set.mem_Iic, hv]
  rw [hfun, integral_piecewise measurableSet_Iic (integrable_const _) (integrable_const _)]
  simp only [setIntegral_const, smul_eq_mul]
  rw [probReal_compl_eq_one_sub measurableSet_Iic]
  have hp : uniform01.real (Set.Iic p) = p := by
    rw [measureReal_def, uniform01_Iic p hp0 hp1, ENNReal.toReal_ofReal hp0]
  rw [hp]

theorem measurable_gen (e m : ℝ → ℝ) (he : Measurable e) (hm : Measurable m) :
    Measurable (gen e m) := by
  have ha : Measurable (fun z : ℝ × ℝ × ℝ => decide (z.2.1 ≤ e z.1)) := by
    apply measurable_to_bool
    convert measurableSet_le (measurable_snd.fst :
      Measurable (fun z : ℝ × ℝ × ℝ => z.2.1)) (he.comp measurable_fst) using 1
    ext z
    simp
  have hy : Measurable (fun z : ℝ × ℝ × ℝ =>
      if z.2.2 ≤ m z.1 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_snd.snd (hm.comp measurable_fst))
      measurable_const measurable_const
  exact measurable_fst.prodMk (ha.prodMk (measurable_const.prodMk hy))

theorem genMeasure_map_covariate (e m : ℝ → ℝ) (he : Measurable e) (hm : Measurable m) :
    (genMeasure e m).map covariate = uniform01 := by
  rw [genMeasure, Measure.map_map measurable_covariate (measurable_gen e m he hm)]
  change (uniform01.prod (uniform01.prod uniform01)).map Prod.fst = uniform01
  simp

/-- The two seed integrals at a fixed `w`. Even an arbitrary `F` only takes four values here. -/
theorem integral_gen_fiber (e m : ℝ → ℝ) (w : ℝ)
    (he : 0 ≤ e w ∧ e w ≤ 1) (hm : 0 ≤ m w ∧ m w ≤ 1) (F : UnitData → ℝ) :
    (∫ z : ℝ × ℝ, F (gen e m (w, z)) ∂uniform01.prod uniform01) =
      e w * m w * F (w, true, 0, 1) + e w * (1 - m w) * F (w, true, 0, 0) +
        (1 - e w) * m w * F (w, false, 0, 1) +
        (1 - e w) * (1 - m w) * F (w, false, 0, 0) := by
  classical
  let f : ℝ × ℝ → ℝ := fun z =>
    if z.1 ≤ e w then
      if z.2 ≤ m w then F (w, true, 0, 1) else F (w, true, 0, 0)
    else if z.2 ≤ m w then F (w, false, 0, 1) else F (w, false, 0, 0)
  have hfun : (fun z : ℝ × ℝ => F (gen e m (w, z))) = f := by
    funext z
    by_cases ha : z.1 ≤ e w <;> by_cases hy : z.2 ≤ m w <;> simp [gen, f, ha, hy]
  have hf : Measurable f :=
    Measurable.ite (measurableSet_le measurable_fst measurable_const)
      (Measurable.ite (measurableSet_le measurable_snd measurable_const)
        measurable_const measurable_const)
      (Measurable.ite (measurableSet_le measurable_snd measurable_const)
        measurable_const measurable_const)
  let C := |F (w, true, 0, 1)| + |F (w, true, 0, 0)| +
    |F (w, false, 0, 1)| + |F (w, false, 0, 0)|
  have hi : Integrable f (uniform01.prod uniform01) := by
    apply Integrable.of_bound hf.aestronglyMeasurable C
    apply ae_of_all
    intro z
    dsimp [f]
    split_ifs <;> (try simp only [Real.norm_eq_abs]) <;>
      dsimp [C] <;> linarith [abs_nonneg (F (w, true, 0, 1)),
        abs_nonneg (F (w, true, 0, 0)), abs_nonneg (F (w, false, 0, 1)),
        abs_nonneg (F (w, false, 0, 0))]
  rw [hfun, integral_prod f hi]
  have hinner (v : ℝ) :
      (∫ y : ℝ, f (v, y) ∂uniform01) =
        if v ≤ e w then
          m w * F (w, true, 0, 1) + (1 - m w) * F (w, true, 0, 0)
        else m w * F (w, false, 0, 1) + (1 - m w) * F (w, false, 0, 0) := by
    by_cases hv : v ≤ e w <;>
      simp only [f, hv, ↓reduceIte] <;>
      exact uniform01_integral_ite _ _ _ hm.1 hm.2
  simp_rw [hinner]
  rw [uniform01_integral_ite _ _ _ he.1 he.2]
  ring

/-- An integral version of the generator formula, reusable for observable indicators. -/
theorem integral_genMeasure (e m : ℝ → ℝ) (he : Measurable e) (hm : Measurable m)
    (heb : ∀ w, 0 ≤ e w ∧ e w ≤ 1) (hmb : ∀ w, 0 ≤ m w ∧ m w ≤ 1)
    (F : UnitData → ℝ) (hF : Integrable F (genMeasure e m)) :
    (∫ u, F u ∂genMeasure e m) =
      ∫ w, e w * m w * F (w, true, 0, 1) + e w * (1 - m w) * F (w, true, 0, 0) +
        (1 - e w) * m w * F (w, false, 0, 1) +
        (1 - e w) * (1 - m w) * F (w, false, 0, 0) ∂uniform01 := by
  have hg := measurable_gen e m he hm
  have hp : Integrable (fun z => F (gen e m z))
      (uniform01.prod (uniform01.prod uniform01)) := hF.comp_measurable hg
  rw [genMeasure, integral_map hg.aemeasurable hF.aestronglyMeasurable,
    integral_prod _ hp]
  exact integral_congr_ae (ae_of_all _ fun w => integral_gen_fiber e m w (heb w) (hmb w) F)

/-- Identify the conditional expectation by all `covariateSigma` set integrals. -/
theorem n2_proof : N2 := by
  classical
  intro e m he hm heb hmb g hg
  let H : ℝ → ℝ := fun w =>
    e w * m w * g (true, 0, 1) + e w * (1 - m w) * g (true, 0, 0) +
      (1 - e w) * m w * g (false, 0, 1) +
      (1 - e w) * (1 - m w) * g (false, 0, 0)
  have hH : Measurable H := by
    dsimp [H]
    exact (((((he.mul hm).mul_const _).add
      ((he.mul (measurable_const.sub hm)).mul_const _)).add
        (((measurable_const.sub he).mul hm).mul_const _)).add
          (((measurable_const.sub he).mul (measurable_const.sub hm)).mul_const _))
  have hgen := measurable_gen e m he hm
  have hF : Measurable (fun u : UnitData => g u.2) := hg.comp measurable_snd
  let C := |g (true, 0, 1)| + |g (true, 0, 0)| +
    |g (false, 0, 1)| + |g (false, 0, 0)|
  have hp : Integrable (fun z => g (gen e m z).2)
      (uniform01.prod (uniform01.prod uniform01)) := by
    apply Integrable.of_bound (hF.comp hgen).aestronglyMeasurable C
    apply ae_of_all
    intro z
    by_cases ha : z.2.1 ≤ e z.1 <;> by_cases hy : z.2.2 ≤ m z.1 <;>
      simp only [Function.comp_apply, gen, ha, hy, ↓reduceIte, decide_true, decide_false,
        Real.norm_eq_abs] <;>
      dsimp [C] <;> linarith [abs_nonneg (g (true, 0, 1)),
        abs_nonneg (g (true, 0, 0)), abs_nonneg (g (false, 0, 1)),
        abs_nonneg (g (false, 0, 0))]
  have hFint : Integrable (fun u : UnitData => g u.2) (genMeasure e m) :=
    (integrable_map_measure hF.aestronglyMeasurable hgen.aemeasurable).mpr hp
  have hfiber (w : ℝ) :
      (∫ z : ℝ × ℝ, g (gen e m (w, z)).2 ∂uniform01.prod uniform01) = H w :=
    integral_gen_fiber e m w (heb w) (hmb w) (fun u => g u.2)
  have hHint : Integrable H uniform01 := by
    have h := hp.integral_prod_left
    simpa only [hfiber] using h
  have hHcov_int : Integrable (fun u : UnitData => H (covariate u)) (genMeasure e m) := by
    have hh : Integrable H ((genMeasure e m).map covariate) := by
      rw [genMeasure_map_covariate e m he hm]
      exact hHint
    exact hh.comp_measurable measurable_covariate
  have hHcov : Measurable[covariateSigma] (fun u : UnitData => H (covariate u)) :=
    hH.comp measurable_covariate_conditioning
  change (genMeasure e m)[fun u => g u.2 | covariateSigma] =ᵐ[genMeasure e m]
    (fun u => H (covariate u))
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq covariateSigma_le hFint
    (fun s _ _ => hHcov_int.integrableOn) _ hHcov.aestronglyMeasurable
  intro s hs _
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hs' : MeasurableSet (covariate ⁻¹' B) := measurable_covariate hB
  have hleft :
      (∫ u in covariate ⁻¹' B, H (covariate u) ∂genMeasure e m) =
        ∫ w in B, H w ∂uniform01 := by
    rw [← genMeasure_map_covariate e m he hm]
    symm
    exact setIntegral_map hB hH.aestronglyMeasurable measurable_covariate.aemeasurable
  have hright :
      (∫ u in covariate ⁻¹' B, g u.2 ∂genMeasure e m) =
        ∫ w in B, H w ∂uniform01 := by
    rw [genMeasure, setIntegral_map hs' hF.aestronglyMeasurable hgen.aemeasurable]
    have hpre : gen e m ⁻¹' (covariate ⁻¹' B) =
        B ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
      ext z
      simp [gen, covariate]
    rw [hpre, setIntegral_prod _ hp.integrableOn]
    simp only [setIntegral_univ, hfiber]
  exact hleft.trans hright.symm

end

end AronowAudit.P047.Wave1.Impossibility
