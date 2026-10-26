import AronowAudit.P006.Wave1.CorrectedRankingBlueprint
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
universe u v
namespace AronowAudit.P006.Wave1.CorrectedRanking
open AronowAudit.P006 MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
noncomputable section

lemma bit_measurable {Ω : Type v} [MeasurableSpace Ω] {T : Ω → Bool}
    (hT : Measurable T) : Measurable (fun ω => bit (T ω)) :=
  (measurable_of_finite bit).comp hT

lemma bit_norm_le_one (t : Bool) : ‖bit t‖ ≤ (1 : ℝ) := by
  cases t <;> norm_num [bit]

lemma integrable_bit {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {T : Ω → Bool} (hT : Measurable T) :
    Integrable (fun ω => bit (T ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (bit_measurable hT).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => bit_norm_le_one (T ω))

lemma integrable_bit_mul {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : Ω → Bool} {f : Ω → ℝ} (hT : Measurable T) (hf : Integrable f μ) :
    Integrable (fun ω => bit (T ω) * f ω) μ :=
  hf.bdd_mul (bit_measurable hT).aestronglyMeasurable
    (Eventually.of_forall (fun ω => bit_norm_le_one (T ω)))

/-- Equality against all indicators identifies the two weighted pushforward measures.
Integrating the second coordinate then lifts the equality to the outcome test. -/
lemma integral_coordinate_of_indicator {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → ℝ × ℝ) (hZ : Measurable Z)
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (ha01 : ∀ ω, 0 ≤ a ω ∧ a ω ≤ 1) (hb01 : ∀ ω, 0 ≤ b ω ∧ b ω ≤ 1)
    (hind : ∀ B : Set (ℝ × ℝ), MeasurableSet B →
      (∫ ω, a ω * B.indicator (fun _ => (1 : ℝ)) (Z ω) ∂μ) =
      ∫ ω, b ω * B.indicator (fun _ => (1 : ℝ)) (Z ω) ∂μ) :
    (∫ ω, a ω * (Z ω).2 ∂μ) = ∫ ω, b ω * (Z ω).2 ∂μ := by
  classical
  let ν (w : Ω → ℝ) := μ.withDensity (fun ω => ENNReal.ofReal (w ω))
  have hfinite (w : Ω → ℝ) (hw : ∀ ω, w ω ≤ 1) : IsFiniteMeasure (ν w) := by
    apply isFiniteMeasure_withDensity
    apply ne_of_lt
    calc
      (∫⁻ ω, ENNReal.ofReal (w ω) ∂μ) ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ :=
        lintegral_mono (fun ω => ENNReal.ofReal_le_one.2 (hw ω))
      _ < ∞ := by simpa using measure_lt_top μ Set.univ
  haveI : IsFiniteMeasure (ν a) := hfinite a (fun ω => (ha01 ω).2)
  haveI : IsFiniteMeasure (ν b) := hfinite b (fun ω => (hb01 ω).2)
  have hmapIntegral (w : Ω → ℝ) (hw : Measurable w) (hw0 : ∀ ω, 0 ≤ w ω)
      (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
      (∫ z, f z ∂(ν w).map Z) = ∫ ω, w ω * f (Z ω) ∂μ := by
    calc
      _ = ∫ ω, f (Z ω) ∂ν w := integral_map hZ.aemeasurable hf.aestronglyMeasurable
      _ = ∫ ω, (ENNReal.ofReal (w ω)).toReal • f (Z ω) ∂μ :=
        integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
          (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun ω => by
          show (ENNReal.ofReal (w ω)).toReal • f (Z ω) = w ω * f (Z ω)
          rw [ENNReal.toReal_ofReal (hw0 ω), smul_eq_mul])
  have heq : (ν a).map Z = (ν b).map Z := by
    ext B hB
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change ((ν a).map Z).real B = ((ν b).map Z).real B
    rw [← integral_indicator_one (μ := (ν a).map Z) hB,
      ← integral_indicator_one (μ := (ν b).map Z) hB]
    rw [hmapIntegral a ha (fun ω => (ha01 ω).1) (B.indicator 1) (measurable_one.indicator hB),
      hmapIntegral b hb (fun ω => (hb01 ω).1) (B.indicator 1) (measurable_one.indicator hB)]
    exact hind B hB
  calc
    _ = ∫ z, z.2 ∂(ν a).map Z :=
      (hmapIntegral a ha (fun ω => (ha01 ω).1) Prod.snd measurable_snd).symm
    _ = ∫ z, z.2 ∂(ν b).map Z := by rw [heq]
    _ = _ := hmapIntegral b hb (fun ω => (hb01 ω).1) Prod.snd measurable_snd

theorem n1_proof : N1.{u,v} := by
  classical
  intro Ω C _ _ n E hS π hπ i
  let μ := E.law π
  let T : Ω → ℝ := fun ω => bit (E.T π i ω)
  let p : Ω → ℝ := fun ω => π (E.X i ω)
  let Z : Ω → ℝ × ℝ := fun ω => (E.Y0 i ω, E.Y1 i ω)
  haveI : IsProbabilityMeasure μ := hS.law_probability π hπ
  have hu := hS.measurable_units π hπ i
  have hX : Measurable (E.X i) := hu.1
  have hT : Measurable T := bit_measurable hu.2.2.2
  have hp : Measurable p := hπ.1.comp hX
  have hZ : Measurable Z := hu.2.1.prodMk hu.2.2.1
  have hm : E.covariateSigma i ≤ (inferInstance : MeasurableSpace Ω) := hX.comap_le
  have hp01 (ω : Ω) : 0 ≤ p ω ∧ p ω ≤ 1 := hπ.2 (E.X i ω)
  have hT01 (ω : Ω) : 0 ≤ T ω ∧ T ω ≤ 1 := by
    dsimp [T]
    cases E.T π i ω <;> norm_num [bit]
  have hpbound : ∀ᵐ ω ∂μ, ‖p ω‖ ≤ (1 : ℝ) := Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hp01 ω).1]
    exact (hp01 ω).2)
  have hpsm : StronglyMeasurable[E.covariateSigma i] p :=
    (hπ.1.comp (comap_measurable (E.X i))).stronglyMeasurable
  have hY : Integrable (E.Y1 i) μ := (hS.integrable_units π hπ i).2.1
  have hTY : Integrable (fun ω => T ω * E.Y1 i ω) μ := integrable_bit_mul hu.2.2.2 hY
  have hpY : Integrable (p * E.Y1 i) μ := hY.bdd_mul hp.aestronglyMeasurable hpbound
  have hmean : Integrable (fun ω => E.μ1 (E.X i ω)) μ :=
    ((hS.covariate_law π hπ i).comp hS.means_measurable.2).integrable_iff.2
      hS.means_integrable.2
  have hcand : Integrable (fun ω => p ω * E.μ1 (E.X i ω)) μ :=
    hmean.bdd_mul hp.aestronglyMeasurable hpbound
  have hcandsm : StronglyMeasurable[E.covariateSigma i] (fun ω => p ω * E.μ1 (E.X i ω)) :=
    hpsm.mul ((hS.means_measurable.2.comp
      (comap_measurable (E.X i))).stronglyMeasurable)
  have hset (s : Set Ω) (hs : MeasurableSet[E.covariateSigma i] s) :
      (∫ ω in s, T ω * E.Y1 i ω ∂μ) = ∫ ω in s, p ω * E.Y1 i ω ∂μ := by
    apply integral_coordinate_of_indicator (μ.restrict s) Z hZ T p hT hp hT01 hp01
    intro B hB
    let I : Ω → ℝ := fun ω => B.indicator (fun _ => (1 : ℝ)) (Z ω)
    have hIm : Measurable I := (measurable_const.indicator hB).comp hZ
    have hI : Integrable I μ := by
      apply (integrable_const (1 : ℝ)).mono' hIm.aestronglyMeasurable
      exact Eventually.of_forall (fun ω => by
        by_cases h : Z ω ∈ B <;> simp [I, Set.indicator, h])
    have hTI : Integrable (fun ω => T ω * I ω) μ := integrable_bit_mul hu.2.2.2 hI
    have hpI : Integrable (p * I) μ := hI.bdd_mul hp.aestronglyMeasurable hpbound
    have hIgn := hS.ignorability π hπ i B hB
    have hpull := condExp_mul_of_stronglyMeasurable_left hpsm hpI hI
    calc
      _ = ∫ ω in s, (μ[fun η => T η * I η | E.covariateSigma i]) ω ∂μ :=
        (setIntegral_condExp hm hTI hs).symm
      _ = ∫ ω in s, p ω * (μ[I | E.covariateSigma i]) ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hIgn)
      _ = ∫ ω in s, (μ[p * I | E.covariateSigma i]) ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hpull.symm)
      _ = _ := setIntegral_condExp hm hpI hs
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hTY
  · intro s _ _
    exact hcand.integrableOn
  · intro s hs _
    have hmeanCE := (hS.conditional_means π hπ i).2
    have hpull := condExp_mul_of_stronglyMeasurable_left hpsm hpY hY
    calc
      _ = ∫ ω in s, p ω * (μ[E.Y1 i | E.covariateSigma i]) ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hmeanCE] with ω hω
        exact congrArg (fun z => p ω * z) hω.symm
      _ = ∫ ω in s, (μ[p * E.Y1 i | E.covariateSigma i]) ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hpull.symm)
      _ = ∫ ω in s, p ω * E.Y1 i ω ∂μ := setIntegral_condExp hm hpY hs
      _ = _ := (hset s hs).symm
  · exact hcandsm.aestronglyMeasurable

end
end AronowAudit.P006.Wave1.CorrectedRanking
