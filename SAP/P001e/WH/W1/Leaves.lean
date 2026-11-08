import SAP.P001e.Defs.WholeW1
import SAP.P001e.Bridge
import AronowAudit.P001.Wave1.Gap.WP001bB2

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W1
universe u v
noncomputable section

/-- T78, intercept normal equation without a rank assumption.
Shift only coefficient zero by t. The RSS changes by -2t sum(e)+n t^2.
Use minimality at t=sum(e)/n and positivity of n to force sum(e)=0.
Matrix.mulVec_add and finite-sum algebra suffice; do not assume an invertible Gram matrix. -/
def T78_L1 : Prop :=
  ∀ {n K : ℕ}, 0 < n → ∀ (X : Matrix (Fin n) (Fin (K+1)) ℝ)
    (Y : Fin n → ℝ) (b : Fin (K+1) → ℝ),
    (∀ i, X i 0 = 1) → (∀ c, residualSS X Y b ≤ residualSS X Y c) →
    (∑ i, (Y i-X.mulVec b i)) = 0

/-- T79, the population conditional-law identity, stable under choice of version.
For the covariate lower orthant B, use condDistrib_ae_eq_condExp for Iic y,
then setIntegral_condExp on X-preimage B. Convert indicators to restricted
integrals. integrable_toReal_condDistrib supplies integrability; pull hH back
with ae_of_ae_map and transport both integrals and integrability. This covers
K=0, and requires no outcome moments or pointwise density uniqueness. -/
def T79_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : ℕ} (Y : Ω → ℝ) (X : Ω → Fin K → ℝ), Measurable Y → Measurable X →
    ∀ (y : ℝ) (x : Fin K → ℝ) (H : (Fin K → ℝ) → ℝ),
    (∀ᵐ z ∂(μ.map X), H z = probability (condDistrib Y X μ z) (Iic y)) →
    Integrable (fun ω => if X ω ∈ W1orthant x then H (X ω) else 0) μ ∧
    probability μ {ω | Y ω ≤ y ∧ X ω ∈ W1orthant x} =
      expectation μ (fun ω => if X ω ∈ W1orthant x then H (X ω) else 0)

/-- T80, extend the existing sharp-bounds result from pointwise to almost-sure support.
Clip Y to max a (min b Y) and replace R by the indicator of R=1. These are
measurable pointwise representatives equal to Y,R almost surely. Apply
missing_data_bounds_and_sharpness, transport the endpoint expectations and the
mean by integral_congr_ae, and retain its completion on the same space.
Its recorded outcome agrees almost surely with the original one even when
R has exceptional nonbinary values. The case a=b needs no division. -/
def T80_L1 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y R : Ω → ℝ), Measurable Y → Measurable R → ∀ a b : ℝ, a ≤ b →
    (∀ᵐ ω ∂μ, Y ω ∈ Icc a b) → (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) →
    let L := expectation μ (fun ω => completeMissing (recordedOutcome (Y ω) (R ω)) (R ω) a)
    let U := expectation μ (fun ω => completeMissing (recordedOutcome (Y ω) (R ω)) (R ω) b)
    L ≤ expectation μ Y ∧ expectation μ Y ≤ U ∧
    ∀ c ∈ Icc L U, ∃ Y' : Ω → ℝ, Measurable Y' ∧
      (∀ ω, Y' ω ∈ Icc a b) ∧ expectation μ Y' = c ∧
      (fun ω => recordedOutcome (Y' ω) (R ω)) =ᵐ[μ]
        (fun ω => recordedOutcome (Y ω) (R ω))

/-- T83, repair response and propensity versions while preserving MAR.
Set R0=1_{R=1}. Given epsilon>0 and p(X)>epsilon almost surely, set
p0(x)=max (p x) epsilon; use epsilon/2 for the everywhere positive bound.
Both replacements agree with the originals almost surely after composition
with X. Transfer IsConditionalMean by integrable congruence and restricted
integral congruence; transfer CondIndependent by condExp_congr_ae on its three
indicator functions. This is a version repair, not an additional MAR premise. -/
def T83_L1 : Prop :=
  ∀ {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X)
    (Y R : Ω → ℝ), Measurable R →
    (∀ᵐ ω ∂μ, R ω = 0 ∨ R ω = 1) → ∀ p : E → ℝ,
    IsConditionalMean μ X R p →
    (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂μ, ε < p (X ω)) → CondIndependent μ X hX Y R →
    ∃ (R0 : Ω → ℝ) (p0 : E → ℝ),
      Measurable R0 ∧ (∀ ω, R0 ω = 0 ∨ R0 ω = 1) ∧ R0 =ᵐ[μ] R ∧
      (fun ω => p0 (X ω)) =ᵐ[μ] (fun ω => p (X ω)) ∧
      IsConditionalMean μ X R0 p0 ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ ω, δ < p0 (X ω)) ∧ CondIndependent μ X hX Y R0

/-- The Gaussian calculation is short enough to discharge in the assembly. -/
theorem T77_assembly : T77WholeStatement.{u} := by
  refine ⟨@AronowAudit.P001.likelihood_correct_function_space, ?_⟩
  intro m s hs
  have heq : W1normalDensity m s = gaussianPDFReal m ⟨s^2, sq_nonneg s⟩ :=
    AronowAudit.P001.normalDensity_eq_gaussianPDFReal m s hs
  have hv : (⟨s^2, sq_nonneg s⟩ : ℝ≥0) ≠ 0 := by
    intro hz
    exact (sq_pos_of_pos hs).ne' (congrArg (fun v : ℝ≥0 => (v : ℝ)) hz)
  have hroot : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hcenter : W1normalDensity m s m = 1/(s*Real.sqrt (2*Real.pi)) := by
    simp [W1normalDensity]
  refine ⟨heq ▸ integrable_gaussianPDFReal m _, ?_, ?_, hcenter, ?_⟩
  · rw [heq]; exact gaussianPDFReal_nonneg m _
  · rw [heq]; exact integral_gaussianPDFReal_eq_one m hv
  · intro hsmall
    rw [hcenter]
    exact (one_lt_div (mul_pos hs hroot)).mpr ((lt_div_iff₀ hroot).mp hsmall)

/-- Assemble the existing joint ML maximum and the new intercept equation. -/
theorem T78_assembly (h1 : T78_L1) : T78WholeStatement := by
  intro n K hn X Y b hX hmin hQ
  obtain ⟨hs, hs2, hmax⟩ := AronowAudit.P001.normal_joint_ml_scale_square hn X Y b hmin hQ
  have hsum := h1 hn X Y b hX hmin
  have hm : (∑ i, (Y i-X.mulVec b i))/(n : ℝ) = 0 := by rw [hsum, zero_div]
  refine ⟨hs, hs2, hmax, hsum, hm, ?_, ?_⟩
  · simp only [hm, sub_zero]; rfl
  · simp only [hm, zero_pow (by decide : 2 ≠ 0), sub_zero]; rfl

private theorem pmf_tail (p : PMF ℝ) (y : ℝ) :
    probability p.toMeasure (Iic y) = W1pmfTail p y := by
  unfold probability W1pmfTail
  rw [PMF.toMeasure_apply p measurableSet_Iic,
    ENNReal.tsum_toReal_eq (fun v => by
      by_cases h : v ∈ Iic y <;> simp [Set.indicator, h, p.apply_ne_top])]
  apply tsum_congr
  intro v
  by_cases h : v ≤ y <;> simp [Set.indicator, h]

private theorem pdf_tail (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (f : ℝ → ℝ) (hf : W1HasPDF ν f) (y : ℝ) :
    probability ν (Iic y) = ∫ v in Iic y, f v :=
  (AronowAudit.P001.pdf_version_change ν f f hf hf.1 hf.2.1 (ae_of_all _ (fun _ => rfl))).2 y

private theorem cdf_map {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) {K : ℕ} (Y : Ω → ℝ) (X : Ω → Fin K → ℝ)
    (hY : Measurable Y) (hX : Measurable X) (y : ℝ) (x : Fin K → ℝ) :
    W1jointCDF (μ.map (fun ω => (Y ω, X ω))) (y,x) =
      probability μ {ω | Y ω ≤ y ∧ X ω ∈ W1orthant x} := by
  have hx : MeasurableSet (W1orthant x) := by
    simpa only [W1orthant, ofPred_forall] using
      (MeasurableSet.iInter (fun k : Fin K =>
        measurableSet_le (measurable_pi_apply k) (measurable_const (a := x k))))
  unfold W1jointCDF probability
  congr 1
  exact Measure.map_apply (hY.prodMk hX)
    (show MeasurableSet {w : ℝ × (Fin K → ℝ) | w.1 ≤ y ∧ w.2 ∈ W1orthant x} from
      (measurable_fst measurableSet_Iic).inter (measurable_snd hx))

private theorem fitted_display {n K : ℕ} (hn : 0 < n) (X : Fin n → Fin K → ℝ)
    (ν : Fin n → Measure ℝ) (hν : ∀ i, IsProbabilityMeasure (ν i))
    (H : Fin n → ℝ → ℝ) (hH : ∀ i y, probability (ν i) (Iic y) = H i y) :
    W1FittedDisplay X ν H := by
  obtain ⟨hprob, hformula⟩ := AronowAudit.P001.ml_plugin_correct_covariate_indices hn X ν hν
  refine ⟨hprob, ⟨W1jointCDF (fittedJointLaw X ν), fittedJointLaw X ν, hprob, rfl⟩, rfl, ?_, ?_⟩
  · intro y x
    change probability (fittedJointLaw X ν) _ = _
    convert hformula y x using 1
    · rfl
    · simp only [W1orthant, mem_ofPred_eq, probability, AronowAudit.P001.prob] at hH ⊢
      simp_rw [hH]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : ∀ k, X i k ≤ x k <;> simp [hx]
  · intro T; rfl

/-- Assemble version-correct population formulas and the two fitted model displays.
Normalization comes from the model laws. The maximization hypothesis identifies
the single supplied parameter as an ML fit; the CDF identity holds for any fit. -/
theorem T79_assembly (h1 : T79_L1.{u}) : T79WholeStatement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ω _ μ _ K Y X hY hX
    let ν := μ.map (fun ω => (Y ω, X ω))
    have hν : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
    let F : W1JointCDF K := ⟨W1jointCDF ν, ν, hν, rfl⟩
    have hF (y : ℝ) (x : Fin K → ℝ) :
        F.val (y,x) = probability μ {ω | Y ω ≤ y ∧ X ω ∈ W1orthant x} :=
      cdf_map μ Y X hY hX y x
    refine ⟨F, rfl, hF, ?_, ?_, ?_⟩
    · intro y x
      rw [hF]
      exact h1 μ Y X hY hX y x _ (ae_of_all _ (fun _ => rfl))
    · intro p hp y x
      rw [hF]
      apply h1 μ Y X hY hX y x (fun z => W1pmfTail (p z) y)
      filter_upwards [hp] with z hz
      rw [hz, pmf_tail]
    · intro f hf y x
      rw [hF]
      apply h1 μ Y X hY hX y x (fun z => ∫ v in Iic y, f v z)
      filter_upwards [hf] with z hz
      exact (pdf_tail _ _ hz y).symm
  · intro n K τ hn Θ p Y X t _hfit
    exact fitted_display hn X _ (fun _ => inferInstance) _ (fun i y => pmf_tail _ y)
  · intro n K τ hn Θ g ν hprob hpdf Y X t hfit
    apply fitted_display hn X _ (fun i => hprob (X i) t hfit.1)
    intro i y
    have := hprob (X i) t hfit.1
    exact pdf_tail _ _ (hpdf (X i) t hfit.1) y

private theorem bounded_integrable {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (a b : ℝ) (hb : ∀ᵐ ω ∂μ, f ω ∈ Icc a b) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable (max |a| |b|)
  filter_upwards [hb] with ω hω
  exact abs_le_max_abs_abs hω.1 hω.2

/-- Add endpoint conditional-mean formulas, finite expectations, observable-law
preservation and the explicit six-unit arithmetic to the sharpness leaf. -/
theorem T80_assembly (h1 : T80_L1.{u}) : T80WholeStatement.{u} := by
  constructor
  · intro Ω _ μ _ Y R hY hR a b hab hbound hbinary _hp0 hp1
    let Ys := fun ω => recordedOutcome (Y ω) (R ω)
    have hYs : Measurable Ys := by dsimp [Ys, recordedOutcome]; fun_prop
    have hYi := bounded_integrable μ Y hY a b hbound
    have hYsi : Integrable Ys μ := by
      apply bounded_integrable μ Ys hYs (min a (-99)) (max b (-99))
      filter_upwards [hbound, hbinary] with ω hy hr
      rcases hr with hr | hr
      · simpa only [Ys, recordedOutcome, hr, mul_zero, sub_zero, mul_one, zero_add] using
          (show (-99 : ℝ) ∈ Icc (min a (-99)) (max b (-99)) from
            ⟨min_le_right _ _, le_max_right _ _⟩)
      · simpa [Ys, recordedOutcome, hr] using
          (show Y ω ∈ Icc (min a (-99)) (max b (-99)) from
            ⟨(min_le_left _ _).trans hy.1, hy.2.trans (le_max_left _ _)⟩)
    have hendpoint (c : ℝ) (hc : c ∈ Icc a b) :
        Integrable (fun ω => completeMissing (Ys ω) (R ω) c) μ := by
      apply bounded_integrable μ _ (by dsimp [Ys, completeMissing, recordedOutcome]; fun_prop) a b
      filter_upwards [hbound, hbinary] with ω hy hr
      rcases hr with hr | hr <;> simpa [Ys, completeMissing, recordedOutcome, hr] using (by
        first | exact hc | exact hy)
    have hli := hendpoint a ⟨le_rfl, hab⟩
    have hui := hendpoint b ⟨hab, le_rfl⟩
    have hfa := AronowAudit.P001.Wave1.bounds_endpoint_formula μ Ys R a hR hbinary hli hp1
    have hfb := AronowAudit.P001.Wave1.bounds_endpoint_formula μ Ys R b hR hbinary hui hp1
    obtain ⟨hlo, hup, hsharp⟩ := h1 μ Y R hY hR a b hab hbound hbinary
    change expectation μ (fun ω => completeMissing (Ys ω) (R ω) a) =
      W1respondentMean μ Ys R*probability μ {ω | R ω = 1}+a*probability μ {ω | R ω = 0} at hfa
    change expectation μ (fun ω => completeMissing (Ys ω) (R ω) b) =
      W1respondentMean μ Ys R*probability μ {ω | R ω = 1}+b*probability μ {ω | R ω = 0} at hfb
    refine ⟨hYi, hYsi, hli, hui, hfa, hfb, ?_, ?_, ?_⟩
    · rw [← hfa]; exact hlo
    · rw [← hfb]; exact hup
    · intro c hc
      rw [← hfa, ← hfb] at hc
      obtain ⟨Y', hm, hb, he, hrecord⟩ := hsharp c hc
      refine ⟨Y', hm, ae_of_all _ hb, bounded_integrable μ Y' hm a b (ae_of_all _ hb),
        he, hrecord, ?_⟩
      apply Measure.map_congr
      filter_upwards [hrecord] with ω hω
      exact congrArg (fun z => (z, R ω)) hω
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext i; fin_cases i <;> norm_num [completeMissing, boundsRecorded, boundsResponse]
    · ext i; fin_cases i <;> norm_num [completeMissing, boundsRecorded, boundsResponse]
    · exact AronowAudit.P001.missing_data_bounds_example
    · norm_num [completeMissing, boundsRecorded, boundsResponse, Fin.sum_univ_succ]
    · norm_num [completeMissing, boundsRecorded, boundsResponse, Fin.sum_univ_succ]

/-- Use repaired versions in the proved MAR donor and transport back. The
uniform lower bound also supplies an integrable dominating multiple of |Y|. -/
theorem T83_assembly (h1 : T83_L1.{u,v}) : T83WholeStatement.{u,v} := by
  intro Ω E _ _ μ _ X hX Y R hY hR hYi hbinary _hp0 _hp1 p hp hpos hmar
  obtain ⟨R0, p0, hR0, hb0, heR, hep, hp0, hpos0, hmar0⟩ :=
    h1 μ X hX Y R hR hbinary p hp hpos hmar
  have hid := AronowAudit.P001.Wave1.mar_reweighting_corrected_hypothesis_proof
    μ X hX Y R0 hY hR0 hYi hb0 p0 hp0 hpos0 hmar0
  have heweight : (fun ω => recordedOutcome (Y ω) (R0 ω)*R0 ω/p0 (X ω)) =ᵐ[μ]
      (fun ω => recordedOutcome (Y ω) (R ω)*R ω/p (X ω)) := by
    filter_upwards [heR, hep] with ω hr hpω
    rw [hr, hpω]
  have hstable : (fun ω => Y ω*R ω/p (X ω)) =ᵐ[μ]
      (fun ω => recordedOutcome (Y ω) (R ω)*R ω/p (X ω)) := by
    filter_upwards [hbinary] with ω hr
    rcases hr with hr | hr <;> simp [recordedOutcome, hr]
  obtain ⟨ε, hε, hb⟩ := hpos
  have hw : Integrable (fun ω => Y ω*(R ω/p (X ω))) μ := by
    apply hYi.mul_bdd (c := 1/ε) (hR.div (hp.1.comp hX)).aestronglyMeasurable
    filter_upwards [hbinary, hb] with ω hr hpω
    change ‖R ω/p (X ω)‖ ≤ 1/ε
    rcases hr with hr | hr
    · simp only [hr, zero_div, norm_zero]; positivity
    · rw [hr, Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one (hε.trans hpω))]
      exact div_le_div₀ (by norm_num) le_rfl hε hpω.le
  have hwi : Integrable (fun ω => Y ω*R ω/p (X ω)) μ := by
    simpa only [div_eq_mul_inv, mul_assoc] using hw
  refine ⟨hwi.congr hstable, ?_, ?_⟩
  · exact hid.trans (integral_congr_ae heweight)
  · exact (integral_congr_ae hstable).symm

end
end SAP.P001e.WH.W1
