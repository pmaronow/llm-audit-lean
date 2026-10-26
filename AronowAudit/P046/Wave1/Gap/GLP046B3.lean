import AronowAudit.P046.Wave1.Gap.GP046B3
import AronowAudit.P046.Wave1.Gap.GP046B5

/-!
The fixed-predictor variance identity for P046-T5.  The conditional binary
moments are integrated using the already proved propensity and XY transfer
lemmas.  All second-moment expansions have explicit integrability proofs.
-/

namespace AronowAudit.P046.Wave1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

/-- Positivity permits multiplying an integrable function by any fixed
natural power of the reciprocal propensity. -/
lemma fixed_variance_inv_integrable (M : Study) (hM : ValidStudy M)
    {f : Unit → ℝ} (hf : Integrable f M.law) (k : ℕ) :
    Integrable (fun o => (M.pi (W o))⁻¹ ^ k * f o) M.law := by
  apply hf.bdd_mul
    (((hM.measurable_pi.comp measurable_fst).inv.pow_const k).aestronglyMeasurable)
  filter_upwards [rcheb_pi_bounds M hM] with o ho
  simpa only [Real.norm_eq_abs, abs_pow, Pi.inv_apply, Function.comp_apply, W] using
    pow_le_pow_left₀ (abs_nonneg _) ho.2.2.1 k

/-- The adjusted summand is genuinely square integrable and has mean mu. -/
lemma fixed_variance_summand_facts (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (mg : Measurable g) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    let f := fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))
    MemLp f 2 M.law ∧ (∫ o, f o ∂M.law) = mu M := by
  letI := hM.probability
  have heq : (fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))) =
      (fun o => htTerm (M.pi (W o)) (X o) (Y o) +
        (1 - X o / M.pi (W o)) * g (W o)) := by
    funext o
    dsimp [adjustedTerm, htTerm]
    ring
  dsimp only
  rw [heq]
  have hl := rcheb_multiplier_L2 M hM g mg hg
  refine ⟨(ht_unit_memLp M hM).add hl, ?_⟩
  rw [integral_add (ht_unit_facts M hM).1 (hl.integrable (by norm_num)),
    (ht_unit_facts M hM).2,
    rcheb_multiplier_mean M hM g mg (hg.integrable (by norm_num)), add_zero]

/-- Averaging the binary treatment gives E[Z_g^2] = E[Y1^2] + R(g).
The coefficients contain only g, g squared, and bounded propensity weights. -/
lemma fixed_variance_second_moment (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (mg : Measurable g) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    (∫ o, (adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o)))^2 ∂M.law) =
      (∫ o, (Y1 o)^2 ∂M.law) + risk M g := by
  letI := hM.probability
  let a : ℝ → ℝ := fun w => (M.pi w)⁻¹^2 +
    2 * ((M.pi w)⁻¹ * g w) - 2 * ((M.pi w)⁻¹^2 * g w)
  let b : ℝ → ℝ := fun w => (M.pi w)⁻¹^2 * (g w)^2 -
    2 * ((M.pi w)⁻¹ * (g w)^2)
  have mpi := hM.measurable_pi
  have ma : Measurable a := by dsimp [a]; fun_prop
  have mb : Measurable b := by dsimp [b]; fun_prop
  have ig := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have ig1 : Integrable (fun o => (M.pi (W o))⁻¹ * g (W o)) M.law := by
    simpa only [pow_one] using fixed_variance_inv_integrable M hM ig 1
  have igsq1 : Integrable (fun o => (M.pi (W o))⁻¹ * (g (W o))^2) M.law := by
    simpa only [pow_one] using fixed_variance_inv_integrable M hM hg.integrable_sq 1
  have ia : Integrable (fun o => a (W o)) M.law := by
    have ii := fixed_variance_inv_integrable M hM (integrable_const (1 : ℝ)) 2
    simp only [mul_one] at ii
    exact (ii.fun_add (ig1.const_mul 2)).sub'
      ((fixed_variance_inv_integrable M hM ig 2).const_mul 2)
  have ib : Integrable (fun o => b (W o)) M.law :=
    (fixed_variance_inv_integrable M hM hg.integrable_sq 2).sub' (igsq1.const_mul 2)
  have mx := rcheb_measurable_X
  have my : Measurable Y1 := (measurable_of_countable bit).comp measurable_snd.snd.snd
  have mp : Measurable (fun o => M.pi (W o)) := mpi.comp measurable_fst
  have bx : ∀ᵐ o ∂M.law, ‖X o‖ ≤ 1 :=
    ae_of_all _ (fun o => by simpa only [Real.norm_eq_abs] using rcheb_X_bound o)
  have by1 : ∀ᵐ o ∂M.law, ‖Y1 o‖ ≤ 1 := ae_of_all _ (fun o => by
    cases hy : o.2.2.2 <;> simp [Y1, bit, hy])
  have bp : ∀ᵐ o ∂M.law, ‖M.pi (W o)‖ ≤ 1 := by
    filter_upwards [rcheb_pi_bounds M hM] with o ho
    simpa only [Real.norm_eq_abs, abs_of_pos ho.1] using ho.2.1.le
  have bxy : ∀ᵐ o ∂M.law, ‖X o * Y1 o‖ ≤ 1 := by
    filter_upwards [bx, by1] with o hx hy
    simpa only [norm_mul, mul_one] using
      mul_le_mul hx hy (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have bpy : ∀ᵐ o ∂M.law, ‖M.pi (W o) * Y1 o‖ ≤ 1 := by
    filter_upwards [bp, by1] with o hp hy
    simpa only [norm_mul, mul_one] using
      mul_le_mul hp hy (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have ixa : Integrable (fun o => a (W o) * (X o * Y1 o)) M.law :=
    ia.mul_bdd (mx.mul my).aestronglyMeasurable bxy
  have ixb : Integrable (fun o => b (W o) * X o) M.law :=
    ib.mul_bdd mx.aestronglyMeasurable bx
  have iap : Integrable (fun o => a (W o) * (M.pi (W o) * Y1 o)) M.law :=
    ia.mul_bdd (mp.mul my).aestronglyMeasurable bpy
  have ibp : Integrable (fun o => b (W o) * M.pi (W o)) M.law :=
    ib.mul_bdd mp.aestronglyMeasurable bp
  have hy := risk_expansion_y_memLp M hM
  have ir : Integrable (fun o => q M (W o) * (Y1 o - g (W o))^2) M.law :=
    risk_expansion_weighted_integrable M hM (hy.sub hg).integrable_sq
  have hsq : (fun o => (adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o)))^2) =
      (fun o => (g (W o))^2 + a (W o) * (X o * Y1 o) + b (W o) * X o) := by
    funext o
    have he : adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o)) =
        X o * Y1 o / M.pi (W o) + (1 - X o / M.pi (W o)) * g (W o) := by
      dsimp [adjustedTerm]
      rw [mul_sub, sub_div, consistency_treated]
      ring
    rw [he]
    cases hx : o.2.1 <;> cases ht : o.2.2.2 <;>
      simp [X, Y1, bit, hx, ht, a, b, div_eq_mul_inv] <;> ring
  rw [hsq, integral_add (hg.integrable_sq.fun_add ixa) ixb,
    integral_add hg.integrable_sq ixa,
    (population_criterion_transfer M hM a ma ia).2,
    (population_criterion_transfer M hM b mb ib).1,
    ← integral_add hg.integrable_sq iap,
    ← integral_add (hg.integrable_sq.fun_add iap) ibp]
  calc
    _ = ∫ o, (Y1 o)^2 + q M (W o) * (Y1 o - g (W o))^2 ∂M.law := by
      apply integral_congr_ae
      filter_upwards [hM.positivity] with o ho
      have hp : M.pi (W o) ≠ 0 := (hM.delta_pos.trans ho.1).ne'
      dsimp [a, b, q]
      cases ht : o.2.2.2 <;> simp [Y1, bit, ht] <;> field_simp [hp] <;> ring
    _ = _ := integral_add hy.integrable_sq ir

/-- The exact variance identity for a Borel predictor. -/
lemma fixed_variance_identity (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (mg : Measurable g) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    variance (fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))) M.law = V M g := by
  letI := hM.probability
  obtain ⟨hf, hmean⟩ := fixed_variance_summand_facts M hM g mg hg
  unfold V
  rw [variance_eq_sub hf, variance_eq_sub (risk_expansion_y_memLp M hM)]
  simp only [Pi.pow_apply]
  rw [fixed_variance_second_moment M hM g mg hg, hmean]
  unfold mu
  ring

/-- Conditional centering at m makes the weighted squared-error cross term
vanish.  This is the weighted regression Pythagoras identity. -/
lemma fixed_variance_risk_decomposition (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (mg : Measurable g) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    risk M g = risk M M.m +
      (∫ o, q M (W o) * (M.m (W o) - g (W o))^2 ∂M.law) := by
  letI := hM.probability
  have hm : covariateSigma ≤ (inferInstance : MeasurableSpace Unit) :=
    measurable_fst.comap_le
  letI : IsFiniteMeasure (M.law.trim hm) := isFiniteMeasure_trim hm
  have hml := p4d_regression_L2 M hM
  have sm : StronglyMeasurable[covariateSigma] (fun o => M.m (W o)) :=
    (hM.measurable_m.comp (comap_measurable W)).stronglyMeasurable
  have hy := risk_expansion_y_memLp M hM
  have my : Measurable Y1 := (measurable_of_countable bit).comp measurable_snd.snd.snd
  have mm : Measurable (fun o => M.m (W o)) := hM.measurable_m.comp measurable_fst
  have by1 : ∀ᵐ o ∂M.law, ‖Y1 o‖ ≤ 1 := ae_of_all _ (fun o => by
    cases ht : o.2.2.2 <;> simp [Y1, bit, ht])
  have bm : ∀ᵐ o ∂M.law, ‖M.m (W o)‖ ≤ 1 := by
    filter_upwards [hM.regression_range] with o ho
    simpa only [Real.norm_eq_abs, abs_of_nonneg ho.1] using ho.2
  let f : ℝ → ℝ := fun w => q M w * (M.m w - g w)
  have mf : Measurable f := by
    dsimp [f, q]
    exact ((measurable_const.sub hM.measurable_pi).div hM.measurable_pi).mul
      (hM.measurable_m.sub mg)
  have hfi : Integrable (fun o => f (W o)) M.law :=
    risk_expansion_weighted_integrable M hM ((hml.sub hg).integrable (by norm_num))
  have ify := hfi.mul_bdd my.aestronglyMeasurable by1
  have ifm := hfi.mul_bdd mm.aestronglyMeasurable bm
  have hce : condExp covariateSigma M.law Y1 =ᵐ[M.law]
      condExp covariateSigma M.law (fun o => M.m (W o)) := by
    rw [condExp_of_stronglyMeasurable hm sm (hml.integrable (by norm_num))]
    exact hM.regression
  have hc := population_criterion_integral_transfer M hM
    (fun o => f (W o)) Y1 (fun o => M.m (W o))
    (mf.comp (comap_measurable W)).stronglyMeasurable hfi my mm by1 bm hce
  have irm : Integrable (fun o => q M (W o) * (Y1 o - M.m (W o))^2) M.law :=
    risk_expansion_weighted_integrable M hM (hy.sub hml).integrable_sq
  have ie : Integrable (fun o => q M (W o) * (M.m (W o) - g (W o))^2) M.law :=
    risk_expansion_weighted_integrable M hM (hml.sub hg).integrable_sq
  have he : (fun o => q M (W o) * (Y1 o - g (W o))^2) =
      (fun o => q M (W o) * (Y1 o - M.m (W o))^2 +
        q M (W o) * (M.m (W o) - g (W o))^2 +
        2 * (f (W o) * Y1 o - f (W o) * M.m (W o))) := by
    funext o
    dsimp [f]
    ring
  unfold risk
  rw [he, integral_add (irm.fun_add ie) ((ify.sub' ifm).const_mul 2),
    integral_add irm ie, integral_const_mul, integral_sub ify ifm, hc,
    sub_self, mul_zero, add_zero]

/-- Both identities for a Borel predictor, using the proved true-regression
variance computation for the explicit Hahn formula. -/
lemma fixed_variance_borel (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (mg : Measurable g) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    variance (fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))) M.law = V M g ∧
    V M g = hahnBound M + (∫ o, q M (W o) * (M.m (W o) - g (W o))^2 ∂M.law) := by
  have hvm : V M M.m = hahnBound M :=
    (fixed_variance_identity M hM M.m hM.measurable_m (p4d_regression_L2 M hM)).symm.trans
      (p4d_summand_facts M hM).2.2
  refine ⟨fixed_variance_identity M hM g mg hg, ?_⟩
  calc
    V M g = V M M.m + (∫ o, q M (W o) * (M.m (W o) - g (W o))^2 ∂M.law) := by
      unfold V
      rw [fixed_variance_risk_decomposition M hM g mg hg]
      ring
    _ = _ := by rw [hvm]

/-- T5(a), T9(a): exact variance identity for a fixed square-integrable prediction. -/
theorem fixed_adjusted_variance_proof (M : Study) (hM : ValidStudy M)
    (g : ℝ → ℝ) (hg : MemLp (fun o => g (W o)) 2 M.law) :
    variance (fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g (W o))) M.law = V M g ∧
    V M g = hahnBound M + (∫ o, q M (W o) * (M.m (W o) - g (W o))^2 ∂M.law) := by
  obtain ⟨g0, mg0, heq⟩ := population_criterion_borel_version M g hg.aestronglyMeasurable
  have hg0 := hg.ae_eq heq
  have hb := fixed_variance_borel M hM g0 mg0 hg0
  have hv : V M g = V M g0 := by
    unfold V
    congr 1
    apply integral_congr_ae
    filter_upwards [heq] with o ho
    rw [ho]
  have he : (∫ o, q M (W o) * (M.m (W o) - g (W o))^2 ∂M.law) =
      (∫ o, q M (W o) * (M.m (W o) - g0 (W o))^2 ∂M.law) := by
    apply integral_congr_ae
    filter_upwards [heq] with o ho
    rw [ho]
  constructor
  · calc
      _ = variance (fun o => adjustedTerm (M.pi (W o)) (X o) (Y o) (g0 (W o))) M.law := by
        apply variance_congr
        filter_upwards [heq] with o ho
        rw [ho]
      _ = V M g0 := hb.1
      _ = V M g := hv.symm
  · rw [hv, he]
    exact hb.2

end
end AronowAudit.P046.Wave1
